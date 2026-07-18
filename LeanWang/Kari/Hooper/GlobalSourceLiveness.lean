/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.CounterArithmeticLiveness
import LeanWang.Kari.Hooper.CounterLiveness
import LeanWang.Kari.Hooper.GlobalSourceProgram
import LeanWang.Kari.Hooper.GlobalSourceSemantics

/-!
# Arbitrary-entry liveness of the global source program

This file discharges the finite-control liveness obligation for the one
global counter program.  Its logical states are exactly the canonical encoded
source state/symbol pairs.  From any private arithmetic state, arbitrary
register values eventually reach a canonical state.  From a canonical state,
one source action either completes and increments `clock` exactly once or the
source transition is undefined and the counter program halts.
-/

noncomputable section

set_option maxRecDepth 10000

namespace LeanWang
namespace Kari
namespace Hooper
namespace GlobalSourceLiveness

open Turing
open CounterMachine CounterProgram CounterArithmetic
open CounterArithmeticLiveness SourceProgram GlobalSourceProgram

abbrev SourceKey := SourceControl.SourceKey
abbrev Alphabet := SourceMachine.Alphabet

/-! ## Logical states and generic linker lemmas -/

/-- The finite list of all canonical source state/symbol control codes. -/
def logicalStates : List State :=
  SourceControl.sourceKeys.map fun key =>
    controlCode (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2)

theorem controlCode_mem_logicalStates
    (state : SourceMachine.State) (head : Alphabet) :
    controlCode state head ∈ logicalStates := by
  let key : SourceKey :=
    (SourceControl.encodeStateFin state, SourceControl.encodeSymbol head)
  apply List.mem_map.mpr
  refine ⟨key, SourceControl.mem_sourceKeys _ _, ?_⟩
  simp [key]

theorem keyControl_mem_logicalStates (key : SourceKey) :
    controlCode (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) ∈ logicalStates :=
  controlCode_mem_logicalStates _ _

/-- The designated encoded source input is already a logical-cycle boundary
of the global counter program. -/
theorem canonicalCounterCfg_isLogical (c : Nat.Partrec.Code) :
    CounterLiveness.IsLogical logicalStates
      (GlobalSourceSemantics.canonicalCounterCfg c) := by
  change controlCode (SourceRegisterSemantics.canonical c).state
      (SourceRegisterSemantics.canonical c).tape.head ∈ logicalStates
  exact controlCode_mem_logicalStates _ _

private theorem step_of_subprogram
    {small large : Program} (hlarge : Deterministic large)
    (hsubset : ∀ rule ∈ small, rule ∈ large)
    {cfg next : Cfg} (hstep : step small cfg = some next) :
    step large cfg = some next := by
  unfold step at hstep ⊢
  cases hlookup : lookupInstruction small cfg.state with
  | none => simp [hlookup] at hstep
  | some instruction =>
      have hrule := rule_mem_of_lookupInstruction_eq_some hlookup
      have hlargeLookup :=
        (lookupInstruction_eq_some_iff_of_deterministic hlarge).2
          (hsubset _ hrule)
      rw [hlargeLookup]
      rw [hlookup] at hstep
      exact hstep

private theorem reaches_of_subprogram
    {small large : Program} (hlarge : Deterministic large)
    (hsubset : ∀ rule ∈ small, rule ∈ large)
    {start finish : Cfg}
    (hreach : StateTransition.Reaches (step small) start finish) :
    StateTransition.Reaches (step large) start finish := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
      apply Relation.ReflTransGen.tail ih
      apply step_of_subprogram hlarge hsubset
      simpa using hstep

private theorem haltsFrom_of_step_none {program : Program} {cfg : Cfg}
    (hstep : step program cfg = none) :
    CounterLiveness.HaltsFrom program cfg :=
  ⟨cfg, Relation.ReflTransGen.refl, hstep⟩

private theorem source_mem_program_iff {state : State} :
    state ∈ sourceStates program ↔
      ∃ key ∈ SourceControl.sourceKeys,
        state ∈ sourceStates (keyProgram key) := by
  simp [program, sourceStates, List.map_flatMap, List.mem_flatMap]

private theorem compileAction_subset_program
    (key : SourceKey) {nextState : SourceMachine.State}
    {action : Turing.TM0.Stmt Alphabet}
    (hmachine : SourceMachine.machine
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) = some (nextState, action)) :
    ∀ rule ∈ compileAction (actionOffset key) nextState
        (SourceControl.decodeSymbol key.2) action,
      rule ∈ program := by
  intro rule hrule
  apply keyProgram_subset_program key
  simp [keyProgram, hmachine, hrule]

/-! ## Arbitrary-entry execution of one compiled action -/

private theorem dispatch_reaches_logical
    (offset : State) (nextState : SourceMachine.State) (head : Alphabet)
    (direction : Turing.Dir) (remainder : Nat) (hremainder : remainder < radix)
    (registers : Registers) :
    ∃ finish,
      StateTransition.Reaches
        (step (compileAction offset nextState head (.move direction)))
        ⟨offset + divisionOffset head + divisionExit radix remainder,
          registers⟩ finish ∧
      finish.state ∈ logicalStates ∧
      finish.registers.clock = registers.clock + 1 := by
  let finish : Cfg :=
    ⟨controlCode nextState (StackEncoding.decodeDigit remainder),
      registers.increment .clock⟩
  have hdispatch : step (moveDispatchProgram offset head nextState)
      ⟨offset + divisionOffset head + divisionExit radix remainder,
        registers⟩ = some finish := by
    simpa [finish] using step_of_lookup_increment
      (lookup_moveDispatchProgram offset head nextState hremainder)
  have hreach : StateTransition.Reaches
      (step (moveDispatchProgram offset head nextState))
      ⟨offset + divisionOffset head + divisionExit radix remainder,
        registers⟩ finish :=
    Relation.ReflTransGen.single (by simpa using hdispatch)
  have hfull := reaches_of_subprogram
    (GlobalSourceProgram.compileAction_deterministic offset nextState head
      (.move direction)) (by
        intro rule hrule
        simp [compileAction, moveCoreProgram, hrule]) hreach
  refine ⟨finish, hfull, controlCode_mem_logicalStates _ _, ?_⟩
  simp [finish, Registers.increment, Registers.get, Registers.set]

private theorem divideState_reaches_logical
    (offset : State) (nextState : SourceMachine.State) (head : Alphabet)
    (direction : Turing.Dir) (localState : Nat)
    (hlocal : localState < divisionSourceCount radix)
    (registers : Registers) :
    ∃ finish,
      StateTransition.Reaches
        (step (compileAction offset nextState head (.move direction)))
        ⟨offset + divisionOffset head + localState, registers⟩ finish ∧
      finish.state ∈ logicalStates ∧
      finish.registers.clock = registers.clock + 1 := by
  have hdistinct : popRegister direction ≠ Register.temp := by
    cases direction <;> decide
  rcases divideFixed_reaches_from_source hdistinct radix_pos
      (offset + divisionOffset head) localState hlocal registers with
    ⟨remainder, middleRegisters, hremainder, hdivide⟩
  have hclock := clock_eq_of_reaches
    (divideFixed_avoidsClock (popRegister direction) .temp (by
      cases direction <;> decide) (by decide) radix
      (offset + divisionOffset head)) hdivide
  change middleRegisters.clock = registers.clock at hclock
  have hdivideFull := reaches_of_subprogram
    (GlobalSourceProgram.compileAction_deterministic offset nextState head
      (.move direction)) (by
        intro rule hrule
        simp [compileAction, moveCoreProgram, hrule]) hdivide
  rcases dispatch_reaches_logical offset nextState head direction remainder
      hremainder middleRegisters with
    ⟨finish, hdispatch, hlogical, hfinishClock⟩
  refine ⟨finish, hdivideFull.trans hdispatch, hlogical, ?_⟩
  omega

private theorem addState_reaches_logical
    (offset : State) (nextState : SourceMachine.State) (head : Alphabet)
    (direction : Turing.Dir) (localState : Nat)
    (hlocal : localState ≤ StackEncoding.digit head)
    (registers : Registers) :
    ∃ finish,
      StateTransition.Reaches
        (step (compileAction offset nextState head (.move direction)))
        ⟨offset + multiplyWidth + localState, registers⟩ finish ∧
      finish.state ∈ logicalStates ∧
      finish.registers.clock = registers.clock + 1 := by
  have hadd := addFixed_reaches_from (pushRegister direction)
    (StackEncoding.digit head) (offset + multiplyWidth) localState hlocal registers
  have hclock := clock_eq_of_reaches
    (addFixed_avoidsClock (pushRegister direction) (by
      cases direction <;> decide) _ _) hadd
  change (addResult (pushRegister direction)
    (StackEncoding.digit head - localState) registers).clock =
      registers.clock at hclock
  have haddFull := reaches_of_subprogram
    (GlobalSourceProgram.compileAction_deterministic offset nextState head
      (.move direction)) (by
        intro rule hrule
        simp [compileAction, moveCoreProgram, hrule]) hadd
  have hexit : offset + multiplyWidth + StackEncoding.digit head =
      offset + divisionOffset head := by
    simp [divisionOffset, Nat.add_assoc]
  rw [hexit] at haddFull
  rcases divideState_reaches_logical offset nextState head direction 0 (by
      simp [divisionSourceCount]) (addResult (pushRegister direction)
        (StackEncoding.digit head - localState) registers) with
    ⟨finish, hdivide, hlogical, hfinishClock⟩
  refine ⟨finish, haddFull.trans hdivide, hlogical, ?_⟩
  omega

private theorem multiplyState_reaches_logical
    (offset : State) (nextState : SourceMachine.State) (head : Alphabet)
    (direction : Turing.Dir) (localState : Nat)
    (hlocal : localState < radix + 3) (registers : Registers) :
    ∃ finish,
      StateTransition.Reaches
        (step (compileAction offset nextState head (.move direction)))
        ⟨offset + localState, registers⟩ finish ∧
      finish.state ∈ logicalStates ∧
      finish.registers.clock = registers.clock + 1 := by
  have hdistinct : pushRegister direction ≠ Register.temp := by
    cases direction <;> decide
  rcases multiplyFixed_reaches_from_source hdistinct radix_pos offset localState
      hlocal registers with ⟨middleRegisters, hmultiply⟩
  have hclock := clock_eq_of_reaches
    (multiplyFixed_avoidsClock (pushRegister direction) .temp (by
      cases direction <;> decide) (by decide) radix offset) hmultiply
  change middleRegisters.clock = registers.clock at hclock
  have hmultiplyFull := reaches_of_subprogram
    (GlobalSourceProgram.compileAction_deterministic offset nextState head
      (.move direction)) (by
        intro rule hrule
        simp [compileAction, moveCoreProgram, hrule]) hmultiply
  change StateTransition.Reaches
    (step (compileAction offset nextState head (.move direction)))
    ⟨offset + localState, registers⟩
    ⟨offset + multiplyWidth, middleRegisters⟩ at hmultiplyFull
  rcases addState_reaches_logical offset nextState head direction 0
      (Nat.zero_le _) middleRegisters with
    ⟨finish, hadd, hlogical, hfinishClock⟩
  refine ⟨finish, hmultiplyFull.trans hadd, hlogical, ?_⟩
  omega

/-- Every owned state of one compiled source action reaches a logical state
and increments the clock exactly once. -/
theorem compileAction_source_reaches_logical
    (offset : State) (nextState : SourceMachine.State) (head : Alphabet)
    (action : Turing.TM0.Stmt Alphabet) {start : Cfg}
    (hsource : start.state ∈ sourceStates
      (compileAction offset nextState head action)) :
    ∃ finish,
      StateTransition.Reaches
        (step (compileAction offset nextState head action)) start finish ∧
      finish.state ∈ logicalStates ∧
      finish.registers.clock = start.registers.clock + 1 := by
  rcases start with ⟨startState, registers⟩
  cases action with
  | write symbol =>
      have hstate : startState = offset := by
        simpa [compileAction, sourceStates] using hsource
      let finish : Cfg :=
        ⟨controlCode nextState symbol, registers.increment .clock⟩
      have hstep : step (compileAction offset nextState head (.write symbol))
          ⟨startState, registers⟩ = some finish := by
        subst startState
        simp [compileAction, finish, step]
      refine ⟨finish, Relation.ReflTransGen.single (by simpa using hstep),
        controlCode_mem_logicalStates _ _, ?_⟩
      simp [finish, Registers.increment, Registers.get, Registers.set]
  | move direction =>
      simp only [compileAction, sourceStates_append] at hsource
      rcases List.mem_append.mp hsource with hcore | hdispatch
      · simp only [moveCoreProgram, sourceStates_append] at hcore
        rcases List.mem_append.mp hcore with hprefix | hdivide
        · rcases List.mem_append.mp hprefix with hmultiply | hadd
          · rcases mem_sourceStates_relocate_iff.mp hmultiply with
              ⟨localState, hlocal, hstate⟩
            have hlocal' : localState < radix + 3 := by
              simpa [multiplyFixedBlock, denseBlock] using hlocal
            subst startState
            exact multiplyState_reaches_logical offset nextState head direction
              localState hlocal' registers
          · rcases mem_sourceStates_relocate_iff.mp hadd with
              ⟨localState, hlocal, hstate⟩
            have hlocal' : localState < StackEncoding.digit head := by
              simpa [addFixedBlock, denseBlock] using hlocal
            subst startState
            exact addState_reaches_logical offset nextState head direction
              localState (Nat.le_of_lt hlocal') registers
        · rcases mem_sourceStates_relocate_iff.mp hdivide with
            ⟨localState, hlocal, hstate⟩
          have hlocal' : localState < divisionSourceCount radix := by
            simpa [divideFixedBlock, denseBlock] using hlocal
          subst startState
          exact divideState_reaches_logical offset nextState head direction
            localState hlocal' registers
      · simp only [moveDispatchProgram, sourceStates, List.map_map,
          List.mem_map] at hdispatch
        rcases hdispatch with ⟨remainder, hremainder, hstate⟩
        have hremainder' : remainder < radix := List.mem_range.mp hremainder
        subst startState
        exact dispatch_reaches_logical offset nextState head direction
          remainder hremainder' registers

/-- Entry-state corollary, including zero-width fixed-addition blocks. -/
theorem compileAction_entry_reaches_logical
    (offset : State) (nextState : SourceMachine.State) (head : Alphabet)
    (action : Turing.TM0.Stmt Alphabet) (registers : Registers) :
    ∃ finish,
      StateTransition.Reaches
        (step (compileAction offset nextState head action))
        ⟨offset, registers⟩ finish ∧
      finish.state ∈ logicalStates ∧
      finish.registers.clock = registers.clock + 1 := by
  cases action with
  | write symbol =>
      apply compileAction_source_reaches_logical
      simp [compileAction, sourceStates]
  | move direction =>
      exact multiplyState_reaches_logical offset nextState head direction 0
        (by omega) registers

/-! ## Whole-program cycle laws -/

theorem canonical_not_source_of_machine_none
    (key : SourceKey)
    (hmachine : SourceMachine.machine
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) = none) :
    controlCode (SourceControl.decodeStateFin key.1)
        (SourceControl.decodeSymbol key.2) ∉ sourceStates program := by
  intro hsource
  rcases source_mem_program_iff.mp hsource with
    ⟨other, _hotherKeys, hotherSource⟩
  rcases source_mem_keyProgram hotherSource with hcanonical | hprivate
  · have hdecoded :
        (SourceControl.decodeStateFin other.1,
            SourceControl.decodeSymbol other.2) =
          (SourceControl.decodeStateFin key.1,
            SourceControl.decodeSymbol key.2) := by
      apply controlCode_injective
      exact hcanonical.symm
    have hother : other = key := decodeKey_injective hdecoded
    subst other
    simp [keyProgram, hmachine, sourceStates] at hotherSource
  · have hcontrol := controlCode_lt_span
        (SourceControl.decodeStateFin key.1)
        (SourceControl.decodeSymbol key.2)
    have hspanOffset : controlSpan ≤ actionOffset other :=
      Nat.le_add_right controlSpan (keyIndex other * actionStride)
    exact (Nat.not_lt_of_ge (hspanOffset.trans hprivate.1)) hcontrol

/-- A canonical counter configuration whose represented source transition is
undefined is terminal in the compiled global counter program. -/
theorem step_logical_eq_none_of_registerStep_none
    (cfg : SourceControl.RegisterCfg) (clock : Nat)
    (hterminal : SourceControl.registerStep cfg = none) :
    step program
      ⟨controlCode cfg.state cfg.tape.head,
        logicalRegisters cfg.tape clock⟩ = none := by
  have hmachine : SourceMachine.machine cfg.state cfg.tape.head = none := by
    simpa [SourceControl.registerStep] using hterminal
  let key : SourceKey :=
    (SourceControl.encodeStateFin cfg.state,
      SourceControl.encodeSymbol cfg.tape.head)
  apply step_eq_none_of_state_not_mem
  have hnot := canonical_not_source_of_machine_none key (by
    simpa [key] using hmachine)
  simpa [key] using hnot

/-- Every logical boundary either executes one complete source action and
ticks the clock, or is a genuine source halt. -/
theorem advance (start : Cfg)
    (hlogical : CounterLiveness.IsLogical logicalStates start) :
    (∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        CounterLiveness.IsLogical logicalStates finish ∧
          finish.registers.clock = start.registers.clock + 1) ∨
      CounterLiveness.HaltsFrom program start := by
  rcases List.mem_map.mp hlogical with ⟨key, _hkey, hstate⟩
  rcases start with ⟨startState, registers⟩
  have hstartState : startState = controlCode
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) := hstate.symm
  subst startState
  cases hmachine : SourceMachine.machine
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) with
  | none =>
      right
      apply haltsFrom_of_step_none
      apply step_eq_none_of_state_not_mem
      exact canonical_not_source_of_machine_none key hmachine
  | some result =>
      rcases result with ⟨nextState, action⟩
      left
      let afterRegisters := if registers.temp = 0 then
        registers else registers.decrement .temp
      let afterDispatch : Cfg := ⟨actionOffset key, afterRegisters⟩
      have hdispatchLocal : step (keyProgram key)
        ⟨controlCode (SourceControl.decodeStateFin key.1)
            (SourceControl.decodeSymbol key.2), registers⟩ =
        some afterDispatch := by
        by_cases htemp : registers.temp = 0 <;>
          simp [keyProgram, hmachine, afterDispatch, afterRegisters, htemp,
            step, Registers.get]
      have hdispatch : step program
          ⟨controlCode (SourceControl.decodeStateFin key.1)
            (SourceControl.decodeSymbol key.2), registers⟩ =
        some afterDispatch :=
        step_of_subprogram program_deterministic
          (keyProgram_subset_program key) hdispatchLocal
      have hdispatchReach : StateTransition.Reaches (step program)
          ⟨controlCode (SourceControl.decodeStateFin key.1)
            (SourceControl.decodeSymbol key.2), registers⟩ afterDispatch :=
        Relation.ReflTransGen.single (by simpa using hdispatch)
      rcases compileAction_entry_reaches_logical (actionOffset key) nextState
          (SourceControl.decodeSymbol key.2) action afterRegisters with
        ⟨finish, hactionLocal, hfinishLogical, hfinishClock⟩
      have haction := reaches_of_subprogram program_deterministic
        (compileAction_subset_program key hmachine) hactionLocal
      refine ⟨finish, hdispatchReach.trans haction,
        hfinishLogical, ?_⟩
      have hafterClock : afterRegisters.clock = registers.clock := by
        by_cases htemp : registers.temp = 0 <;>
          simp [afterRegisters, htemp, Registers.decrement,
            Registers.get, Registers.set]
      change finish.registers.clock = registers.clock + 1
      omega

/-- Every arbitrary program state either reaches a logical boundary or
reaches an immediate halt.  In particular, malformed arithmetic registers do
not create a private immortal orbit. -/
theorem settle (start : Cfg) :
    (∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        CounterLiveness.IsLogical logicalStates finish) ∨
      CounterLiveness.HaltsFrom program start := by
  by_cases hlogical : start.state ∈ logicalStates
  · left
    exact ⟨start, Relation.ReflTransGen.refl, hlogical⟩
  by_cases hsource : start.state ∈ sourceStates program
  · rcases source_mem_program_iff.mp hsource with
      ⟨key, _hkey, hkeySource⟩
    rcases source_mem_keyProgram hkeySource with hcanonical | hprivate
    · exfalso
      apply hlogical
      rw [hcanonical]
      exact keyControl_mem_logicalStates key
    · unfold keyProgram at hkeySource
      cases hmachine : SourceMachine.machine
          (SourceControl.decodeStateFin key.1)
          (SourceControl.decodeSymbol key.2) with
      | none => simp [hmachine, sourceStates] at hkeySource
      | some result =>
          rcases result with ⟨nextState, action⟩
          have hactionSource : start.state ∈ sourceStates
              (compileAction (actionOffset key) nextState
                (SourceControl.decodeSymbol key.2) action) := by
            simp only [hmachine, sourceStates, List.map_cons,
              List.mem_cons] at hkeySource
            rcases hkeySource with hcanonical | haction
            · exfalso
              apply hlogical
              rw [hcanonical]
              exact keyControl_mem_logicalStates key
            · exact haction
          rcases compileAction_source_reaches_logical (actionOffset key)
              nextState (SourceControl.decodeSymbol key.2) action hactionSource with
            ⟨finish, hlocalReach, hfinishLogical, _hclock⟩
          left
          exact ⟨finish,
            reaches_of_subprogram program_deterministic
              (compileAction_subset_program key hmachine) hlocalReach,
            hfinishLogical⟩
  · right
    exact haltsFrom_of_step_none (step_eq_none_of_state_not_mem hsource)

/-- Concrete cycle laws for the fixed global source program. -/
def cycleLaws : CounterLiveness.CycleLaws program where
  logicalStates := logicalStates
  deterministic := program_deterministic
  settle := settle
  advance := advance

end GlobalSourceLiveness
end Hooper
end Kari
end LeanWang
