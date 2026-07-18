/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SourceControl
import LeanWang.Kari.Hooper.CounterArithmetic
import Mathlib.Data.Finite.Sum

/-!
# Counter programs for one source-machine transition

This file compiles the three actions of the fixed source machine into the
four-register counter language.  The scanned symbol lives in finite control;
the two one-sided tape codes live in registers `left` and `right`; `temp` is
scratch space and is zero both before and after every compiled transition.

For a move, the program first pushes the old scanned symbol onto the opposite
stack, then divides the entered stack by the alphabet radix.  Division leaves
its remainder in a finite family of reserved control states.  A final clock
instruction dispatches that remainder to the next encoded state/symbol pair.
Thus one source transition increases `clock` exactly once, irrespective of
the amount of arithmetic work needed to implement it.
-/

noncomputable section

set_option maxRecDepth 10000

namespace LeanWang
namespace Kari
namespace Hooper
namespace SourceProgram

open Turing
open CounterMachine CounterProgram CounterArithmetic

abbrev Alphabet := SourceMachine.Alphabet

/-! ## Small linker lemmas -/

theorem lookupInstruction_append_of_some
    {first second : Program} {state : State} {instruction : Instruction}
    (hlookup : lookupInstruction first state = some instruction) :
    lookupInstruction (first ++ second) state = some instruction := by
  induction first with
  | nil => simp at hlookup
  | cons rule first ih =>
      rcases rule with ⟨source, headInstruction⟩
      by_cases hstate : state = source
      · subst source
        simpa [lookupInstruction] using hlookup
      · simp only [List.cons_append,
          lookupInstruction_cons_ne hstate] at hlookup ⊢
        exact ih hlookup

theorem lookupInstruction_append_of_none
    {first second : Program} {state : State}
    (hlookup : lookupInstruction first state = none) :
    lookupInstruction (first ++ second) state =
      lookupInstruction second state := by
  induction first with
  | nil => rfl
  | cons rule first ih =>
      rcases rule with ⟨source, headInstruction⟩
      have hstate : state ≠ source := by
        intro heq
        subst source
        simp at hlookup
      simp only [List.cons_append,
        lookupInstruction_cons_ne hstate] at hlookup ⊢
      exact ih hlookup

theorem step_append_left
    {first second : Program} {cfg next : Cfg}
    (hstep : step first cfg = some next) :
    step (first ++ second) cfg = some next := by
  unfold step at hstep ⊢
  cases hlookup : lookupInstruction first cfg.state with
  | none => simp [hlookup] at hstep
  | some instruction =>
      rw [hlookup] at hstep
      rw [lookupInstruction_append_of_some hlookup]
      exact hstep

theorem step_append_right_of_not_mem
    {first second : Program} {cfg next : Cfg}
    (hstate : cfg.state ∉ sourceStates first)
    (hstep : step second cfg = some next) :
    step (first ++ second) cfg = some next := by
  unfold step at hstep ⊢
  have hnone : lookupInstruction first cfg.state = none :=
    lookupInstruction_eq_none_of_not_mem hstate
  rw [lookupInstruction_append_of_none hnone]
  exact hstep

theorem source_mem_of_step_some
    {program : Program} {cfg next : Cfg}
    (hstep : step program cfg = some next) :
    cfg.state ∈ sourceStates program := by
  unfold step at hstep
  cases hlookup : lookupInstruction program cfg.state with
  | none => simp [hlookup] at hstep
  | some instruction =>
      exact List.mem_map.mpr
        ⟨(cfg.state, instruction),
          rule_mem_of_lookupInstruction_eq_some hlookup, rfl⟩

theorem reaches_append_left
    {first second : Program} {start finish : Cfg}
    (hreach : StateTransition.Reaches (step first) start finish) :
    StateTransition.Reaches (step (first ++ second)) start finish := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
      exact Relation.ReflTransGen.tail ih (step_append_left hstep)

theorem reaches_append_right_of_source_disjoint
    {first second : Program} {start finish : Cfg}
    (hdisjoint : List.Disjoint (sourceStates first) (sourceStates second))
    (hreach : StateTransition.Reaches (step second) start finish) :
    StateTransition.Reaches (step (first ++ second)) start finish := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
      apply Relation.ReflTransGen.tail ih
      apply step_append_right_of_not_mem
      · intro hfirst
        exact hdisjoint hfirst (source_mem_of_step_some hstep)
      · exact hstep

theorem instantiate_source_disjoint_of_before
    {first second : Block} (hfirst : first.WellFormed)
    (hsecond : second.WellFormed)
    {firstOffset secondOffset : State}
    (hbefore : firstOffset + first.width ≤ secondOffset) :
    List.Disjoint (sourceStates (first.instantiate firstOffset))
      (sourceStates (second.instantiate secondOffset)) := by
  rw [List.disjoint_iff_ne]
  intro left hleft right hright heq
  rcases Block.source_mem_instantiate hfirst hleft with
    ⟨_, hleftUpper⟩
  rcases Block.source_mem_instantiate hsecond hright with
    ⟨hrightLower, _⟩
  subst right
  exact (Nat.not_lt_of_ge (hbefore.trans hrightLower)) hleftUpper

private theorem disjoint_append_left
    {first second third : List State}
    (hfirst : List.Disjoint first third)
    (hsecond : List.Disjoint second third) :
    List.Disjoint (first ++ second) third := by
  rw [List.disjoint_iff_ne] at hfirst hsecond ⊢
  intro state hstate other hother heq
  rcases List.mem_append.mp hstate with hstate | hstate
  · exact hfirst state hstate other hother heq
  · exact hsecond state hstate other hother heq

/-! ## Logical register representation -/

/-- The source alphabet radix used by the generic stack encoding. -/
def radix : Nat := StackEncoding.base Alphabet

theorem radix_pos : 0 < radix :=
  StackEncoding.base_pos Alphabet

/-- Encode the finite source-control pair carried between arithmetic blocks. -/
def controlCode (state : SourceMachine.State) (head : Alphabet) : State :=
  SourceControl.encodeState state * SourceControl.numSymbols +
    SourceControl.symbolDigit head

/-- Put the two logical tape stacks into the physical counter registers. -/
def logicalRegisters
    (tape : StackEncoding.TapeRegisters Alphabet) (clock : Nat) : Registers where
  left := tape.left
  right := tape.right
  temp := 0
  clock := clock

@[simp]
theorem logicalRegisters_get_temp
    (tape : StackEncoding.TapeRegisters Alphabet) (clock : Nat) :
    (logicalRegisters tape clock).get .temp = 0 :=
  rfl

@[simp]
theorem logicalRegisters_increment_clock
    (tape : StackEncoding.TapeRegisters Alphabet) (clock : Nat) :
    (logicalRegisters tape clock).increment .clock =
      logicalRegisters tape (clock + 1) :=
  rfl

/-- Logical tape effect of one already-selected source action. -/
def actionTape (action : Turing.TM0.Stmt Alphabet)
    (tape : StackEncoding.TapeRegisters Alphabet) :
    StackEncoding.TapeRegisters Alphabet :=
  match action with
  | .move .left => tape.moveLeft
  | .move .right => tape.moveRight
  | .write a => tape.write a

/-! ## Arithmetic core of a head move -/

def pushRegister : Turing.Dir → Register
  | .left => .right
  | .right => .left

def popRegister : Turing.Dir → Register
  | .left => .left
  | .right => .right

def popValue (direction : Turing.Dir)
    (tape : StackEncoding.TapeRegisters Alphabet) : Nat :=
  match direction with
  | .left => tape.left
  | .right => tape.right

def multiplyWidth : Nat := radix + 3

def divisionOffset (head : Alphabet) : Nat :=
  multiplyWidth + StackEncoding.digit head

/-- Arithmetic program for a move, before the finite-control clock branch. -/
def moveCoreProgram (offset : State) (direction : Turing.Dir)
    (head : Alphabet) : Program :=
  ((multiplyFixedBlock (pushRegister direction) .temp radix).instantiate offset ++
    (addFixedBlock (pushRegister direction) (StackEncoding.digit head)).instantiate
      (offset + multiplyWidth)) ++
  (divideFixedBlock (popRegister direction) .temp radix).instantiate
      (offset + divisionOffset head)

/-- Reserved division exit reached by the arithmetic move core. -/
def moveCoreExit (offset : State) (head : Alphabet)
    (direction : Turing.Dir) (tape : StackEncoding.TapeRegisters Alphabet) : State :=
  offset + divisionOffset head +
    divisionExit radix (popValue direction tape % radix)

private theorem moveArithmeticResult
    (direction : Turing.Dir)
    (tape : StackEncoding.TapeRegisters Alphabet) (clock : Nat) :
    divideCleanResult (popRegister direction) .temp radix
      (addResult (pushRegister direction) (StackEncoding.digit tape.head)
        (multiplyCleanResult (pushRegister direction) .temp radix
          (logicalRegisters tape clock))) =
      logicalRegisters (actionTape (.move direction) tape) clock := by
  cases direction <;> cases tape <;>
    simp [divideCleanResult, addResult, multiplyCleanResult,
      logicalRegisters, actionTape, pushRegister, popRegister,
      StackEncoding.TapeRegisters.moveLeft,
      StackEncoding.TapeRegisters.moveRight,
      StackEncoding.push, StackEncoding.pop, radix,
      Registers.get, Registers.set] <;> omega

/-- Exact arithmetic simulation of a head move.  The remainder exit records
the new scanned symbol; scratch is restored to zero and the clock is unchanged. -/
theorem moveCore_reaches (offset : State) (direction : Turing.Dir)
    (tape : StackEncoding.TapeRegisters Alphabet) (clock : Nat) :
    StateTransition.Reaches
      (step (moveCoreProgram offset direction tape.head))
      ⟨offset, logicalRegisters tape clock⟩
      ⟨moveCoreExit offset tape.head direction tape,
        logicalRegisters (actionTape (.move direction) tape) clock⟩ := by
  let multiplyBlock :=
    multiplyFixedBlock (pushRegister direction) .temp radix
  let addBlock :=
    addFixedBlock (pushRegister direction) (StackEncoding.digit tape.head)
  let divideBlock :=
    divideFixedBlock (popRegister direction) .temp radix
  let multiplyProgram := multiplyBlock.instantiate offset
  let addProgram := addBlock.instantiate (offset + multiplyWidth)
  let divideProgram := divideBlock.instantiate
    (offset + divisionOffset tape.head)
  let initial := logicalRegisters tape clock
  let afterMultiply := multiplyCleanResult
    (pushRegister direction) .temp radix initial
  let afterAdd := addResult (pushRegister direction)
    (StackEncoding.digit tape.head) afterMultiply
  have hregistersDistinct : pushRegister direction ≠ Register.temp := by
    cases direction <;> decide
  have hpopDistinct : popRegister direction ≠ Register.temp := by
    cases direction <;> decide
  have hmultiply : StateTransition.Reaches (step multiplyProgram)
      ⟨offset, initial⟩
      ⟨offset + multiplyWidth, afterMultiply⟩ := by
    simpa [multiplyProgram, multiplyBlock, multiplyWidth, afterMultiply,
      initial] using
      (multiplyFixed_reaches_of_temp_zero hregistersDistinct radix_pos offset
        initial (logicalRegisters_get_temp tape clock))
  have hadd : StateTransition.Reaches (step addProgram)
      ⟨offset + multiplyWidth, afterMultiply⟩
      ⟨offset + divisionOffset tape.head, afterAdd⟩ := by
    simpa [addProgram, addBlock, divisionOffset, afterAdd,
      Nat.add_assoc] using
      (addFixed_reaches (pushRegister direction)
        (StackEncoding.digit tape.head) (offset + multiplyWidth) afterMultiply)
  have htempAfterMultiply : afterMultiply.get .temp = 0 := by
    dsimp [afterMultiply, initial]
    exact multiplyCleanResult_get_temp hregistersDistinct radix _
  have htempAfterAdd : afterAdd.get .temp = 0 := by
    dsimp [afterAdd]
    exact addResult_get_other (by
      cases direction <;> decide) _ afterMultiply |>.trans htempAfterMultiply
  have hdivide : StateTransition.Reaches (step divideProgram)
      ⟨offset + divisionOffset tape.head, afterAdd⟩
      ⟨moveCoreExit offset tape.head direction tape,
        divideCleanResult (popRegister direction) .temp radix afterAdd⟩ := by
    have hpop : afterAdd.get (popRegister direction) =
        popValue direction tape := by
      cases direction <;> cases tape <;>
        simp [afterAdd, afterMultiply, initial, popValue, pushRegister,
          popRegister, addResult, multiplyCleanResult, logicalRegisters,
          Registers.get, Registers.set]
    have h := divideFixed_reaches_of_temp_zero hpopDistinct radix_pos
      (offset + divisionOffset tape.head) afterAdd htempAfterAdd
    rw [hpop] at h
    simpa [divideProgram, moveCoreExit, Nat.add_assoc] using h
  have hmultiplyAdd : StateTransition.Reaches
      (step (multiplyProgram ++ addProgram))
      ⟨offset, initial⟩
      ⟨offset + divisionOffset tape.head, afterAdd⟩ := by
    have hmulFull := reaches_append_left (second := addProgram) hmultiply
    have hdisjoint := instantiate_source_disjoint_of_before
      (multiplyFixedBlock_wellFormed
        (pushRegister direction) .temp radix)
      (addFixedBlock_wellFormed (pushRegister direction)
        (StackEncoding.digit tape.head))
      (firstOffset := offset) (secondOffset := offset + multiplyWidth)
      (by simp [multiplyWidth])
    have haddFull := reaches_append_right_of_source_disjoint hdisjoint hadd
    exact hmulFull.trans haddFull
  have hmulDiv := instantiate_source_disjoint_of_before
    (multiplyFixedBlock_wellFormed (pushRegister direction) .temp radix)
    (divideFixedBlock_wellFormed (popRegister direction) .temp radix)
    (firstOffset := offset)
    (secondOffset := offset + divisionOffset tape.head) (by
      simp [multiplyWidth, divisionOffset])
  have haddDiv := instantiate_source_disjoint_of_before
    (addFixedBlock_wellFormed (pushRegister direction)
      (StackEncoding.digit tape.head))
    (divideFixedBlock_wellFormed (popRegister direction) .temp radix)
    (firstOffset := offset + multiplyWidth)
    (secondOffset := offset + divisionOffset tape.head) (by
      simp [divisionOffset, Nat.add_assoc])
  have hprefixDiv : List.Disjoint
      (sourceStates (multiplyProgram ++ addProgram))
      (sourceStates divideProgram) := by
    rw [sourceStates_append]
    exact disjoint_append_left hmulDiv haddDiv
  have hdivideFull :=
    reaches_append_right_of_source_disjoint hprefixDiv hdivide
  have hall := (reaches_append_left (second := divideProgram) hmultiplyAdd).trans
    hdivideFull
  rw [moveArithmeticResult direction tape clock] at hall
  change StateTransition.Reaches
    (step (moveCoreProgram offset direction tape.head))
    ⟨offset, logicalRegisters tape clock⟩
    ⟨moveCoreExit offset tape.head direction tape,
      logicalRegisters (actionTape (.move direction) tape) clock⟩ at hall
  exact hall

/-! ## Remainder dispatch and complete actions -/

/-- One clock-and-control rule for each possible division remainder. -/
def moveDispatchProgram (offset : State) (head : Alphabet)
    (nextState : SourceMachine.State) : Program :=
  (List.range radix).map fun remainder =>
    (offset + divisionOffset head + divisionExit radix remainder,
      .increment .clock
        (controlCode nextState (StackEncoding.decodeDigit remainder)))

theorem moveDispatchProgram_deterministic
    (offset : State) (head : Alphabet) (nextState : SourceMachine.State) :
    Deterministic (moveDispatchProgram offset head nextState) := by
  rw [Deterministic]
  simp only [moveDispatchProgram, sourceStates, List.map_map]
  exact List.nodup_range.map fun left right heq => by
    simp only [Function.comp_apply] at heq
    simp [divisionExit] at heq
    omega

theorem lookup_moveDispatchProgram
    (offset : State) (head : Alphabet) (nextState : SourceMachine.State)
    {remainder : Nat} (hremainder : remainder < radix) :
    lookupInstruction (moveDispatchProgram offset head nextState)
        (offset + divisionOffset head + divisionExit radix remainder) =
      some (.increment .clock
        (controlCode nextState (StackEncoding.decodeDigit remainder))) := by
  apply (lookupInstruction_eq_some_iff_of_deterministic
    (moveDispatchProgram_deterministic offset head nextState)).2
  apply List.mem_map.mpr
  exact ⟨remainder, List.mem_range.mpr hremainder, rfl⟩

theorem moveCoreExit_not_source (offset : State) (head : Alphabet)
    (direction : Turing.Dir) (tape : StackEncoding.TapeRegisters Alphabet) :
    moveCoreExit offset head direction tape ∉
      sourceStates (moveCoreProgram offset direction head) := by
  intro hsource
  change moveCoreExit offset head direction tape ∈
    sourceStates
      (((multiplyFixedBlock (pushRegister direction) .temp radix).instantiate offset ++
        (addFixedBlock (pushRegister direction)
          (StackEncoding.digit head)).instantiate
            (offset + multiplyWidth)) ++
        (divideFixedBlock (popRegister direction) .temp radix).instantiate
          (offset + divisionOffset head)) at hsource
  rw [sourceStates_append, sourceStates_append] at hsource
  rcases List.mem_append.mp hsource with hprefix | hdivide
  · rcases List.mem_append.mp hprefix with hmultiply | hadd
    · rcases Block.source_mem_instantiate
        (multiplyFixedBlock_wellFormed (pushRegister direction) .temp radix)
        hmultiply with ⟨_, hupper⟩
      apply (Nat.not_lt_of_ge ?_) hupper
      dsimp [moveCoreExit, divisionOffset, multiplyWidth]
      omega
    · rcases Block.source_mem_instantiate
        (addFixedBlock_wellFormed (pushRegister direction)
          (StackEncoding.digit head)) hadd with ⟨_, hupper⟩
      apply (Nat.not_lt_of_ge ?_) hupper
      dsimp [moveCoreExit, divisionOffset, multiplyWidth]
      omega
  · rcases mem_sourceStates_relocate_iff.mp hdivide with
      ⟨localState, hlocal, heq⟩
    have hlocalEq : localState =
        divisionExit radix (popValue direction tape % radix) := by
      simpa [moveCoreExit, Nat.add_assoc] using heq.symm
    subst localState
    exact divisionExit_not_source
      (Nat.mod_lt _ radix_pos) hlocal

/-- Compile one already-selected source action at a fresh entry state. -/
def compileAction (offset : State) (nextState : SourceMachine.State)
    (head : Alphabet) (action : Turing.TM0.Stmt Alphabet) : Program :=
  match action with
  | .move direction =>
      moveCoreProgram offset direction head ++
        moveDispatchProgram offset head nextState
  | .write a =>
      [(offset, .increment .clock (controlCode nextState a))]

/-- Exact action-level simulation.  A completed source action restores
scratch, updates the finite-control state/scanned symbol, and ticks once. -/
theorem compileAction_reaches (offset : State)
    (nextState : SourceMachine.State) (action : Turing.TM0.Stmt Alphabet)
    (tape : StackEncoding.TapeRegisters Alphabet) (clock : Nat) :
    StateTransition.Reaches
      (step (compileAction offset nextState tape.head action))
      ⟨offset, logicalRegisters tape clock⟩
      ⟨controlCode nextState (actionTape action tape).head,
        logicalRegisters (actionTape action tape) (clock + 1)⟩ := by
  cases action with
  | write a =>
      apply Relation.ReflTransGen.single
      simp [compileAction, actionTape, logicalRegisters, controlCode,
        StackEncoding.TapeRegisters.write, step,
        Registers.increment, Registers.get, Registers.set]
  | move direction =>
      have hcore := moveCore_reaches offset direction tape clock
      have hcoreFull := reaches_append_left
        (second := moveDispatchProgram offset tape.head nextState) hcore
      let remainder := popValue direction tape % radix
      have hremainder : remainder < radix := Nat.mod_lt _ radix_pos
      have hcoreNone : lookupInstruction
          (moveCoreProgram offset direction tape.head)
          (moveCoreExit offset tape.head direction tape) = none :=
        lookupInstruction_eq_none_of_not_mem
          (moveCoreExit_not_source offset tape.head direction tape)
      have hdispatchLookup : lookupInstruction
          (compileAction offset nextState tape.head (.move direction))
          (moveCoreExit offset tape.head direction tape) =
        some (.increment .clock
          (controlCode nextState (StackEncoding.decodeDigit remainder))) := by
        simp only [compileAction]
        rw [lookupInstruction_append_of_none hcoreNone]
        exact lookup_moveDispatchProgram offset tape.head nextState hremainder
      have hdispatch : step
          (compileAction offset nextState tape.head (.move direction))
          ⟨moveCoreExit offset tape.head direction tape,
            logicalRegisters (actionTape (.move direction) tape) clock⟩ =
        some ⟨controlCode nextState
            (StackEncoding.decodeDigit remainder),
          logicalRegisters (actionTape (.move direction) tape) (clock + 1)⟩ := by
        simpa using step_of_lookup_increment
          (cfg := ⟨moveCoreExit offset tape.head direction tape,
            logicalRegisters (actionTape (.move direction) tape) clock⟩)
          hdispatchLookup
      have hall := Relation.ReflTransGen.tail hcoreFull hdispatch
      have hhead : (actionTape (.move direction) tape).head =
          StackEncoding.decodeDigit remainder := by
        cases direction <;>
          simp [actionTape, StackEncoding.TapeRegisters.moveLeft,
            StackEncoding.TapeRegisters.moveRight, StackEncoding.top,
            remainder, popValue, radix]
      rw [hhead]
      exact hall

/-! ## A defined high-level source step -/

/-- Compile the source transition selected by one high-level register
configuration.  Halting configurations compile to the empty program. -/
def compileDefinedStep (offset : State) (cfg : SourceControl.RegisterCfg) : Program :=
  match SourceMachine.machine cfg.state cfg.tape.head with
  | none => []
  | some (nextState, action) =>
      compileAction offset nextState cfg.tape.head action

/-- Every defined `SourceControl.registerStep` is exactly simulated by its
finite four-register program. -/
theorem compileDefinedStep_reaches (offset : State)
    {cfg nextCfg : SourceControl.RegisterCfg}
    (hstep : SourceControl.registerStep cfg = some nextCfg)
    (clock : Nat) :
    StateTransition.Reaches
      (step (compileDefinedStep offset cfg))
      ⟨offset, logicalRegisters cfg.tape clock⟩
      ⟨controlCode nextCfg.state nextCfg.tape.head,
        logicalRegisters nextCfg.tape (clock + 1)⟩ := by
  rcases cfg with ⟨state, tape⟩
  simp only [SourceControl.registerStep] at hstep
  cases hmachine : SourceMachine.machine state tape.head with
  | none => simp [hmachine] at hstep
  | some result =>
      rcases result with ⟨nextState, action⟩
      simp only [hmachine, Option.map_some, Option.some.injEq] at hstep
      subst nextCfg
      simp only [compileDefinedStep, hmachine]
      change StateTransition.Reaches
        (step (compileAction offset nextState tape.head action))
        ⟨offset, logicalRegisters tape clock⟩
        ⟨controlCode nextState (actionTape action tape).head,
          logicalRegisters (actionTape action tape) (clock + 1)⟩
      exact compileAction_reaches offset nextState action tape clock

/-- At offset zero, compiling a selected finite action is computable. -/
theorem compileActionZero_computable :
    Computable fun input :
        SourceMachine.State × Alphabet × Turing.TM0.Stmt Alphabet =>
      compileAction 0 input.1 input.2.1 input.2.2 := by
  letI : Finite (FiniteTM0.Action SourceControl.numSymbols) :=
    Finite.of_injective FiniteTM0.Action.equivCode
      FiniteTM0.Action.equivCode.injective
  letI : Finite (Turing.TM0.Stmt Alphabet) :=
    Finite.of_injective SourceControl.encodeAction
      SourceControl.actionEquiv.injective
  exact (Primrec.dom_finite _).to_comp

end SourceProgram
end Hooper
end Kari
end LeanWang
