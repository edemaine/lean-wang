/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SourceProgram

/-!
# One finite counter program for the complete fixed source machine

`SourceProgram` compiles one already-selected source transition.  This file
links every defined state/symbol transition of `SourceMachine.machine` into a
single deterministic four-register program.

Canonical state/symbol codes occupy a finite prefix of the counter control
space.  Every bounded state/symbol key owns one fixed-width private interval
above that prefix.  A canonical rule checks that `temp` is zero and enters the
key's private action code; the action returns directly to the canonical code
of the next state and scanned symbol.  The fixed-width allocation makes all
private source-state intervals disjoint without inspecting the transition
table's higher-order source states.
-/

noncomputable section

set_option maxRecDepth 10000

namespace LeanWang
namespace Kari
namespace Hooper
namespace GlobalSourceProgram

open Turing
open CounterMachine CounterProgram CounterArithmetic
open SourceProgram

abbrev Alphabet := SourceMachine.Alphabet
abbrev SourceKey := SourceControl.SourceKey

/-! ## Canonical and private control-state layout -/

/-- Size of the prefix containing every canonical state/symbol pair. -/
def controlSpan : Nat :=
  SourceControl.numStates * SourceControl.numSymbols

/-- Mixed-radix bounded index of one source state/symbol key. -/
def keyFin (key : SourceKey) : Fin controlSpan :=
  finProdFinEquiv key

def keyIndex (key : SourceKey) : Nat :=
  (keyFin key).val

theorem keyIndex_lt (key : SourceKey) : keyIndex key < controlSpan :=
  (keyFin key).isLt

theorem keyIndex_injective : Function.Injective keyIndex := by
  intro first second heq
  apply finProdFinEquiv.injective
  exact Fin.ext heq

/-- One uniform private interval is large enough for any compiled action. -/
def actionStride : Nat :=
  multiplyWidth + radix + divisionWidth radix

theorem actionStride_pos : 0 < actionStride := by
  have hradix := radix_pos
  unfold actionStride multiplyWidth
  omega

theorem multiplyWidth_le_actionStride : multiplyWidth ≤ actionStride := by
  unfold actionStride
  exact Nat.le_add_right multiplyWidth (radix + divisionWidth radix)

theorem divisionAllocation_le_actionStride (head : Alphabet) :
    divisionOffset head + divisionWidth radix ≤ actionStride := by
  have hdigit := Nat.le_of_lt (StackEncoding.digit_lt_base head)
  change StackEncoding.digit head ≤ radix at hdigit
  unfold divisionOffset actionStride
  exact Nat.add_le_add_right
    (Nat.add_le_add_left hdigit multiplyWidth) (divisionWidth radix)

theorem divisionOffset_le_actionStride (head : Alphabet) :
    divisionOffset head ≤ actionStride :=
  (Nat.le_add_right (divisionOffset head) (divisionWidth radix)).trans
    (divisionAllocation_le_actionStride head)

/-- Start of the private action interval owned by `key`. -/
def actionOffset (key : SourceKey) : State :=
  controlSpan + keyIndex key * actionStride

/-- Canonical control is the mixed-radix value of the encoded pair. -/
theorem controlCode_eq_keyIndex (state : SourceMachine.State)
    (head : Alphabet) :
    controlCode state head =
      keyIndex (SourceControl.encodeStateFin state,
        SourceControl.encodeSymbol head) := by
  simp [controlCode, keyIndex, keyFin, finProdFinEquiv,
    SourceControl.encodeState, SourceControl.symbolDigit,
    Nat.add_comm, Nat.mul_comm]

theorem controlCode_lt_span (state : SourceMachine.State) (head : Alphabet) :
    controlCode state head < controlSpan := by
  rw [controlCode_eq_keyIndex]
  exact keyIndex_lt _

theorem controlCode_injective :
    Function.Injective
      (fun pair : SourceMachine.State × Alphabet =>
        controlCode pair.1 pair.2) := by
  intro first second heq
  have hkeys :
      (SourceControl.encodeStateFin first.1,
          SourceControl.encodeSymbol first.2) =
        (SourceControl.encodeStateFin second.1,
          SourceControl.encodeSymbol second.2) := by
    apply keyIndex_injective
    simpa only [← controlCode_eq_keyIndex] using heq
  apply Prod.ext
  · exact SourceControl.encodeStateFin_injective
      (congrArg Prod.fst hkeys)
  · exact SourceControl.encodeSymbol_injective
      (congrArg Prod.snd hkeys)

theorem decodeKey_injective : Function.Injective
    (fun key : SourceKey =>
      (SourceControl.decodeStateFin key.1,
        SourceControl.decodeSymbol key.2)) := by
  intro first second heq
  apply Prod.ext
  · exact SourceControl.stateEquivFin.symm.injective
      (congrArg Prod.fst heq)
  · exact SourceControl.alphabetEquivFin.symm.injective
      (congrArg Prod.snd heq)

/-! ## Bounds and determinism of one private action -/

private theorem deterministic_append
    {first second : Program} (hfirst : Deterministic first)
    (hsecond : Deterministic second)
    (hdisjoint : List.Disjoint (sourceStates first) (sourceStates second)) :
    Deterministic (first ++ second) := by
  rw [Deterministic, sourceStates_append]
  exact List.Nodup.append hfirst hsecond hdisjoint

private theorem source_disjoint_of_intervals
    {first second : Program} {firstOffset firstWidth secondOffset : Nat}
    (hfirst : ∀ state ∈ sourceStates first,
      firstOffset ≤ state ∧ state < firstOffset + firstWidth)
    (hsecond : ∀ state ∈ sourceStates second, secondOffset ≤ state)
    (hbefore : firstOffset + firstWidth ≤ secondOffset) :
    List.Disjoint (sourceStates first) (sourceStates second) := by
  rw [List.disjoint_iff_ne]
  intro left hleft right hright heq
  rcases hfirst left hleft with ⟨_, hleftUpper⟩
  have hrightLower := hsecond right hright
  subst right
  exact (Nat.not_lt_of_ge (hbefore.trans hrightLower)) hleftUpper

theorem moveCoreProgram_deterministic (offset : State)
    (direction : Turing.Dir) (head : Alphabet) :
    Deterministic (moveCoreProgram offset direction head) := by
  let multiplyBlock :=
    multiplyFixedBlock (pushRegister direction) .temp radix
  let addBlock :=
    addFixedBlock (pushRegister direction) (StackEncoding.digit head)
  let divideBlock :=
    divideFixedBlock (popRegister direction) .temp radix
  let multiplyProgram := multiplyBlock.instantiate offset
  let addProgram := addBlock.instantiate (offset + multiplyWidth)
  let divideProgram := divideBlock.instantiate (offset + divisionOffset head)
  have hmultiply : Deterministic multiplyProgram :=
    deterministic_relocate
      (multiplyFixedBlock_wellFormed
        (pushRegister direction) .temp radix).1 offset
  have hadd : Deterministic addProgram :=
    deterministic_relocate
      (addFixedBlock_wellFormed (pushRegister direction)
        (StackEncoding.digit head)).1 (offset + multiplyWidth)
  have hdivide : Deterministic divideProgram :=
    deterministic_relocate
      (divideFixedBlock_wellFormed
        (popRegister direction) .temp radix).1
      (offset + divisionOffset head)
  have hmulAdd := instantiate_source_disjoint_of_before
    (multiplyFixedBlock_wellFormed (pushRegister direction) .temp radix)
    (addFixedBlock_wellFormed (pushRegister direction)
      (StackEncoding.digit head))
    (firstOffset := offset) (secondOffset := offset + multiplyWidth)
    (by simp [multiplyWidth])
  have hmulDiv := instantiate_source_disjoint_of_before
    (multiplyFixedBlock_wellFormed (pushRegister direction) .temp radix)
    (divideFixedBlock_wellFormed (popRegister direction) .temp radix)
    (firstOffset := offset) (secondOffset := offset + divisionOffset head)
    (by simp [multiplyWidth, divisionOffset])
  have haddDiv := instantiate_source_disjoint_of_before
    (addFixedBlock_wellFormed (pushRegister direction)
      (StackEncoding.digit head))
    (divideFixedBlock_wellFormed (popRegister direction) .temp radix)
    (firstOffset := offset + multiplyWidth)
    (secondOffset := offset + divisionOffset head)
    (by simp [divisionOffset, Nat.add_assoc])
  have hpref : Deterministic (multiplyProgram ++ addProgram) :=
    deterministic_append hmultiply hadd hmulAdd
  have hprefDiv : List.Disjoint
      (sourceStates (multiplyProgram ++ addProgram))
      (sourceStates divideProgram) := by
    rw [sourceStates_append, List.disjoint_iff_ne]
    intro state hstate other hother heq
    rcases List.mem_append.mp hstate with hstate | hstate
    · exact (List.disjoint_iff_ne.mp hmulDiv) state hstate other hother heq
    · exact (List.disjoint_iff_ne.mp haddDiv) state hstate other hother heq
  change Deterministic ((multiplyProgram ++ addProgram) ++ divideProgram)
  exact deterministic_append hpref hdivide hprefDiv

private theorem dispatch_source_not_core (offset : State)
    (direction : Turing.Dir) (head : Alphabet) {state : State}
    (hstate : state ∈ sourceStates
      (moveDispatchProgram offset head
        (default : SourceMachine.State))) :
    state ∉ sourceStates (moveCoreProgram offset direction head) := by
  simp only [moveDispatchProgram, sourceStates, List.map_map,
    List.mem_map] at hstate
  rcases hstate with ⟨remainder, hremainder, rfl⟩
  have hremainderLt : remainder < radix := List.mem_range.mp hremainder
  let tape : StackEncoding.TapeRegisters Alphabet :=
    match direction with
    | .left => ⟨head, remainder, 0⟩
    | .right => ⟨head, 0, remainder⟩
  have hpop : popValue direction tape = remainder := by
    cases direction <;> rfl
  have hnot := moveCoreExit_not_source offset head direction tape
  rw [moveCoreExit, hpop, Nat.mod_eq_of_lt hremainderLt] at hnot
  exact hnot

theorem compileAction_deterministic (offset : State)
    (nextState : SourceMachine.State) (head : Alphabet)
    (action : Turing.TM0.Stmt Alphabet) :
    Deterministic (compileAction offset nextState head action) := by
  cases action with
  | write a => simp [compileAction, Deterministic, sourceStates]
  | move direction =>
      apply deterministic_append
        (moveCoreProgram_deterministic offset direction head)
        (moveDispatchProgram_deterministic offset head nextState)
      rw [List.disjoint_iff_ne]
      intro coreState hcore dispatchState hdispatch heq
      subst dispatchState
      apply (dispatch_source_not_core offset direction head ?_) hcore
      simpa [moveDispatchProgram, sourceStates] using hdispatch

theorem source_mem_compileAction
    {offset : State} {nextState : SourceMachine.State} {head : Alphabet}
    {action : Turing.TM0.Stmt Alphabet} {state : State}
    (hstate : state ∈ sourceStates
      (compileAction offset nextState head action)) :
    offset ≤ state ∧ state < offset + actionStride := by
  cases action with
  | write a =>
      change state ∈ [offset] at hstate
      simp only [List.mem_singleton] at hstate
      subst state
      constructor
      · exact Nat.le_refl _
      · exact Nat.lt_add_of_pos_right actionStride_pos
  | move direction =>
      simp only [compileAction, sourceStates_append, List.mem_append] at hstate
      rcases hstate with hcore | hdispatch
      · change state ∈ sourceStates
          (((multiplyFixedBlock (pushRegister direction) .temp radix).instantiate
              offset ++
            (addFixedBlock (pushRegister direction)
              (StackEncoding.digit head)).instantiate
                (offset + multiplyWidth)) ++
            (divideFixedBlock (popRegister direction) .temp radix).instantiate
              (offset + divisionOffset head)) at hcore
        rw [sourceStates_append, sourceStates_append] at hcore
        rcases List.mem_append.mp hcore with hprefix | hdivide
        · rcases List.mem_append.mp hprefix with hmultiply | hadd
          · rcases Block.source_mem_instantiate
              (multiplyFixedBlock_wellFormed
                (pushRegister direction) .temp radix) hmultiply with
              ⟨hlower, hupper⟩
            simp only [multiplyFixedBlock_width] at hupper
            exact ⟨hlower, lt_of_lt_of_le hupper
              (Nat.add_le_add_left multiplyWidth_le_actionStride offset)⟩
          · rcases Block.source_mem_instantiate
              (addFixedBlock_wellFormed (pushRegister direction)
                (StackEncoding.digit head)) hadd with ⟨hlower, hupper⟩
            simp only [addFixedBlock_width] at hupper
            constructor
            · exact (Nat.le_add_right offset multiplyWidth).trans hlower
            · have hthreshold :
                  offset + multiplyWidth + StackEncoding.digit head ≤
                    offset + actionStride := by
                rw [show offset + multiplyWidth + StackEncoding.digit head =
                  offset + divisionOffset head by
                    simp [divisionOffset, Nat.add_assoc]]
                exact Nat.add_le_add_left
                  (divisionOffset_le_actionStride head) offset
              exact lt_of_lt_of_le hupper hthreshold
        · rcases Block.source_mem_instantiate
            (divideFixedBlock_wellFormed
              (popRegister direction) .temp radix) hdivide with
            ⟨hlower, hupper⟩
          simp only [divideFixedBlock_width] at hupper
          constructor
          · exact (Nat.le_add_right offset (divisionOffset head)).trans hlower
          · have hthreshold :
                offset + divisionOffset head + divisionWidth radix ≤
                  offset + actionStride := by
              rw [Nat.add_assoc]
              exact Nat.add_le_add_left
                (divisionAllocation_le_actionStride head) offset
            exact lt_of_lt_of_le hupper hthreshold
      · simp only [moveDispatchProgram, sourceStates, List.map_map,
          List.mem_map] at hdispatch
        rcases hdispatch with ⟨remainder, hremainder, rfl⟩
        have hremainderLt : remainder < radix := List.mem_range.mp hremainder
        change offset ≤
            offset + divisionOffset head + divisionExit radix remainder ∧
          offset + divisionOffset head + divisionExit radix remainder <
            offset + actionStride
        constructor
        · rw [Nat.add_assoc]
          exact Nat.le_add_right offset
            (divisionOffset head + divisionExit radix remainder)
        · have hexit := divisionExit_lt_width hremainderLt
          exact lt_of_lt_of_le
            (Nat.add_lt_add_left hexit (offset + divisionOffset head))
            (by
              simpa [Nat.add_assoc] using
                Nat.add_le_add_left
                  (divisionAllocation_le_actionStride head) offset)

/-! ## Per-key segments and the fixed global program -/

/-- Program segment owned by one bounded state/symbol key. -/
def keyProgram (key : SourceKey) : Program :=
  match SourceMachine.machine (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) with
  | none => []
  | some (nextState, action) =>
      (controlCode (SourceControl.decodeStateFin key.1)
          (SourceControl.decodeSymbol key.2),
        .decrement .temp (actionOffset key) (actionOffset key)) ::
      compileAction (actionOffset key) nextState
        (SourceControl.decodeSymbol key.2) action

/-- The one fixed finite counter program simulating `SourceMachine.machine`. -/
def program : Program :=
  SourceControl.sourceKeys.flatMap keyProgram

theorem keyProgram_deterministic (key : SourceKey) :
    Deterministic (keyProgram key) := by
  unfold keyProgram
  split
  · simp [Deterministic, sourceStates]
  · next nextState action hmachine =>
      rw [Deterministic]
      simp only [sourceStates, List.map_cons, List.nodup_cons]
      constructor
      · intro hcanonical
        have hbounds := source_mem_compileAction hcanonical
        have hcontrol := controlCode_lt_span
          (SourceControl.decodeStateFin key.1)
          (SourceControl.decodeSymbol key.2)
        have hspanOffset : controlSpan ≤ actionOffset key := by
          exact Nat.le_add_right controlSpan (keyIndex key * actionStride)
        exact (Nat.not_lt_of_ge (hspanOffset.trans hbounds.1)) hcontrol
      · exact compileAction_deterministic (actionOffset key) nextState
          (SourceControl.decodeSymbol key.2) action

theorem source_mem_keyProgram
    {key : SourceKey} {state : State}
    (hstate : state ∈ sourceStates (keyProgram key)) :
    state = controlCode (SourceControl.decodeStateFin key.1)
        (SourceControl.decodeSymbol key.2) ∨
      actionOffset key ≤ state ∧ state < actionOffset key + actionStride := by
  unfold keyProgram at hstate
  split at hstate
  · simp [sourceStates] at hstate
  · next nextState action hmachine =>
      simp only [sourceStates, List.map_cons, List.mem_cons] at hstate
      rcases hstate with hstate | hstate
      · exact Or.inl hstate
      · exact Or.inr (source_mem_compileAction hstate)

private theorem private_intervals_disjoint {first second : SourceKey}
    (hne : first ≠ second) {state : State}
    (hfirst : actionOffset first ≤ state ∧
      state < actionOffset first + actionStride)
    (hsecond : actionOffset second ≤ state ∧
      state < actionOffset second + actionStride) : False := by
  have hindex : keyIndex first ≠ keyIndex second := by
    exact fun h => hne (keyIndex_injective h)
  rcases lt_or_gt_of_ne hindex with hlt | hgt
  · have hsucc : keyIndex first + 1 ≤ keyIndex second :=
      Nat.succ_le_iff.mpr hlt
    have hscaled := Nat.mul_le_mul_right actionStride hsucc
    have hbefore : actionOffset first + actionStride ≤
        actionOffset second := by
      unfold actionOffset
      simpa [Nat.add_mul, Nat.add_assoc] using
        Nat.add_le_add_left hscaled controlSpan
    exact (Nat.not_lt_of_ge (hbefore.trans hsecond.1)) hfirst.2
  · have hsucc : keyIndex second + 1 ≤ keyIndex first :=
      Nat.succ_le_iff.mpr hgt
    have hscaled := Nat.mul_le_mul_right actionStride hsucc
    have hbefore : actionOffset second + actionStride ≤
        actionOffset first := by
      unfold actionOffset
      simpa [Nat.add_mul, Nat.add_assoc] using
        Nat.add_le_add_left hscaled controlSpan
    exact (Nat.not_lt_of_ge (hbefore.trans hfirst.1)) hsecond.2

theorem keyProgram_source_disjoint {first second : SourceKey}
    (hne : first ≠ second) :
    List.Disjoint (sourceStates (keyProgram first))
      (sourceStates (keyProgram second)) := by
  rw [List.disjoint_iff_ne]
  intro left hleft right hright heq
  subst right
  rcases source_mem_keyProgram hleft with hleftCanonical | hleftPrivate
  · rcases source_mem_keyProgram hright with
        hrightCanonical | hrightPrivate
    · apply hne
      apply decodeKey_injective
      apply controlCode_injective
      exact hleftCanonical.symm.trans hrightCanonical
    · have hcontrol := controlCode_lt_span
          (SourceControl.decodeStateFin first.1)
          (SourceControl.decodeSymbol first.2)
      rw [← hleftCanonical] at hcontrol
      have hspanOffset : controlSpan ≤ actionOffset second := by
        exact Nat.le_add_right controlSpan (keyIndex second * actionStride)
      exact (Nat.not_lt_of_ge
        (hspanOffset.trans hrightPrivate.1)) hcontrol
  · rcases source_mem_keyProgram hright with
        hrightCanonical | hrightPrivate
    · have hcontrol := controlCode_lt_span
          (SourceControl.decodeStateFin second.1)
          (SourceControl.decodeSymbol second.2)
      rw [← hrightCanonical] at hcontrol
      have hspanOffset : controlSpan ≤ actionOffset first := by
        exact Nat.le_add_right controlSpan (keyIndex first * actionStride)
      exact (Nat.not_lt_of_ge
        (hspanOffset.trans hleftPrivate.1)) hcontrol
    · exact (private_intervals_disjoint hne hleftPrivate hrightPrivate).elim

private theorem sourceStates_program :
    sourceStates program =
      SourceControl.sourceKeys.flatMap
        (fun key => sourceStates (keyProgram key)) := by
  simp [program, sourceStates, List.map_flatMap]

theorem program_deterministic : Deterministic program := by
  rw [Deterministic, sourceStates_program, List.nodup_flatMap]
  constructor
  · intro key _
    exact keyProgram_deterministic key
  · exact SourceControl.sourceKeys_nodup.imp fun {first second} hne =>
      keyProgram_source_disjoint hne

/-! ## Whole-program simulation -/

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

theorem keyProgram_subset_program (key : SourceKey) :
    ∀ rule ∈ keyProgram key, rule ∈ program := by
  intro rule hrule
  unfold program
  exact List.mem_flatMap.mpr
    ⟨key, SourceControl.mem_sourceKeys _ _, hrule⟩

private theorem keyProgram_reaches
    (key : SourceKey) {nextState : SourceMachine.State}
    {action : Turing.TM0.Stmt Alphabet}
    (hmachine : SourceMachine.machine
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) = some (nextState, action))
    (tape : StackEncoding.TapeRegisters Alphabet)
    (hhead : tape.head = SourceControl.decodeSymbol key.2) (clock : Nat) :
    StateTransition.Reaches (step (keyProgram key))
      ⟨controlCode (SourceControl.decodeStateFin key.1) tape.head,
        logicalRegisters tape clock⟩
      ⟨controlCode nextState (actionTape action tape).head,
        logicalRegisters (actionTape action tape) (clock + 1)⟩ := by
  rw [hhead]
  let registers := logicalRegisters tape clock
  have hdispatch : step (keyProgram key)
      ⟨controlCode (SourceControl.decodeStateFin key.1)
          (SourceControl.decodeSymbol key.2), registers⟩ =
    some ⟨actionOffset key, registers⟩ := by
    simp [keyProgram, hmachine, step,
      registers, logicalRegisters, Registers.get]
  have hdispatchReach : StateTransition.Reaches (step (keyProgram key))
      ⟨controlCode (SourceControl.decodeStateFin key.1)
          (SourceControl.decodeSymbol key.2), registers⟩
      ⟨actionOffset key, registers⟩ :=
    Relation.ReflTransGen.single (by simpa using hdispatch)
  have haction := compileAction_reaches (actionOffset key) nextState action
    tape clock
  rw [hhead] at haction
  have hcanonicalNotAction : controlCode
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) ∉
      sourceStates (compileAction (actionOffset key) nextState
        (SourceControl.decodeSymbol key.2) action) := by
    intro hsource
    have hbounds := source_mem_compileAction hsource
    have hcontrol := controlCode_lt_span
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2)
    have hspanOffset : controlSpan ≤ actionOffset key := by
      exact Nat.le_add_right controlSpan (keyIndex key * actionStride)
    exact (Nat.not_lt_of_ge (hspanOffset.trans hbounds.1)) hcontrol
  have hdisjoint : List.Disjoint
      [controlCode (SourceControl.decodeStateFin key.1)
        (SourceControl.decodeSymbol key.2)]
      (sourceStates (compileAction (actionOffset key) nextState
        (SourceControl.decodeSymbol key.2) action)) := by
    simp [hcanonicalNotAction]
  have hdisjointProgram : List.Disjoint
      (sourceStates
        [(controlCode (SourceControl.decodeStateFin key.1)
            (SourceControl.decodeSymbol key.2),
          .decrement .temp (actionOffset key) (actionOffset key))])
      (sourceStates (compileAction (actionOffset key) nextState
        (SourceControl.decodeSymbol key.2) action)) := by
    simpa [sourceStates] using hdisjoint
  have hactionFull := reaches_append_right_of_source_disjoint
    hdisjointProgram haction
  have hkeyProgram : keyProgram key =
      [(controlCode (SourceControl.decodeStateFin key.1)
          (SourceControl.decodeSymbol key.2),
        .decrement .temp (actionOffset key) (actionOffset key))] ++
      compileAction (actionOffset key) nextState
        (SourceControl.decodeSymbol key.2) action := by
    simp [keyProgram, hmachine]
  rw [hkeyProgram] at hdispatchReach ⊢
  exact hdispatchReach.trans hactionFull

/-- One global-program execution segment exactly simulates one defined source
register step and advances the Hooper clock by one. -/
theorem registerStep_reaches {cfg nextCfg : SourceControl.RegisterCfg}
    (hstep : SourceControl.registerStep cfg = some nextCfg) (clock : Nat) :
    StateTransition.Reaches (step program)
      ⟨controlCode cfg.state cfg.tape.head,
        logicalRegisters cfg.tape clock⟩
      ⟨controlCode nextCfg.state nextCfg.tape.head,
        logicalRegisters nextCfg.tape (clock + 1)⟩ := by
  let key : SourceKey :=
    (SourceControl.encodeStateFin cfg.state,
      SourceControl.encodeSymbol cfg.tape.head)
  simp only [SourceControl.registerStep] at hstep
  cases hmachine : SourceMachine.machine cfg.state cfg.tape.head with
  | none => simp [hmachine] at hstep
  | some result =>
      rcases result with ⟨nextState, action⟩
      simp only [hmachine, Option.map_some, Option.some.injEq] at hstep
      subst nextCfg
      have hlocal := keyProgram_reaches key
        (nextState := nextState) (action := action) (by
          simpa [key] using hmachine)
        cfg.tape (by simp [key]) clock
      have hglobal := reaches_of_subprogram program_deterministic
        (keyProgram_subset_program key) hlocal
      change StateTransition.Reaches (step program)
        ⟨controlCode cfg.state cfg.tape.head,
          logicalRegisters cfg.tape clock⟩
        ⟨controlCode nextState (actionTape action cfg.tape).head,
          logicalRegisters (actionTape action cfg.tape) (clock + 1)⟩
      simpa [key] using hglobal

/-- Exact iteration corollary.  After `n` defined high-level source steps,
the fixed counter program reaches the corresponding logical encoding and its
clock has increased by exactly `n`. -/
theorem iterate_registerStep_reaches (n : Nat)
    {cfg nextCfg : SourceControl.RegisterCfg}
    (hiterate : Dynamics.iterate SourceControl.registerStep n cfg =
      some nextCfg) (clock : Nat) :
    StateTransition.Reaches (step program)
      ⟨controlCode cfg.state cfg.tape.head,
        logicalRegisters cfg.tape clock⟩
      ⟨controlCode nextCfg.state nextCfg.tape.head,
        logicalRegisters nextCfg.tape (clock + n)⟩ := by
  induction n generalizing cfg nextCfg clock with
  | zero =>
      simp only [Dynamics.iterate_zero] at hiterate
      cases Option.some.inj hiterate
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      rw [Dynamics.iterate_succ] at hiterate
      cases hprefix : Dynamics.iterate SourceControl.registerStep n cfg with
      | none => simp [hprefix] at hiterate
      | some middle =>
          have hone : SourceControl.registerStep middle = some nextCfg := by
            simpa [hprefix] using hiterate
          have hfirst := ih hprefix clock
          have hlast := registerStep_reaches hone (clock + n)
          have hall := hfirst.trans hlast
          rw [show (clock + n) + 1 = clock + (n + 1) by omega] at hall
          change StateTransition.Reaches (step program)
            ⟨controlCode cfg.state cfg.tape.head,
              logicalRegisters cfg.tape clock⟩
            ⟨controlCode nextCfg.state nextCfg.tape.head,
              logicalRegisters nextCfg.tape (clock + (n + 1))⟩ at hall
          exact hall

/-- An immortal source run supplies global-program checkpoints with
arbitrarily large clock values. -/
theorem immortalFrom_has_clock_checkpoints
    {cfg : SourceControl.RegisterCfg}
    (himmortal : Dynamics.ImmortalFrom SourceControl.registerStep cfg)
    (clock n : Nat) :
    ∃ nextCfg : SourceControl.RegisterCfg,
      StateTransition.Reaches (step program)
      ⟨controlCode cfg.state cfg.tape.head,
        logicalRegisters cfg.tape clock⟩
      ⟨controlCode nextCfg.state nextCfg.tape.head,
        logicalRegisters nextCfg.tape (clock + n)⟩ := by
  unfold Dynamics.ImmortalFrom Dynamics.Survives at himmortal
  rcases himmortal n with ⟨nextCfg, hiterate⟩
  exact ⟨nextCfg, iterate_registerStep_reaches n hiterate clock⟩

/-- The fixed global compiler is a primitive-recursive constant.  In
particular it is independent of the source input code stored on the tape. -/
theorem program_primrec : Primrec fun _ : Unit => program :=
  Primrec.const program

theorem program_computable : Computable fun _ : Unit => program :=
  program_primrec.to_comp

end GlobalSourceProgram
end Hooper
end Kari
end LeanWang
