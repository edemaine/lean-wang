/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedExactContinuation
import LeanWang.Kari.Hooper.CounterControlGeneratedSearchGap

/-!
# Exact coordinates after a resumed marker shift

A resumed generated caller may occur in the middle of an increment or
positive-decrement marker schedule.  This file records its exact position in
that schedule and normalizes the successful found-state continuation back to
absolute coordinates of the recovered parent backing.

Both generated shift families search in one direction, move the found
boundary one cell in the opposite direction, and depart in the original
search direction.  Hence the head returns to the old target coordinate
`frame.limit`; that coordinate is blank, while the moved boundary is exactly
at `frame.limit - 1`, the distance retained by the resumed search.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlResumedShiftCoordinates

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlBridge
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality
open CounterControlGeneratedSearchGap
open CounterControlPrefixInstructionResolution
open CounterControlPrefixResume

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Exact positions in the two compiled shift schedules -/

/-- Position of a raw command in an increment-shift compiler invocation.
The `before`/`remaining` decomposition retains the exact continuation
schedule, not merely the boundary label of the selected command. -/
structure IncrementShiftPosition
    (growth : Turing.Dir) (source searchSlot : Nat) (first : Bool)
    (labels : List (Fin 5)) (raw : RawCommand) : Type where
  before : List (Fin 5)
  current : Fin 5
  remaining : List (Fin 5)
  raw_eq : raw = .markerShift
    ⟨growth, source, searchSlot + before.length⟩ current .left .right
    (match remaining with
      | [] => directRef growth source bodyDirectBase
      | _ :: _ => searchRef growth source
          (searchSlot + before.length + 1))
    (some .left)
    (if first && before.isEmpty then
      some (directRef growth source testDirectSlot) else none)
  labels_eq : labels = before ++ current :: remaining

/-- Position of a raw command in a decrement-shift compiler invocation. -/
structure DecrementShiftPosition
    (growth : Turing.Dir) (source searchSlot : Nat)
    (labels : List (Fin 5)) (raw : RawCommand) : Type where
  before : List (Fin 5)
  current : Fin 5
  remaining : List (Fin 5)
  raw_eq : raw = .markerShift
    ⟨growth, source, searchSlot + before.length⟩ current .right .left
    (match remaining with
      | [] => directRef growth source finishDirectSlot
      | _ :: _ => searchRef growth source
          (searchSlot + before.length + 1))
    (some .right) none
  labels_eq : labels = before ++ current :: remaining

/-- Membership inversion for the recursive increment-shift compiler. -/
theorem incrementShiftPosition_of_mem_aux
    (growth : Turing.Dir) (source searchSlot : Nat) (first : Bool)
    (labels : List (Fin 5)) (raw : RawCommand)
    (hraw : raw ∈ incrementShiftCommandsAux growth source searchSlot first
      labels) :
    Nonempty (IncrementShiftPosition growth source searchSlot first labels
      raw) := by
  induction labels generalizing searchSlot first raw with
  | nil => simp [incrementShiftCommandsAux] at hraw
  | cons expected labels ih =>
      simp only [incrementShiftCommandsAux, List.mem_cons] at hraw
      rcases hraw with hhead | htail
      · subst raw
        refine ⟨⟨[], expected, labels, ?_, rfl⟩⟩
        cases labels <;> simp
      · rcases ih (searchSlot + 1) false raw htail with ⟨position⟩
        refine ⟨⟨expected :: position.before, position.current,
          position.remaining, ?_, ?_⟩⟩
        · simpa only [List.length_cons, Bool.and_false, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            position.raw_eq
        · simp only [List.cons_append]
          rw [← position.labels_eq]

/-- Membership inversion for the recursive decrement-shift compiler. -/
theorem decrementShiftPosition_of_mem_aux
    (growth : Turing.Dir) (source searchSlot : Nat)
    (labels : List (Fin 5)) (raw : RawCommand)
    (hraw : raw ∈ decrementShiftCommandsAux growth source searchSlot labels) :
    Nonempty (DecrementShiftPosition growth source searchSlot labels raw) := by
  induction labels generalizing searchSlot raw with
  | nil => simp [decrementShiftCommandsAux] at hraw
  | cons expected labels ih =>
      simp only [decrementShiftCommandsAux, List.mem_cons] at hraw
      rcases hraw with hhead | htail
      · subst raw
        refine ⟨⟨[], expected, labels, ?_, rfl⟩⟩
        cases labels <;> simp
      · rcases ih (searchSlot + 1) raw htail with ⟨position⟩
        refine ⟨⟨expected :: position.before, position.current,
          position.remaining, ?_, ?_⟩⟩
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using position.raw_eq
        · simp only [List.cons_append]
          rw [← position.labels_eq]

/-- Specialized position witness for a selected increment schedule. -/
theorem incrementShiftPosition_of_mem
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (raw : RawCommand)
    (hraw : raw ∈ incrementShiftCommands growth source register) :
    Nonempty (IncrementShiftPosition growth source bodySearchBase true
      (MarkerShift.incrementOrder register) raw) := by
  exact incrementShiftPosition_of_mem_aux growth source bodySearchBase true
    (MarkerShift.incrementOrder register) raw hraw

/-- Specialized position witness for a selected decrement schedule. -/
theorem decrementShiftPosition_of_mem
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (raw : RawCommand)
    (hraw : raw ∈ decrementShiftCommands growth source register) :
    Nonempty (DecrementShiftPosition growth source secondarySearchBase
      (MarkerShift.decrementOrder register) raw) := by
  exact decrementShiftPosition_of_mem_aux growth source secondarySearchBase
    (MarkerShift.decrementOrder register) raw hraw

/-- Commands compiled after a selected increment-shift position remain
members of the original compiler invocation. -/
theorem incrementShiftCommandsAux_tail_mem
    (growth : Turing.Dir) (source searchSlot : Nat) (first : Bool)
    (before : List (Fin 5)) (current : Fin 5)
    (remaining : List (Fin 5)) (raw : RawCommand)
    (hraw : raw ∈ incrementShiftCommandsAux growth source
      (searchSlot + before.length + 1) false remaining) :
    raw ∈ incrementShiftCommandsAux growth source searchSlot first
      (before ++ current :: remaining) := by
  induction before generalizing searchSlot first with
  | nil =>
      simp only [List.nil_append, incrementShiftCommandsAux, List.mem_cons]
      exact Or.inr (by simpa using hraw)
  | cons previous before ih =>
      simp only [List.cons_append, incrementShiftCommandsAux,
        List.mem_cons]
      apply Or.inr
      apply ih (searchSlot := searchSlot + 1) (first := false)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hraw

/-- Commands compiled after a selected decrement-shift position remain
members of the original compiler invocation. -/
theorem decrementShiftCommandsAux_tail_mem
    (growth : Turing.Dir) (source searchSlot : Nat)
    (before : List (Fin 5)) (current : Fin 5)
    (remaining : List (Fin 5)) (raw : RawCommand)
    (hraw : raw ∈ decrementShiftCommandsAux growth source
      (searchSlot + before.length + 1) remaining) :
    raw ∈ decrementShiftCommandsAux growth source searchSlot
      (before ++ current :: remaining) := by
  induction before generalizing searchSlot with
  | nil =>
      simp only [List.nil_append, decrementShiftCommandsAux, List.mem_cons]
      exact Or.inr (by simpa using hraw)
  | cons previous before ih =>
      simp only [List.cons_append, decrementShiftCommandsAux,
        List.mem_cons]
      apply Or.inr
      apply ih (searchSlot := searchSlot + 1)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hraw

/-! ## Exact suffix traces -/

/-- Tape after one collision-free generated shift, expressed only in terms
of its physically oriented search direction.  The head finishes back at the
old target cell. -/
def shiftStepTape (searchDirection : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5) : FullTM0.Tape (Symbol numTags) :=
  (((outer.moveN searchDirection distance).write blankSymbol).move
      (NestingMachine.opposite searchDirection)).write
    (boundarySymbol expected) |>.move searchDirection

/-- Exact finite-gap trace through a nonempty suffix of a marker-shift
schedule.  Unlike forward schedule semantics, this trace assumes no
pre-existing canonical core. -/
inductive ShiftTailGaps (searchDirection : Turing.Dir) :
    List (Fin 5) → FullTM0.Tape (Symbol numTags) →
      FullTM0.Tape (Symbol numTags) → Prop where
  | nil (T : FullTM0.Tape (Symbol numTags)) :
      ShiftTailGaps searchDirection [] T T
  | cons (expected : Fin 5) (remaining : List (Fin 5))
      (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
      (gap : SearchGap (fun symbol => symbol = blankSymbol)
        (Target.boundary expected).Matches outer searchDirection distance)
      (positive : 0 < distance)
      (finish : FullTM0.Tape (Symbol numTags))
      (tail : ShiftTailGaps searchDirection remaining
        (shiftStepTape searchDirection outer distance expected) finish) :
      ShiftTailGaps searchDirection (expected :: remaining) outer finish

private theorem shiftStepTape_read
    (searchDirection : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5) :
    (shiftStepTape searchDirection outer distance expected).read =
      blankSymbol := by
  cases searchDirection <;>
    simp [shiftStepTape, FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.write]

private theorem shift_destination_blank_of_gap
    (searchDirection : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5)
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer searchDirection distance)
    (positive : 0 < distance) :
    ((((outer.moveN searchDirection distance).write blankSymbol).move
      (NestingMachine.opposite searchDirection)).read) = blankSymbol := by
  have hblank := gap.blank (show distance - 1 < distance by omega)
  have hmove : (outer.moveN searchDirection distance).move
      (NestingMachine.opposite searchDirection) =
      outer.moveN searchDirection (distance - 1) := by
    funext position
    cases searchDirection <;>
      simp [FullTM0.Tape.move, FullTM0.Tape.moveN,
        FullTM0.Tape.offset, NestingMachine.opposite] <;>
      congr 1 <;> omega
  have hwrite :
      ((((outer.moveN searchDirection distance).write blankSymbol).move
        (NestingMachine.opposite searchDirection)).read) =
      (((outer.moveN searchDirection distance).move
        (NestingMachine.opposite searchDirection)).read) := by
    cases searchDirection <;>
      simp [FullTM0.Tape.read, FullTM0.Tape.move,
        FullTM0.Tape.write, NestingMachine.opposite]
  rw [hwrite, hmove]
  simpa [FullTM0.Tape.read_moveN] using hblank

private theorem markerShift_gap_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift address expected search shift success
      departure collision ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩) :
    ∃ distance, SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth search) distance := by
  let raw := RawCommand.markerShift address expected search shift success
    departure collision
  rcases gap_of_reachable_search_on_immortal_orbit base c hmortal raw hraw
      outer (by simpa [raw, RawCommand.address] using himmortal) with
    ⟨distance, hgap⟩
  refine ⟨distance, ?_⟩
  rw [CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [raw, CounterControlCommandAt.compileRawAtTag, Command.target,
    Command.searchDirection] using hgap

private theorem markerShift_reaches_success_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (collision : Option ControlRef)
    (hreverse : orient address.growth shift =
      NestingMachine.opposite (orient address.growth search))
    (hraw : RawCommand.markerShift address expected search shift success
      (some search) collision ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (gap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer
      (orient address.growth search) distance)
    (positive : 0 < distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c address, outer⟩
      ⟨resolve base c success,
        shiftStepTape (orient address.growth search) outer distance
          expected⟩ := by
  let raw := RawCommand.markerShift address expected search shift success
    (some search) collision
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      outer
      (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection
      distance := by
    rw [CounterControlCommandAt.compileRawCommand_spec]
    simpa [raw, CounterControlCommandAt.compileRawAtTag, Command.target,
      Command.searchDirection] using gap
  have hshort : CounterControlSearchResolution.ShortResolves base c
      (distance + 1) := by
    intro shorter _
    exact CounterControlFiniteConverse.resolves_all base c shorter
  have hsearch := CounterControlSearchResolution.rawSearch_reaches_found_or_halts
    base c (distance + 1) hshort raw hraw outer distance (by omega)
      hcompiledGap
  rcases hsearch with hfound | hhalts
  · have hdirection :
        (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection =
          orient address.growth search := by
      rw [CounterControlCommandAt.compileRawCommand_spec]
      simp [raw, CounterControlCommandAt.compileRawAtTag,
        Command.searchDirection]
    rw [hdirection] at hfound
    let foundTape := outer.moveN (orient address.growth search) distance
    have hmatch :
        (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
          foundTape.read := by
      rw [CounterControlCommandAt.compileRawCommand_spec]
      simpa [raw, foundTape, CounterControlCommandAt.compileRawAtTag,
        Command.target, FullTM0.Tape.read_moveN] using gap.marked
    have hfree : ¬ ShiftDestinationOccupied raw foundTape := by
      intro hoccupied
      have hblank := shift_destination_blank_of_gap
        (orient address.growth search) outer distance expected gap positive
      change (((foundTape.write blankSymbol).move
        (orient address.growth shift)).read ≠ blankSymbol) at hoccupied
      rw [hreverse] at hoccupied
      exact hoccupied hblank
    have hcontinue :=
      (exact_found_continuation base c raw hraw foundTape hmatch).reachesSuccess_of_destinationFree
        hfree
    have hrun := hfound.trans hcontinue
    have htape : exactSuccessTape raw foundTape =
        shiftStepTape (orient address.growth search) outer distance
          expected := by
      dsimp only [raw, foundTape, exactSuccessTape, Option.map_some]
      rw [hreverse]
      rfl
    rw [htape] at hrun
    dsimp only [raw, RawCommand.address, rawSuccessRef] at hrun
    exact hrun
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, outer⟩).mp himmortal hhalts)

/-- Starting at any nonempty increment-shift suffix on an immortal orbit,
all remaining marker shifts succeed and reach the schedule's final direct
handoff.  The result retains every actual finite gap. -/
theorem reaches_incrementShiftTail_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source searchSlot : Nat) (first : Bool)
    (expected : Fin 5) (remaining : List (Fin 5))
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommandsAux growth source searchSlot first
          (expected :: remaining) → raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : outer.read = blankSymbol)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, searchSlot⟩, outer⟩) :
    ∃ finish,
      ShiftTailGaps (orient growth .left) (expected :: remaining)
          outer finish ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot⟩, outer⟩
          ⟨resolve base c (directRef growth source bodyDirectBase), finish⟩ := by
  induction remaining generalizing expected searchSlot first outer with
  | nil =>
      let collision := if first then
        some (directRef growth source testDirectSlot) else none
      let raw : RawCommand := .markerShift ⟨growth, source, searchSlot⟩
        expected .left .right (directRef growth source bodyDirectBase)
        (some .left) collision
      have hraw : raw ∈ rawCommands := by
        apply hcommands raw
        simp [raw, collision, incrementShiftCommandsAux]
      rcases markerShift_gap_of_immortal base c hmortal
          ⟨growth, source, searchSlot⟩ expected .left .right
          (directRef growth source bodyDirectBase) (some .left) collision
          hraw outer himmortal with ⟨distance, gap⟩
      have hpositive : 0 < distance := by
        by_contra hnot
        have hzero : distance = 0 := Nat.eq_zero_of_not_pos hnot
        subst distance
        have hmatch : (Target.boundary expected).Matches outer.read := by
          simpa [FullTM0.Tape.read] using gap.marked
        exact target_not_blank (Target.boundary expected)
          (hblank ▸ hmatch)
      have hreverse : orient growth .right =
          NestingMachine.opposite (orient growth .left) := by
        cases growth <;> rfl
      have hstep := markerShift_reaches_success_of_immortal base c
        ⟨growth, source, searchSlot⟩ expected .left .right
        (directRef growth source bodyDirectBase) collision hreverse hraw
        outer distance gap hpositive himmortal
      let shifted := shiftStepTape (orient growth .left) outer distance
        expected
      refine ⟨shifted, .cons expected [] outer distance gap hpositive shifted
        (.nil shifted), ?_⟩
      simpa [shifted] using hstep
  | cons next tail ih =>
      let success := searchRef growth source (searchSlot + 1)
      let collision := if first then
        some (directRef growth source testDirectSlot) else none
      let raw : RawCommand := .markerShift ⟨growth, source, searchSlot⟩
        expected .left .right success (some .left) collision
      have hraw : raw ∈ rawCommands := by
        apply hcommands raw
        simp [raw, success, collision, incrementShiftCommandsAux]
      rcases markerShift_gap_of_immortal base c hmortal
          ⟨growth, source, searchSlot⟩ expected .left .right success
          (some .left) collision hraw outer himmortal with
        ⟨distance, gap⟩
      have hpositive : 0 < distance := by
        by_contra hnot
        have hzero : distance = 0 := Nat.eq_zero_of_not_pos hnot
        subst distance
        have hmatch : (Target.boundary expected).Matches outer.read := by
          simpa [FullTM0.Tape.read] using gap.marked
        exact target_not_blank (Target.boundary expected)
          (hblank ▸ hmatch)
      have hreverse : orient growth .right =
          NestingMachine.opposite (orient growth .left) := by
        cases growth <;> rfl
      have hstep := markerShift_reaches_success_of_immortal base c
        ⟨growth, source, searchSlot⟩ expected .left .right success collision
        hreverse hraw outer distance gap hpositive himmortal
      let shifted := shiftStepTape (orient growth .left) outer distance
        expected
      have hstep' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot⟩, outer⟩
          ⟨searchState base c ⟨growth, source, searchSlot + 1⟩,
            shifted⟩ := by
        simpa [success, searchRef, resolve, shifted] using hstep
      have himmortalShifted : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot + 1⟩,
            shifted⟩ :=
        FullTM0.ImmortalFrom.of_reaches himmortal hstep'
      have hcommandsTail : ∀ command,
          command ∈ incrementShiftCommandsAux growth source
              (searchSlot + 1) false (next :: tail) →
            command ∈ rawCommands := by
        intro command hcommand
        apply hcommands command
        simpa only [incrementShiftCommandsAux, List.mem_cons] using
          (Or.inr hcommand)
      rcases ih (searchSlot + 1) false next hcommandsTail shifted
          (shiftStepTape_read _ _ _ _) himmortalShifted with
        ⟨finish, trace, htail⟩
      exact ⟨finish,
        .cons expected (next :: tail) outer distance gap hpositive finish
          trace,
        hstep'.trans htail⟩

/-- Starting at any nonempty decrement-shift suffix on an immortal orbit,
all remaining marker shifts succeed and reach `finishDirectSlot`. -/
theorem reaches_decrementShiftTail_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source searchSlot : Nat)
    (expected : Fin 5) (remaining : List (Fin 5))
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommandsAux growth source searchSlot
          (expected :: remaining) → raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : outer.read = blankSymbol)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, searchSlot⟩, outer⟩) :
    ∃ finish,
      ShiftTailGaps (orient growth .right) (expected :: remaining)
          outer finish ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot⟩, outer⟩
          ⟨resolve base c (directRef growth source finishDirectSlot),
            finish⟩ := by
  induction remaining generalizing expected searchSlot outer with
  | nil =>
      let raw : RawCommand := .markerShift ⟨growth, source, searchSlot⟩
        expected .right .left (directRef growth source finishDirectSlot)
        (some .right) none
      have hraw : raw ∈ rawCommands := by
        apply hcommands raw
        simp [raw, decrementShiftCommandsAux]
      rcases markerShift_gap_of_immortal base c hmortal
          ⟨growth, source, searchSlot⟩ expected .right .left
          (directRef growth source finishDirectSlot) (some .right) none
          hraw outer himmortal with ⟨distance, gap⟩
      have hpositive : 0 < distance := by
        by_contra hnot
        have hzero : distance = 0 := Nat.eq_zero_of_not_pos hnot
        subst distance
        have hmatch : (Target.boundary expected).Matches outer.read := by
          simpa [FullTM0.Tape.read] using gap.marked
        exact target_not_blank (Target.boundary expected)
          (hblank ▸ hmatch)
      have hreverse : orient growth .left =
          NestingMachine.opposite (orient growth .right) := by
        cases growth <;> rfl
      have hstep := markerShift_reaches_success_of_immortal base c
        ⟨growth, source, searchSlot⟩ expected .right .left
        (directRef growth source finishDirectSlot) none hreverse hraw outer
        distance gap hpositive himmortal
      let shifted := shiftStepTape (orient growth .right) outer distance
        expected
      refine ⟨shifted, .cons expected [] outer distance gap hpositive shifted
        (.nil shifted), ?_⟩
      simpa [shifted] using hstep
  | cons next tail ih =>
      let success := searchRef growth source (searchSlot + 1)
      let raw : RawCommand := .markerShift ⟨growth, source, searchSlot⟩
        expected .right .left success (some .right) none
      have hraw : raw ∈ rawCommands := by
        apply hcommands raw
        simp [raw, success, decrementShiftCommandsAux]
      rcases markerShift_gap_of_immortal base c hmortal
          ⟨growth, source, searchSlot⟩ expected .right .left success
          (some .right) none hraw outer himmortal with ⟨distance, gap⟩
      have hpositive : 0 < distance := by
        by_contra hnot
        have hzero : distance = 0 := Nat.eq_zero_of_not_pos hnot
        subst distance
        have hmatch : (Target.boundary expected).Matches outer.read := by
          simpa [FullTM0.Tape.read] using gap.marked
        exact target_not_blank (Target.boundary expected)
          (hblank ▸ hmatch)
      have hreverse : orient growth .left =
          NestingMachine.opposite (orient growth .right) := by
        cases growth <;> rfl
      have hstep := markerShift_reaches_success_of_immortal base c
        ⟨growth, source, searchSlot⟩ expected .right .left success none
        hreverse hraw outer distance gap hpositive himmortal
      let shifted := shiftStepTape (orient growth .right) outer distance
        expected
      have hstep' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot⟩, outer⟩
          ⟨searchState base c ⟨growth, source, searchSlot + 1⟩,
            shifted⟩ := by
        simpa [success, searchRef, resolve, shifted] using hstep
      have himmortalShifted : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, searchSlot + 1⟩,
            shifted⟩ :=
        FullTM0.ImmortalFrom.of_reaches himmortal hstep'
      have hcommandsTail : ∀ command,
          command ∈ decrementShiftCommandsAux growth source
              (searchSlot + 1) (next :: tail) → command ∈ rawCommands := by
        intro command hcommand
        apply hcommands command
        simpa only [decrementShiftCommandsAux, List.mem_cons] using
          (Or.inr hcommand)
      rcases ih (searchSlot + 1) next hcommandsTail shifted
          (shiftStepTape_read _ _ _ _) himmortalShifted with
        ⟨finish, trace, htail⟩
      exact ⟨finish,
        .cons expected (next :: tail) outer distance gap hpositive finish
          trace,
        hstep'.trans htail⟩

/-! ## Absolute parent coordinates after the selected shift -/

/-- Recovered parent backing after moving the found boundary one cell back
toward the resumed search origin. -/
def shiftedParentBacking
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (expected : Fin 5) : FullTM0.Tape (Symbol numTags) :=
  writeLogical frame.growth
    (writeLogical frame.growth resumed.parentFrame.outer frame.limit
      blankSymbol)
    (frame.limit - 1) (boundarySymbol expected)

private theorem markerShiftTape_atLogical
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (limit : Nat) (expected : Fin 5) (hlimit : 0 < limit) :
    ((((atLogical growth T limit).write blankSymbol).move
          (NestingMachine.opposite growth)).write
        (boundarySymbol expected)).move growth =
      atLogical growth
        (writeLogical growth
          (writeLogical growth T limit blankSymbol)
          (limit - 1) (boundarySymbol expected)) limit := by
  have hsucc : limit - 1 + 1 = limit := by omega
  rw [← hsucc]
  cases growth with
  | left =>
      simpa [OrientedMarkerTape.orientDirection,
        NestingMachine.opposite] using
        (shiftLeft_departRight_atLogical .left T (limit - 1)
          (boundarySymbol expected))
  | right =>
      simpa [OrientedMarkerTape.orientDirection,
        NestingMachine.opposite] using
        (shiftLeft_departRight_atLogical .right T (limit - 1)
          (boundarySymbol expected))

/-- Constructor-facing rewrite for the exact successful tape of any
selected generated marker shift.  Generated-direction classification supplies
the reversal; no increment/decrement family case split is required. -/
theorem exactSuccessTape_eq_shiftedParentBacking
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : resumed.selectedRaw = .markerShift address expected search shift
      success (some search) collision) :
    exactSuccessTape resumed.selectedRaw resumed.parentFoundTape =
      atLogical frame.growth (shiftedParentBacking resumed expected)
        frame.limit := by
  have hmem : RawCommand.markerShift address expected search shift success
      (some search) collision ∈ rawCommands := by
    simpa [hraw] using resumed.selectedRaw_mem
  have hsearch : orient address.growth search = frame.growth := by
    have hdirection := resumed.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
    rw [hraw] at hdirection
    exact hdirection
  have hshift :=
    CounterControlRawCallerClassification.markerShift_oriented_shift_eq_opposite_search
      address expected search shift success (some search) collision hmem
  rw [hsearch] at hshift
  rw [hraw]
  simp only [exactSuccessTape, Option.map_some]
  rw [hsearch, hshift]
  exact markerShiftTape_atLogical frame.growth resumed.parentFrame.outer
    frame.limit expected resumed.limit_pos

/-- Exact successful marker-shift handoff in parent absolute coordinates. -/
structure ShiftHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (expected : Fin 5) : Type where
  selectedRaw_eq : ∃ address search shift success collision,
    resumed.selectedRaw = .markerShift address expected search shift success
      (some search) collision
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (CounterControlParentContinuation.foundCfg resumed.next)
    ⟨resolve base c
        (CounterControlCommandContinuationMortality.rawSuccessRef
          resumed.selectedRaw),
      atLogical frame.growth (shiftedParentBacking resumed expected)
        frame.limit⟩

namespace ShiftHandoff

variable {base : Nat} {c : Nat.Partrec.Code}
variable {frame : PrefixEnvelope}
variable {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
variable {resumed : PrefixResumedSearch base c frame start}
variable {expected : Fin 5}

/-- The old target coordinate is blank after the shift. -/
theorem source_blank (_handoff : ShiftHandoff resumed expected) :
    logicalTape frame.growth (shiftedParentBacking resumed expected)
      frame.limit = blankSymbol := by
  unfold shiftedParentBacking
  rw [writeLogical_of_ne frame.growth _ (frame.limit - 1) frame.limit]
  · exact writeLogical_at frame.growth resumed.parentFrame.outer frame.limit
      blankSymbol
  · have hpositive := resumed.limit_pos
    omega

/-- The moved boundary occupies exactly the coordinate retained as the
resumed search distance. -/
theorem boundary_at_resumedDistance
    (_handoff : ShiftHandoff resumed expected) :
    logicalTape frame.growth (shiftedParentBacking resumed expected)
      resumed.next.distance = boundarySymbol expected := by
  rw [resumed.distance_eq]
  exact writeLogical_at frame.growth _ (frame.limit - 1)
    (boundarySymbol expected)

/-- The resumed distance lies strictly before the now-blank old target
coordinate. -/
theorem distance_lt_source
    (_handoff : ShiftHandoff resumed expected) :
    resumed.next.distance < frame.limit := by
  rw [resumed.distance_eq]
  have hpositive := resumed.limit_pos
  omega

/-- Coordinates other than the old source and new destination retain the
recovered parent backing exactly. -/
theorem unchanged
    (_handoff : ShiftHandoff resumed expected) (position : Nat)
    (hsource : position ≠ frame.limit)
    (hdestination : position ≠ frame.limit - 1) :
    logicalTape frame.growth (shiftedParentBacking resumed expected) position =
      logicalTape frame.growth resumed.parentFrame.outer position := by
  unfold shiftedParentBacking
  rw [writeLogical_of_ne frame.growth _ (frame.limit - 1) position _
      hdestination,
    writeLogical_of_ne frame.growth _ frame.limit position _ hsource]

end ShiftHandoff

private theorem shiftHandoff_of_selectedRaw_eq
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : resumed.selectedRaw = .markerShift address expected search shift
      success (some search) collision)
    (hsearch : orient address.growth search = frame.growth)
    (hshift : orient address.growth shift =
      NestingMachine.opposite frame.growth) :
    Nonempty (ShiftHandoff resumed expected) := by
  have hrun := resumed.reaches_selectedRaw_success
  have htape : exactSuccessTape resumed.selectedRaw resumed.parentFoundTape =
      atLogical frame.growth (shiftedParentBacking resumed expected)
        frame.limit := by
    rw [hraw]
    simp only [exactSuccessTape, Option.map_some]
    rw [hsearch, hshift]
    exact markerShiftTape_atLogical frame.growth resumed.parentFrame.outer
      frame.limit expected resumed.limit_pos
  rw [htape] at hrun
  exact ⟨⟨⟨address, search, shift, success, collision, hraw⟩, hrun⟩⟩

/-- A selected resumed increment-shift caller reaches its exact normalized
parent backing, together with its precise suffix position. -/
theorem incrementShift_handoff
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hcommand : resumed.selectedRaw ∈
      incrementShiftCommands growth source register) :
    ∃ position : IncrementShiftPosition growth source bodySearchBase true
        (MarkerShift.incrementOrder register) resumed.selectedRaw,
      Nonempty (ShiftHandoff resumed position.current) := by
  rcases incrementShiftPosition_of_mem growth source register
      resumed.selectedRaw hcommand with ⟨position⟩
  refine ⟨position, ?_⟩
  have hsearch : orient growth .left = frame.growth := by
    have hdirection := resumed.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
    rw [position.raw_eq] at hdirection
    exact hdirection
  have hshift : orient growth .right =
      NestingMachine.opposite frame.growth := by
    rw [← hsearch]
    cases growth <;> rfl
  apply shiftHandoff_of_selectedRaw_eq resumed
    ⟨growth, source, bodySearchBase + position.before.length⟩
    position.current .left .right
    (match position.remaining with
      | [] => directRef growth source bodyDirectBase
      | _ :: _ => searchRef growth source
          (bodySearchBase + position.before.length + 1))
    (if true && position.before.isEmpty then
      some (directRef growth source testDirectSlot) else none)
    position.raw_eq hsearch hshift

/-- A selected resumed positive-decrement shift reaches its exact normalized
parent backing, together with its precise suffix position. -/
theorem decrementShift_handoff
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hcommand : resumed.selectedRaw ∈
      decrementShiftCommands growth source register) :
    ∃ position : DecrementShiftPosition growth source secondarySearchBase
        (MarkerShift.decrementOrder register) resumed.selectedRaw,
      Nonempty (ShiftHandoff resumed position.current) := by
  rcases decrementShiftPosition_of_mem growth source register
      resumed.selectedRaw hcommand with ⟨position⟩
  refine ⟨position, ?_⟩
  have hsearch : orient growth .right = frame.growth := by
    have hdirection := resumed.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
    rw [position.raw_eq] at hdirection
    exact hdirection
  have hshift : orient growth .left =
      NestingMachine.opposite frame.growth := by
    rw [← hsearch]
    cases growth <;> rfl
  apply shiftHandoff_of_selectedRaw_eq resumed
    ⟨growth, source, secondarySearchBase + position.before.length⟩
    position.current .right .left
    (match position.remaining with
      | [] => directRef growth source finishDirectSlot
      | _ :: _ => searchRef growth source
          (secondarySearchBase + position.before.length + 1))
    none position.raw_eq hsearch hshift

/-! ## Selected callers advanced through the remaining shift schedule -/

/-- A selected resumed increment shift, advanced through every later shift
in the same compiled schedule. -/
structure IncrementShiftSuffixReached
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register) : Type where
  position : IncrementShiftPosition growth source bodySearchBase true
    (MarkerShift.incrementOrder register) resumed.selectedRaw
  handoff : ShiftHandoff resumed position.current
  finish : FullTM0.Tape (Symbol numTags)
  tailGaps : ShiftTailGaps (orient growth .left) position.remaining
    (atLogical frame.growth
      (shiftedParentBacking resumed position.current) frame.limit) finish
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (CounterControlParentContinuation.foundCfg resumed.next)
    ⟨resolve base c (directRef growth source bodyDirectBase), finish⟩

/-- A selected resumed decrement shift, advanced through every later shift
in the same compiled schedule. -/
structure DecrementShiftSuffixReached
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register) : Type where
  position : DecrementShiftPosition growth source secondarySearchBase
    (MarkerShift.decrementOrder register) resumed.selectedRaw
  handoff : ShiftHandoff resumed position.current
  finish : FullTM0.Tape (Symbol numTags)
  tailGaps : ShiftTailGaps (orient growth .right) position.remaining
    (atLogical frame.growth
      (shiftedParentBacking resumed position.current) frame.limit) finish
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (CounterControlParentContinuation.foundCfg resumed.next)
    ⟨resolve base c (directRef growth source finishDirectSlot), finish⟩

/-- Compose the exact selected increment handoff with the generic immortal
suffix traversal. -/
theorem incrementShift_suffix_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : resumed.selectedRaw ∈
      incrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (CounterControlParentContinuation.foundCfg resumed.next)) :
    Nonempty (IncrementShiftSuffixReached resumed growth source register) := by
  rcases incrementShift_handoff resumed growth source register hcommand with
    ⟨position, ⟨handoff⟩⟩
  let shifted := atLogical frame.growth
    (shiftedParentBacking resumed position.current) frame.limit
  cases hremaining : position.remaining with
  | nil =>
      have hreach := handoff.reaches
      have href : rawSuccessRef resumed.selectedRaw =
          directRef growth source bodyDirectBase := by
        rw [position.raw_eq, hremaining]
        rfl
      rw [href] at hreach
      exact ⟨⟨position, handoff, shifted,
        by simpa [hremaining, shifted] using (ShiftTailGaps.nil shifted),
        by simpa [shifted] using hreach⟩⟩
  | cons expected remaining =>
      have hhand := handoff.reaches
      have href : rawSuccessRef resumed.selectedRaw =
          searchRef growth source
            (bodySearchBase + position.before.length + 1) := by
        have heq := congrArg rawSuccessRef position.raw_eq
        simpa [hremaining, rawSuccessRef] using heq
      have hhand' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (CounterControlParentContinuation.foundCfg resumed.next)
          ⟨searchState base c
              ⟨growth, source,
                bodySearchBase + position.before.length + 1⟩,
            shifted⟩ := by
        rw [href] at hhand
        simpa [searchRef, resolve, shifted] using hhand
      have himmortalShifted : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source,
                bodySearchBase + position.before.length + 1⟩,
            shifted⟩ :=
        FullTM0.ImmortalFrom.of_reaches himmortal hhand'
      have hblank : shifted.read = blankSymbol := by
        change (atLogical frame.growth
          (shiftedParentBacking resumed position.current)
            frame.limit).read = blankSymbol
        rw [atLogical_read]
        exact handoff.source_blank
      have hcommands : ∀ command,
          command ∈ incrementShiftCommandsAux growth source
              (bodySearchBase + position.before.length + 1) false
              (expected :: remaining) → command ∈ rawCommands := by
        intro command htail
        apply CounterControlPlan.command_mem_rawCommands_of_rule
          growth hrule
        have hfull : command ∈
            incrementShiftCommands growth source register := by
          unfold incrementShiftCommands
          rw [position.labels_eq, hremaining]
          apply incrementShiftCommandsAux_tail_mem growth source
            bodySearchBase true position.before position.current
              (expected :: remaining) command
          exact htail
        simp [commandsForRule, incrementCommands, hfull]
      rcases reaches_incrementShiftTail_of_immortal base c hmortal growth
          source (bodySearchBase + position.before.length + 1) false
          expected remaining hcommands shifted hblank himmortalShifted with
        ⟨finish, trace, htail⟩
      exact ⟨⟨position, handoff, finish,
        by simpa [hremaining, shifted] using trace,
        hhand'.trans htail⟩⟩

/-- Compose the exact selected decrement handoff with the generic immortal
suffix traversal. -/
theorem decrementShift_suffix_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : resumed.selectedRaw ∈
      decrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (CounterControlParentContinuation.foundCfg resumed.next)) :
    Nonempty (DecrementShiftSuffixReached resumed growth source register) := by
  rcases decrementShift_handoff resumed growth source register hcommand with
    ⟨position, ⟨handoff⟩⟩
  let shifted := atLogical frame.growth
    (shiftedParentBacking resumed position.current) frame.limit
  cases hremaining : position.remaining with
  | nil =>
      have hreach := handoff.reaches
      have href : rawSuccessRef resumed.selectedRaw =
          directRef growth source finishDirectSlot := by
        rw [position.raw_eq, hremaining]
        rfl
      rw [href] at hreach
      exact ⟨⟨position, handoff, shifted,
        by simpa [hremaining, shifted] using (ShiftTailGaps.nil shifted),
        by simpa [shifted] using hreach⟩⟩
  | cons expected remaining =>
      have hhand := handoff.reaches
      have href : rawSuccessRef resumed.selectedRaw =
          searchRef growth source
            (secondarySearchBase + position.before.length + 1) := by
        have heq := congrArg rawSuccessRef position.raw_eq
        simpa [hremaining, rawSuccessRef] using heq
      have hhand' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (CounterControlParentContinuation.foundCfg resumed.next)
          ⟨searchState base c
              ⟨growth, source,
                secondarySearchBase + position.before.length + 1⟩,
            shifted⟩ := by
        rw [href] at hhand
        simpa [searchRef, resolve, shifted] using hhand
      have himmortalShifted : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c
              ⟨growth, source,
                secondarySearchBase + position.before.length + 1⟩,
            shifted⟩ :=
        FullTM0.ImmortalFrom.of_reaches himmortal hhand'
      have hblank : shifted.read = blankSymbol := by
        change (atLogical frame.growth
          (shiftedParentBacking resumed position.current)
            frame.limit).read = blankSymbol
        rw [atLogical_read]
        exact handoff.source_blank
      have hcommands : ∀ command,
          command ∈ decrementShiftCommandsAux growth source
              (secondarySearchBase + position.before.length + 1)
              (expected :: remaining) → command ∈ rawCommands := by
        intro command htail
        apply CounterControlPlan.command_mem_rawCommands_of_rule
          growth hrule
        have hfull : command ∈
            decrementShiftCommands growth source register := by
          unfold decrementShiftCommands
          rw [position.labels_eq, hremaining]
          apply decrementShiftCommandsAux_tail_mem growth source
            secondarySearchBase position.before position.current
              (expected :: remaining) command
          exact htail
        simp [commandsForRule, decrementCommands, hfull]
      rcases reaches_decrementShiftTail_of_immortal base c hmortal growth
          source (secondarySearchBase + position.before.length + 1)
          expected remaining hcommands shifted hblank himmortalShifted with
        ⟨finish, trace, htail⟩
      exact ⟨⟨position, handoff, finish,
        by simpa [hremaining, shifted] using trace,
        hhand'.trans htail⟩⟩

end

end CounterControlResumedShiftCoordinates
end Hooper
end Kari
end LeanWang
