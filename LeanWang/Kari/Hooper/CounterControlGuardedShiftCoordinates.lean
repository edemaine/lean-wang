/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedCoordinates
import LeanWang.Kari.Hooper.CounterControlResumedShiftCoordinates

/-!
# Marker-shift continuations from a guarded generated search

The level-aware `PrefixResumedSearch` used by the first parent-embedding
proof carries much more geometry than a marker shift needs.  A successful
generated marker shift only needs the exact search gap and one blank cell
behind its entry head.  These are precisely the fields of
`CounterControlGuardedSearch.GuardedSearch`.

This file uses the generic guarded command-coordinate API and advances
selected increment or positive-decrement shifts through the rest of their
compiled schedules.
The shifted tape is expressed relative to `GuardedSearch.parentOuter`; thus
the retained parent gap has length `current.distance + 1`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedSearch

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlBridge
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlResumedShiftCoordinates

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

namespace GuardedSearch

variable {base : Nat} {c : Nat.Partrec.Code}

/-- Parent-relative tape after a selected marker shift succeeds.  Its head
returns to the old target, while the boundary has moved to parent coordinate
`current.distance`. -/
def shiftedParentBacking (current : GuardedSearch base c)
    (expected : Fin 5) : FullTM0.Tape (Symbol numTags) :=
  shiftStepTape current.direction current.parentOuter
    (current.current.distance + 1) expected

/-- Constructor-facing normalization of a selected marker shift's exact
successful tape to the recovered parent coordinates. -/
theorem exactSuccessTape_eq_shiftedParentBacking
    (current : GuardedSearch base c)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : current.selectedRaw = .markerShift address expected search shift
      success (some search) collision) :
    exactSuccessTape current.selectedRaw current.foundTape =
      current.shiftedParentBacking expected := by
  have hmem : RawCommand.markerShift address expected search shift success
      (some search) collision ∈ rawCommands := by
    simpa [hraw] using current.selectedRaw_mem
  have hsearch : orient address.growth search = current.direction := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [hraw] at hdirection
    exact hdirection
  have hshift :=
    CounterControlRawCallerClassification.markerShift_oriented_shift_eq_opposite_search
      address expected search shift success (some search) collision hmem
  rw [hsearch] at hshift
  rw [hraw]
  simp only [exactSuccessTape, Option.map_some]
  rw [hsearch, hshift, current.foundTape_eq_parentMoveN]
  rfl

/-- Exact successful handoff of a selected guarded marker shift. -/
structure ShiftHandoff (current : GuardedSearch base c)
    (expected : Fin 5) : Type where
  selectedRaw_eq : ∃ address search shift success collision,
    current.selectedRaw = .markerShift address expected search shift success
      (some search) collision
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨resolve base c (rawSuccessRef current.selectedRaw),
      current.shiftedParentBacking expected⟩

namespace ShiftHandoff

variable {current : GuardedSearch base c} {expected : Fin 5}

/-- The old target cell is blank after the shift and final departure. -/
theorem source_blank (_handoff : ShiftHandoff current expected) :
    (current.shiftedParentBacking expected).read = blankSymbol := by
  cases hdirection : current.direction <;>
    simp [shiftedParentBacking, shiftStepTape, hdirection,
      NestingMachine.opposite, FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.write]

/-- One step back from the handoff head reads the moved boundary. -/
theorem destination_boundary (_handoff : ShiftHandoff current expected) :
    ((current.shiftedParentBacking expected).move
      (NestingMachine.opposite current.direction)).read =
        boundarySymbol expected := by
  cases hdirection : current.direction <;>
    simp [shiftedParentBacking, shiftStepTape, hdirection,
      NestingMachine.opposite, FullTM0.Tape.read, FullTM0.Tape.move,
      FullTM0.Tape.write]

end ShiftHandoff

private theorem shiftHandoff_of_selectedRaw_eq
    (current : GuardedSearch base c)
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : current.selectedRaw = .markerShift address expected search shift
      success (some search) collision) :
    Nonempty (ShiftHandoff current expected) := by
  have hrun := current.reaches_selectedRaw_success
  rw [current.exactSuccessTape_eq_shiftedParentBacking address expected
    search shift success collision hraw] at hrun
  exact ⟨⟨⟨address, search, shift, success, collision, hraw⟩, hrun⟩⟩

/-- Position and exact handoff for a selected increment-shift caller. -/
theorem incrementShift_handoff
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hcommand : current.selectedRaw ∈
      incrementShiftCommands growth source register) :
    ∃ position : IncrementShiftPosition growth source bodySearchBase true
        (MarkerShift.incrementOrder register) current.selectedRaw,
      Nonempty (ShiftHandoff current position.current) := by
  rcases incrementShiftPosition_of_mem growth source register
      current.selectedRaw hcommand with ⟨position⟩
  refine ⟨position, ?_⟩
  apply shiftHandoff_of_selectedRaw_eq current
    ⟨growth, source, bodySearchBase + position.before.length⟩
    position.current .left .right
    (match position.remaining with
      | [] => directRef growth source bodyDirectBase
      | _ :: _ => searchRef growth source
          (bodySearchBase + position.before.length + 1))
    (if true && position.before.isEmpty then
      some (directRef growth source testDirectSlot) else none)
    position.raw_eq

/-- Position and exact handoff for a selected positive-decrement shift. -/
theorem decrementShift_handoff
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hcommand : current.selectedRaw ∈
      decrementShiftCommands growth source register) :
    ∃ position : DecrementShiftPosition growth source secondarySearchBase
        (MarkerShift.decrementOrder register) current.selectedRaw,
      Nonempty (ShiftHandoff current position.current) := by
  rcases decrementShiftPosition_of_mem growth source register
      current.selectedRaw hcommand with ⟨position⟩
  refine ⟨position, ?_⟩
  apply shiftHandoff_of_selectedRaw_eq current
    ⟨growth, source, secondarySearchBase + position.before.length⟩
    position.current .right .left
    (match position.remaining with
      | [] => directRef growth source finishDirectSlot
      | _ :: _ => searchRef growth source
          (secondarySearchBase + position.before.length + 1))
    none position.raw_eq

/-- A selected guarded increment shift advanced through all later shifts in
the same compiled schedule. -/
structure IncrementShiftSuffixReached
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) : Type where
  position : IncrementShiftPosition growth source bodySearchBase true
    (MarkerShift.incrementOrder register) current.selectedRaw
  handoff : ShiftHandoff current position.current
  finish : FullTM0.Tape (Symbol numTags)
  tailGaps : ShiftTailGaps (orient growth .left) position.remaining
    (current.shiftedParentBacking position.current) finish
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨resolve base c (directRef growth source bodyDirectBase), finish⟩

/-- A selected guarded decrement shift advanced through all later shifts in
the same compiled schedule. -/
structure DecrementShiftSuffixReached
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) : Type where
  position : DecrementShiftPosition growth source secondarySearchBase
    (MarkerShift.decrementOrder register) current.selectedRaw
  handoff : ShiftHandoff current position.current
  finish : FullTM0.Tape (Symbol numTags)
  tailGaps : ShiftTailGaps (orient growth .right) position.remaining
    (current.shiftedParentBacking position.current) finish
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨resolve base c (directRef growth source finishDirectSlot), finish⟩

/-- Compose a selected guarded increment handoff with immortal traversal of
the remaining shift suffix. -/
theorem incrementShift_suffix_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      incrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (IncrementShiftSuffixReached current growth source register) := by
  rcases incrementShift_handoff current growth source register hcommand with
    ⟨position, ⟨handoff⟩⟩
  let shifted := current.shiftedParentBacking position.current
  cases hremaining : position.remaining with
  | nil =>
      have hreach := handoff.reaches
      have href : rawSuccessRef current.selectedRaw =
          directRef growth source bodyDirectBase := by
        rw [position.raw_eq, hremaining]
        rfl
      rw [href] at hreach
      exact ⟨⟨position, handoff, shifted,
        by simpa [hremaining, shifted] using (ShiftTailGaps.nil shifted),
        by simpa [shifted] using hreach⟩⟩
  | cons expected remaining =>
      have hhand := handoff.reaches
      have href : rawSuccessRef current.selectedRaw =
          searchRef growth source
            (bodySearchBase + position.before.length + 1) := by
        have heq := congrArg rawSuccessRef position.raw_eq
        simpa [hremaining, rawSuccessRef] using heq
      have hhand' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (foundCfg current.current)
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
        exact handoff.source_blank
      have hcommands : ∀ command,
          command ∈ incrementShiftCommandsAux growth source
              (bodySearchBase + position.before.length + 1) false
              (expected :: remaining) → command ∈ rawCommands := by
        intro command htail
        apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
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

/-- Compose a selected guarded decrement handoff with immortal traversal of
the remaining shift suffix. -/
theorem decrementShift_suffix_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      decrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (DecrementShiftSuffixReached current growth source register) := by
  rcases decrementShift_handoff current growth source register hcommand with
    ⟨position, ⟨handoff⟩⟩
  let shifted := current.shiftedParentBacking position.current
  cases hremaining : position.remaining with
  | nil =>
      have hreach := handoff.reaches
      have href : rawSuccessRef current.selectedRaw =
          directRef growth source finishDirectSlot := by
        rw [position.raw_eq, hremaining]
        rfl
      rw [href] at hreach
      exact ⟨⟨position, handoff, shifted,
        by simpa [hremaining, shifted] using (ShiftTailGaps.nil shifted),
        by simpa [shifted] using hreach⟩⟩
  | cons expected remaining =>
      have hhand := handoff.reaches
      have href : rawSuccessRef current.selectedRaw =
          searchRef growth source
            (secondarySearchBase + position.before.length + 1) := by
        have heq := congrArg rawSuccessRef position.raw_eq
        simpa [hremaining, rawSuccessRef] using heq
      have hhand' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (foundCfg current.current)
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
        exact handoff.source_blank
      have hcommands : ∀ command,
          command ∈ decrementShiftCommandsAux growth source
              (secondarySearchBase + position.before.length + 1)
              (expected :: remaining) → command ∈ rawCommands := by
        intro command htail
        apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
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

end GuardedSearch

end

end CounterControlGuardedSearch
end Hooper
end Kari
end LeanWang
