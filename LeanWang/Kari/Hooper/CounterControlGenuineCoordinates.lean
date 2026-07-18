/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlParentContinuation
import LeanWang.Kari.Hooper.CounterControlExactCommandContinuation
import LeanWang.Kari.Hooper.CounterControlRawCallerClassification

/-!
# Exact coordinates of an arbitrary genuine generated search

This is the guard-free counterpart of `CounterControlGuardedCoordinates`.
It names the selected raw command and exact found tape of any packaged genuine
search, and exposes the constructor-level found continuation.  Marker shifts
may still take a collision exit here; the one-cell destination-freedom result
belongs specifically to the guarded layer.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGlobalUnnesting

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlParentContinuation
open CounterControlExactCommandContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

namespace GenuineSearch

variable {base : Nat} {c : Nat.Partrec.Code}

/-- Raw command selected by the generated search index. -/
def selectedRaw (current : GenuineSearch base c) : RawCommand :=
  rawCommands.get current.search

theorem selectedRaw_mem (current : GenuineSearch base c) :
    current.selectedRaw ∈ rawCommands :=
  List.get_mem rawCommands current.search

@[simp] theorem rawTag_selectedRaw (current : GenuineSearch base c) :
    CounterControlCommandAt.rawTag current.selectedRaw
        current.selectedRaw_mem = current.search := by
  apply CounterControlCommandAt.rawTag_eq_of_get_eq
  rfl

@[simp] theorem compileRawCommand_selectedRaw
    (current : GenuineSearch base c) :
    CounterControlCommandAt.compileRawCommand base c current.selectedRaw
        current.selectedRaw_mem = command base c current.search := by
  unfold CounterControlCommandAt.compileRawCommand command
  rw [current.rawTag_selectedRaw]

/-- Physical direction of the selected generated search. -/
def direction (current : GenuineSearch base c) : Turing.Dir :=
  (command base c current.search).searchDirection

theorem selectedRaw_direction_eq (current : GenuineSearch base c) :
    (CounterControlCommandAt.compileRawCommand base c current.selectedRaw
      current.selectedRaw_mem).searchDirection = current.direction := by
  rw [current.compileRawCommand_selectedRaw]
  rfl

/-- Tape centered at the advertised target found by the search. -/
def foundTape (current : GenuineSearch base c) :
    FullTM0.Tape (Symbol numTags) :=
  current.outer.moveN current.direction current.distance

theorem foundCfg_eq (current : GenuineSearch base c) :
    foundCfg current =
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c current.selectedRaw.address),
        current.foundTape⟩ := by
  rfl

/-- The selected compiled target matches the exact found tape. -/
theorem selectedRaw_target_matches_foundTape
    (current : GenuineSearch base c) :
    (CounterControlCommandAt.compileRawCommand base c current.selectedRaw
      current.selectedRaw_mem).target.Matches current.foundTape.read := by
  rw [current.compileRawCommand_selectedRaw]
  simpa [foundTape, direction, FullTM0.Tape.read_moveN] using
    current.gap.marked

/-- Exact constructor-level continuation from the advertised found state.
Unlike the guarded specialization, this retains success, collision, and
blocked alternatives. -/
def foundContinuationOutcome (current : GenuineSearch base c) :
    FoundContinuationOutcome base c current.selectedRaw
      current.selectedRaw_mem current.foundTape :=
  exact_found_continuation base c current.selectedRaw
    current.selectedRaw_mem current.foundTape
    current.selectedRaw_target_matches_foundTape

end GenuineSearch

end

end CounterControlGlobalUnnesting
end Hooper
end Kari
end LeanWang
