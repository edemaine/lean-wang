/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlExactCommandContinuation
import LeanWang.Kari.Hooper.CounterControlRawCallerClassification
import LeanWang.Kari.Hooper.CounterControlResumedCoordinates

/-!
# Exact successful continuation of a resumed parent command

The recovered parent geometry puts a blank immediately behind the target of
the resumed search.  Every generated marker shift moves in precisely that
direction, opposite to its search direction.  Consequently the exact generic
found-command classification always takes its success branch here: neither a
collision exit nor a blocked shift is possible.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPrefixResume
namespace PrefixResumedSearch

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlParentContinuation
open CounterControlExactCommandContinuation
open CounterControlRawCallerClassification
open CounterControlPrefixInstructionResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

variable {base : Nat} {c : Nat.Partrec.Code}
variable {frame : PrefixEnvelope}
variable {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}

/-- The exact found tape of a resumed parent caller cannot present an
occupied marker-shift destination.  For navigation commands the assertion is
definitionally false; for marker shifts it follows from generated-direction
classification and the retained blank immediately behind the target. -/
theorem selectedRaw_destinationFree
    (resumed : PrefixResumedSearch base c frame start) :
    ¬ ShiftDestinationOccupied resumed.selectedRaw
      resumed.parentFoundTape := by
  cases hselected : resumed.selectedRaw with
  | boundaryNavigation address expected direction success action =>
      simp [ShiftDestinationOccupied]
  | tagNavigation address direction success =>
      simp [ShiftDestinationOccupied]
  | markerShift address expected search shift success departure collision =>
      intro hoccupied
      have hmem : RawCommand.markerShift address expected search shift success
          departure collision ∈ rawCommands := by
        simpa [hselected] using resumed.selectedRaw_mem
      have hopposite := markerShift_oriented_shift_eq_opposite_search
        address expected search shift success departure collision hmem
      have hsearch : orient address.growth search = frame.growth := by
        have hdirection := resumed.selectedRaw_direction_eq
        rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
        rw [hselected] at hdirection
        exact hdirection
      rw [hsearch] at hopposite
      have hblank := resumed.reverse_shift_destination_blank
        (orient address.growth shift) hopposite
      exact hoccupied hblank

/-- The selected generated command continues from the exact found parent
coordinate to its exact success reference and tape.  This is the clean
finite-command handoff needed by the parent-embedding proof. -/
theorem reaches_selectedRaw_success
    (resumed : PrefixResumedSearch base c frame start) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next)
      ⟨resolve base c
          (CounterControlCommandContinuationMortality.rawSuccessRef
            resumed.selectedRaw),
        exactSuccessTape resumed.selectedRaw resumed.parentFoundTape⟩ := by
  have outcome := exact_found_continuation base c resumed.selectedRaw
    resumed.selectedRaw_mem resumed.parentFoundTape
    resumed.selectedRaw_target_matches_parentFoundTape
  have hrun := outcome.reachesSuccess_of_destinationFree
    resumed.selectedRaw_destinationFree
  rw [resumed.foundCfg_eq_parentFound]
  exact hrun

end

end PrefixResumedSearch
end CounterControlPrefixResume
end Hooper
end Kari
end LeanWang
