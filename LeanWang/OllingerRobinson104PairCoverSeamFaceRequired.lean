/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamFaceRecurrence
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBase
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBase
import LeanWang.OllingerRobinson104PairCoverSeamPathFaces

/-!
# Required parity face families

This adapter is the only face-recurrence module that imports the expensive
bounded parity certificates.  Ordinary changes to the semantic recurrence can
therefore rebuild without replaying those native checks.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamFaceRequired

open PairCoverSeamFaceRecurrence PairCoverSeamFacesAt
  PairCoverSeamPathBoundedBase PairCoverSeamPathFaces
  ShadedFreeLineRecurrence

/-- The cached odd search supplies both odd depth-zero face invariants. -/
theorem oddBase :
    VerticalBoundaryFacesAt .odd 0 ∧ HorizontalBoundaryFacesAt .odd 0 :=
  ⟨PairCoverSeamPathFaces.BoundedPaths.verticalBoundaryFacesAt
      PairCoverSeamPathOddBase.boundedPaths,
    PairCoverSeamPathFaces.BoundedPaths.horizontalBoundaryFacesAt
      PairCoverSeamPathOddBase.boundedPaths⟩

/-- The cached even search supplies both even depth-one face invariants. -/
theorem evenBase :
    VerticalBoundaryFacesAt .even 1 ∧ HorizontalBoundaryFacesAt .even 1 :=
  ⟨PairCoverSeamPathFaces.BoundedPaths.verticalBoundaryFacesAt
      PairCoverSeamPathEvenBase.boundedPaths,
    PairCoverSeamPathFaces.BoundedPaths.horizontalBoundaryFacesAt
      PairCoverSeamPathEvenBase.boundedPaths⟩

/-- All face invariants used by the two canonical light-board families. -/
theorem requiredFaces
    (oddSteps : ∀ depth : Nat, StepData .odd depth)
    (evenSteps : ∀ depth : Nat, StepData .even (1 + depth)) :
    ∀ depth : Nat,
      (VerticalBoundaryFacesAt .even (1 + depth) ∧
        HorizontalBoundaryFacesAt .even (1 + depth)) ∧
      (VerticalBoundaryFacesAt .odd depth ∧
        HorizontalBoundaryFacesAt .odd depth) := by
  intro depth
  constructor
  · have faces := iterateFrom evenBase evenSteps depth
    simpa [Nat.add_comm] using faces
  · simpa using iterateFrom oddBase (by simpa using oddSteps) depth

end PairCoverSeamFaceRequired
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
