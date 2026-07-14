/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedPaths
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBase
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBase
import LeanWang.OllingerRobinson104PairCoverSeamPathFaces
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# All-depth boundary-face recurrence

The expensive bounded seam searches are needed only at the two parity bases.
After that, the face refinement theorem consumes two smaller semantic inputs:
the finite created-coordinate paths and the exact residual paths.  This module
packages that induction with the actual even-depth-one and odd-depth-zero
bases used by the light-board construction.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamFaceRecurrence

open PairCoverSeamCreatedPaths PairCoverSeamFacesAt
  PairCoverSeamPathBoundedBase PairCoverSeamPathFaces
  PairCoverSeamResidualDirectPaths PairCoverSeamResidualDirectPathTargets
  ShadedFreeLineRecurrence

/-- The shade-independent path data needed for one face-refinement step. -/
structure StepData (phase : Phase) (depth : Nat) : Prop where
  created : CoveredCreatedPathsAt phase depth
  residual : DirectResidualPathsAt phase depth

/-- Same-family target selection is the proof-facing residual input. -/
theorem StepData.ofFamilyTargets
    {phase : Phase} {depth : Nat}
    (created : CoveredCreatedPathsAt phase depth)
    (targets : FamilyTargetsAt phase depth) :
    StepData phase depth :=
  ⟨created, targets.toDirectPaths⟩

/-- One semantic path package advances both boundary-face invariants. -/
theorem StepData.refine
    {phase : Phase} {depth : Nat}
    (data : StepData phase depth)
    (faces : VerticalBoundaryFacesAt phase depth ∧
      HorizontalBoundaryFacesAt phase depth) :
    VerticalBoundaryFacesAt phase (depth + 1) ∧
      HorizontalBoundaryFacesAt phase (depth + 1) :=
  data.created.refineFaces faces data.created
    data.residual.verticalResidual data.residual.horizontalResidual

/-- Iterate semantic face refinement from any certified starting depth. -/
theorem iterateFrom
    {phase : Phase} {start : Nat}
    (base : VerticalBoundaryFacesAt phase start ∧
      HorizontalBoundaryFacesAt phase start)
    (steps : ∀ offset : Nat, StepData phase (start + offset)) :
    ∀ offset : Nat,
      VerticalBoundaryFacesAt phase (start + offset) ∧
        HorizontalBoundaryFacesAt phase (start + offset) := by
  intro offset
  induction offset with
  | zero => simpa using base
  | succ offset ih =>
      have next := (steps offset).refine ih
      simpa [Nat.add_assoc] using next

/-- The cached odd search supplies both odd depth-zero face invariants. -/
theorem oddBase :
    VerticalBoundaryFacesAt .odd 0 ∧ HorizontalBoundaryFacesAt .odd 0 :=
  ⟨PairCoverSeamPathOddBase.boundedPaths.verticalBoundaryFacesAt,
    PairCoverSeamPathOddBase.boundedPaths.horizontalBoundaryFacesAt⟩

/-- The cached even search supplies both even depth-one face invariants. -/
theorem evenBase :
    VerticalBoundaryFacesAt .even 1 ∧ HorizontalBoundaryFacesAt .even 1 :=
  ⟨PairCoverSeamPathEvenBase.boundedPaths.verticalBoundaryFacesAt,
    PairCoverSeamPathEvenBase.boundedPaths.horizontalBoundaryFacesAt⟩

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
  · exact iterateFrom oddBase (by simpa using oddSteps) depth

end PairCoverSeamFaceRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
