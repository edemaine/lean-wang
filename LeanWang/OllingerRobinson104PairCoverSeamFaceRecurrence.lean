/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedPaths
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# All-depth boundary-face recurrence

After the parity bases, the face refinement theorem consumes two smaller
semantic inputs: the finite created-coordinate paths and the exact residual
paths.  This lightweight module packages that induction without importing the
expensive bounded-search certificates.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamFaceRecurrence

open PairCoverSeamCreatedPaths PairCoverSeamFacesAt
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
  data.created.refineFaces faces data.residual.verticalResidual
    data.residual.horizontalResidual

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

end PairCoverSeamFaceRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
