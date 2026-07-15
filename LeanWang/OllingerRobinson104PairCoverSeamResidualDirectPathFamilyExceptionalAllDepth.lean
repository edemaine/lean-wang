/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalCreatedColumn
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalCreatedRow

/-! Exceptional same-family targets at every hierarchy depth. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalAllDepth

open PairCoverSeamResidualDirectPathFamilyExceptionalCreatedColumn
  PairCoverSeamResidualDirectPathFamilyExceptionalCreatedRow
  PairCoverSeamResidualDirectPathFamilyExceptionalRecurrence
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  ShadedFreeLineRecurrence

/-- The finite created-source certificates discharge the local successor
obligation at every depth. -/
theorem createdAt (phase : Phase) (depth : Nat) :
    CreatedExceptionalFamilyTargetsAt phase (depth + 1) where
  row := PairCoverSeamResidualDirectPathFamilyExceptionalCreatedRow.row
  column :=
    PairCoverSeamResidualDirectPathFamilyExceptionalCreatedColumn.column

/-- Base certificates, exact sparse predecessors, and created-source paths
jointly supply exceptional targets at all hierarchy depths. -/
theorem allDepth (phase : Phase) :
    ∀ depth, ExceptionalFamilyTargetsAt phase depth := by
  intro depth
  induction depth with
  | zero =>
      cases phase with
      | even => exact evenBase
      | odd => exact oddBase
  | succ depth ih =>
      exact
        PairCoverSeamResidualDirectPathFamilyExceptionalRecurrence.ExceptionalFamilyTargetsAt.succ
          ih (createdAt phase depth)

theorem even : ∀ depth, ExceptionalFamilyTargetsAt .even depth :=
  allDepth .even

theorem odd : ∀ depth, ExceptionalFamilyTargetsAt .odd depth :=
  allDepth .odd

end PairCoverSeamResidualDirectPathFamilyExceptionalAllDepth
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
