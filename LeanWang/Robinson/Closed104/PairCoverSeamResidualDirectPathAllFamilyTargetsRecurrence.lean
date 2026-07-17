/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceRow
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceColumn

/-!
# Free-line-general target recurrence

The row and column projection arguments combine into the semantic recurrence
used by the residual seam proof.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence

open PairCoverSeamCreatedPaths
  PairCoverSeamResidualDirectPathAllFamilyTargets
  PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceColumn
  PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceRow
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  ShadedFreeLineRecurrence

/-- Advance all hierarchy-family targets by one projection step. -/
theorem AllFamilyTargetsAt.succ
    {phase : Phase} {depth : Nat}
    (old : AllFamilyTargetsAt phase depth)
    (exceptional : ExceptionalFamilyTargetsAt phase (depth + 1))
    (created : CoveredCreatedPathsAt phase depth) :
    AllFamilyTargetsAt phase (depth + 1) := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary wrongFacing
    exact rowSucc old exceptional created grid parentX parentY
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary wrongFacing
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary wrongFacing
    exact columnSucc old exceptional created grid parentX parentY
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary wrongFacing

end PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
