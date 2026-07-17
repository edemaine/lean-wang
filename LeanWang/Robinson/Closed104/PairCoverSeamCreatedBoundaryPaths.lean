/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedPaths
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathAllFamilyTargetsPaths

/-!
# Created-boundary seam obligations

Projection-closed family targets already produce a seam path whenever the
selected boundary is sparse.  The remaining finite-audit interface therefore
only needs to cover newly created selected boundaries.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundaryPaths

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedPaths PairCoverSeamResidualDirectPaths
  PairCoverSeamResidualDirectPathAllFamilyTargets
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

/-- Pure red-graph path obligations with a newly created selected boundary. -/
structure CreatedBoundaryPathsAt (phase : Phase) (depth : Nat) : Prop where
  vertical : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    ((row < boundary ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            column boundary)
          (quadrantAt column boundary) = some .north)) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬IsSparseCoordinate boundary →
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary
  horizontal : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    ((column < boundary ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            boundary row)
          (quadrantAt boundary row) = some .east)) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬IsSparseCoordinate boundary →
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary

set_option maxRecDepth 20000 in
/-- Family targets extend created-boundary paths to all cases consumed by the
target recurrence. -/
theorem CreatedBoundaryPathsAt.toCovered
    {phase : Phase} {depth : Nat}
    (created : CreatedBoundaryPathsAt phase depth)
    (targets : AllFamilyTargetsAt phase depth) :
    CoveredCreatedPathsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      wrongFacing notFits _covered
    by_cases sparseBoundary : IsSparseCoordinate boundary
    · exact targets.verticalPath grid parentX parentY
        columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
        notFits sparseBoundary wrongFacing
    · exact created.vertical grid parentX parentY
        columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
        wrongFacing notFits sparseBoundary
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
      wrongFacing notFits _covered
    by_cases sparseBoundary : IsSparseCoordinate boundary
    · exact targets.horizontalPath grid parentX parentY
        columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
        notFits sparseBoundary wrongFacing
    · exact created.horizontal grid parentX parentY
        columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
        wrongFacing notFits sparseBoundary

end PairCoverSeamCreatedBoundaryPaths
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
