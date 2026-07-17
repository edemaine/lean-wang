/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathAllFamilyTargets
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedPaths

/-!
# Created-boundary target seeds

When projection exposes a newly created selected boundary, the finite created
seam path is already an endpoint target in the source's hierarchy family.
These two adapters package that branch of the target recurrence.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargetsCreated

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedPaths PairCoverSeamPathTranslation
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyTargetOfPath
  PairCoverSeamResidualDirectPathTargets
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem queryGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  calc
    _ = iterateRefine (refinementDepth phase (depth + 1) + 2) grid :=
      PairCoverSeamPathTranslation.globalGrid_eq_total
        phase (depth + 1) grid
    _ = _ := by
      congr 1
      simp only [outerLevel, refinementDepth]
      omega

/-- A created horizontal source boundary supplies a row target in any family
already carried by that source. -/
theorem rowTarget
    {phase : Phase} {depth : Nat}
    (created : CoveredCreatedPathsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (boundarySouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryNorth :
      boundary < quarterNorth (successorEast phase (depth + 1) parentY))
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .north))
    (notFits : ¬FitsContainedVerticalChild phase (depth + 1)
      parentX parentY column row boundary)
    (createdBoundary : ¬IsSparseCoordinate boundary)
    {family : HierarchyFamily}
    (sourceFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
      (horizontalPort
        (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
        column boundary)
      (outerLevel phase (depth + 1)) parentX parentY family) :
    RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX)
      column row boundary family := by
  have path := created.vertical grid parentX parentY columnWest columnEast
    rowSouth rowNorth boundarySouth boundaryNorth wrongFacing notFits
    (Or.inl createdBoundary)
  rw [queryGrid_eq_outerGrid phase depth grid] at path
  exact RowFamilyTarget.ofVerticalSeamPath sourceFamily path

/-- Column-dual created-boundary target seed. -/
theorem columnTarget
    {phase : Phase} {depth : Nat}
    (created : CoveredCreatedPathsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (boundaryWest :
      quarterWest (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryEast :
      boundary < quarterEast (successorEast phase (depth + 1) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .east))
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 1)
      parentX parentY column row boundary)
    (createdBoundary : ¬IsSparseCoordinate boundary)
    {family : HierarchyFamily}
    (sourceFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
      (verticalPort
        (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
        boundary row)
      (outerLevel phase (depth + 1)) parentX parentY family) :
    ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY)
      row column boundary family := by
  have path := created.horizontal grid parentX parentY
    columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
    wrongFacing notFits (Or.inl createdBoundary)
  rw [queryGrid_eq_outerGrid phase depth grid] at path
  exact ColumnFamilyTarget.ofHorizontalSeamPath sourceFamily path

end PairCoverSeamResidualDirectPathAllFamilyTargetsCreated
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
