/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyPredecessorHierarchy
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Target-only residual family obligations

The source side of `FamilyTargetsAt` follows from the all-depth hierarchy
predecessor theorem.  This module retains that inherited coarse source as
explicit data and factors the remaining proof down to selecting a compatible
target.  In particular, no finite search is needed to rediscover the source's
hierarchy family.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathInheritedFamilyTargets

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyPredecessorHierarchy
  PairCoverSeamResidualDirectPathTargets
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- The coarse source and hierarchy family inherited by a sparse horizontal
fine source. -/
structure HorizontalInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY column boundary : Nat) where
  oldColumn : Nat
  oldBoundary : Nat
  family : HierarchyFamily
  oldColumnBounds : InCollar
    (successorWest phase depth parentX)
    (successorEast phase depth parentX) oldColumn
  oldBoundaryBounds : InCollar
    (successorWest phase depth parentY)
    (successorEast phase depth parentY) oldBoundary
  sameBlock : oldColumn / 2 = column / 8
  boundarySparse : sparseCoordinate oldBoundary = boundary
  oldInterior : Signals.horizontalInterior?
    (componentAt (refinedGrid phase (depth + 1) grid) oldColumn oldBoundary)
    (quadrantAt oldColumn oldBoundary) ≠ none
  oldFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 1) grid)
    (horizontalPort (refinedGrid phase (depth + 1) grid)
      oldColumn oldBoundary)
    (outerLevel phase depth) parentX parentY family
  fineFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 2) grid)
    (horizontalPort (refinedGrid phase (depth + 2) grid) column boundary)
    (outerLevel phase (depth + 1)) parentX parentY family

/-- Vertical dual of `HorizontalInheritedSource`. -/
structure VerticalInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY boundary row : Nat) where
  oldBoundary : Nat
  oldRow : Nat
  family : HierarchyFamily
  oldBoundaryBounds : InCollar
    (successorWest phase depth parentX)
    (successorEast phase depth parentX) oldBoundary
  oldRowBounds : InCollar
    (successorWest phase depth parentY)
    (successorEast phase depth parentY) oldRow
  sameBlock : oldRow / 2 = row / 8
  boundarySparse : sparseCoordinate oldBoundary = boundary
  oldInterior : Signals.verticalInterior?
    (componentAt (refinedGrid phase (depth + 1) grid) oldBoundary oldRow)
    (quadrantAt oldBoundary oldRow) ≠ none
  oldFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 1) grid)
    (verticalPort (refinedGrid phase (depth + 1) grid) oldBoundary oldRow)
    (outerLevel phase depth) parentX parentY family
  fineFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 2) grid)
    (verticalPort (refinedGrid phase (depth + 2) grid) boundary row)
    (outerLevel phase (depth + 1)) parentX parentY family

theorem horizontalInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary : Nat}
    (columnBounds : InCollar
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column)
    (boundaryBounds : InCollar
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    Nonempty (HorizontalInheritedSource phase depth grid parentX parentY
      column boundary) := by
  rcases horizontalSourceFamily phase depth grid parentX parentY
      columnBounds boundaryBounds sparseBoundary interior with
    ⟨oldColumn, oldBoundary, family, oldColumnBounds, oldBoundaryBounds,
      sameBlock, boundarySparse, oldInterior, oldFamily, fineFamily⟩
  exact ⟨⟨oldColumn, oldBoundary, family, oldColumnBounds, oldBoundaryBounds,
    sameBlock, boundarySparse, oldInterior, oldFamily, fineFamily⟩⟩

theorem verticalInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row : Nat}
    (boundaryBounds : InCollar
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) boundary)
    (rowBounds : InCollar
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    Nonempty (VerticalInheritedSource phase depth grid
      parentX parentY boundary row) := by
  rcases verticalSourceFamily phase depth grid parentX parentY
      boundaryBounds rowBounds sparseBoundary interior with
    ⟨oldBoundary, oldRow, family, oldBoundaryBounds, oldRowBounds,
      sameBlock, boundarySparse, oldInterior, oldFamily, fineFamily⟩
  exact ⟨⟨oldBoundary, oldRow, family, oldBoundaryBounds, oldRowBounds,
    sameBlock, boundarySparse, oldInterior, oldFamily, fineFamily⟩⟩

/-- The remaining target-only obligation at one hierarchy depth. -/
structure InheritedFamilyTargetsAt (phase : Phase) (depth : Nat) : Prop where
  row : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate row →
    (((row < boundary) ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      ((boundary < row) ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .north)) →
    ∀ source : HorizontalInheritedSource phase depth grid
      parentX parentY column boundary,
      RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX)
        column row boundary source.family
  column : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate column →
    (((column < boundary) ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      ((boundary < column) ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .east)) →
    ∀ source : VerticalInheritedSource phase depth grid
      parentX parentY boundary row,
      ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY)
        row column boundary source.family

private theorem fineGrid_eq
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 2) grid =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  unfold refinedGrid outerLevel refinementDepth
  congr 1

/-- Target recognition for the inherited source family supplies the complete
joint source/target obligation. -/
theorem InheritedFamilyTargetsAt.toFamilyTargetsAt
    {phase : Phase} {depth : Nat}
    (targets : InheritedFamilyTargetsAt phase depth) :
    FamilyTargetsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary createdRow orientation
    have columnBounds : InCollar
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX) column := by
      constructor
      · unfold InCollar quarterWest at *
        omega
      · exact columnEast
    have boundaryBounds : InCollar
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY) boundary := by
      constructor
      · simp only [quarterWest, quarterSouth] at boundarySouth ⊢
        omega
      · simpa [quarterNorth, quarterEast] using boundaryNorth
    have interior : Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
        (quadrantAt column boundary) ≠ none := by
      rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      rcases orientation with orientation | orientation
      · rw [orientation.2]
        simp
      · rw [orientation.2]
        simp
    rcases horizontalInheritedSource phase depth grid parentX parentY
      columnBounds boundaryBounds sparseBoundary interior with ⟨source⟩
    have target := targets.row grid parentX parentY columnWest columnEast
      rowSouth rowNorth boundarySouth boundaryNorth notFits sparseBoundary
      createdRow orientation source
    have sourceFamily := source.fineFamily
    rw [fineGrid_eq phase depth grid] at sourceFamily
    exact ⟨source.family, sourceFamily, target⟩
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary createdColumn orientation
    have boundaryBounds : InCollar
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX) boundary := by
      constructor
      · unfold InCollar quarterWest at *
        omega
      · exact boundaryEast
    have rowBounds : InCollar
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY) row := by
      constructor
      · simp only [quarterWest, quarterSouth] at rowSouth ⊢
        omega
      · simpa [quarterNorth, quarterEast] using rowNorth
    have interior : Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
        (quadrantAt boundary row) ≠ none := by
      rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      rcases orientation with orientation | orientation
      · rw [orientation.2]
        simp
      · rw [orientation.2]
        simp
    rcases verticalInheritedSource phase depth grid parentX parentY
      boundaryBounds rowBounds sparseBoundary interior with ⟨source⟩
    have target := targets.column grid parentX parentY columnWest columnEast
      boundaryWest boundaryEast rowSouth rowNorth notFits sparseBoundary
      createdColumn orientation source
    have sourceFamily := source.fineFamily
    rw [fineGrid_eq phase depth grid] at sourceFamily
    exact ⟨source.family, sourceFamily, target⟩

end PairCoverSeamResidualDirectPathInheritedFamilyTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
