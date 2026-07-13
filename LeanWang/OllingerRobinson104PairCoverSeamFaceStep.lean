/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamFaceRefinement

/-!
# Isolate the created-coordinate seam recurrence

The inherited refinement theorem handles a seam query when its query line,
free line, and nearest selected boundary are literal sparse coordinates.  This
module proves that a one-step face recurrence needs no other global case: it is
enough to discharge queries for which at least one of those three coordinates
is genuinely created by the two-level refinement.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamFaceStep

open RedCycles RedShadeCycles RedShadeGraphRefinement RedShadePaths
  ShadedFreeLineRecurrence
  ShadedPlaneSignalGrid ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal PairCoverSeamArithmetic
  PairCoverSeamComposition PairCoverSeamFacesAt PairCoverSeamFaceRefinement
  PairCoverSeamRefinementCoordinates RefinedCoordinateProjection

set_option maxRecDepth 20000

/-- The genuinely created cases of the vertical face recurrence. -/
structure CreatedVerticalBoundaryFacesAt (phase : Phase) (depth : Nat) : Prop where
  above : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    (∀ y, row < y → y < boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬(IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
      IsSparseCoordinate boundary) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .north
  below : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    (∀ y, boundary < y → y < row →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬(IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
      IsSparseCoordinate boundary) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .south

/-- Horizontal dual of `CreatedVerticalBoundaryFacesAt`. -/
structure CreatedHorizontalBoundaryFacesAt (phase : Phase) (depth : Nat) : Prop where
  right : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    (∀ x, column < x → x < boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬(IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
      IsSparseCoordinate boundary) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .east
  left : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    (∀ x, boundary < x → x < column →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬(IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
      IsSparseCoordinate boundary) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .west

private theorem lower_sparse_bound
    {phase : Phase} {depth parent coarse : Nat}
    (bound : quarterWest (successorWest phase (depth + 1) parent) <
      sparseCoordinate coarse) :
    quarterWest (successorWest phase depth parent) < coarse := by
  rw [← sparseCoordinate_lt_iff, sparseCoordinate_quarterWest,
    ← successorWest_succ]
  exact bound

private theorem upper_sparse_bound
    {phase : Phase} {depth parent coarse : Nat}
    (bound : sparseCoordinate coarse <
      quarterEast (successorEast phase (depth + 1) parent)) :
    coarse < quarterEast (successorEast phase depth parent) := by
  rw [← sparseCoordinate_lt_iff, sparseCoordinate_quarterEast,
    ← successorEast_succ]
  exact bound

private theorem lower_sparse_south_bound
    {phase : Phase} {depth parent coarse : Nat}
    (bound : quarterSouth (successorWest phase (depth + 1) parent) <
      sparseCoordinate coarse) :
    quarterSouth (successorWest phase depth parent) < coarse := by
  rw [← sparseCoordinate_lt_iff, sparseCoordinate_quarterSouth,
    ← successorWest_succ]
  exact bound

private theorem upper_sparse_north_bound
    {phase : Phase} {depth parent coarse : Nat}
    (bound : sparseCoordinate coarse <
      quarterNorth (successorEast phase (depth + 1) parent)) :
    coarse < quarterNorth (successorEast phase depth parent) := by
  rw [← sparseCoordinate_lt_iff, sparseCoordinate_quarterNorth,
    ← successorEast_succ]
  exact bound

/-- Inherited faces plus the genuinely created cases give the full next-depth
vertical face invariant. -/
theorem VerticalBoundaryFacesAt.refine
    {phase : Phase} {depth : Nat}
    (faces : VerticalBoundaryFacesAt phase depth)
    (created : CreatedVerticalBoundaryFacesAt phase depth) :
    VerticalBoundaryFacesAt phase (depth + 1) := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hrowSouth hrowBoundary hboundaryNorth
      freeRow selected noneBetween notFits
    by_cases inherited : IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
        IsSparseCoordinate boundary
    · rcases inherited with
        ⟨⟨oldColumn, rfl⟩, ⟨oldRow, rfl⟩, ⟨oldBoundary, rfl⟩⟩
      exact PairCoverSeamFaceRefinement.VerticalBoundaryFacesAt.above_sparse
        faces grid shadeGrid parentX parentY valid
        (lower_sparse_bound hcolumnWest) (upper_sparse_bound hcolumnEast)
        (lower_sparse_south_bound hrowSouth)
        ((sparseCoordinate_lt_iff).1 hrowBoundary)
        (upper_sparse_north_bound hboundaryNorth) freeRow selected
        noneBetween notFits
    · exact created.above grid shadeGrid parentX parentY valid hcolumnWest
        hcolumnEast hrowSouth hrowBoundary hboundaryNorth freeRow selected
        noneBetween notFits inherited
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hboundarySouth hboundaryRow hrowNorth
      freeRow selected noneBetween notFits
    by_cases inherited : IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
        IsSparseCoordinate boundary
    · rcases inherited with
        ⟨⟨oldColumn, rfl⟩, ⟨oldRow, rfl⟩, ⟨oldBoundary, rfl⟩⟩
      exact PairCoverSeamFaceRefinement.VerticalBoundaryFacesAt.below_sparse
        faces grid shadeGrid parentX parentY valid
        (lower_sparse_bound hcolumnWest) (upper_sparse_bound hcolumnEast)
        (lower_sparse_south_bound hboundarySouth)
        ((sparseCoordinate_lt_iff).1 hboundaryRow)
        (upper_sparse_north_bound hrowNorth) freeRow selected
        noneBetween notFits
    · exact created.below grid shadeGrid parentX parentY valid hcolumnWest
        hcolumnEast hboundarySouth hboundaryRow hrowNorth freeRow selected
        noneBetween notFits inherited

/-- Horizontal dual of `VerticalBoundaryFacesAt.refine`. -/
theorem HorizontalBoundaryFacesAt.refine
    {phase : Phase} {depth : Nat}
    (faces : HorizontalBoundaryFacesAt phase depth)
    (created : CreatedHorizontalBoundaryFacesAt phase depth) :
    HorizontalBoundaryFacesAt phase (depth + 1) := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnBoundary hboundaryEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits
    by_cases inherited : IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
        IsSparseCoordinate boundary
    · rcases inherited with
        ⟨⟨oldColumn, rfl⟩, ⟨oldRow, rfl⟩, ⟨oldBoundary, rfl⟩⟩
      exact PairCoverSeamFaceRefinement.HorizontalBoundaryFacesAt.right_sparse
        faces grid shadeGrid parentX parentY valid
        (lower_sparse_bound hcolumnWest)
        ((sparseCoordinate_lt_iff).1 hcolumnBoundary)
        (upper_sparse_bound hboundaryEast)
        (lower_sparse_south_bound hrowSouth)
        (upper_sparse_north_bound hrowNorth) freeColumn selected
        noneBetween notFits
    · exact created.right grid shadeGrid parentX parentY valid hcolumnWest
        hcolumnBoundary hboundaryEast hrowSouth hrowNorth freeColumn selected
        noneBetween notFits inherited
  · intro grid shadeGrid parentX parentY column row boundary valid
      hboundaryWest hboundaryColumn hcolumnEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits
    by_cases inherited : IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
        IsSparseCoordinate boundary
    · rcases inherited with
        ⟨⟨oldColumn, rfl⟩, ⟨oldRow, rfl⟩, ⟨oldBoundary, rfl⟩⟩
      exact PairCoverSeamFaceRefinement.HorizontalBoundaryFacesAt.left_sparse
        faces grid shadeGrid parentX parentY valid
        (lower_sparse_bound hboundaryWest)
        ((sparseCoordinate_lt_iff).1 hboundaryColumn)
        (upper_sparse_bound hcolumnEast)
        (lower_sparse_south_bound hrowSouth)
        (upper_sparse_north_bound hrowNorth) freeColumn selected
        noneBetween notFits
    · exact created.left grid shadeGrid parentX parentY valid hboundaryWest
        hboundaryColumn hcolumnEast hrowSouth hrowNorth freeColumn selected
        noneBetween notFits inherited

end PairCoverSeamFaceStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
