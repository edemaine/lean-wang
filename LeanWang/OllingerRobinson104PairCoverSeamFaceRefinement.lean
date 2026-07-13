/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamFacesAt
import LeanWang.OllingerRobinson104PairCoverSeamProjection

/-!
# Refining pair-cover boundary faces

This module lifts a fixed-depth face certificate through the inherited sparse
copy of the next two-substitution refinement.  Newly created coordinate
intervals are handled separately.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamFaceRefinement

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphProjection RedShadePaths ShadedFreeLineRecurrence
  ShadedPlaneSignalGrid ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal PairCoverSeamArithmetic
  PairCoverSeamComposition PairCoverSeamFacesAt PairCoverSeamProjection
  PairCoverSeamRefinementCoordinates

set_option maxRecDepth 20000

/-- The `above` face conclusion lifts when the query, free row, and selected
boundary are all literal sparse coordinates. -/
theorem VerticalBoundaryFacesAt.above_sparse
    {phase : Phase} {depth : Nat}
    (faces : VerticalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY : Nat) {column row boundary : Nat}
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid)
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowBoundary : row < boundary)
    (hboundaryNorth : boundary < quarterNorth
      (successorEast phase depth parentY))
    (freeRow : IsFreeRow
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) (sparseCoordinate row))
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate column) (sparseCoordinate boundary))
      (quadrantAt (sparseCoordinate column) (sparseCoordinate boundary))
      (shadeGrid (sparseCoordinate column) (sparseCoordinate boundary)) ≠ none)
    (noneBetween : ∀ y, sparseCoordinate row < y →
      y < sparseCoordinate boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) (sparseCoordinate column) y)
        (quadrantAt (sparseCoordinate column) y)
        (shadeGrid (sparseCoordinate column) y) = none)
    (notFits : ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      (sparseCoordinate column) (sparseCoordinate row)
      (sparseCoordinate boundary)) :
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate column) (sparseCoordinate boundary))
      (quadrantAt (sparseCoordinate column) (sparseCoordinate boundary))
      (shadeGrid (sparseCoordinate column) (sparseCoordinate boundary)) =
        some .north := by
  let oldGrid := iterateRefine 2 (refinedGrid phase depth grid)
  have valid' : ValidShadeGrid (iterateRefine 2 oldGrid) shadeGrid := by
    simpa only [oldGrid, refinedGrid_succ] using valid
  have freeRow' : IsFreeRow (iterateRefine 2 oldGrid) shadeGrid
      (4 * successorWest phase depth parentX)
      (4 * successorEast phase depth parentX) (sparseCoordinate row) := by
    simpa only [oldGrid, refinedGrid_succ, successorWest_succ,
      successorEast_succ] using freeRow
  have selected' : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 oldGrid)
        (sparseCoordinate column) (sparseCoordinate boundary))
      (quadrantAt (sparseCoordinate column) (sparseCoordinate boundary))
      (shadeGrid (sparseCoordinate column) (sparseCoordinate boundary)) ≠ none := by
    simpa only [oldGrid, refinedGrid_succ] using selected
  have noneBetween' : ∀ y, sparseCoordinate row < y →
      y < sparseCoordinate boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 oldGrid) (sparseCoordinate column) y)
        (quadrantAt (sparseCoordinate column) y)
        (shadeGrid (sparseCoordinate column) y) = none := by
    simpa only [oldGrid, refinedGrid_succ] using noneBetween
  have freeCoarse : IsFreeRow oldGrid (projectStateGrid shadeGrid)
      (successorWest phase depth parentX)
      (successorEast phase depth parentX) row :=
    isFreeRow_project_of_sparse valid' freeRow'
  have selectedCoarse : ShadedSignals.selectedHorizontalFor
      (componentAt oldGrid column boundary) (quadrantAt column boundary)
      (projectStateGrid shadeGrid column boundary) ≠ none := by
    rw [selectedHorizontal_projectStateGrid_eq_sparse valid']
    exact selected'
  have noneBetweenCoarse : ∀ y, row < y → y < boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt oldGrid column y) (quadrantAt column y)
        (projectStateGrid shadeGrid column y) = none :=
    noSelectedHorizontalBetween_project_of_sparse valid' noneBetween'
  have notFitsCoarse : ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary := by
    simpa only [RefinedCoordinateProjection.coarseCoordinate_sparseCoordinate] using
      notFitsContainedVerticalChild_coarseCoordinate notFits
  have coarseResult := faces.above grid (projectStateGrid shadeGrid)
    parentX parentY (projectStateGrid_valid valid') hcolumnWest hcolumnEast
    hrowSouth hrowBoundary hboundaryNorth freeCoarse selectedCoarse
    noneBetweenCoarse notFitsCoarse
  rw [selectedHorizontal_projectStateGrid_eq_sparse valid'] at coarseResult
  simpa only [oldGrid, refinedGrid_succ] using coarseResult

/-- The `below` face conclusion lifts on literal sparse coordinates. -/
theorem VerticalBoundaryFacesAt.below_sparse
    {phase : Phase} {depth : Nat}
    (faces : VerticalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY : Nat) {column row boundary : Nat}
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid)
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hboundarySouth : quarterSouth
      (successorWest phase depth parentY) < boundary)
    (hboundaryRow : boundary < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (freeRow : IsFreeRow
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) (sparseCoordinate row))
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate column) (sparseCoordinate boundary))
      (quadrantAt (sparseCoordinate column) (sparseCoordinate boundary))
      (shadeGrid (sparseCoordinate column) (sparseCoordinate boundary)) ≠ none)
    (noneBetween : ∀ y, sparseCoordinate boundary < y →
      y < sparseCoordinate row →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) (sparseCoordinate column) y)
        (quadrantAt (sparseCoordinate column) y)
        (shadeGrid (sparseCoordinate column) y) = none)
    (notFits : ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      (sparseCoordinate column) (sparseCoordinate row)
      (sparseCoordinate boundary)) :
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate column) (sparseCoordinate boundary))
      (quadrantAt (sparseCoordinate column) (sparseCoordinate boundary))
      (shadeGrid (sparseCoordinate column) (sparseCoordinate boundary)) =
        some .south := by
  let oldGrid := iterateRefine 2 (refinedGrid phase depth grid)
  have valid' : ValidShadeGrid (iterateRefine 2 oldGrid) shadeGrid := by
    simpa only [oldGrid, refinedGrid_succ] using valid
  have freeRow' : IsFreeRow (iterateRefine 2 oldGrid) shadeGrid
      (4 * successorWest phase depth parentX)
      (4 * successorEast phase depth parentX) (sparseCoordinate row) := by
    simpa only [oldGrid, refinedGrid_succ, successorWest_succ,
      successorEast_succ] using freeRow
  have selected' : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 oldGrid)
        (sparseCoordinate column) (sparseCoordinate boundary))
      (quadrantAt (sparseCoordinate column) (sparseCoordinate boundary))
      (shadeGrid (sparseCoordinate column) (sparseCoordinate boundary)) ≠ none := by
    simpa only [oldGrid, refinedGrid_succ] using selected
  have noneBetween' : ∀ y, sparseCoordinate boundary < y →
      y < sparseCoordinate row →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 oldGrid) (sparseCoordinate column) y)
        (quadrantAt (sparseCoordinate column) y)
        (shadeGrid (sparseCoordinate column) y) = none := by
    simpa only [oldGrid, refinedGrid_succ] using noneBetween
  have freeCoarse : IsFreeRow oldGrid (projectStateGrid shadeGrid)
      (successorWest phase depth parentX)
      (successorEast phase depth parentX) row :=
    isFreeRow_project_of_sparse valid' freeRow'
  have selectedCoarse : ShadedSignals.selectedHorizontalFor
      (componentAt oldGrid column boundary) (quadrantAt column boundary)
      (projectStateGrid shadeGrid column boundary) ≠ none := by
    rw [selectedHorizontal_projectStateGrid_eq_sparse valid']
    exact selected'
  have noneBetweenCoarse : ∀ y, boundary < y → y < row →
      ShadedSignals.selectedHorizontalFor
        (componentAt oldGrid column y) (quadrantAt column y)
        (projectStateGrid shadeGrid column y) = none :=
    noSelectedHorizontalBetween_project_of_sparse valid' noneBetween'
  have notFitsCoarse : ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary := by
    simpa only [RefinedCoordinateProjection.coarseCoordinate_sparseCoordinate] using
      notFitsContainedVerticalChild_coarseCoordinate notFits
  have coarseResult := faces.below grid (projectStateGrid shadeGrid)
    parentX parentY (projectStateGrid_valid valid') hcolumnWest hcolumnEast
    hboundarySouth hboundaryRow hrowNorth freeCoarse selectedCoarse
    noneBetweenCoarse notFitsCoarse
  rw [selectedHorizontal_projectStateGrid_eq_sparse valid'] at coarseResult
  simpa only [oldGrid, refinedGrid_succ] using coarseResult

/-- The `right` face conclusion lifts on literal sparse coordinates. -/
theorem HorizontalBoundaryFacesAt.right_sparse
    {phase : Phase} {depth : Nat}
    (faces : HorizontalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY : Nat) {column row boundary : Nat}
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid)
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnBoundary : column < boundary)
    (hboundaryEast : boundary < quarterEast
      (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (freeColumn : IsFreeColumn
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) (sparseCoordinate column))
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate boundary) (sparseCoordinate row))
      (quadrantAt (sparseCoordinate boundary) (sparseCoordinate row))
      (shadeGrid (sparseCoordinate boundary) (sparseCoordinate row)) ≠ none)
    (noneBetween : ∀ x, sparseCoordinate column < x →
      x < sparseCoordinate boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) x (sparseCoordinate row))
        (quadrantAt x (sparseCoordinate row))
        (shadeGrid x (sparseCoordinate row)) = none)
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      (sparseCoordinate column) (sparseCoordinate row)
      (sparseCoordinate boundary)) :
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate boundary) (sparseCoordinate row))
      (quadrantAt (sparseCoordinate boundary) (sparseCoordinate row))
      (shadeGrid (sparseCoordinate boundary) (sparseCoordinate row)) =
        some .east := by
  let oldGrid := iterateRefine 2 (refinedGrid phase depth grid)
  have valid' : ValidShadeGrid (iterateRefine 2 oldGrid) shadeGrid := by
    simpa only [oldGrid, refinedGrid_succ] using valid
  have freeColumn' : IsFreeColumn (iterateRefine 2 oldGrid) shadeGrid
      (4 * successorWest phase depth parentY)
      (4 * successorEast phase depth parentY) (sparseCoordinate column) := by
    simpa only [oldGrid, refinedGrid_succ, successorWest_succ,
      successorEast_succ] using freeColumn
  have selected' : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 oldGrid)
        (sparseCoordinate boundary) (sparseCoordinate row))
      (quadrantAt (sparseCoordinate boundary) (sparseCoordinate row))
      (shadeGrid (sparseCoordinate boundary) (sparseCoordinate row)) ≠ none := by
    simpa only [oldGrid, refinedGrid_succ] using selected
  have noneBetween' : ∀ x, sparseCoordinate column < x →
      x < sparseCoordinate boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 oldGrid) x (sparseCoordinate row))
        (quadrantAt x (sparseCoordinate row))
        (shadeGrid x (sparseCoordinate row)) = none := by
    simpa only [oldGrid, refinedGrid_succ] using noneBetween
  have freeCoarse : IsFreeColumn oldGrid (projectStateGrid shadeGrid)
      (successorWest phase depth parentY)
      (successorEast phase depth parentY) column :=
    isFreeColumn_project_of_sparse valid' freeColumn'
  have selectedCoarse : ShadedSignals.selectedVerticalFor
      (componentAt oldGrid boundary row) (quadrantAt boundary row)
      (projectStateGrid shadeGrid boundary row) ≠ none := by
    rw [selectedVertical_projectStateGrid_eq_sparse valid']
    exact selected'
  have noneBetweenCoarse : ∀ x, column < x → x < boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt oldGrid x row) (quadrantAt x row)
        (projectStateGrid shadeGrid x row) = none :=
    noSelectedVerticalBetween_project_of_sparse valid' noneBetween'
  have notFitsCoarse : ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary := by
    simpa only [RefinedCoordinateProjection.coarseCoordinate_sparseCoordinate] using
      notFitsContainedHorizontalChild_coarseCoordinate notFits
  have coarseResult := faces.right grid (projectStateGrid shadeGrid)
    parentX parentY (projectStateGrid_valid valid') hcolumnWest
    hcolumnBoundary hboundaryEast hrowSouth hrowNorth freeCoarse
    selectedCoarse noneBetweenCoarse notFitsCoarse
  rw [selectedVertical_projectStateGrid_eq_sparse valid'] at coarseResult
  simpa only [oldGrid, refinedGrid_succ] using coarseResult

/-- The `left` face conclusion lifts on literal sparse coordinates. -/
theorem HorizontalBoundaryFacesAt.left_sparse
    {phase : Phase} {depth : Nat}
    (faces : HorizontalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY : Nat) {column row boundary : Nat}
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid)
    (hboundaryWest : quarterWest
      (successorWest phase depth parentX) < boundary)
    (hboundaryColumn : boundary < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (freeColumn : IsFreeColumn
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) (sparseCoordinate column))
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate boundary) (sparseCoordinate row))
      (quadrantAt (sparseCoordinate boundary) (sparseCoordinate row))
      (shadeGrid (sparseCoordinate boundary) (sparseCoordinate row)) ≠ none)
    (noneBetween : ∀ x, sparseCoordinate boundary < x →
      x < sparseCoordinate column →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) x (sparseCoordinate row))
        (quadrantAt x (sparseCoordinate row))
        (shadeGrid x (sparseCoordinate row)) = none)
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      (sparseCoordinate column) (sparseCoordinate row)
      (sparseCoordinate boundary)) :
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        (sparseCoordinate boundary) (sparseCoordinate row))
      (quadrantAt (sparseCoordinate boundary) (sparseCoordinate row))
      (shadeGrid (sparseCoordinate boundary) (sparseCoordinate row)) =
        some .west := by
  let oldGrid := iterateRefine 2 (refinedGrid phase depth grid)
  have valid' : ValidShadeGrid (iterateRefine 2 oldGrid) shadeGrid := by
    simpa only [oldGrid, refinedGrid_succ] using valid
  have freeColumn' : IsFreeColumn (iterateRefine 2 oldGrid) shadeGrid
      (4 * successorWest phase depth parentY)
      (4 * successorEast phase depth parentY) (sparseCoordinate column) := by
    simpa only [oldGrid, refinedGrid_succ, successorWest_succ,
      successorEast_succ] using freeColumn
  have selected' : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 oldGrid)
        (sparseCoordinate boundary) (sparseCoordinate row))
      (quadrantAt (sparseCoordinate boundary) (sparseCoordinate row))
      (shadeGrid (sparseCoordinate boundary) (sparseCoordinate row)) ≠ none := by
    simpa only [oldGrid, refinedGrid_succ] using selected
  have noneBetween' : ∀ x, sparseCoordinate boundary < x →
      x < sparseCoordinate column →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 oldGrid) x (sparseCoordinate row))
        (quadrantAt x (sparseCoordinate row))
        (shadeGrid x (sparseCoordinate row)) = none := by
    simpa only [oldGrid, refinedGrid_succ] using noneBetween
  have freeCoarse : IsFreeColumn oldGrid (projectStateGrid shadeGrid)
      (successorWest phase depth parentY)
      (successorEast phase depth parentY) column :=
    isFreeColumn_project_of_sparse valid' freeColumn'
  have selectedCoarse : ShadedSignals.selectedVerticalFor
      (componentAt oldGrid boundary row) (quadrantAt boundary row)
      (projectStateGrid shadeGrid boundary row) ≠ none := by
    rw [selectedVertical_projectStateGrid_eq_sparse valid']
    exact selected'
  have noneBetweenCoarse : ∀ x, boundary < x → x < column →
      ShadedSignals.selectedVerticalFor
        (componentAt oldGrid x row) (quadrantAt x row)
        (projectStateGrid shadeGrid x row) = none :=
    noSelectedVerticalBetween_project_of_sparse valid' noneBetween'
  have notFitsCoarse : ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary := by
    simpa only [RefinedCoordinateProjection.coarseCoordinate_sparseCoordinate] using
      notFitsContainedHorizontalChild_coarseCoordinate notFits
  have coarseResult := faces.left grid (projectStateGrid shadeGrid)
    parentX parentY (projectStateGrid_valid valid') hboundaryWest
    hboundaryColumn hcolumnEast hrowSouth hrowNorth freeCoarse
    selectedCoarse noneBetweenCoarse notFitsCoarse
  rw [selectedVertical_projectStateGrid_eq_sparse valid'] at coarseResult
  simpa only [oldGrid, refinedGrid_succ] using coarseResult

end PairCoverSeamFaceRefinement
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
