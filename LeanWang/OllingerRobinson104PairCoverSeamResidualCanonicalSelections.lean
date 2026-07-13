/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBridges

/-!
# Localized descendant selections for residual seams

The earlier factorization asked for a descendant selection from every
arbitrary oriented cycle.  The hierarchy proof only supplies one particular
canonical ancestor, and its level and block address are essential to choosing
a connected separating cycle.  This module states the selection obligation
with that exact witness and assembles it directly with the all-depth ancestry
theorem.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalSelections

open RedCycles RedShadeCycles
  PairCoverSeamArithmetic PairCoverSeamResidualCycles
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorHierarchy
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  RefinedCoordinateProjection SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Source-dependent geometric selection obligations.  Unlike
`ResidualDescendantSelectionsAt`, these retain the canonical hierarchy address
and the actual even path reached by the selected source. -/
structure LocalizedResidualSelectionsAt (phase : Phase) (depth : Nat) : Prop where
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
    CanonicalCycleAncestorWithin
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (PairCoverSeamShadePaths.horizontalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (outerLevel phase (depth + 1)) parentX parentY →
    RowSeparatingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column boundary row
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
    CanonicalCycleAncestorWithin
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (PairCoverSeamShadePaths.verticalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (outerLevel phase (depth + 1)) parentX parentY →
    ColumnSeparatingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary row column

private theorem horizontalInterior_ne_none_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.VerticalInterior}
    (selected : ShadedSignals.selectedHorizontalFor component quadrant state =
      some interior) :
    Signals.horizontalInterior? component quadrant ≠ none := by
  unfold ShadedSignals.selectedHorizontalFor at selected
  split at selected
  · simpa [selected]
  · contradiction

private theorem verticalInterior_ne_none_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.HorizontalInterior}
    (selected : ShadedSignals.selectedVerticalFor component quadrant state =
      some interior) :
    Signals.verticalInterior? component quadrant ≠ none := by
  unfold ShadedSignals.selectedVerticalFor at selected
  split at selected
  · simpa [selected]
  · contradiction

private theorem horizontalAncestor
    {phase : Phase} {depth : Nat}
    (grid : Nat → Nat → Index) (parentX parentY column boundary : Nat)
    (columnWest : quarterWest
      (successorWest phase (depth + 1) parentX) < column)
    (columnEast : column < quarterEast
      (successorEast phase (depth + 1) parentX))
    (boundarySouth : quarterSouth
      (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryNorth : boundary < quarterNorth
      (successorEast phase (depth + 1) parentY))
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) column boundary)
      (quadrantAt column boundary) ≠ none) :
    CanonicalCycleAncestorWithin
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (PairCoverSeamShadePaths.horizontalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (outerLevel phase (depth + 1)) parentX parentY := by
  have hierarchy := sourceAncestorsWithinAt phase (depth + 1)
    grid parentX parentY
  have interior' : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
    exact interior
  have ancestor := hierarchy.horizontal
    (by
      constructor
      · unfold quarterWest at columnWest ⊢
        omega
      · exact columnEast)
    (by
      constructor
      · unfold quarterSouth at boundarySouth
        unfold quarterWest
        omega
      · simpa [quarterNorth, quarterEast] using boundaryNorth)
    interior'
  simpa only [SparseFreeLinePlaneLocalStep.refinedGrid_succ] using ancestor

private theorem verticalAncestor
    {phase : Phase} {depth : Nat}
    (grid : Nat → Nat → Index) (parentX parentY boundary row : Nat)
    (boundaryWest : quarterWest
      (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryEast : boundary < quarterEast
      (successorEast phase (depth + 1) parentX))
    (rowSouth : quarterSouth
      (successorWest phase (depth + 1) parentY) < row)
    (rowNorth : row < quarterNorth
      (successorEast phase (depth + 1) parentY))
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) boundary row)
      (quadrantAt boundary row) ≠ none) :
    CanonicalCycleAncestorWithin
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (PairCoverSeamShadePaths.verticalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (outerLevel phase (depth + 1)) parentX parentY := by
  have hierarchy := sourceAncestorsWithinAt phase (depth + 1)
    grid parentX parentY
  have interior' : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
    exact interior
  have ancestor := hierarchy.vertical
    (by
      constructor
      · unfold quarterWest at boundaryWest ⊢
        omega
      · exact boundaryEast)
    (by
      constructor
      · unfold quarterSouth at rowSouth
        unfold quarterWest
        omega
      · simpa [quarterNorth, quarterEast] using rowNorth)
    interior'
  simpa only [SparseFreeLinePlaneLocalStep.refinedGrid_succ] using ancestor

/-- Localized selections and the proved all-depth source ancestry give all
four residual cycle witnesses. -/
theorem residualCycleWitnessesAt
    {phase : Phase} {depth : Nat}
    (selections : LocalizedResidualSelectionsAt phase depth) :
    ResidualCycleWitnessesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary
      columnWest columnEast rowSouth rowBoundary boundaryNorth selected
      _ notFits sparseBoundary createdRow
    apply selections.row grid parentX parentY columnWest columnEast rowSouth
      (rowBoundary.trans boundaryNorth) (rowSouth.trans rowBoundary)
      boundaryNorth notFits sparseBoundary createdRow
    exact horizontalAncestor grid parentX parentY column boundary
      columnWest columnEast (rowSouth.trans rowBoundary) boundaryNorth
      (horizontalInterior_ne_none_of_selected selected)
  · intro grid shadeGrid parentX parentY column row boundary
      columnWest columnEast boundarySouth boundaryRow rowNorth selected
      _ notFits sparseBoundary createdRow
    apply selections.row grid parentX parentY columnWest columnEast
      (boundarySouth.trans boundaryRow) rowNorth boundarySouth
      (boundaryRow.trans rowNorth) notFits sparseBoundary createdRow
    exact horizontalAncestor grid parentX parentY column boundary
      columnWest columnEast boundarySouth (boundaryRow.trans rowNorth)
      (horizontalInterior_ne_none_of_selected selected)
  · intro grid shadeGrid parentX parentY column row boundary
      columnWest columnBoundary boundaryEast rowSouth rowNorth selected
      _ notFits sparseBoundary createdColumn
    apply selections.column grid parentX parentY columnWest
      (columnBoundary.trans boundaryEast)
      (columnWest.trans columnBoundary) boundaryEast rowSouth rowNorth
      notFits sparseBoundary createdColumn
    exact verticalAncestor grid parentX parentY boundary row
      (columnWest.trans columnBoundary) boundaryEast rowSouth rowNorth
      (verticalInterior_ne_none_of_selected selected)
  · intro grid shadeGrid parentX parentY column row boundary
      boundaryWest boundaryColumn columnEast rowSouth rowNorth selected
      _ notFits sparseBoundary createdColumn
    apply selections.column grid parentX parentY
      (boundaryWest.trans boundaryColumn) columnEast boundaryWest
      (boundaryColumn.trans columnEast) rowSouth rowNorth
      notFits sparseBoundary createdColumn
    exact verticalAncestor grid parentX parentY boundary row
      boundaryWest (boundaryColumn.trans columnEast) rowSouth rowNorth
      (verticalInterior_ne_none_of_selected selected)

end PairCoverSeamResidualCanonicalSelections
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
