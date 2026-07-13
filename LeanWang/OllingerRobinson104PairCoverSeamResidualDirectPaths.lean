/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycles

/-!
# Direct path certificates for residual seams

The semantic contradiction only needs an even path from the selected boundary
to either a transverse segment on the free line or a parallel segment strictly
between the source and that line.  Requiring this path to factor through a
canonical square cycle is sufficient but unnecessarily strong near the outer
board boundary.  This module records the direct, shade-independent obligation.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPaths

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualCycles
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence ShadedPlaneSignalGrid
  Signals.FreeCellLocal SparseFreeLinePlaneBase

set_option maxRecDepth 20000

/-- The two direct red-graph paths needed by all four residual orientations. -/
structure DirectResidualPathsAt (phase : Phase) (depth : Nat) : Prop where
  row : forall (grid : Nat -> Nat -> Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column ->
    column < quarterEast (successorEast phase (depth + 1) parentX) ->
    quarterSouth (successorWest phase (depth + 1) parentY) < row ->
    row < quarterNorth (successorEast phase (depth + 1) parentY) ->
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary ->
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) ->
    Not (FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary) ->
    IsSparseCoordinate boundary ->
    Not (IsSparseCoordinate row) ->
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) column boundary)
      (quadrantAt column boundary) ≠ none ->
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary
  column : forall (grid : Nat -> Nat -> Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column ->
    column < quarterEast (successorEast phase (depth + 1) parentX) ->
    quarterWest (successorWest phase (depth + 1) parentX) < boundary ->
    boundary < quarterEast (successorEast phase (depth + 1) parentX) ->
    quarterSouth (successorWest phase (depth + 1) parentY) < row ->
    row < quarterNorth (successorEast phase (depth + 1) parentY) ->
    Not (FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary) ->
    IsSparseCoordinate boundary ->
    Not (IsSparseCoordinate column) ->
    Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) boundary row)
      (quadrantAt boundary row) ≠ none ->
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary

private theorem horizontalInterior_ne_none_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.VerticalInterior}
    (selected : ShadedSignals.selectedHorizontalFor component quadrant state =
      some interior) :
    Signals.horizontalInterior? component quadrant ≠ none := by
  unfold ShadedSignals.selectedHorizontalFor at selected
  split at selected
  · simp [selected]
  · contradiction

private theorem verticalInterior_ne_none_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.HorizontalInterior}
    (selected : ShadedSignals.selectedVerticalFor component quadrant state =
      some interior) :
    Signals.verticalInterior? component quadrant ≠ none := by
  unfold ShadedSignals.selectedVerticalFor at selected
  split at selected
  · simp [selected]
  · contradiction

/-- Direct row paths discharge both vertical residual orientations. -/
theorem DirectResidualPathsAt.verticalResidual
    {phase : Phase} {depth : Nat}
    (paths : DirectResidualPathsAt phase depth) :
    PairCoverSeamCreatedPaths.ResidualVerticalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      columnWest columnEast rowSouth rowBoundary boundaryNorth
      freeRow selected noneBetween notFits sparseBoundary createdRow
    cases selectedEq : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column boundary)
        (quadrantAt column boundary) (shadeGrid column boundary) with
    | none => exact (selected selectedEq).elim
    | some interior =>
        cases interior with
        | north => rfl
        | south =>
            exact (false_of_verticalSeamPath valid freeRow selected (by
              intro y between
              rcases between with between | between
              · exact noneBetween y between.1 between.2
              · omega)
              (paths.row grid parentX parentY columnWest columnEast rowSouth
                (rowBoundary.trans boundaryNorth)
                (rowSouth.trans rowBoundary) boundaryNorth notFits
                sparseBoundary createdRow
                (horizontalInterior_ne_none_of_selected selectedEq))).elim
  · intro grid shadeGrid parentX parentY column row boundary valid
      columnWest columnEast boundarySouth boundaryRow rowNorth
      freeRow selected noneBetween notFits sparseBoundary createdRow
    cases selectedEq : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column boundary)
        (quadrantAt column boundary) (shadeGrid column boundary) with
    | none => exact (selected selectedEq).elim
    | some interior =>
        cases interior with
        | north =>
            exact (false_of_verticalSeamPath valid freeRow selected (by
              intro y between
              rcases between with between | between
              · omega
              · exact noneBetween y between.1 between.2)
              (paths.row grid parentX parentY columnWest columnEast
                (boundarySouth.trans boundaryRow) rowNorth boundarySouth
                (boundaryRow.trans rowNorth) notFits sparseBoundary createdRow
                (horizontalInterior_ne_none_of_selected selectedEq))).elim
        | south => rfl

/-- Direct column paths discharge both horizontal residual orientations. -/
theorem DirectResidualPathsAt.horizontalResidual
    {phase : Phase} {depth : Nat}
    (paths : DirectResidualPathsAt phase depth) :
    PairCoverSeamCreatedPaths.ResidualHorizontalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      columnWest columnBoundary boundaryEast rowSouth rowNorth
      freeColumn selected noneBetween notFits sparseBoundary createdColumn
    cases selectedEq : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          boundary row)
        (quadrantAt boundary row) (shadeGrid boundary row) with
    | none => exact (selected selectedEq).elim
    | some interior =>
        cases interior with
        | west =>
            exact (false_of_horizontalSeamPath valid freeColumn selected (by
              intro x between
              rcases between with between | between
              · exact noneBetween x between.1 between.2
              · omega)
              (paths.column grid parentX parentY columnWest
                (columnBoundary.trans boundaryEast)
                (columnWest.trans columnBoundary) boundaryEast rowSouth
                rowNorth notFits sparseBoundary createdColumn
                (verticalInterior_ne_none_of_selected selectedEq))).elim
        | east => rfl
  · intro grid shadeGrid parentX parentY column row boundary valid
      boundaryWest boundaryColumn columnEast rowSouth rowNorth
      freeColumn selected noneBetween notFits sparseBoundary createdColumn
    cases selectedEq : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          boundary row)
        (quadrantAt boundary row) (shadeGrid boundary row) with
    | none => exact (selected selectedEq).elim
    | some interior =>
        cases interior with
        | west => rfl
        | east =>
            exact (false_of_horizontalSeamPath valid freeColumn selected (by
              intro x between
              rcases between with between | between
              · omega
              · exact noneBetween x between.1 between.2)
              (paths.column grid parentX parentY
                (boundaryWest.trans boundaryColumn) columnEast boundaryWest
                (boundaryColumn.trans columnEast) rowSouth rowNorth notFits
                sparseBoundary createdColumn
                (verticalInterior_ne_none_of_selected selectedEq))).elim

end PairCoverSeamResidualDirectPaths
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
