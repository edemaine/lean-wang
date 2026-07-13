/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedPaths
import LeanWang.OllingerRobinson104PairCoverSeamCycleContradictions

/-!
# Cycle witnesses for residual seam faces

The semantic residual is reduced to four geometric obligations.  In each
wrong-facing case, the hierarchy must supply a red cycle strictly crossed by
the created free line and an even route from the selected boundary into it.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCycles

open Figure16 OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadePaths RedShadeCycleConnectivity
  RedShadeGraphBoards ShadedPlaneSignalGrid Signals.FreeCellLocal
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase
  PairCoverSeamArithmetic PairCoverSeamShadePaths
  PairCoverSeamCycleContradictions PairCoverSeamComposition
  PairCoverSeamCreatedPaths PairCoverSeamPathSearch
  RefinedCoordinateProjection

set_option maxRecDepth 20000

/-- A cycle reached by the selected horizontal boundary and separating it from
the queried row.  Either the row crosses the cycle, or one horizontal side of
the cycle is a selected boundary strictly between the query and the source. -/
def RowSeparatingCycle
    (grid : Nat → Nat → Index) (outerWest outerEast column boundary row : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      quarterWest outerWest < quarterWest west ∧
      quarterWest west < quarterEast outerEast ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      ∃ entry, OnCycle west east south north entry ∧
        Path grid (horizontalPort grid column boundary) entry false ∧
        ((quarterSouth south < row ∧ row < quarterNorth north) ∨
          StrictBetween row boundary (quarterSouth south) ∨
          StrictBetween row boundary (quarterNorth north))

/-- Horizontal dual of `RowSeparatingCycle`. -/
def ColumnSeparatingCycle
    (grid : Nat → Nat → Index) (outerSouth outerNorth boundary row column : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      quarterSouth outerSouth < quarterSouth south ∧
      quarterSouth south < quarterNorth outerNorth ∧
      quarterSouth south < row ∧ row < quarterNorth north ∧
      ∃ entry, OnCycle west east south north entry ∧
        Path grid (verticalPort grid boundary row) entry false ∧
        ((quarterWest west < column ∧ column < quarterEast east) ∨
          StrictBetween column boundary (quarterWest west) ∨
          StrictBetween column boundary (quarterEast east))

/-- Pure hierarchy obligations for the four wrong-facing semantic residuals.
Validity and freeness are deliberately absent: they are consumed only after
the geometric witness has been constructed. -/
structure ResidualCycleWitnessesAt (phase : Phase) (depth : Nat) : Prop where
  above : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .south →
    (∀ y, row < y → y < boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate row →
    RowSeparatingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column boundary row
  below : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .north →
    (∀ y, boundary < y → y < row →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate row →
    RowSeparatingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column boundary row
  right : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .west →
    (∀ x, column < x → x < boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate column →
    ColumnSeparatingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary row column
  left : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .east →
    (∀ x, boundary < x → x < column →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate column →
    ColumnSeparatingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary row column

private theorem verticalInterior_ne_none_of_hasVertical
    (component : Figure16.Thick) (quadrant : Quadrant)
    (present : RedShades.hasVertical component quadrant = true) :
    Signals.verticalInterior? component quadrant ≠ none := by
  cases component <;> cases quadrant <;>
    simp_all [Signals.verticalInterior?, RedShades.hasVertical, Quadrant.xBit]

private theorem horizontalInterior_ne_none_of_hasHorizontal
    (component : Figure16.Thick) (quadrant : Quadrant)
    (present : RedShades.hasHorizontal component quadrant = true) :
    Signals.horizontalInterior? component quadrant ≠ none := by
  cases component <;> cases quadrant <;>
    simp_all [Signals.horizontalInterior?, RedShades.hasHorizontal, Quadrant.yBit]

private theorem verticalPort_on_west
    {grid : Nat → Nat → Index} {west east south north row : Nat}
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north) :
    OnCycle west east south north
      (verticalPort grid (quarterWest west) row) := by
  unfold verticalPort
  split
  · exact OnCycle.westSouth row rowSouth rowNorth
  · exact OnCycle.westNorth row rowSouth rowNorth

private theorem horizontalPort_on_south
    {grid : Nat → Nat → Index} {west east south north column : Nat}
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east) :
    OnCycle west east south north
      (horizontalPort grid column (quarterSouth south)) := by
  unfold horizontalPort
  split
  · exact OnCycle.southWest column columnWest columnEast
  · exact OnCycle.southEast column columnWest columnEast

private theorem horizontalPort_on_north
    {grid : Nat → Nat → Index} {west east south north column : Nat}
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east) :
    OnCycle west east south north
      (horizontalPort grid column (quarterNorth north)) := by
  unfold horizontalPort
  split
  · exact OnCycle.northWest column columnWest columnEast
  · exact OnCycle.northEast column columnWest columnEast

private theorem verticalPort_on_east
    {grid : Nat → Nat → Index} {west east south north row : Nat}
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north) :
    OnCycle west east south north
      (verticalPort grid (quarterEast east) row) := by
  unfold verticalPort
  split
  · exact OnCycle.eastSouth row rowSouth rowNorth
  · exact OnCycle.eastNorth row rowSouth rowNorth

private theorem rowSeparatingCycle_seamPath
    {grid : Nat → Nat → Index}
    {outerWest outerEast column boundary row : Nat}
    (separating : RowSeparatingCycle grid outerWest outerEast
      column boundary row) :
    VerticalSeamPath grid outerWest outerEast column row boundary := by
  rcases separating with ⟨west, east, south, north, cycle,
    cycleWestInside, cycleWestInside', columnWest, columnEast,
    entry, entryOnCycle, sourceToCycle, separation⟩
  rcases separation with crossing | southBetween | northBetween
  · left
    have targetPresent := RedShadeCycles.CycleOn.west_path
      cycle crossing.1 crossing.2
    have targetOnCycle : OnCycle west east south north
        (verticalPort grid (quarterWest west) row) :=
      verticalPort_on_west crossing.1 crossing.2
    refine ⟨quarterWest west, cycleWestInside, cycleWestInside',
      verticalInterior_ne_none_of_hasVertical _ _ targetPresent, ?_⟩
    exact Path.trans sourceToCycle
      (onCycle_connected cycle entryOnCycle targetOnCycle)
  · right
    have targetPresent := RedShadeCycles.CycleOn.south_path
      cycle columnWest columnEast
    have targetOnCycle : OnCycle west east south north
        (horizontalPort grid column (quarterSouth south)) :=
      horizontalPort_on_south columnWest columnEast
    refine ⟨quarterSouth south, southBetween,
      horizontalInterior_ne_none_of_hasHorizontal _ _ targetPresent, ?_⟩
    exact Path.trans sourceToCycle
      (onCycle_connected cycle entryOnCycle targetOnCycle)
  · right
    have targetPresent := RedShadeCycles.CycleOn.north_path
      cycle columnWest columnEast
    have targetOnCycle : OnCycle west east south north
        (horizontalPort grid column (quarterNorth north)) :=
      horizontalPort_on_north columnWest columnEast
    refine ⟨quarterNorth north, northBetween,
      horizontalInterior_ne_none_of_hasHorizontal _ _ targetPresent, ?_⟩
    exact Path.trans sourceToCycle
      (onCycle_connected cycle entryOnCycle targetOnCycle)

private theorem columnSeparatingCycle_seamPath
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column : Nat}
    (separating : ColumnSeparatingCycle grid outerSouth outerNorth
      boundary row column) :
    HorizontalSeamPath grid outerSouth outerNorth row column boundary := by
  rcases separating with ⟨west, east, south, north, cycle,
    cycleSouthInside, cycleSouthInside', rowSouth, rowNorth,
    entry, entryOnCycle, sourceToCycle, separation⟩
  rcases separation with crossing | westBetween | eastBetween
  · left
    have targetPresent := RedShadeCycles.CycleOn.south_path
      cycle crossing.1 crossing.2
    have targetOnCycle : OnCycle west east south north
        (horizontalPort grid column (quarterSouth south)) :=
      horizontalPort_on_south crossing.1 crossing.2
    refine ⟨quarterSouth south, cycleSouthInside, cycleSouthInside',
      horizontalInterior_ne_none_of_hasHorizontal _ _ targetPresent, ?_⟩
    exact Path.trans sourceToCycle
      (onCycle_connected cycle entryOnCycle targetOnCycle)
  · right
    have targetPresent := RedShadeCycles.CycleOn.west_path
      cycle rowSouth rowNorth
    have targetOnCycle : OnCycle west east south north
        (verticalPort grid (quarterWest west) row) :=
      verticalPort_on_west rowSouth rowNorth
    refine ⟨quarterWest west, westBetween,
      verticalInterior_ne_none_of_hasVertical _ _ targetPresent, ?_⟩
    exact Path.trans sourceToCycle
      (onCycle_connected cycle entryOnCycle targetOnCycle)
  · right
    have targetPresent := RedShadeCycles.CycleOn.east_path
      cycle rowSouth rowNorth
    have targetOnCycle : OnCycle west east south north
        (verticalPort grid (quarterEast east) row) :=
      verticalPort_on_east rowSouth rowNorth
    refine ⟨quarterEast east, eastBetween,
      verticalInterior_ne_none_of_hasVertical _ _ targetPresent, ?_⟩
    exact Path.trans sourceToCycle
      (onCycle_connected cycle entryOnCycle targetOnCycle)

private theorem false_of_rowSeparatingCycle
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {outerWest outerEast column boundary row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid outerWest outerEast row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (noneBetween : ∀ y, StrictBetween row boundary y →
      ShadedSignals.selectedHorizontalFor
        (componentAt grid column y) (quadrantAt column y)
        (stateGrid column y) = none)
    (separating : RowSeparatingCycle grid outerWest outerEast
      column boundary row) : False :=
  false_of_verticalSeamPath valid freeRow selected noneBetween
    (rowSeparatingCycle_seamPath separating)

private theorem false_of_columnSeparatingCycle
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {outerSouth outerNorth boundary row column : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid outerSouth outerNorth column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (noneBetween : ∀ x, StrictBetween column boundary x →
      ShadedSignals.selectedVerticalFor
        (componentAt grid x row) (quadrantAt x row)
        (stateGrid x row) = none)
    (separating : ColumnSeparatingCycle grid outerSouth outerNorth
      boundary row column) : False :=
  false_of_horizontalSeamPath valid freeColumn selected noneBetween
    (columnSeparatingCycle_seamPath separating)

/-- Cycle witnesses discharge both vertical residual orientations. -/
theorem ResidualCycleWitnessesAt.verticalResidual
    {phase : Phase} {depth : Nat}
    (witnesses : ResidualCycleWitnessesAt phase depth) :
    ResidualVerticalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hrowSouth hrowBoundary hboundaryNorth
      freeRow selected noneBetween notFits sparseBoundary createdRow
    cases hselected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column boundary)
        (quadrantAt column boundary) (shadeGrid column boundary) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | north => rfl
        | south =>
            exact (false_of_rowSeparatingCycle valid freeRow selected (by
              intro y hbetween
              rcases hbetween with hbetween | hbetween
              · exact noneBetween y hbetween.1 hbetween.2
              · omega)
              (witnesses.above grid shadeGrid parentX parentY hcolumnWest
                hcolumnEast hrowSouth hrowBoundary hboundaryNorth hselected
                noneBetween notFits sparseBoundary createdRow)).elim
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hboundarySouth hboundaryRow hrowNorth
      freeRow selected noneBetween notFits sparseBoundary createdRow
    cases hselected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column boundary)
        (quadrantAt column boundary) (shadeGrid column boundary) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | north =>
            exact (false_of_rowSeparatingCycle valid freeRow selected (by
              intro y hbetween
              rcases hbetween with hbetween | hbetween
              · omega
              · exact noneBetween y hbetween.1 hbetween.2)
              (witnesses.below grid shadeGrid parentX parentY hcolumnWest
                hcolumnEast hboundarySouth hboundaryRow hrowNorth hselected
                noneBetween notFits sparseBoundary createdRow)).elim
        | south => rfl

/-- Cycle witnesses discharge both horizontal residual orientations. -/
theorem ResidualCycleWitnessesAt.horizontalResidual
    {phase : Phase} {depth : Nat}
    (witnesses : ResidualCycleWitnessesAt phase depth) :
    ResidualHorizontalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnBoundary hboundaryEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits sparseBoundary createdColumn
    cases hselected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          boundary row)
        (quadrantAt boundary row) (shadeGrid boundary row) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | west =>
            exact (false_of_columnSeparatingCycle valid freeColumn selected (by
              intro x hbetween
              rcases hbetween with hbetween | hbetween
              · exact noneBetween x hbetween.1 hbetween.2
              · omega)
              (witnesses.right grid shadeGrid parentX parentY hcolumnWest
                hcolumnBoundary hboundaryEast hrowSouth hrowNorth hselected
                noneBetween notFits sparseBoundary createdColumn)).elim
        | east => rfl
  · intro grid shadeGrid parentX parentY column row boundary valid
      hboundaryWest hboundaryColumn hcolumnEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits sparseBoundary createdColumn
    cases hselected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          boundary row)
        (quadrantAt boundary row) (shadeGrid boundary row) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | west => rfl
        | east =>
            exact (false_of_columnSeparatingCycle valid freeColumn selected (by
              intro x hbetween
              rcases hbetween with hbetween | hbetween
              · omega
              · exact noneBetween x hbetween.1 hbetween.2)
              (witnesses.left grid shadeGrid parentX parentY hboundaryWest
                hboundaryColumn hcolumnEast hrowSouth hrowNorth hselected
                noneBetween notFits sparseBoundary createdColumn)).elim

end PairCoverSeamResidualCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
