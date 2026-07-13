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
  RedShadePaths
  RedShadeGraphBoards ShadedPlaneSignalGrid Signals.FreeCellLocal
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase
  PairCoverSeamArithmetic PairCoverSeamShadePaths
  PairCoverSeamCycleContradictions PairCoverSeamComposition
  PairCoverSeamCreatedPaths
  RefinedCoordinateProjection

set_option maxRecDepth 20000

/-- An enclosing cycle crossed horizontally by the queried row. -/
def RowCrossingCycle
    (grid : Nat → Nat → Index) (outerWest outerEast column boundary row : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      quarterSouth south < row ∧ row < quarterNorth north ∧
      quarterWest outerWest < quarterWest west ∧
      quarterWest west < quarterEast outerEast ∧
      ∃ entry, OnCycle west east south north entry ∧
        Path grid (horizontalPort grid column boundary) entry false

/-- An enclosing cycle crossed vertically by the queried column. -/
def ColumnCrossingCycle
    (grid : Nat → Nat → Index) (outerSouth outerNorth boundary row column : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      quarterSouth outerSouth < quarterSouth south ∧
      quarterSouth south < quarterNorth outerNorth ∧
      ∃ entry, OnCycle west east south north entry ∧
        Path grid (verticalPort grid boundary row) entry false

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
    RowCrossingCycle
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
    RowCrossingCycle
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
    ColumnCrossingCycle
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
    ColumnCrossingCycle
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary row column

private theorem false_of_rowCrossingCycle
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {outerWest outerEast column boundary row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid outerWest outerEast row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (crossing : RowCrossingCycle grid outerWest outerEast
      column boundary row) : False := by
  rcases crossing with ⟨west, east, south, north, cycle, rowSouth, rowNorth,
    cycleWestInside, cycleWestInside', entry, entryOnCycle, sourceToCycle⟩
  exact freeRow_forbids_selected_cycle_route valid freeRow cycle
    rowSouth rowNorth cycleWestInside cycleWestInside' selected entryOnCycle
    sourceToCycle

private theorem false_of_columnCrossingCycle
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {outerSouth outerNorth boundary row column : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid outerSouth outerNorth column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (crossing : ColumnCrossingCycle grid outerSouth outerNorth
      boundary row column) : False := by
  rcases crossing with ⟨west, east, south, north, cycle, columnWest, columnEast,
    cycleSouthInside, cycleSouthInside', entry, entryOnCycle, sourceToCycle⟩
  exact freeColumn_forbids_selected_cycle_route valid freeColumn cycle
    columnWest columnEast cycleSouthInside cycleSouthInside' selected
    entryOnCycle sourceToCycle

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
            exact (false_of_rowCrossingCycle valid freeRow selected
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
            exact (false_of_rowCrossingCycle valid freeRow selected
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
            exact (false_of_columnCrossingCycle valid freeColumn selected
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
            exact (false_of_columnCrossingCycle valid freeColumn selected
              (witnesses.left grid shadeGrid parentX parentY hboundaryWest
                hboundaryColumn hcolumnEast hrowSouth hrowNorth hselected
                noneBetween notFits sparseBoundary createdColumn)).elim

end PairCoverSeamResidualCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
