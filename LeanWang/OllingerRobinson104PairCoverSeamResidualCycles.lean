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
wrong-facing case, the hierarchy must supply a red cycle containing the
selected boundary port and strictly crossed by the created free line.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCycles

open Figure16 OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphRefinement RedShadePaths
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
      OnCycle west east south north (horizontalPort grid column boundary)

/-- An enclosing cycle crossed vertically by the queried column. -/
def ColumnCrossingCycle
    (grid : Nat → Nat → Index) (outerSouth outerNorth boundary row column : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      quarterSouth outerSouth < quarterSouth south ∧
      quarterSouth south < quarterNorth outerNorth ∧
      OnCycle west east south north (verticalPort grid boundary row)

def NorthSideCrossingCycle
    (grid : Nat → Nat → Index) (outerWest outerEast column boundary row : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧ boundary = quarterNorth north ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      quarterSouth south < row ∧ row < quarterNorth north ∧
      quarterWest outerWest < quarterWest west ∧
      quarterWest west < quarterEast outerEast

def SouthSideCrossingCycle
    (grid : Nat → Nat → Index) (outerWest outerEast column boundary row : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧ boundary = quarterSouth south ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      quarterSouth south < row ∧ row < quarterNorth north ∧
      quarterWest outerWest < quarterWest west ∧
      quarterWest west < quarterEast outerEast

def EastSideCrossingCycle
    (grid : Nat → Nat → Index) (outerSouth outerNorth boundary row column : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧ boundary = quarterEast east ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      quarterSouth south < row ∧ row < quarterNorth north ∧
      quarterSouth outerSouth < quarterSouth south ∧
      quarterSouth south < quarterNorth outerNorth

def WestSideCrossingCycle
    (grid : Nat → Nat → Index) (outerSouth outerNorth boundary row column : Nat) :
    Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧ boundary = quarterWest west ∧
      quarterWest west < column ∧ column < quarterEast east ∧
      quarterSouth south < row ∧ row < quarterNorth north ∧
      quarterSouth outerSouth < quarterSouth south ∧
      quarterSouth south < quarterNorth outerNorth

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

/-- A cycle whose north side is the selected boundary supplies the `above`
crossing witness. -/
theorem rowCrossingCycle_of_northSide
    {grid : Nat → Nat → Index}
    {outerWest outerEast column boundary row west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundaryNorth : boundary = quarterNorth north)
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east)
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north)
    (cycleWestInside : quarterWest outerWest < quarterWest west)
    (cycleWestInside' : quarterWest west < quarterEast outerEast) :
    RowCrossingCycle grid outerWest outerEast column boundary row := by
  subst boundary
  exact ⟨west, east, south, north, cycle, rowSouth, rowNorth,
    cycleWestInside, cycleWestInside',
    horizontalPort_on_north columnWest columnEast⟩

/-- A cycle whose south side is the selected boundary supplies the `below`
crossing witness. -/
theorem rowCrossingCycle_of_southSide
    {grid : Nat → Nat → Index}
    {outerWest outerEast column boundary row west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundarySouth : boundary = quarterSouth south)
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east)
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north)
    (cycleWestInside : quarterWest outerWest < quarterWest west)
    (cycleWestInside' : quarterWest west < quarterEast outerEast) :
    RowCrossingCycle grid outerWest outerEast column boundary row := by
  subst boundary
  exact ⟨west, east, south, north, cycle, rowSouth, rowNorth,
    cycleWestInside, cycleWestInside',
    horizontalPort_on_south columnWest columnEast⟩

/-- A cycle whose east side is the selected boundary supplies the `right`
crossing witness. -/
theorem columnCrossingCycle_of_eastSide
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundaryEast : boundary = quarterEast east)
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east)
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north)
    (cycleSouthInside : quarterSouth outerSouth < quarterSouth south)
    (cycleSouthInside' : quarterSouth south < quarterNorth outerNorth) :
    ColumnCrossingCycle grid outerSouth outerNorth boundary row column := by
  subst boundary
  exact ⟨west, east, south, north, cycle, columnWest, columnEast,
    cycleSouthInside, cycleSouthInside',
    verticalPort_on_east rowSouth rowNorth⟩

/-- A cycle whose west side is the selected boundary supplies the `left`
crossing witness. -/
theorem columnCrossingCycle_of_westSide
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundaryWest : boundary = quarterWest west)
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east)
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north)
    (cycleSouthInside : quarterSouth outerSouth < quarterSouth south)
    (cycleSouthInside' : quarterSouth south < quarterNorth outerNorth) :
    ColumnCrossingCycle grid outerSouth outerNorth boundary row column := by
  subst boundary
  exact ⟨west, east, south, north, cycle, columnWest, columnEast,
    cycleSouthInside, cycleSouthInside',
    verticalPort_on_west rowSouth rowNorth⟩

theorem NorthSideCrossingCycle.toRowCrossing
    {grid : Nat → Nat → Index} {outerWest outerEast column boundary row : Nat}
    (side : NorthSideCrossingCycle grid outerWest outerEast
      column boundary row) :
    RowCrossingCycle grid outerWest outerEast column boundary row := by
  rcases side with ⟨west, east, south, north, cycle, boundaryNorth,
    columnWest, columnEast, rowSouth, rowNorth, cycleWestInside,
    cycleWestInside'⟩
  exact rowCrossingCycle_of_northSide cycle boundaryNorth columnWest columnEast
    rowSouth rowNorth cycleWestInside cycleWestInside'

theorem SouthSideCrossingCycle.toRowCrossing
    {grid : Nat → Nat → Index} {outerWest outerEast column boundary row : Nat}
    (side : SouthSideCrossingCycle grid outerWest outerEast
      column boundary row) :
    RowCrossingCycle grid outerWest outerEast column boundary row := by
  rcases side with ⟨west, east, south, north, cycle, boundarySouth,
    columnWest, columnEast, rowSouth, rowNorth, cycleWestInside,
    cycleWestInside'⟩
  exact rowCrossingCycle_of_southSide cycle boundarySouth columnWest columnEast
    rowSouth rowNorth cycleWestInside cycleWestInside'

theorem EastSideCrossingCycle.toColumnCrossing
    {grid : Nat → Nat → Index} {outerSouth outerNorth boundary row column : Nat}
    (side : EastSideCrossingCycle grid outerSouth outerNorth
      boundary row column) :
    ColumnCrossingCycle grid outerSouth outerNorth boundary row column := by
  rcases side with ⟨west, east, south, north, cycle, boundaryEast,
    columnWest, columnEast, rowSouth, rowNorth, cycleSouthInside,
    cycleSouthInside'⟩
  exact columnCrossingCycle_of_eastSide cycle boundaryEast columnWest columnEast
    rowSouth rowNorth cycleSouthInside cycleSouthInside'

theorem WestSideCrossingCycle.toColumnCrossing
    {grid : Nat → Nat → Index} {outerSouth outerNorth boundary row column : Nat}
    (side : WestSideCrossingCycle grid outerSouth outerNorth
      boundary row column) :
    ColumnCrossingCycle grid outerSouth outerNorth boundary row column := by
  rcases side with ⟨west, east, south, north, cycle, boundaryWest,
    columnWest, columnEast, rowSouth, rowNorth, cycleSouthInside,
    cycleSouthInside'⟩
  exact columnCrossingCycle_of_westSide cycle boundaryWest columnWest columnEast
    rowSouth rowNorth cycleSouthInside cycleSouthInside'

/-- A retained north side of a coarse cycle is literally the north side of
its two-level refinement. -/
theorem rowCrossingCycle_of_refined_northSide
    {grid : Nat → Nat → Index}
    {outerWest outerEast column boundary row west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundaryNorth : boundary = sparseCoordinate (quarterNorth north))
    (columnWest : quarterWest (4 * west) < column)
    (columnEast : column < quarterEast (4 * east))
    (rowSouth : quarterSouth (4 * south) < row)
    (rowNorth : row < quarterNorth (4 * north))
    (cycleWestInside : quarterWest outerWest < quarterWest (4 * west))
    (cycleWestInside' : quarterWest (4 * west) < quarterEast outerEast) :
    RowCrossingCycle (iterateRefine 2 grid) outerWest outerEast
      column boundary row := by
  have fineCycle := cycle.iterateRefine 2
  simp only [RedCycles.doubleN_eq] at fineCycle
  exact rowCrossingCycle_of_northSide fineCycle
    (by simpa using boundaryNorth) columnWest columnEast rowSouth rowNorth
    cycleWestInside cycleWestInside'

/-- A retained south side of a coarse cycle is literally the south side of
its two-level refinement. -/
theorem rowCrossingCycle_of_refined_southSide
    {grid : Nat → Nat → Index}
    {outerWest outerEast column boundary row west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundarySouth : boundary = sparseCoordinate (quarterSouth south))
    (columnWest : quarterWest (4 * west) < column)
    (columnEast : column < quarterEast (4 * east))
    (rowSouth : quarterSouth (4 * south) < row)
    (rowNorth : row < quarterNorth (4 * north))
    (cycleWestInside : quarterWest outerWest < quarterWest (4 * west))
    (cycleWestInside' : quarterWest (4 * west) < quarterEast outerEast) :
    RowCrossingCycle (iterateRefine 2 grid) outerWest outerEast
      column boundary row := by
  have fineCycle := cycle.iterateRefine 2
  simp only [RedCycles.doubleN_eq] at fineCycle
  exact rowCrossingCycle_of_southSide fineCycle
    (by simpa using boundarySouth) columnWest columnEast rowSouth rowNorth
    cycleWestInside cycleWestInside'

/-- A retained east side of a coarse cycle is literally the east side of its
two-level refinement. -/
theorem columnCrossingCycle_of_refined_eastSide
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundaryEast : boundary = sparseCoordinate (quarterEast east))
    (columnWest : quarterWest (4 * west) < column)
    (columnEast : column < quarterEast (4 * east))
    (rowSouth : quarterSouth (4 * south) < row)
    (rowNorth : row < quarterNorth (4 * north))
    (cycleSouthInside : quarterSouth outerSouth < quarterSouth (4 * south))
    (cycleSouthInside' : quarterSouth (4 * south) < quarterNorth outerNorth) :
    ColumnCrossingCycle (iterateRefine 2 grid) outerSouth outerNorth
      boundary row column := by
  have fineCycle := cycle.iterateRefine 2
  simp only [RedCycles.doubleN_eq] at fineCycle
  exact columnCrossingCycle_of_eastSide fineCycle
    (by simpa using boundaryEast) columnWest columnEast rowSouth rowNorth
    cycleSouthInside cycleSouthInside'

/-- A retained west side of a coarse cycle is literally the west side of its
two-level refinement. -/
theorem columnCrossingCycle_of_refined_westSide
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column west east south north : Nat}
    (cycle : CycleOn grid west east south north)
    (boundaryWest : boundary = sparseCoordinate (quarterWest west))
    (columnWest : quarterWest (4 * west) < column)
    (columnEast : column < quarterEast (4 * east))
    (rowSouth : quarterSouth (4 * south) < row)
    (rowNorth : row < quarterNorth (4 * north))
    (cycleSouthInside : quarterSouth outerSouth < quarterSouth (4 * south))
    (cycleSouthInside' : quarterSouth (4 * south) < quarterNorth outerNorth) :
    ColumnCrossingCycle (iterateRefine 2 grid) outerSouth outerNorth
      boundary row column := by
  have fineCycle := cycle.iterateRefine 2
  simp only [RedCycles.doubleN_eq] at fineCycle
  exact columnCrossingCycle_of_westSide fineCycle
    (by simpa using boundaryWest) columnWest columnEast rowSouth rowNorth
    cycleSouthInside cycleSouthInside'

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
    NorthSideCrossingCycle
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
    SouthSideCrossingCycle
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
    EastSideCrossingCycle
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
    WestSideCrossingCycle
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
    cycleWestInside, cycleWestInside', sourceOnCycle⟩
  exact freeRow_forbids_selected_cycle_crossing valid freeRow cycle
    rowSouth rowNorth cycleWestInside cycleWestInside' selected sourceOnCycle

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
    cycleSouthInside, cycleSouthInside', sourceOnCycle⟩
  exact freeColumn_forbids_selected_cycle_crossing valid freeColumn cycle
    columnWest columnEast cycleSouthInside cycleSouthInside' selected
    sourceOnCycle

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
              ((witnesses.above grid shadeGrid parentX parentY hcolumnWest
                hcolumnEast hrowSouth hrowBoundary hboundaryNorth hselected
                noneBetween notFits sparseBoundary createdRow).toRowCrossing)).elim
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
              ((witnesses.below grid shadeGrid parentX parentY hcolumnWest
                hcolumnEast hboundarySouth hboundaryRow hrowNorth hselected
                noneBetween notFits sparseBoundary createdRow).toRowCrossing)).elim
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
              ((witnesses.right grid shadeGrid parentX parentY hcolumnWest
                hcolumnBoundary hboundaryEast hrowSouth hrowNorth hselected
                noneBetween notFits sparseBoundary createdColumn).toColumnCrossing)).elim
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
              ((witnesses.left grid shadeGrid parentX parentY hboundaryWest
                hboundaryColumn hcolumnEast hrowSouth hrowNorth hselected
                noneBetween notFits sparseBoundary createdColumn).toColumnCrossing)).elim

end PairCoverSeamResidualCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
