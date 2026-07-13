/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycles
import LeanWang.OllingerRobinson104RedShadeCycleBridgeComposition

/-!
# Descendant-cycle witnesses for residual seam faces

Robinson's hierarchy argument first routes a selected boundary into an
enclosing border, then chooses a descendant border that crosses the queried
free line or separates it from the selected boundary.  The hierarchy bridges
have even parity, so this composition produces exactly the cycle witness used
by the residual seam contradiction.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCycleBridges

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement RedShadeCycleConnectivity
  RedShadeCycleBridgeComposition PairCoverSeamResidualCycles
  ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  PairCoverSeamArithmetic
  RefinedCoordinateProjection SparseFreeLineLocalProjection
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- An even route from one source port into an enclosing hierarchy cycle. -/
def CycleAncestor (grid : Nat → Nat → Index) (source : Port) : Prop :=
  ∃ west east south north, CycleOn grid west east south north ∧
    ∃ entry, OnCycle west east south north entry ∧
      Path grid source entry false

/-- Prepending an even route preserves cycle ancestry. -/
theorem CycleAncestor.of_evenPath
    {grid : Nat → Nat → Index} {source target : Port}
    (ancestor : CycleAncestor grid target)
    (path : Path grid source target false) :
    CycleAncestor grid source := by
  rcases ancestor with
    ⟨west, east, south, north, cycle, entry, entryOnCycle, tail⟩
  refine ⟨west, east, south, north, cycle, entry, entryOnCycle, ?_⟩
  simpa using Path.trans path tail

/-- Cycle ancestry survives two substitutions on the literal sparse copy of a
live source port. -/
theorem CycleAncestor.refineSparse
    {grid : Nat → Nat → Index} {source : Port}
    (ancestor : CycleAncestor grid source)
    (sourceLive : portPresent grid source = true) :
    CycleAncestor (RedCycles.iterateRefine 2 grid) (sparsePort source) := by
  rcases ancestor with
    ⟨west, east, south, north, cycle, entry, entryOnCycle, path⟩
  have fineCycle := cycle.iterateRefine 2
  have entryLive := portPresent_of_onCycle cycle entryOnCycle
  refine ⟨4 * west, 4 * east, 4 * south, 4 * north, ?_,
    sparsePort entry, onCycle_sparse entryOnCycle, ?_⟩
  · simpa [RedCycles.doubleN_eq] using fineCycle
  · exact path_refine_sparse path sourceLive entryLive

/-- An even fine-grid connector into a sparse coarse source transports the
coarse source's cycle ancestry. -/
theorem CycleAncestor.refineThrough
    {grid : Nat → Nat → Index} {source target : Port}
    (ancestor : CycleAncestor grid source)
    (sourceLive : portPresent grid source = true)
    (connector : Path (RedCycles.iterateRefine 2 grid)
      target (sparsePort source) false) :
    CycleAncestor (RedCycles.iterateRefine 2 grid) target :=
  (ancestor.refineSparse sourceLive).of_evenPath connector

/-- The horizontal selector chooses a live endpoint of every horizontal
interior segment. -/
theorem horizontalPort_present_of_interior
    {grid : Nat → Nat → Index} {x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none) :
    portPresent grid (PairCoverSeamShadePaths.horizontalPort grid x y) = true := by
  by_cases hwest :
      RedShades.hasWest (componentAt grid x y) (quadrantAt x y) = true
  · simpa [PairCoverSeamShadePaths.horizontalPort, hwest, portPresent]
  · rcases live_endpoint_of_horizontalInterior interior with westLive | eastLive
    · change RedShades.hasWest (componentAt grid x y)
          (quadrantAt x y) = true at westLive
      exact (hwest westLive).elim
    · simpa [PairCoverSeamShadePaths.horizontalPort, hwest] using eastLive

/-- The vertical selector chooses a live endpoint of every vertical interior
segment. -/
theorem verticalPort_present_of_interior
    {grid : Nat → Nat → Index} {x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none) :
    portPresent grid (PairCoverSeamShadePaths.verticalPort grid x y) = true := by
  by_cases hsouth :
      RedShades.hasSouth (componentAt grid x y) (quadrantAt x y) = true
  · simpa [PairCoverSeamShadePaths.verticalPort, hsouth, portPresent]
  · rcases live_endpoint_of_verticalInterior interior with southLive | northLive
    · change RedShades.hasSouth (componentAt grid x y)
          (quadrantAt x y) = true at southLive
      exact (hsouth southLive).elim
    · simpa [PairCoverSeamShadePaths.verticalPort, hsouth] using northLive

/-- A bridged descendant of an ancestor cycle supplies the row geometry needed
by `RowSeparatingCycle`. -/
def RowDescendantSelection
    (grid : Nat → Nat → Index) (outerWest outerEast column boundary row : Nat)
    (ancestorWest ancestorEast ancestorSouth ancestorNorth : Nat) : Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      EvenCycleBridge grid ancestorWest ancestorEast ancestorSouth ancestorNorth
        west east south north ∧
      quarterWest outerWest < quarterWest west ∧
      quarterWest west < quarterEast outerEast ∧
      ((quarterSouth south < row ∧ row < quarterNorth north) ∨
        (quarterWest west < column ∧ column < quarterEast east) ∧
          PairCoverSeamPathSearch.StrictBetween row boundary
            (quarterSouth south) ∨
        (quarterWest west < column ∧ column < quarterEast east) ∧
          PairCoverSeamPathSearch.StrictBetween row boundary
            (quarterNorth north))

/-- Horizontal dual of `RowDescendantSelection`. -/
def ColumnDescendantSelection
    (grid : Nat → Nat → Index) (outerSouth outerNorth boundary row column : Nat)
    (ancestorWest ancestorEast ancestorSouth ancestorNorth : Nat) : Prop :=
  ∃ west east south north,
    CycleOn grid west east south north ∧
      EvenCycleBridge grid ancestorWest ancestorEast ancestorSouth ancestorNorth
        west east south north ∧
      quarterSouth outerSouth < quarterSouth south ∧
      quarterSouth south < quarterNorth outerNorth ∧
      ((quarterWest west < column ∧ column < quarterEast east) ∨
        (quarterSouth south < row ∧ row < quarterNorth north) ∧
          PairCoverSeamPathSearch.StrictBetween column boundary
            (quarterWest west) ∨
        (quarterSouth south < row ∧ row < quarterNorth north) ∧
          PairCoverSeamPathSearch.StrictBetween column boundary
            (quarterEast east))

/-- An even route into an ancestor cycle extends across an even hierarchy
bridge to the descendant cycle. -/
theorem pathToDescendantCycle
    {grid : Nat → Nat → Index}
    {ancestorWest ancestorEast ancestorSouth ancestorNorth : Nat}
    {descendantWest descendantEast descendantSouth descendantNorth : Nat}
    {source ancestorEntry : Port}
    (ancestorCycle : CycleOn grid ancestorWest ancestorEast
      ancestorSouth ancestorNorth)
    (ancestorEntryOnCycle : OnCycle ancestorWest ancestorEast
      ancestorSouth ancestorNorth ancestorEntry)
    (sourceToAncestor : Path grid source ancestorEntry false)
    (bridge : EvenCycleBridge grid ancestorWest ancestorEast
      ancestorSouth ancestorNorth descendantWest descendantEast
      descendantSouth descendantNorth) :
    ∃ descendantEntry,
      OnCycle descendantWest descendantEast descendantSouth descendantNorth
        descendantEntry ∧
      Path grid source descendantEntry false := by
  rcases bridge with ⟨ancestorExit, descendantEntry, ancestorExitOnCycle,
    descendantEntryOnCycle, bridgePath⟩
  have aroundAncestor := onCycle_connected ancestorCycle
    ancestorEntryOnCycle ancestorExitOnCycle
  refine ⟨descendantEntry, descendantEntryOnCycle, ?_⟩
  simpa [Bool.xor_assoc] using
    Path.trans sourceToAncestor (Path.trans aroundAncestor bridgePath)

/-- Package a descendant reached from an enclosing cycle as the row witness
used by the residual vertical-face proof. -/
theorem rowSeparatingCycle_of_bridge
    {grid : Nat → Nat → Index}
    {outerWest outerEast column boundary row : Nat}
    {ancestorWest ancestorEast ancestorSouth ancestorNorth : Nat}
    {descendantWest descendantEast descendantSouth descendantNorth : Nat}
    {ancestorEntry : Port}
    (ancestorCycle : CycleOn grid ancestorWest ancestorEast
      ancestorSouth ancestorNorth)
    (descendantCycle : CycleOn grid descendantWest descendantEast
      descendantSouth descendantNorth)
    (ancestorEntryOnCycle : OnCycle ancestorWest ancestorEast
      ancestorSouth ancestorNorth ancestorEntry)
    (sourceToAncestor : Path grid
      (PairCoverSeamShadePaths.horizontalPort grid column boundary)
      ancestorEntry false)
    (bridge : EvenCycleBridge grid ancestorWest ancestorEast
      ancestorSouth ancestorNorth descendantWest descendantEast
      descendantSouth descendantNorth)
    (descendantWestInside :
      RedShadeCycles.quarterWest outerWest <
        RedShadeCycles.quarterWest descendantWest)
    (descendantWestInside' :
      RedShadeCycles.quarterWest descendantWest <
        RedShadeCycles.quarterEast outerEast)
    (separation :
      (RedShadeCycles.quarterSouth descendantSouth < row ∧
        row < RedShadeCycles.quarterNorth descendantNorth) ∨
      (RedShadeCycles.quarterWest descendantWest < column ∧
        column < RedShadeCycles.quarterEast descendantEast) ∧
          PairCoverSeamPathSearch.StrictBetween row boundary
            (RedShadeCycles.quarterSouth descendantSouth) ∨
      (RedShadeCycles.quarterWest descendantWest < column ∧
        column < RedShadeCycles.quarterEast descendantEast) ∧
          PairCoverSeamPathSearch.StrictBetween row boundary
            (RedShadeCycles.quarterNorth descendantNorth)) :
    RowSeparatingCycle grid outerWest outerEast column boundary row := by
  rcases pathToDescendantCycle ancestorCycle ancestorEntryOnCycle
      sourceToAncestor bridge with
    ⟨descendantEntry, descendantEntryOnCycle, sourceToDescendant⟩
  exact ⟨descendantWest, descendantEast, descendantSouth, descendantNorth,
    descendantCycle, descendantWestInside, descendantWestInside',
    descendantEntry, descendantEntryOnCycle, sourceToDescendant, separation⟩

/-- Horizontal dual of `rowSeparatingCycle_of_bridge`. -/
theorem columnSeparatingCycle_of_bridge
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column : Nat}
    {ancestorWest ancestorEast ancestorSouth ancestorNorth : Nat}
    {descendantWest descendantEast descendantSouth descendantNorth : Nat}
    {ancestorEntry : Port}
    (ancestorCycle : CycleOn grid ancestorWest ancestorEast
      ancestorSouth ancestorNorth)
    (descendantCycle : CycleOn grid descendantWest descendantEast
      descendantSouth descendantNorth)
    (ancestorEntryOnCycle : OnCycle ancestorWest ancestorEast
      ancestorSouth ancestorNorth ancestorEntry)
    (sourceToAncestor : Path grid
      (PairCoverSeamShadePaths.verticalPort grid boundary row)
      ancestorEntry false)
    (bridge : EvenCycleBridge grid ancestorWest ancestorEast
      ancestorSouth ancestorNorth descendantWest descendantEast
      descendantSouth descendantNorth)
    (descendantSouthInside :
      RedShadeCycles.quarterSouth outerSouth <
        RedShadeCycles.quarterSouth descendantSouth)
    (descendantSouthInside' :
      RedShadeCycles.quarterSouth descendantSouth <
        RedShadeCycles.quarterNorth outerNorth)
    (separation :
      (RedShadeCycles.quarterWest descendantWest < column ∧
        column < RedShadeCycles.quarterEast descendantEast) ∨
      (RedShadeCycles.quarterSouth descendantSouth < row ∧
        row < RedShadeCycles.quarterNorth descendantNorth) ∧
          PairCoverSeamPathSearch.StrictBetween column boundary
            (RedShadeCycles.quarterWest descendantWest) ∨
      (RedShadeCycles.quarterSouth descendantSouth < row ∧
        row < RedShadeCycles.quarterNorth descendantNorth) ∧
          PairCoverSeamPathSearch.StrictBetween column boundary
            (RedShadeCycles.quarterEast descendantEast)) :
    ColumnSeparatingCycle grid outerSouth outerNorth boundary row column := by
  rcases pathToDescendantCycle ancestorCycle ancestorEntryOnCycle
      sourceToAncestor bridge with
    ⟨descendantEntry, descendantEntryOnCycle, sourceToDescendant⟩
  exact ⟨descendantWest, descendantEast, descendantSouth, descendantNorth,
    descendantCycle, descendantSouthInside, descendantSouthInside',
    descendantEntry, descendantEntryOnCycle, sourceToDescendant, separation⟩

theorem rowSeparatingCycle_of_ancestor_selection
    {grid : Nat → Nat → Index} {outerWest outerEast column boundary row : Nat}
    (ancestor : CycleAncestor grid
      (PairCoverSeamShadePaths.horizontalPort grid column boundary))
    (select : ∀ west east south north,
      CycleOn grid west east south north →
      RowDescendantSelection grid outerWest outerEast column boundary row
        west east south north) :
    RowSeparatingCycle grid outerWest outerEast column boundary row := by
  rcases ancestor with ⟨ancestorWest, ancestorEast, ancestorSouth,
    ancestorNorth, ancestorCycle, ancestorEntry, ancestorEntryOnCycle,
    sourceToAncestor⟩
  rcases select ancestorWest ancestorEast ancestorSouth ancestorNorth
      ancestorCycle with
    ⟨west, east, south, north, descendantCycle, bridge,
      westInside, westInside', separation⟩
  exact rowSeparatingCycle_of_bridge ancestorCycle descendantCycle
    ancestorEntryOnCycle sourceToAncestor bridge westInside westInside'
    separation

theorem columnSeparatingCycle_of_ancestor_selection
    {grid : Nat → Nat → Index}
    {outerSouth outerNorth boundary row column : Nat}
    (ancestor : CycleAncestor grid
      (PairCoverSeamShadePaths.verticalPort grid boundary row))
    (select : ∀ west east south north,
      CycleOn grid west east south north →
      ColumnDescendantSelection grid outerSouth outerNorth boundary row column
        west east south north) :
    ColumnSeparatingCycle grid outerSouth outerNorth boundary row column := by
  rcases ancestor with ⟨ancestorWest, ancestorEast, ancestorSouth,
    ancestorNorth, ancestorCycle, ancestorEntry, ancestorEntryOnCycle,
    sourceToAncestor⟩
  rcases select ancestorWest ancestorEast ancestorSouth ancestorNorth
      ancestorCycle with
    ⟨west, east, south, north, descendantCycle, bridge,
      southInside, southInside', separation⟩
  exact columnSeparatingCycle_of_bridge ancestorCycle descendantCycle
    ancestorEntryOnCycle sourceToAncestor bridge southInside southInside'
    separation

/-- Query-independent ancestry obligations for retained selected boundaries. -/
structure ResidualSourceAncestorsAt (phase : Phase) (depth : Nat) : Prop where
  horizontal : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    Signals.horizontalInterior?
      (componentAt (RedCycles.iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) column boundary)
      (quadrantAt column boundary) ≠ none →
    IsSparseCoordinate boundary →
    CycleAncestor
      (RedCycles.iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (PairCoverSeamShadePaths.horizontalPort
        (RedCycles.iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
  vertical : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {boundary row : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    Signals.verticalInterior?
      (componentAt (RedCycles.iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) boundary row)
      (quadrantAt boundary row) ≠ none →
    IsSparseCoordinate boundary →
    CycleAncestor
      (RedCycles.iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (PairCoverSeamShadePaths.verticalPort
        (RedCycles.iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)

/-- Pure coordinate choice of a bridged descendant after source ancestry has
identified an enclosing cycle. -/
structure ResidualDescendantSelectionsAt (phase : Phase) (depth : Nat) : Prop where
  row : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary west east south north : Nat},
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
    CycleOn (RedCycles.iterateRefine 2
      (refinedGrid phase (depth + 1) grid)) west east south north →
    RowDescendantSelection
      (RedCycles.iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column boundary row
      west east south north
  column : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary west east south north : Nat},
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
    CycleOn (RedCycles.iterateRefine 2
      (refinedGrid phase (depth + 1) grid)) west east south north →
    ColumnDescendantSelection
      (RedCycles.iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary row column
      west east south north

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

set_option maxHeartbeats 5000000 in
-- The fine grid occurs dependently in both factorized obligations.
theorem residualCycleWitnessesAt_of_ancestors_of_selections
    {phase : Phase} {depth : Nat}
    (ancestors : ResidualSourceAncestorsAt phase depth)
    (selections : ResidualDescendantSelectionsAt phase depth) :
    ResidualCycleWitnessesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary
      columnWest columnEast rowSouth rowBoundary boundaryNorth selected
      _ notFits sparseBoundary createdRow
    apply rowSeparatingCycle_of_ancestor_selection
    · exact ancestors.horizontal grid parentX parentY columnWest columnEast
        (rowSouth.trans rowBoundary) boundaryNorth
        (horizontalInterior_ne_none_of_selected selected) sparseBoundary
    · intro west east south north cycle
      exact selections.row grid parentX parentY columnWest columnEast rowSouth
        (rowBoundary.trans boundaryNorth) (rowSouth.trans rowBoundary)
        boundaryNorth notFits sparseBoundary createdRow cycle
  · intro grid shadeGrid parentX parentY column row boundary
      columnWest columnEast boundarySouth boundaryRow rowNorth selected
      _ notFits sparseBoundary createdRow
    apply rowSeparatingCycle_of_ancestor_selection
    · exact ancestors.horizontal grid parentX parentY columnWest columnEast
        boundarySouth (boundaryRow.trans rowNorth)
        (horizontalInterior_ne_none_of_selected selected) sparseBoundary
    · intro west east south north cycle
      exact selections.row grid parentX parentY columnWest columnEast
        (boundarySouth.trans boundaryRow) rowNorth boundarySouth
        (boundaryRow.trans rowNorth) notFits sparseBoundary createdRow cycle
  · intro grid shadeGrid parentX parentY column row boundary
      columnWest columnBoundary boundaryEast rowSouth rowNorth selected
      _ notFits sparseBoundary createdColumn
    apply columnSeparatingCycle_of_ancestor_selection
    · exact ancestors.vertical grid parentX parentY
        (columnWest.trans columnBoundary) boundaryEast rowSouth rowNorth
        (verticalInterior_ne_none_of_selected selected) sparseBoundary
    · intro west east south north cycle
      exact selections.column grid parentX parentY columnWest
        (columnBoundary.trans boundaryEast)
        (columnWest.trans columnBoundary) boundaryEast rowSouth rowNorth
        notFits sparseBoundary createdColumn cycle
  · intro grid shadeGrid parentX parentY column row boundary
      boundaryWest boundaryColumn columnEast rowSouth rowNorth selected
      _ notFits sparseBoundary createdColumn
    apply columnSeparatingCycle_of_ancestor_selection
    · exact ancestors.vertical grid parentX parentY boundaryWest
        (boundaryColumn.trans columnEast) rowSouth rowNorth
        (verticalInterior_ne_none_of_selected selected) sparseBoundary
    · intro west east south north cycle
      exact selections.column grid parentX parentY
        (boundaryWest.trans boundaryColumn) columnEast boundaryWest
        (boundaryColumn.trans columnEast) rowSouth rowNorth
        notFits sparseBoundary createdColumn cycle

end PairCoverSeamResidualCycleBridges
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
