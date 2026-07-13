/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamShadePaths
import LeanWang.OllingerRobinson104RedShadeCycleConnectivity

/-!
# Cycle-level seam contradictions

The residual seam argument is global: a wrong-facing selected boundary belongs
to a light red cycle that closes outside a small audit window.  If the queried
free line crosses the interior of that cycle, even connectivity around the
cycle carries the selected light shade to a perpendicular red interior on the
free line, contradicting freeness.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCycleContradictions

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadePaths RedShadeCycleConnectivity
  PairCoverSeamShadePaths ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

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

/-- A selected horizontal cycle side cannot enclose a row that is free across
the cycle's west side. -/
theorem freeRow_forbids_selected_cycle_crossing
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {outerWest outerEast west east south north column boundary row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid outerWest outerEast row)
    (cycle : CycleOn grid west east south north)
    (rowSouth : quarterSouth south < row)
    (rowNorth : row < quarterNorth north)
    (cycleWestInside : quarterWest outerWest < quarterWest west)
    (cycleWestInside' : quarterWest west < quarterEast outerEast)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (sourceOnCycle : OnCycle west east south north
      (horizontalPort grid column boundary)) : False := by
  have targetPresent := RedShadeCycles.CycleOn.west_path
    cycle rowSouth rowNorth
  have targetInterior : Signals.verticalInterior?
      (componentAt grid (quarterWest west) row)
      (quadrantAt (quarterWest west) row) ≠ none :=
    verticalInterior_ne_none_of_hasVertical _ _ targetPresent
  have targetOnCycle : OnCycle west east south north
      (verticalPort grid (quarterWest west) row) :=
    verticalPort_on_west rowSouth rowNorth
  have path := onCycle_connected cycle sourceOnCycle targetOnCycle
  exact freeRow_forbids_even_path valid freeRow cycleWestInside
    cycleWestInside' selected targetInterior path

/-- Horizontal dual of `freeRow_forbids_selected_cycle_crossing`. -/
theorem freeColumn_forbids_selected_cycle_crossing
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {outerSouth outerNorth west east south north column boundary row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid outerSouth outerNorth column)
    (cycle : CycleOn grid west east south north)
    (columnWest : quarterWest west < column)
    (columnEast : column < quarterEast east)
    (cycleSouthInside : quarterSouth outerSouth < quarterSouth south)
    (cycleSouthInside' : quarterSouth south < quarterNorth outerNorth)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (sourceOnCycle : OnCycle west east south north
      (verticalPort grid boundary row)) : False := by
  have targetPresent := RedShadeCycles.CycleOn.south_path
    cycle columnWest columnEast
  have targetInterior : Signals.horizontalInterior?
      (componentAt grid column (quarterSouth south))
      (quadrantAt column (quarterSouth south)) ≠ none :=
    horizontalInterior_ne_none_of_hasHorizontal _ _ targetPresent
  have targetOnCycle : OnCycle west east south north
      (horizontalPort grid column (quarterSouth south)) :=
    horizontalPort_on_south columnWest columnEast
  have path := onCycle_connected cycle sourceOnCycle targetOnCycle
  exact freeColumn_forbids_even_path valid freeColumn cycleSouthInside
    cycleSouthInside' selected targetInterior path

end PairCoverSeamCycleContradictions
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
