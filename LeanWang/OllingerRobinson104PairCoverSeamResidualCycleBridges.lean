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
  RedShadeCycleConnectivity
  RedShadeCycleBridgeComposition PairCoverSeamResidualCycles

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

end PairCoverSeamResidualCycleBridges
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
