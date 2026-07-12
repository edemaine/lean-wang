/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleConnectivity
import LeanWang.OllingerRobinson104TranslatedRedShadeCrossingPaths

/-!
# Composition of bridges between red cycles

Two odd crossing bridges through a common oriented cycle compose to an even
bridge.  The connecting path on the common cycle is even, so this is the
parity-preserving two-level step used by the recursive exceptional free line.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycleBridgeComposition

open OrientedRedCycles RedCycles RedShadeGraph RedShadeGraphBoards
  RedShadeCycleConnectivity RedShadeCycleCrossingPaths
  TranslatedRedShadeCrossings TranslatedRedShadeCrossingPaths

/-- An explicit even path from one oriented cycle to another. -/
def EvenCycleBridge
    (grid : Nat → Nat → Index)
    (firstWest firstEast firstSouth firstNorth : Nat)
    (secondWest secondEast secondSouth secondNorth : Nat) : Prop :=
  ∃ firstPort secondPort,
    OnCycle firstWest firstEast firstSouth firstNorth firstPort ∧
      OnCycle secondWest secondEast secondSouth secondNorth secondPort ∧
      Path grid firstPort secondPort false

/-- Two odd bridges compose evenly through their common oriented cycle. -/
theorem odd_trans_odd
    {grid : Nat → Nat → Index}
    {firstWest firstEast firstSouth firstNorth : Nat}
    {middleWest middleEast middleSouth middleNorth : Nat}
    {lastWest lastEast lastSouth lastNorth : Nat}
    (middle : CycleOn grid middleWest middleEast middleSouth middleNorth)
    (first : OddCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      middleWest middleEast middleSouth middleNorth)
    (second : OddCycleBridge grid
      middleWest middleEast middleSouth middleNorth
      lastWest lastEast lastSouth lastNorth) :
    EvenCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      lastWest lastEast lastSouth lastNorth := by
  rcases first with ⟨firstPort, middleEntry, firstOnCycle,
    entryOnCycle, firstPath⟩
  rcases second with ⟨middleExit, lastPort, exitOnCycle,
    lastOnCycle, secondPath⟩
  have middlePath := onCycle_connected middle entryOnCycle exitOnCycle
  refine ⟨firstPort, lastPort, firstOnCycle, lastOnCycle, ?_⟩
  simpa [Bool.xor_assoc] using
    Path.trans firstPath (Path.trans middlePath secondPath)

/-- Two successive corner descendants are evenly bridged to their ancestor. -/
theorem twoCornerBridge
    (grid : Nat → Nat → Index) {level : Nat} (hlevel : 2 ≤ level)
    (blockX blockY : Nat)
    (firstCornerX firstCornerY secondCornerX secondCornerY : Fin 2) :
    EvenCycleBridge (iterateRefine (level + 2) grid)
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3))
      (2 ^ (level - 2) *
        (4 * (2 * (2 * blockX + firstCornerX.val) + secondCornerX.val) + 1))
      (2 ^ (level - 2) *
        (4 * (2 * (2 * blockX + firstCornerX.val) + secondCornerX.val) + 3))
      (2 ^ (level - 2) *
        (4 * (2 * (2 * blockY + firstCornerY.val) + secondCornerY.val) + 1))
      (2 ^ (level - 2) *
        (4 * (2 * (2 * blockY + firstCornerY.val) + secondCornerY.val) + 3)) := by
  have hlevelOne : 1 ≤ level := by omega
  have hchildLevel : 1 ≤ level - 1 := by omega
  let middleX := 2 * blockX + firstCornerX.val
  let middleY := 2 * blockY + firstCornerY.val
  have first := cornerBridge grid hlevelOne blockX blockY
    firstCornerX firstCornerY
  have middle := cornerSmallCycle grid hlevelOne blockX blockY
    firstCornerX firstCornerY
  have second := cornerBridge (iterateRefine 1 grid) hchildLevel
    middleX middleY secondCornerX secondCornerY
  have hgrid :
      iterateRefine (level - 1 + 2) (iterateRefine 1 grid) =
        iterateRefine (level + 2) grid := by
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  rw [hgrid] at second
  simpa [middleX, middleY, Nat.sub_sub] using
    odd_trans_odd middle first second

end RedShadeCycleBridgeComposition
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
