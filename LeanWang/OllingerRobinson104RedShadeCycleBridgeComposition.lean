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

open OrientedRedCycles RedShadeGraph RedShadeGraphBoards
  RedShadeCycleConnectivity RedShadeCycleCrossingPaths

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

end RedShadeCycleBridgeComposition
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
