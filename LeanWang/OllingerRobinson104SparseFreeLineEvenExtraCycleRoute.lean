/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleBridgeComposition
import LeanWang.OllingerRobinson104ShadedFreeLinePatternRefinement

/-!
# Packaging refined-cycle routes as free-line projections

An odd route starting anywhere on the refined outer cycle can be backed by a
literal sparse copy of an old-cycle port.  This converts the nested-cycle
geometry directly into the `ProjectsTo` witnesses consumed by live row and
column certificates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCycleRoute

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement RedShadeCycleConnectivity
  RedShadeCycleBridgeComposition ShadedFreeLinePatternRefinement

/-- Package an odd refined-cycle route as a projection from the old cycle. -/
def projectsTo_of_refinedCyclePath
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (oldCycle : CycleOn grid west east south north)
    (fineCycle : CycleOn (RedCycles.iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north))
    {source fineStart target : Port}
    (sourceOnCycle : OnCycle west east south north source)
    (fineStartOnCycle : OnCycle
      (4 * west) (4 * east) (4 * south) (4 * north) fineStart)
    (tail : Path (RedCycles.iterateRefine 2 grid) fineStart target true)
    (targetLive : portPresent (RedCycles.iterateRefine 2 grid) target = true) :
    ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target := by
  have sparseSourceOnCycle : OnCycle
      (4 * west) (4 * east) (4 * south) (4 * north)
      (sparsePort source) := onCycle_sparse sourceOnCycle
  have connector := onCycle_connected fineCycle
    sparseSourceOnCycle fineStartOnCycle
  exact ProjectsTo.ofCyclePath oldCycle sourceOnCycle
    (by simpa [Bool.xor_assoc] using Path.trans connector tail) targetLive

/-- A descendant-cycle tail reached by an even bridge is an old-cycle projection. -/
theorem projectsTo_of_evenBridgeTail
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (oldCycle : CycleOn grid west east south north)
    (fineCycle : CycleOn (RedCycles.iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north))
    {descendantWest descendantEast descendantSouth descendantNorth : Nat}
    (descendantCycle : CycleOn (RedCycles.iterateRefine 2 grid)
      descendantWest descendantEast descendantSouth descendantNorth)
    (bridge : EvenCycleBridge (RedCycles.iterateRefine 2 grid)
      (4 * west) (4 * east) (4 * south) (4 * north)
      descendantWest descendantEast descendantSouth descendantNorth)
    {source descendantStart target : Port}
    (sourceOnCycle : OnCycle west east south north source)
    (descendantStartOnCycle : OnCycle descendantWest descendantEast
      descendantSouth descendantNorth descendantStart)
    (tail : Path (RedCycles.iterateRefine 2 grid)
      descendantStart target true)
    (targetLive : portPresent (RedCycles.iterateRefine 2 grid) target = true) :
    Nonempty (ProjectsTo (grid := grid) (west := west) (east := east)
      (south := south) (north := north) target) := by
  rcases even_trans_odd descendantCycle bridge descendantStartOnCycle tail with
    ⟨fineStart, fineStartOnCycle, path⟩
  exact ⟨projectsTo_of_refinedCyclePath oldCycle fineCycle sourceOnCycle
    fineStartOnCycle path targetLive⟩

end SparseFreeLineEvenExtraCycleRoute
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
