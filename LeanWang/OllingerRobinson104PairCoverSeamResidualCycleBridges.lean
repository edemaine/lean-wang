/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamShadePaths
import LeanWang.OllingerRobinson104SignalFreeCellLocal
import LeanWang.OllingerRobinson104SparseFreeLineLocalProjection

/-! Port-presence lemmas for residual seam endpoints. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCycleBridges

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  SparseFreeLineLocalProjection Signals.FreeCellLocal

/-- An even route from one source port into an enclosing hierarchy cycle. -/
def CycleAncestor (grid : Nat → Nat → Index) (source : Port) : Prop :=
  ∃ west east south north, CycleOn grid west east south north ∧
    ∃ entry, OnCycle west east south north entry ∧
      Path grid source entry false

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

end PairCoverSeamResidualCycleBridges
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
