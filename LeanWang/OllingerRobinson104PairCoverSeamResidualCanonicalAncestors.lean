/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycleLocalTransport
import LeanWang.OllingerRobinson104PairCoverSeamResidualCycleBridges
import LeanWang.OllingerRobinson104TranslatedRedShadeCrossingPaths

/-!
# Canonical hierarchy ancestors for residual seam sources

Residual source ancestry must remember which Robinson hierarchy cycle it
reaches.  This module packages the cycle's scale and block coordinates and
normalizes the arbitrary parity returned by the created-source audit.  An even
local route stops on the audited cell cycle; an odd local route crosses the
odd child-to-parent bridge and therefore reaches the parent cycle evenly.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCanonicalAncestors

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeCycleConnectivity
  RedShadeCycleCrossingPaths OrientedRedBoardTranslations
  TranslatedRedShadeCrossingPaths
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCycleLocalTransport
  RefinedCoordinateProjection ShadedFreeLinePatternRefinement
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- An even route to a specifically named cycle in the Robinson hierarchy. -/
def CanonicalCycleAncestor (grid : Nat → Nat → Index)
    (source : Port) : Prop :=
  ∃ level blockX blockY,
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- Forgetting the hierarchy name recovers the original cycle-ancestry
interface. -/
theorem CanonicalCycleAncestor.toCycleAncestor
    {grid : Nat → Nat → Index} {source : Port}
    (ancestor : CanonicalCycleAncestor grid source) :
    CycleAncestor grid source := by
  rcases ancestor with
    ⟨level, blockX, blockY, cycle, entry, entryOnCycle, path⟩
  exact ⟨_, _, _, _, cycle, entry, entryOnCycle, path⟩

/-- Prepending an even route preserves the canonical hierarchy name. -/
theorem CanonicalCycleAncestor.of_evenPath
    {grid : Nat → Nat → Index} {source target : Port}
    (ancestor : CanonicalCycleAncestor grid target)
    (path : Path grid source target false) :
    CanonicalCycleAncestor grid source := by
  rcases ancestor with
    ⟨level, blockX, blockY, cycle, entry, entryOnCycle, tail⟩
  exact ⟨level, blockX, blockY, cycle, entry, entryOnCycle,
    by simpa using Path.trans path tail⟩

/-- Two substitutions preserve the canonical cycle name, increasing its scale
by two while retaining its hierarchy block. -/
theorem CanonicalCycleAncestor.refineSparse
    {grid : Nat → Nat → Index} {source : Port}
    (ancestor : CanonicalCycleAncestor grid source)
    (sourceLive : portPresent grid source = true) :
    CanonicalCycleAncestor (iterateRefine 2 grid) (sparsePort source) := by
  rcases ancestor with
    ⟨level, blockX, blockY, cycle, entry, entryOnCycle, path⟩
  have fineCycle := cycle.iterateRefine 2
  have entryLive := portPresent_of_onCycle cycle entryOnCycle
  have hscale : 2 ^ (level + 2) = 4 * 2 ^ level := by
    rw [pow_add]
    norm_num
    ac_rfl
  refine ⟨level + 2, blockX, blockY, ?_, sparsePort entry, ?_, ?_⟩
  · simpa [RedCycles.doubleN_eq, hscale, Nat.mul_assoc] using fineCycle
  · simpa [hscale, Nat.mul_assoc] using onCycle_sparse entryOnCycle
  · exact path_refine_sparse path sourceLive entryLive

/-- A created source in a three-level refinement reaches a named hierarchy
cycle evenly.  The retained level records whether parity normalization stopped
at the cell cycle or its parent. -/
theorem ofLocalCycleRoute
    (grid : Nat → Nat → Index) {source : Port}
    (route : LocalCycleRouteAt (iterateRefine 1 grid) source) :
    CanonicalCycleAncestor (iterateRefine 3 grid) source := by
  unfold LocalCycleRouteAt at route
  rw [PlaneRedBoards.iterateRefine_add] at route
  rcases route with
    ⟨blockX, blockY, entry, parity, childCycle, entryOnChild, sourcePath⟩
  cases hparity : parity
  · refine ⟨0, blockX, blockY, ?_, entry, ?_, ?_⟩
    · simpa using childCycle
    · simpa using entryOnChild
    · simpa [hparity] using sourcePath
  · let parentX := blockX / 2
    let parentY := blockY / 2
    let cornerX : Fin 2 := ⟨blockX % 2, Nat.mod_lt _ (by decide)⟩
    let cornerY : Fin 2 := ⟨blockY % 2, Nat.mod_lt _ (by decide)⟩
    have hblockX : 2 * parentX + cornerX.val = blockX := by
      have := Nat.mod_add_div blockX 2
      dsimp [parentX, cornerX]
      omega
    have hblockY : 2 * parentY + cornerY.val = blockY := by
      have := Nat.mod_add_div blockY 2
      dsimp [parentY, cornerY]
      omega
    have bridge := cornerBridge grid (level := 1) (by omega)
      parentX parentY cornerX cornerY
    have bridge' : OddCycleBridge (iterateRefine 3 grid)
        (2 * (4 * parentX + 1)) (2 * (4 * parentX + 3))
        (2 * (4 * parentY + 1)) (2 * (4 * parentY + 3))
        (4 * blockX + 1) (4 * blockX + 3)
        (4 * blockY + 1) (4 * blockY + 3) := by
      simpa [hblockX, hblockY] using bridge
    rcases bridge' with
      ⟨parentEntry, childExit, parentEntryOnCycle, childExitOnCycle,
        bridgePath⟩
    have aroundChild := onCycle_connected childCycle
      entryOnChild childExitOnCycle
    have sourceToParent : Path (iterateRefine 3 grid)
        source parentEntry false := by
      have sourcePath' : Path (iterateRefine 3 grid) source entry true := by
        simpa [hparity] using sourcePath
      simpa [Bool.xor_assoc] using
        Path.trans sourcePath'
          (Path.trans aroundChild (path_symm bridgePath))
    refine ⟨1, parentX, parentY, ?_, parentEntry, ?_, sourceToParent⟩
    · simpa using at_scale grid 1 parentX parentY
    · simpa using parentEntryOnCycle

set_option maxHeartbeats 2000000 in
-- The selector depends on the refinement equality used to expose its route.
/-- Horizontal created boundaries terminate at a named local hierarchy cycle. -/
theorem horizontalCreated
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 3 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    CanonicalCycleAncestor (iterateRefine 3 grid)
      (PairCoverSeamShadePaths.horizontalPort
        (iterateRefine 3 grid) column boundary) := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.horizontalCreated
    (iterateRefine 1 grid) column boundary createdBoundary interior'
  simpa [hgrid] using ofLocalCycleRoute grid route

set_option maxHeartbeats 2000000 in
-- The selector depends on the refinement equality used to expose its route.
/-- Vertical created boundaries terminate at a named local hierarchy cycle. -/
theorem verticalCreated
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 3 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    CanonicalCycleAncestor (iterateRefine 3 grid)
      (PairCoverSeamShadePaths.verticalPort
        (iterateRefine 3 grid) boundary row) := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.verticalCreated
    (iterateRefine 1 grid) boundary row createdBoundary interior'
  simpa [hgrid] using ofLocalCycleRoute grid route

end PairCoverSeamResidualCanonicalAncestors
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
