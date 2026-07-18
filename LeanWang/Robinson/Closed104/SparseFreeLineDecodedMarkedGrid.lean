/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.SparseFreeLinePlaneMarkedGrid
import LeanWang.Robinson.Closed104.CanonicalShadeMarkedFreeGrid

/-! Marked free grids in actual decoded routed-product planes. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineDecodedMarkedGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  RedShadeCrossingBoards ShadedFreeLineRecurrence SparseFreeLinePlaneBase
  SparseFreeLinePlaneMarkedGrid CanonicalShadeComparison
  CanonicalShadeMarkedFreeGrid ShadedSubstitution

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 2000000 in
-- The two light-cycle cases use different phase representations of one grid.
theorem unboundedMarkedFreeGrid_with_light
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int)
    (root : (ShadedPlaneShadeGrid.coarseGrid decoded
      (2 * (1 + size) + 2) coarseOrigin) 0 0 = 0) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    (CycleOn (iterateRefine (level + 2) coarse)
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) ∧
      CycleShade state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) .light ∧
      Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2))) ∨
      (CycleOn (iterateRefine (level + 2) coarse)
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) ∧
        CycleShade state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) .light ∧
        Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1))) := by
  let level := 2 * (1 + size)
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
  let state := ShadedPlaneShadeGrid.stateGrid decoded
    (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
  have coarseRoot : coarse 0 0 = 0 := by
    simpa only [coarse, level] using root
  have hlevel : 1 ≤ level := by simp [level]; omega
  have valid : ValidShadeGrid (iterateRefine (level + 2) coarse) state :=
    ShadedPlaneShadeGrid.refined_stateGrid_valid decoded
      (level + 2) coarseOrigin
  have light := ShadedPlaneShadeGrid.hasLightCycleAtLevel decoded hlevel coarseOrigin
  change HasLightCycleAtLevel state level at light
  have hlargePow : 2 ^ level = 4 ^ (1 + size) := by
    dsimp [level]
    rw [pow_mul]
    norm_num
  have hsmallPow : 2 ^ (level - 1) = 2 * 4 ^ size := by
    dsimp [level]
    rw [show 2 * (1 + size) - 1 = 1 + 2 * size by omega, pow_add, pow_mul]
    norm_num
  have hwestOdd : west .odd size = 2 ^ (level - 1) := by
    simp [west, ShadedFreeLineRecurrence.scale, Phase.factor, hsmallPow]
  have heastOdd : east .odd size = 3 * 2 ^ (level - 1) := by
    simp [east, ShadedFreeLineRecurrence.scale, Phase.factor, hsmallPow]
  rcases light with largeLight | smallLight
  · left
    have cycle := RedShadeCrossingBoards.largeCycle coarse level
    have directValid : ValidShadeGrid (actualGrid (size + 1) coarse) state := by
      simpa only [actualGrid, level, Nat.add_comm] using valid
    have directLight : CycleShade state
        (CanonicalShadeComparison.scale (size + 1))
        (3 * CanonicalShadeComparison.scale (size + 1))
        (CanonicalShadeComparison.scale (size + 1))
        (3 * CanonicalShadeComparison.scale (size + 1)) .light := by
      simpa only [CanonicalShadeComparison.scale, hlargePow,
        Nat.add_comm] using largeLight
    exact ⟨cycle, largeLight, ⟨by
      have witness := markedFreeGrid size coarse state seedNode coarseRoot
        seedNode_parent directValid directLight
      have gridEq : actualGrid (size + 1) coarse =
          iterateRefine (level + 2) coarse := by
        unfold actualGrid
        congr 1
        dsimp [level]
        omega
      have hlargePow' : 2 ^ level = 4 ^ (size + 1) := by
        simpa only [Nat.add_comm] using hlargePow
      simp only [CanonicalShadeComparison.scale] at witness
      rw [gridEq, ← hlargePow'] at witness
      exact witness⟩⟩
  · right
    let shifted := iterateRefine 1 coarse
    have shiftedRoot : shifted 0 0 = 0 := by
      dsimp only [shifted, iterateRefine]
      rw [show 0 = 2 * 0 by omega, show 0 = 2 * 0 by omega,
        refineIndexGrid_even_even, coarseRoot]
      native_decide
    have cycle := RedShadeCrossingBoards.smallCycle coarse hlevel
    have hgridSmall : refinedGrid .odd size shifted =
        iterateRefine (level + 2) coarse := by
      unfold refinedGrid
      dsimp [shifted]
      rw [PlaneRedBoards.iterateRefine_add]
      congr 1
      simp [refinementDepth, Phase.extra, level]
      omega
    have validOdd : ValidShadeGrid (refinedGrid .odd size shifted) state := by
      rw [hgridSmall]
      exact valid
    have cycleOdd : CycleOn (refinedGrid .odd size shifted)
        (west .odd size) (east .odd size)
        (west .odd size) (east .odd size) := by
      simpa only [hgridSmall, hwestOdd, heastOdd] using cycle
    have lightOdd : CycleShade state
        (west .odd size) (east .odd size)
        (west .odd size) (east .odd size) .light := by
      simpa only [hwestOdd, heastOdd] using smallLight
    exact ⟨cycle, smallLight, ⟨by
      simpa only [hgridSmall, hwestOdd, heastOdd] using
        oddMarkedWitness size shifted shiftedRoot validOdd cycleOdd lightOdd⟩⟩

set_option maxHeartbeats 2000000 in
-- Compatibility wrapper retaining the original grid-only interface.
theorem unboundedMarkedFreeGrid
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int)
    (root : (ShadedPlaneShadeGrid.coarseGrid decoded
      (2 * (1 + size) + 2) coarseOrigin) 0 0 = 0) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2)) ∨
      Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1)) := by
  rcases unboundedMarkedFreeGrid_with_light decoded size coarseOrigin root with
    ⟨_, _, grid⟩ | ⟨_, _, grid⟩
  · exact Or.inl grid
  · exact Or.inr grid

end SparseFreeLineDecodedMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
