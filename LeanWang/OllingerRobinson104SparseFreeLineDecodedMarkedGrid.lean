/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLinePlaneMarkedGrid

/-! Marked free grids in actual decoded routed-product planes. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineDecodedMarkedGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  RedShadeCrossingBoards ShadedFreeLineRecurrence SparseFreeLinePlaneBase
  SparseFreeLinePlaneMarkedGrid

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

set_option maxHeartbeats 2000000 in
-- The two light-cycle cases use different phase representations of one grid.
theorem unboundedMarkedFreeGrid_with_light
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int) :
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
  have hdepthEven : refinementDepth .even (1 + size) = level + 2 := by
    simp [refinementDepth, Phase.extra, level]
  have hwestEven : west .even (1 + size) = 2 ^ level := by
    simp [west, scale, Phase.factor, hlargePow]
  have heastEven : east .even (1 + size) = 3 * 2 ^ level := by
    simp [east, scale, Phase.factor, hlargePow]
  have hwestOdd : west .odd size = 2 ^ (level - 1) := by
    simp [west, scale, Phase.factor, hsmallPow]
  have heastOdd : east .odd size = 3 * 2 ^ (level - 1) := by
    simp [east, scale, Phase.factor, hsmallPow]
  rcases light with largeLight | smallLight
  · left
    have cycle := RedShadeCrossingBoards.largeCycle coarse level
    have validEven : ValidShadeGrid (refinedGrid .even (1 + size) coarse) state := by
      simpa only [refinedGrid, hdepthEven] using valid
    have cycleEven : CycleOn (refinedGrid .even (1 + size) coarse)
        (west .even (1 + size)) (east .even (1 + size))
        (west .even (1 + size)) (east .even (1 + size)) := by
      simpa only [refinedGrid, hdepthEven, hwestEven, heastEven] using cycle
    have lightEven : CycleShade state
        (west .even (1 + size)) (east .even (1 + size))
        (west .even (1 + size)) (east .even (1 + size)) .light := by
      simpa only [hwestEven, heastEven] using largeLight
    exact ⟨cycle, largeLight, ⟨by
      simpa only [refinedGrid, hdepthEven, hwestEven, heastEven] using
        evenMarkedWitness size coarse validEven cycleEven lightEven⟩⟩
  · right
    let shifted := iterateRefine 1 coarse
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
        oddMarkedWitness size shifted validOdd cycleOdd lightOdd⟩⟩

set_option maxHeartbeats 2000000 in
-- Compatibility wrapper retaining the original grid-only interface.
theorem unboundedMarkedFreeGrid
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int) :
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
  rcases unboundedMarkedFreeGrid_with_light decoded size coarseOrigin with
    ⟨_, _, grid⟩ | ⟨_, _, grid⟩
  · exact Or.inl grid
  · exact Or.inr grid

end SparseFreeLineDecodedMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
