/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionPairCoverRecurrence
import LeanWang.OllingerRobinson104ShadedRoutedScaffoldForward

/-!
# Connect pair-cover recurrence to the routed scaffold

This adapter translates the complete pair-cover families into the hierarchy
obligation used by the unbounded free-grid construction.
-/

noncomputable section

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace ShadedObstructionPairCoverRecurrence

open RedCycles RedShadeCycles RedShadePaths ShadedFreeLineRecurrence
  ShadedPlaneSignalGrid ShadedObstructionGeometryCover
  ShadedRoutedScaffoldForward SparseFreeLinePlaneBase

set_option maxRecDepth 20000

set_option maxHeartbeats 1000000 in
-- Normalizing the even and odd recurrence grids against the common tower grid.
/-- The two complete pair-cover families supply the exact forward hierarchy
obligation. -/
theorem lightBoardPairCovers_of_allHolds
    (holds : AllHolds) : LightBoardPairCovers := by
  intro T seed x decoded size coarseOrigin
  let level := 2 * (1 + size)
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded
    (level + 2) coarseOrigin
  let state := ShadedPlaneShadeGrid.stateGrid decoded
    (ShadedPlaneShadeGrid.fineParentOrigin decoded
      (level + 2) coarseOrigin)
  have valid : ValidShadeGrid (iterateRefine (level + 2) coarse) state :=
    ShadedPlaneShadeGrid.refined_stateGrid_valid decoded
      (level + 2) coarseOrigin
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
  let shifted := iterateRefine 1 coarse
  have hgridOdd : refinedGrid .odd size shifted =
      iterateRefine (level + 2) coarse := by
    unfold refinedGrid
    dsimp [shifted]
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    simp [refinementDepth, Phase.extra, level]
    omega
  have hwestOdd : west .odd size = 2 ^ (level - 1) := by
    simp [west, scale, Phase.factor, hsmallPow]
  have heastOdd : east .odd size = 3 * 2 ^ (level - 1) := by
    simp [east, scale, Phase.factor, hsmallPow]
  have evenValid : ValidShadeGrid
      (refinedGrid .even (1 + size) coarse) state := by
    simpa only [refinedGrid, hdepthEven] using valid
  have oddValid : ValidShadeGrid (refinedGrid .odd size shifted) state := by
    rw [hgridOdd]
    exact valid
  have evenCover := (holds size).1 coarse state evenValid
  have oddCover := (holds size).2 shifted state oddValid
  constructor
  · intro _
    simpa only [refinedGrid, hdepthEven, hwestEven, heastEven] using evenCover
  · intro _
    simpa only [hgridOdd, hwestOdd, heastOdd] using oddCover

end ShadedObstructionPairCoverRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104

end
