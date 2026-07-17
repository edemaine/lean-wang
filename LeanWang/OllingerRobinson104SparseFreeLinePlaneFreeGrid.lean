/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLinePlaneProjectionStep
import LeanWang.OllingerRobinson104ShadedPlaneShadeGrid

/-! Semantic sparse free grids in actual decoded planes. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneFreeGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths RedShadeCrossingBoards
  ShadedFreeGrid ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid SparseFreeLineOffsets
  SparseFreeLinePlaneBase

set_option maxRecDepth 20000

/-- Arbitrary-grid graph certificates become semantic free rows and columns
inside any light cycle with the matching sparse bounds. -/
def freeGridOfGraphHolds
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    (graph : GridGraphHolds phase depth grid)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid phase depth grid) stateGrid)
    (cycle : CycleOn (refinedGrid phase depth grid)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth))
    (shaded : CycleShade stateGrid
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth) .light) :
    FreeGrid (refinedGrid phase depth grid) stateGrid
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth) (offsets depth).length where
  columnAt := fun index => lineCoordinate phase depth (offsetAt depth index)
  rowAt := fun index => lineCoordinate phase depth (offsetAt depth index)
  column_strictMono := by
    intro first second hlt
    have hmono := offsetAt_strictMono depth hlt
    cases phase <;> simp [lineCoordinate, Phase.factor] <;> omega
  row_strictMono := by
    intro first second hlt
    have hmono := offsetAt_strictMono depth hlt
    cases phase <;> simp [lineCoordinate, Phase.factor] <;> omega
  column_west := by
    intro index
    have hpositive := (offsetAt_full_bounds depth index).1
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, scale, Phase.factor,
        quarterWest] <;> omega
  column_east := by
    intro index
    have hbound := (offsetAt_full_bounds depth index).2
    rw [pow_succ] at hbound
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, east, scale, Phase.factor,
        quarterWest, quarterEast] <;> omega
  row_south := by
    intro index
    have hpositive := (offsetAt_full_bounds depth index).1
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, scale, Phase.factor,
        quarterWest, quarterSouth] <;> omega
  row_north := by
    intro index
    have hbound := (offsetAt_full_bounds depth index).2
    rw [pow_succ] at hbound
    cases phase <;>
      simp [lineCoordinate, quarterStart, west, east, scale, Phase.factor,
        quarterWest, quarterNorth] <;> omega
  freeColumn := by
    intro index
    apply isFreeColumn_of_certificate valid cycle shaded
    exact (graph.2 (offsetAt depth index)
      (offsetAt_mem depth index)).toColumnCertificate
  freeRow := by
    intro index
    apply isFreeRow_of_certificate valid cycle shaded
    exact (graph.1 (offsetAt depth index)
      (offsetAt_mem depth index)).toRowCertificate

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

set_option maxHeartbeats 2000000 in
-- Normalizing the two phase/depth representations of the same refined grid is intensive.
/-- Every decoded product plane contains an arbitrarily large sparse free grid.
The disjunction records which of the two comparable Robinson cycles is light. -/
theorem unboundedFreeGrid
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    Nonempty (FreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2)) ∨
      Nonempty (FreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1)) := by
  let level := 2 * (1 + size)
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
  let state := ShadedPlaneShadeGrid.stateGrid decoded
    (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
  have hlevel : 1 ≤ level := by simp [level]; omega
  have valid : ValidShadeGrid (iterateRefine (level + 2) coarse) state := by
    exact ShadedPlaneShadeGrid.refined_stateGrid_valid decoded
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
    have graph :=
      (SparseFreeLinePlaneProjectionStep.graphHolds_unbounded coarse size).1
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
    have grid := freeGridOfGraphHolds graph validEven cycleEven lightEven
    exact ⟨by
      simpa only [refinedGrid, hdepthEven, hwestEven, heastEven,
        offsets_length, show 1 + size + 1 = size + 2 by omega] using grid⟩
  · right
    let shifted := iterateRefine 1 coarse
    have graph :=
      (SparseFreeLinePlaneProjectionStep.graphHolds_unbounded shifted size).2
    have cycle := RedShadeCrossingBoards.smallCycle coarse hlevel
    have hgridSmall : refinedGrid .odd size shifted =
        iterateRefine (level + 2) coarse := by
      unfold refinedGrid
      dsimp [shifted]
      rw [PlaneRedBoards.iterateRefine_add]
      congr 1
      simp [refinementDepth, Phase.extra, level]
      omega
    have valid' : ValidShadeGrid (refinedGrid .odd size shifted) state := by
      rw [hgridSmall]
      exact valid
    have cycle' : CycleOn (refinedGrid .odd size shifted)
        (west .odd size) (east .odd size)
        (west .odd size) (east .odd size) := by
      simpa only [hgridSmall, hwestOdd, heastOdd] using cycle
    have lightOdd : CycleShade state
        (west .odd size) (east .odd size)
        (west .odd size) (east .odd size) .light := by
      simpa only [hwestOdd, heastOdd] using smallLight
    have grid := freeGridOfGraphHolds graph valid' cycle' lightOdd
    exact ⟨by
      simpa only [hgridSmall, hwestOdd, heastOdd, offsets_length] using grid⟩

end SparseFreeLinePlaneFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
