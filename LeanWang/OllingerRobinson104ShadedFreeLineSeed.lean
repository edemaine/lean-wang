/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedLightBoardFreeLines
import LeanWang.OllingerRobinson104RedShadeInnerBoards
import LeanWang.OllingerRobinson104RefinementTranslation
import Mathlib.Tactic.IntervalCases

/-!
The central free row and column in the first two-level same-shade recurrence
block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineSeed

open RedCycles ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem centerRow_no_vertical
    (grid : Nat → Nat → Index) {quarterX : Nat}
    (hwest : 9 < quarterX) (heast : quarterX < 24) :
    Signals.verticalInterior?
      (componentAt (iterateRefine 4 grid) quarterX 16)
      (quadrantAt quarterX 16) = none := by
  interval_cases quarterX <;>
    simp [componentAt, quadrantAt, iterateRefine, RedCycles.refineIndexGrid,
      RedCycles.parityOffset]
  all_goals generalize grid 0 0 = parent; revert parent; native_decide

set_option linter.style.nativeDecide false in
theorem centerColumn_no_horizontal
    (grid : Nat → Nat → Index) {quarterY : Nat}
    (hsouth : 9 < quarterY) (hnorth : quarterY < 24) :
    Signals.horizontalInterior?
      (componentAt (iterateRefine 4 grid) 16 quarterY)
      (quadrantAt 16 quarterY) = none := by
  interval_cases quarterY <;>
    simp [componentAt, quadrantAt, iterateRefine, RedCycles.refineIndexGrid,
      RedCycles.parityOffset]
  all_goals generalize grid 0 0 = parent; revert parent; native_decide

theorem centerRow_free (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State) :
    IsFreeRow (iterateRefine 4 grid) shadeGrid 4 12 16 := by
  intro quarterX hwest heast
  apply ShadedSignals.selectedVerticalFor_of_none
  exact centerRow_no_vertical grid (by
    simp [RedShadeCycles.quarterWest] at hwest
    omega) (by
    simp [RedShadeCycles.quarterEast] at heast
    omega)

theorem centerColumn_free (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State) :
    IsFreeColumn (iterateRefine 4 grid) shadeGrid 4 12 16 := by
  intro quarterY hsouth hnorth
  apply ShadedSignals.selectedHorizontalFor_of_none
  exact centerColumn_no_horizontal grid (by
    simp [RedShadeCycles.quarterSouth] at hsouth
    omega) (by
    simp [RedShadeCycles.quarterNorth] at hnorth
    omega)

theorem center_clear
    (grid : Nat → Nat → Index)
    {shadeGrid : Nat → Nat → RedShades.State}
    {signalGrid : Nat → Nat → Signals.State}
    (shaded : RedShadeCycles.CycleShade shadeGrid 4 12 4 12 .light)
    (valid : ValidGrid (iterateRefine 4 grid) shadeGrid signalGrid) :
    signalGrid 16 16 = Signals.clearState := by
  apply RedShadeCycles.CycleShade.clear_at_free_crossing shaded
    (OrientedRedBoardTranslations.at_scale grid 2 0 0) valid
  · simp [RedShadeCycles.quarterWest]
  · simp [RedShadeCycles.quarterEast]
  · simp [RedShadeCycles.quarterSouth]
  · simp [RedShadeCycles.quarterNorth]
  · exact centerRow_free grid shadeGrid
  · exact centerColumn_free grid shadeGrid

theorem centerRow_no_vertical_at
    (grid : Nat → Nat → Index) (blockX blockY : Nat) {quarterX : Nat}
    (hwest : 32 * blockX + 9 < quarterX)
    (heast : quarterX < 32 * blockX + 24) :
    Signals.verticalInterior?
      (componentAt (iterateRefine 4 grid) quarterX (32 * blockY + 16))
      (quadrantAt quarterX (32 * blockY + 16)) = none := by
  let localX := quarterX - 32 * blockX
  have hlocalWest : 9 < localX := by omega
  have hlocalEast : localX < 24 := by omega
  have hx : 32 * blockX + localX = quarterX := by omega
  have hlocal := centerRow_no_vertical
    (RefinementTranslation.shiftGrid grid blockX blockY)
    hlocalWest hlocalEast
  have htransport := RefinementTranslation.verticalInterior_iterateRefine_shift
    4 grid blockX blockY localX 16
  norm_num at htransport
  rw [htransport] at hlocal
  simpa only [hx] using hlocal

theorem centerColumn_no_horizontal_at
    (grid : Nat → Nat → Index) (blockX blockY : Nat) {quarterY : Nat}
    (hsouth : 32 * blockY + 9 < quarterY)
    (hnorth : quarterY < 32 * blockY + 24) :
    Signals.horizontalInterior?
      (componentAt (iterateRefine 4 grid) (32 * blockX + 16) quarterY)
      (quadrantAt (32 * blockX + 16) quarterY) = none := by
  let localY := quarterY - 32 * blockY
  have hlocalSouth : 9 < localY := by omega
  have hlocalNorth : localY < 24 := by omega
  have hy : 32 * blockY + localY = quarterY := by omega
  have hlocal := centerColumn_no_horizontal
    (RefinementTranslation.shiftGrid grid blockX blockY)
    hlocalSouth hlocalNorth
  have htransport :=
    RefinementTranslation.horizontalInterior_iterateRefine_shift
      4 grid blockX blockY 16 localY
  norm_num at htransport
  rw [htransport] at hlocal
  simpa only [hy] using hlocal

theorem centerRow_free_at (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State) (blockX blockY : Nat) :
    IsFreeRow (iterateRefine 4 grid) shadeGrid
      (16 * blockX + 4) (16 * blockX + 12) (32 * blockY + 16) := by
  intro quarterX hwest heast
  apply ShadedSignals.selectedVerticalFor_of_none
  apply centerRow_no_vertical_at grid blockX blockY
  · simp [RedShadeCycles.quarterWest] at hwest
    omega
  · simp [RedShadeCycles.quarterEast] at heast
    omega

theorem centerColumn_free_at (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State) (blockX blockY : Nat) :
    IsFreeColumn (iterateRefine 4 grid) shadeGrid
      (16 * blockY + 4) (16 * blockY + 12) (32 * blockX + 16) := by
  intro quarterY hsouth hnorth
  apply ShadedSignals.selectedHorizontalFor_of_none
  apply centerColumn_no_horizontal_at grid blockX blockY
  · simp [RedShadeCycles.quarterSouth] at hsouth
    omega
  · simp [RedShadeCycles.quarterNorth] at hnorth
    omega

theorem center_clear_at
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {shadeGrid : Nat → Nat → RedShades.State}
    {signalGrid : Nat → Nat → Signals.State}
    (shaded : RedShadeCycles.CycleShade shadeGrid
      (16 * blockX + 4) (16 * blockX + 12)
      (16 * blockY + 4) (16 * blockY + 12) .light)
    (valid : ValidGrid (iterateRefine 4 grid) shadeGrid signalGrid) :
    signalGrid (32 * blockX + 16) (32 * blockY + 16) =
      Signals.clearState := by
  apply RedShadeCycles.CycleShade.clear_at_free_crossing shaded
    (OrientedRedBoardTranslations.at_scale grid 2 blockX blockY) valid
  · simp [RedShadeCycles.quarterWest]
  · simp [RedShadeCycles.quarterEast]
  · simp [RedShadeCycles.quarterSouth]
  · simp [RedShadeCycles.quarterNorth]
  · exact centerRow_free_at grid shadeGrid blockX blockY
  · exact centerColumn_free_at grid shadeGrid blockX blockY

end ShadedFreeLineSeed
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
