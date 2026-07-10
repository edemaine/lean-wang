/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedLightBoardFreeLines
import LeanWang.OllingerRobinson104RedShadeInnerBoards
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

end ShadedFreeLineSeed
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
