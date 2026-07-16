/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedCarrierBorderHierarchyCertificate
import Mathlib.Tactic.IntervalCases

/-!
# The selected-border hierarchy on substitution supertiles

The finite extended-patch certificate is promoted here to the general
recursive border formula and then projected back to concrete substitution
supertiles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

open ShadedCarrierHierarchy ShadedCarrierBorderFactor
open ShadedCarrierBorderFactorSupertiles

theorem selectedBorder_succ_child
    (level blockX blockY childX childY x y : Nat) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY) + y) =
      firstBorder
        (liftBorder (2 * childX + x) <|
          selectedBorder level
            (2 * blockX + ceilDivFour (2 * childX + x))
            (2 * blockY + ceilDivFour (2 * childY + y)))
        (liftBorder (2 * childX + x) <|
          frameBorder 0
            (2 * (blockX % 2) + ceilDivFour (2 * childX + x))
            (2 * (blockY % 2) + ceilDivFour (2 * childY + y))) := by
  rw [show 2 * (4 * blockX + childX) + x =
      8 * blockX + (2 * childX + x) by omega]
  rw [show 2 * (4 * blockY + childY) + y =
      8 * blockY + (2 * childY + y) by omega]
  exact selectedBorder_succ_block level blockX blockY
    (2 * childX + x) (2 * childY + y)

theorem selectedBorder_eq_refinedBorder
    (level blockX blockY childX childY x y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4)
    (hx : x < 3) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY) + y) =
      refinedBorder (state level blockX blockY) childX childY x y := by
  rw [selectedBorder_succ_child]
  interval_cases childX <;> interval_cases childY <;>
    interval_cases x <;> interval_cases y <;>
    simp [refinedBorder, state, patchEntry, extendedPatch, ceilDivFour,
      List.range_succ]

theorem selectedBorder_eq_refinedColumnBorder
    (level blockX blockY childX childY x y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4)
    (hx : x < 3) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY) + y)
        (2 * (4 * blockX + childX) + x) =
      refinedColumnBorder (state level blockX blockY)
        childX childY x y := by
  rw [selectedBorder_succ_child level blockY blockX childY childX y x]
  interval_cases childX <;> interval_cases childY <;>
    interval_cases x <;> interval_cases y <;>
    simp [refinedColumnBorder, state, patchEntry, extendedPatch, ceilDivFour,
      List.range_succ]

theorem selectedBorder_eq_refinedBorder_zero_zero
    (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX))
        (2 * (4 * blockY + childY)) =
      refinedBorder (state level blockX blockY) childX childY 0 0 := by
  simpa using selectedBorder_eq_refinedBorder level blockX blockY
    childX childY 0 0 hchildX hchildY (by omega) (by omega)

theorem selectedBorder_eq_refinedBorder_x_zero
    (level blockX blockY childX childY y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX))
        (2 * (4 * blockY + childY) + y) =
      refinedBorder (state level blockX blockY) childX childY 0 y := by
  simpa using selectedBorder_eq_refinedBorder level blockX blockY
    childX childY 0 y hchildX hchildY (by omega) hy

theorem selectedBorder_eq_refinedBorder_y_zero
    (level blockX blockY childX childY x : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hx : x < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY)) =
      refinedBorder (state level blockX blockY) childX childY x 0 := by
  simpa using selectedBorder_eq_refinedBorder level blockX blockY
    childX childY x 0 hchildX hchildY hx (by omega)

theorem selectedBorder_eq_refinedColumnBorder_zero_zero
    (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY))
        (2 * (4 * blockX + childX)) =
      refinedColumnBorder (state level blockX blockY)
        childX childY 0 0 := by
  simpa using selectedBorder_eq_refinedColumnBorder level blockX blockY
    childX childY 0 0 hchildX hchildY (by omega) (by omega)

theorem selectedBorder_eq_refinedColumnBorder_x_zero
    (level blockX blockY childX childY y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY) + y)
        (2 * (4 * blockX + childX)) =
      refinedColumnBorder (state level blockX blockY)
        childX childY 0 y := by
  simpa using selectedBorder_eq_refinedColumnBorder level blockX blockY
    childX childY 0 y hchildX hchildY (by omega) hy

theorem selectedBorder_eq_refinedColumnBorder_y_zero
    (level blockX blockY childX childY x : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hx : x < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY))
        (2 * (4 * blockX + childX) + x) =
      refinedColumnBorder (state level blockX blockY)
        childX childY x 0 := by
  simpa using selectedBorder_eq_refinedColumnBorder level blockX blockY
    childX childY x 0 hchildX hchildY hx (by omega)

theorem extendedPatch_succ (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    extendedPatch (level + 1)
        (4 * blockX + childX) (4 * blockY + childY) =
      refinePatch (state level blockX blockY) childX childY := by
  unfold extendedPatch refinePatch
  apply congrArg₂ (fun rows columns => rows ++ columns)
  · simp [selectedBorder_eq_refinedBorder,
      selectedBorder_eq_refinedBorder_zero_zero,
      selectedBorder_eq_refinedBorder_x_zero,
      selectedBorder_eq_refinedBorder_y_zero,
      hchildX, hchildY, List.range_succ]
  · simp [selectedBorder_eq_refinedColumnBorder,
      selectedBorder_eq_refinedColumnBorder_zero_zero,
      selectedBorder_eq_refinedColumnBorder_x_zero,
      selectedBorder_eq_refinedColumnBorder_y_zero,
      hchildX, hchildY, List.range_succ]

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
