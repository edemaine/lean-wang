/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeCycleEvenDescendants

/-!
# Odd bridges to base-four descendant cycles

An odd-scale Robinson cycle first crosses one of four corner cycles and then
reaches any finest descendant by the existing even-depth bridge.  Thus every
finest descendant has the opposite shade from the odd root.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycleOddDescendants

open OrientedRedCycles RedShadeGraph RedShadeGraphBoards
  RedShadeCycleCrossingPaths RedShadeCycleBridgeComposition
  RedShadeCycleEvenDescendants TranslatedRedShadeCrossingPaths
  OrientedRedBoardTranslations

private def corner (depth coordinate : Nat)
    (bound : coordinate < 2 * 4 ^ depth) : Fin 2 :=
  ⟨coordinate / 4 ^ depth, by
    apply (Nat.div_lt_iff_lt_mul (pow_pos (by decide) _)).2
    simpa [Nat.mul_comm] using bound⟩

private theorem corner_lower (depth coordinate : Nat)
    (bound : coordinate < 2 * 4 ^ depth) :
    4 ^ depth * (corner depth coordinate bound).val ≤ coordinate := by
  dsimp [corner]
  exact Nat.mul_div_le coordinate (4 ^ depth)

private theorem corner_upper (depth coordinate : Nat)
    (bound : coordinate < 2 * 4 ^ depth) :
    coordinate < 4 ^ depth * ((corner depth coordinate bound).val + 1) := by
  dsimp [corner]
  exact Nat.lt_mul_div_succ coordinate (pow_pos (by decide) _)

/-- Every finest cell cycle in the odd root supertile is oddly connected to
the odd root cycle. -/
theorem rootDescendantBridge
    (depth : Nat) (grid : Nat → Nat → Index) (cellX cellY : Nat)
    (hcellX : cellX < 2 * 4 ^ depth)
    (hcellY : cellY < 2 * 4 ^ depth) :
    RedShadeCycleCrossingPaths.OddCycleBridge
      (RedCycles.iterateRefine (2 * depth + 4) grid)
      (2 * 4 ^ depth) (2 * (3 * 4 ^ depth))
      (2 * 4 ^ depth) (2 * (3 * 4 ^ depth))
      (4 * cellX + 1) (4 * cellX + 3)
      (4 * cellY + 1) (4 * cellY + 3) := by
  let cornerX := corner depth cellX hcellX
  let cornerY := corner depth cellY hcellY
  have first := cornerBridge (RedCycles.iterateRefine 1 grid)
    (level := 2 * depth + 1) (by omega) 0 0 cornerX cornerY
  have second := RedShadeCycleEvenDescendants.descendantBridge depth
    (RedCycles.iterateRefine 2 grid) cornerX.val cornerY.val cellX cellY
    (corner_lower depth cellX hcellX)
    (corner_upper depth cellX hcellX)
    (corner_lower depth cellY hcellY)
    (corner_upper depth cellY hcellY)
  have middle := at_scale (RedCycles.iterateRefine 2 grid)
    (2 * depth) cornerX.val cornerY.val
  have firstGrid :
      RedCycles.iterateRefine (2 * depth + 1 + 2)
          (RedCycles.iterateRefine 1 grid) =
        RedCycles.iterateRefine (2 * depth + 4) grid := by
    rw [PlaneRedBoards.iterateRefine_add]
  have secondGrid :
      RedCycles.iterateRefine (2 * depth + 2)
          (RedCycles.iterateRefine 2 grid) =
        RedCycles.iterateRefine (2 * depth + 4) grid := by
    rw [PlaneRedBoards.iterateRefine_add]
  rw [firstGrid] at first
  rw [secondGrid] at second middle
  have hsub : 2 * depth + 1 - 1 = 2 * depth := by omega
  rw [hsub] at first
  have first' := first
  simp only [Nat.mul_zero, Nat.zero_add] at first'
  have composed := CycleBridge.trans middle first' second
  have hpowOdd : 2 ^ (2 * depth + 1) = 2 * 4 ^ depth := by
    rw [pow_succ, pow_mul]
    norm_num
    omega
  rw [hpowOdd] at composed
  simpa [Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using composed

end RedShadeCycleOddDescendants
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
