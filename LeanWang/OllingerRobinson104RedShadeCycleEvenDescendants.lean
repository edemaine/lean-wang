/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleBridgeComposition

/-!
# Even bridges to base-four descendant cycles

Pairs of Robinson substitution levels preserve crossing parity.  Iterating the
two-corner bridge therefore connects an ancestor board evenly to every
depth-two cell board in its base-four descendant block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycleEvenDescendants

open OrientedRedCycles RedShadeGraph RedShadeGraphBoards
  RedShadeCycleBridgeComposition OrientedRedBoardTranslations

private def highBit (digit : Fin 4) : Fin 2 :=
  ⟨digit.val / 2, by omega⟩

private def lowBit (digit : Fin 4) : Fin 2 :=
  ⟨digit.val % 2, Nat.mod_lt _ (by decide)⟩

private theorem bits_eq (digit : Fin 4) :
    2 * (highBit digit).val + (lowBit digit).val = digit.val := by
  have h := Nat.mod_add_div digit.val 2
  dsimp [highBit, lowBit]
  omega

/-- Every cell in a base-four descendant block is evenly connected to its
ancestor board after the corresponding even number of refinements. -/
theorem descendantBridge : ∀ (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY cellX cellY : Nat),
    4 ^ depth * blockX ≤ cellX →
    cellX < 4 ^ depth * (blockX + 1) →
    4 ^ depth * blockY ≤ cellY →
    cellY < 4 ^ depth * (blockY + 1) →
    EvenCycleBridge (RedCycles.iterateRefine (2 * depth + 2) grid)
      (2 ^ (2 * depth) * (4 * blockX + 1))
      (2 ^ (2 * depth) * (4 * blockX + 3))
      (2 ^ (2 * depth) * (4 * blockY + 1))
      (2 ^ (2 * depth) * (4 * blockY + 3))
      (4 * cellX + 1) (4 * cellX + 3)
      (4 * cellY + 1) (4 * cellY + 3)
  | 0, grid, blockX, blockY, cellX, cellY,
      hcellXLower, hcellXUpper, hcellYLower, hcellYUpper => by
      have hx : cellX = blockX := by norm_num at hcellXLower hcellXUpper; omega
      have hy : cellY = blockY := by norm_num at hcellYLower hcellYUpper; omega
      subst cellX
      subst cellY
      have cycle := depthTwo_at grid blockX blockY
      simpa using EvenCycleBridge.refl cycle (by omega)
  | depth + 1, grid, blockX, blockY, cellX, cellY,
      hcellXLower, hcellXUpper, hcellYLower, hcellYUpper => by
      let scale := 4 ^ depth
      have hscale : 0 < scale := pow_pos (by decide) _
      have hquotXLower : 4 * blockX ≤ cellX / scale := by
        apply (Nat.le_div_iff_mul_le hscale).2
        rw [pow_succ] at hcellXLower
        calc
          4 * blockX * scale = 4 ^ depth * 4 * blockX := by
            dsimp [scale]
            ac_rfl
          _ ≤ cellX := hcellXLower
      have hquotXUpper : cellX / scale < 4 * (blockX + 1) := by
        apply (Nat.div_lt_iff_lt_mul hscale).2
        rw [pow_succ] at hcellXUpper
        calc
          cellX < 4 ^ depth * 4 * (blockX + 1) := hcellXUpper
          _ = 4 * (blockX + 1) * scale := by
            dsimp [scale]
            ac_rfl
      have hquotYLower : 4 * blockY ≤ cellY / scale := by
        apply (Nat.le_div_iff_mul_le hscale).2
        rw [pow_succ] at hcellYLower
        calc
          4 * blockY * scale = 4 ^ depth * 4 * blockY := by
            dsimp [scale]
            ac_rfl
          _ ≤ cellY := hcellYLower
      have hquotYUpper : cellY / scale < 4 * (blockY + 1) := by
        apply (Nat.div_lt_iff_lt_mul hscale).2
        rw [pow_succ] at hcellYUpper
        calc
          cellY < 4 ^ depth * 4 * (blockY + 1) := hcellYUpper
          _ = 4 * (blockY + 1) * scale := by
            dsimp [scale]
            ac_rfl
      let digitX : Fin 4 := ⟨cellX / scale - 4 * blockX, by
        omega⟩
      let digitY : Fin 4 := ⟨cellY / scale - 4 * blockY, by
        omega⟩
      let middleX := 4 * blockX + digitX.val
      let middleY := 4 * blockY + digitY.val
      have hmiddleX : middleX = cellX / scale := by
        dsimp [middleX, digitX]
        omega
      have hmiddleY : middleY = cellY / scale := by
        dsimp [middleY, digitY]
        omega
      have hnextXLower : scale * middleX ≤ cellX := by
        rw [hmiddleX]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self cellX scale
      have hnextXUpper : cellX < scale * (middleX + 1) := by
        rw [hmiddleX]
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ cellX hscale
      have hnextYLower : scale * middleY ≤ cellY := by
        rw [hmiddleY]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self cellY scale
      have hnextYUpper : cellY < scale * (middleY + 1) := by
        rw [hmiddleY]
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ cellY hscale
      have first := twoCornerBridge grid (level := 2 * (depth + 1)) (by omega)
        blockX blockY (highBit digitX) (highBit digitY)
        (lowBit digitX) (lowBit digitY)
      have second := descendantBridge depth (RedCycles.iterateRefine 2 grid)
        middleX middleY cellX cellY
        hnextXLower hnextXUpper hnextYLower hnextYUpper
      have middleCycle := at_scale (RedCycles.iterateRefine 2 grid)
        (2 * depth) middleX middleY
      have hgrid :
          RedCycles.iterateRefine (2 * depth + 2)
              (RedCycles.iterateRefine 2 grid) =
            RedCycles.iterateRefine (2 * (depth + 1) + 2) grid := by
        rw [PlaneRedBoards.iterateRefine_add]
        congr 1
      rw [hgrid] at second middleCycle
      have hlevel : 2 * (depth + 1) - 2 = 2 * depth := by omega
      have hbitsX :
          2 * (2 * blockX + (highBit digitX).val) + (lowBit digitX).val =
            middleX := by
        have hbits := bits_eq digitX
        dsimp [middleX]
        omega
      have hbitsY :
          2 * (2 * blockY + (highBit digitY).val) + (lowBit digitY).val =
            middleY := by
        have hbits := bits_eq digitY
        dsimp [middleY]
        omega
      have first' : EvenCycleBridge
          (RedCycles.iterateRefine (2 * (depth + 1) + 2) grid)
          (2 ^ (2 * (depth + 1)) * (4 * blockX + 1))
          (2 ^ (2 * (depth + 1)) * (4 * blockX + 3))
          (2 ^ (2 * (depth + 1)) * (4 * blockY + 1))
          (2 ^ (2 * (depth + 1)) * (4 * blockY + 3))
          (2 ^ (2 * depth) * (4 * middleX + 1))
          (2 ^ (2 * depth) * (4 * middleX + 3))
          (2 ^ (2 * depth) * (4 * middleY + 1))
          (2 ^ (2 * depth) * (4 * middleY + 3)) := by
        rw [hlevel, hbitsX, hbitsY] at first
        exact first
      exact even_trans_even middleCycle first' second

/-- Root-block form of `descendantBridge`. -/
theorem rootDescendantBridge
    (depth : Nat) (grid : Nat → Nat → Index) (cellX cellY : Nat)
    (hcellX : cellX < 4 ^ depth) (hcellY : cellY < 4 ^ depth) :
    EvenCycleBridge (RedCycles.iterateRefine (2 * depth + 2) grid)
      (4 ^ depth) (3 * 4 ^ depth) (4 ^ depth) (3 * 4 ^ depth)
      (4 * cellX + 1) (4 * cellX + 3)
      (4 * cellY + 1) (4 * cellY + 3) := by
  have hpow : 2 ^ (2 * depth) = 4 ^ depth := by
    rw [pow_mul]
    norm_num
  have bridge := descendantBridge depth grid 0 0 cellX cellY
    (by simp) (by simpa using hcellX) (by simp) (by simpa using hcellY)
  rw [hpow] at bridge
  simpa [Nat.mul_comm] using bridge

end RedShadeCycleEvenDescendants
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
