/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeCycleBridgeComposition

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

/-- One coordinate of a descendant cell, split into its next base-four digit
and the remaining lower-order block. -/
private structure DescendantCoordinate (depth block cell : Nat) where
  digit : Fin 4
  middle : Nat
  lower : 4 ^ depth * middle ≤ cell
  upper : cell < 4 ^ depth * (middle + 1)
  bits :
    2 * (2 * block + (highBit digit).val) + (lowBit digit).val = middle

private def descendantCoordinate {depth block cell : Nat}
    (lower : 4 ^ (depth + 1) * block ≤ cell)
    (upper : cell < 4 ^ (depth + 1) * (block + 1)) :
    DescendantCoordinate depth block cell := by
  let scale := 4 ^ depth
  have scalePositive : 0 < scale := pow_pos (by decide) _
  have quotientLower : 4 * block ≤ cell / scale := by
    apply (Nat.le_div_iff_mul_le scalePositive).2
    rw [pow_succ] at lower
    calc
      4 * block * scale = 4 ^ depth * 4 * block := by
        dsimp [scale]
        ac_rfl
      _ ≤ cell := lower
  have quotientUpper : cell / scale < 4 * (block + 1) := by
    apply (Nat.div_lt_iff_lt_mul scalePositive).2
    rw [pow_succ] at upper
    calc
      cell < 4 ^ depth * 4 * (block + 1) := upper
      _ = 4 * (block + 1) * scale := by
        dsimp [scale]
        ac_rfl
  let digit : Fin 4 := ⟨cell / scale - 4 * block, by omega⟩
  let middle := cell / scale
  have middleEq : 4 * block + digit.val = middle := by
    dsimp [digit, middle]
    omega
  refine ⟨digit, middle, ?_, ?_, ?_⟩
  · dsimp [middle, scale]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self cell (4 ^ depth)
  · dsimp [middle, scale]
    simpa [Nat.mul_comm] using
      Nat.lt_mul_div_succ cell (pow_pos (by decide) depth)
  · have digitBits := bits_eq digit
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
      have xCoordinate := descendantCoordinate hcellXLower hcellXUpper
      have yCoordinate := descendantCoordinate hcellYLower hcellYUpper
      have first := twoCornerBridge grid (level := 2 * (depth + 1)) (by omega)
        blockX blockY (highBit xCoordinate.digit) (highBit yCoordinate.digit)
        (lowBit xCoordinate.digit) (lowBit yCoordinate.digit)
      have second := descendantBridge depth (RedCycles.iterateRefine 2 grid)
        xCoordinate.middle yCoordinate.middle cellX cellY
        xCoordinate.lower xCoordinate.upper yCoordinate.lower yCoordinate.upper
      have middleCycle := at_scale (RedCycles.iterateRefine 2 grid)
        (2 * depth) xCoordinate.middle yCoordinate.middle
      have hgrid :
          RedCycles.iterateRefine (2 * depth + 2)
              (RedCycles.iterateRefine 2 grid) =
            RedCycles.iterateRefine (2 * (depth + 1) + 2) grid := by
        rw [PlaneRedBoards.iterateRefine_add]
        congr 1
      rw [hgrid] at second middleCycle
      have hlevel : 2 * (depth + 1) - 2 = 2 * depth := by omega
      have first' : EvenCycleBridge
          (RedCycles.iterateRefine (2 * (depth + 1) + 2) grid)
          (2 ^ (2 * (depth + 1)) * (4 * blockX + 1))
          (2 ^ (2 * (depth + 1)) * (4 * blockX + 3))
          (2 ^ (2 * (depth + 1)) * (4 * blockY + 1))
          (2 ^ (2 * (depth + 1)) * (4 * blockY + 3))
          (2 ^ (2 * depth) * (4 * xCoordinate.middle + 1))
          (2 ^ (2 * depth) * (4 * xCoordinate.middle + 3))
          (2 ^ (2 * depth) * (4 * yCoordinate.middle + 1))
          (2 ^ (2 * depth) * (4 * yCoordinate.middle + 3)) := by
        rw [hlevel, xCoordinate.bits, yCoordinate.bits] at first
        exact first
      exact CycleBridge.trans middleCycle first' second

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
