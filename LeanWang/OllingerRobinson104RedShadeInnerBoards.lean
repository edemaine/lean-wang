/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104TranslatedRedShadeCrossings

/-!
The four same-shade two-level descendants lying strictly inside a translated
Robinson board.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeInnerBoards

open RedCycles RedShadeCycles RedShadePaths TranslatedRedShadeCrossings

set_option maxRecDepth 20000

def oppositeBit (bit : Fin 2) : Fin 2 :=
  ⟨1 - bit.val, by omega⟩

def innerBlock (block : Nat) (side : Fin 2) : Nat :=
  4 * block + 1 + side.val

@[simp] theorem cornerBits_eq_innerBlock (block : Nat) (side : Fin 2) :
  2 * (2 * block + side.val) + (oppositeBit side).val =
      innerBlock block side := by
  fin_cases side <;> simp [oppositeBit, innerBlock] <;> omega

theorem innerBlock_bounds (block : Nat) (side : Fin 2) :
    4 * block < innerBlock block side ∧
      innerBlock block side < 4 * block + 3 := by
  fin_cases side <;> simp [innerBlock]

/-- Every one of the four inner quarter-scale boards has its parent's shade. -/
theorem exists_same_innerShade_of_parent
    (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    {level : Nat} (hlevel : 2 ≤ level) (blockX blockY : Nat)
    (innerX innerY : Fin 2) {parentShade : RedShades.Shade}
    (parentShaded : CycleShade stateGrid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) parentShade)
    (valid : ValidShadeGrid (iterateRefine (level + 2) grid) stateGrid) :
    CycleShade stateGrid
      (2 ^ (level - 2) * (4 * innerBlock blockX innerX + 1))
      (2 ^ (level - 2) * (4 * innerBlock blockX innerX + 3))
      (2 ^ (level - 2) * (4 * innerBlock blockY innerY + 1))
      (2 ^ (level - 2) * (4 * innerBlock blockY innerY + 3))
      parentShade := by
  have descendant := exists_same_grandchildShade_of_parent grid hlevel
    blockX blockY innerX innerY (oppositeBit innerX) (oppositeBit innerY)
    parentShaded valid
  simpa only [cornerBits_eq_innerBlock] using descendant

theorem innerBoard_strictly_inside
    {level : Nat} (hlevel : 2 ≤ level) (block : Nat) (inner : Fin 2) :
    2 ^ level * (4 * block + 1) <
        2 ^ (level - 2) * (4 * innerBlock block inner + 1) ∧
      2 ^ (level - 2) * (4 * innerBlock block inner + 3) <
        2 ^ level * (4 * block + 3) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  simp only [Nat.add_sub_cancel_left]
  have hpow : 2 ^ (2 + extra) = 4 * 2 ^ extra := by
    rw [show 2 + extra = extra + 2 by omega, pow_add]
    norm_num
    omega
  rw [hpow]
  have hpositive : 0 < 2 ^ extra := pow_pos (by decide) _
  fin_cases inner <;> simp [innerBlock] <;> constructor <;> nlinarith

/-- The two inner board intervals partition the parent interior in order. -/
theorem innerBoards_order
    {level : Nat} (hlevel : 2 ≤ level) (block : Nat) :
    2 ^ level * (4 * block + 1) <
        2 ^ (level - 2) * (4 * innerBlock block (0 : Fin 2) + 1) ∧
      2 ^ (level - 2) * (4 * innerBlock block (0 : Fin 2) + 1) <
        2 ^ (level - 2) * (4 * innerBlock block (0 : Fin 2) + 3) ∧
      2 ^ (level - 2) * (4 * innerBlock block (0 : Fin 2) + 3) <
        2 ^ (level - 2) * (4 * innerBlock block (1 : Fin 2) + 1) ∧
      2 ^ (level - 2) * (4 * innerBlock block (1 : Fin 2) + 1) <
        2 ^ (level - 2) * (4 * innerBlock block (1 : Fin 2) + 3) ∧
      2 ^ (level - 2) * (4 * innerBlock block (1 : Fin 2) + 3) <
        2 ^ level * (4 * block + 3) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  simp only [Nat.add_sub_cancel_left]
  have hpow : 2 ^ (2 + extra) = 4 * 2 ^ extra := by
    rw [show 2 + extra = extra + 2 by omega, pow_add]
    norm_num
    omega
  rw [hpow]
  have hpositive : 0 < 2 ^ extra := pow_pos (by decide) _
  simp [innerBlock]
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · nlinarith

end RedShadeInnerBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
