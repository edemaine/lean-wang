/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleCrossingPaths

/-!
# Odd paths to translated half-scale corner boards

Every half-scale corner board crosses its parent in one of four orientations.
The corresponding crossing tile gives an explicit odd graph bridge between
the parent cycle and that child cycle.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace TranslatedRedShadeCrossingPaths

open OrientedRedBoardTranslations OrientedRedCycles RedCycles
  RedShadeCycles TranslatedRedShadeCrossings RedShadeCycleCrossingPaths

set_option maxRecDepth 20000

/-- Every translated corner child has an odd crossing path from its parent. -/
theorem cornerBridge
    (grid : Nat → Nat → Index) {level : Nat} (hlevel : 1 ≤ level)
    (blockX blockY : Nat) (cornerX cornerY : Fin 2) :
    OddCycleBridge (iterateRefine (level + 2) grid)
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3))
      (2 ^ (level - 1) * (4 * (2 * blockX + cornerX.val) + 1))
      (2 ^ (level - 1) * (4 * (2 * blockX + cornerX.val) + 3))
      (2 ^ (level - 1) * (4 * (2 * blockY + cornerY.val) + 1))
      (2 ^ (level - 1) * (4 * (2 * blockY + cornerY.val) + 3)) := by
  let large := at_scale grid level blockX blockY
  let small := cornerSmallCycle grid hlevel blockX blockY cornerX cornerY
  have hpow : 2 ^ level = 2 * 2 ^ (level - 1) := by
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlevel
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.add_comm, pow_succ]
    omega
  have hpositive : 0 < 2 ^ (level - 1) := pow_pos (by decide) _
  fin_cases cornerX <;> fin_cases cornerY
  · apply north_crosses_west large small <;> dsimp at * <;>
      rw [hpow] <;> nlinarith
  · apply south_crosses_west large small <;> dsimp at * <;>
      rw [hpow] <;> nlinarith
  · apply north_crosses_east large small <;> dsimp at * <;>
      rw [hpow] <;> nlinarith
  · apply south_crosses_east large small <;> dsimp at * <;>
      rw [hpow] <;> nlinarith

end TranslatedRedShadeCrossingPaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
