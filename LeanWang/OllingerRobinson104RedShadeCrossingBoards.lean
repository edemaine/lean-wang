/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycles
import LeanWang.OllingerRobinson104OrientedPlaneRedBoards

/-!
Two comparable canonical boards crossing in the same refined grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCrossingBoards

open RedCycles PlaneRedBoards OrientedRedCycles OrientedPlaneRedBoards

set_option maxRecDepth 20000

/-- The usual canonical board at refinement level `level`. -/
theorem largeCycle (grid : Nat → Nat → Index) (level : Nat) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) := by
  have cycle := grid_depthTwo_has_orientedCycleOn grid |>.iterateRefine level
  simp only [doubleN_eq, Nat.mul_one] at cycle
  have hgrid : iterateRefine level (iterateRefine 2 grid) =
      iterateRefine (level + 2) grid :=
    iterateRefine_add level 2 grid
  rw [hgrid] at cycle
  simpa [mul_comm] using cycle

/-- A board seeded one refinement later, of half the side length. -/
theorem smallCycle (grid : Nat → Nat → Index) {level : Nat}
    (hlevel : 1 ≤ level) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) := by
  have cycle := grid_depthTwo_has_orientedCycleOn (iterateRefine 1 grid)
    |>.iterateRefine (level - 1)
  simp only [doubleN_eq, Nat.mul_one] at cycle
  have hgrid :
      iterateRefine (level - 1) (iterateRefine 2 (iterateRefine 1 grid)) =
        iterateRefine (level + 2) grid := by
    rw [iterateRefine_add (level - 1) 2,
      iterateRefine_add (level - 1 + 2) 1]
    congr 1
    omega
  rw [hgrid] at cycle
  simpa [mul_comm] using cycle

/-- The half-scale board crosses the southwest sides of the large board. -/
theorem crossing_coordinates {level : Nat} (hlevel : 1 ≤ level) :
    2 ^ (level - 1) < 2 ^ level ∧
      2 ^ level < 3 * 2 ^ (level - 1) ∧
      3 * 2 ^ (level - 1) < 3 * 2 ^ level := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  simp only [Nat.add_sub_cancel_left]
  have hsucc : 2 ^ (1 + extra) = 2 * 2 ^ extra := by
    calc
      2 ^ (1 + extra) = 2 ^ (extra + 1) := by rw [Nat.add_comm]
      _ = 2 ^ extra * 2 := pow_succ 2 extra
      _ = 2 * 2 ^ extra := by ac_rfl
  rw [hsucc]
  have hpow : 0 < 2 ^ extra := pow_pos (by decide) _
  omega

end RedShadeCrossingBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
