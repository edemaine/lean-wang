/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedWindowClosureCheck

/-! Structural closure of recursive exceptional created-segment windows. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCreatedWindowClosure

open RedCycles RedShadeGraphRefinement RefinementTranslation
  ShadedFreeLineRecurrence SparseFreeLineEvenExtraCreatedWindowAudit

set_option maxRecDepth 20000

def oldGrid (depth : Nat) (parent : Index) : Nat → Nat → Index :=
  localGrid .even (depth + 1) parent

def firstBlock (depth : Nat) : Nat := 4 ^ (depth + 1)

def blockCount (depth : Nat) : Nat := 2 * firstBlock depth

def centerBlock (depth : Nat) : Nat := 2 * firstBlock depth + 1

def verticalWindowAt (depth : Nat) (parent : Index) (blockX : Nat) : Window :=
  (List.range 3).flatMap fun y =>
    (List.range 3).map fun x =>
      oldGrid depth parent (blockX - 1 + x) (centerBlock depth - 1 + y)

def horizontalWindowAt (depth : Nat) (parent : Index) (blockY : Nat) : Window :=
  (List.range 3).flatMap fun y =>
    (List.range 3).map fun x =>
      oldGrid depth parent (centerBlock depth - 1 + x) (blockY - 1 + y)

theorem oldGrid_succ (depth : Nat) (parent : Index) :
    oldGrid (depth + 1) parent = iterateRefine 2 (oldGrid depth parent) := by
  simpa [oldGrid, Nat.add_assoc] using localGrid_succ .even (depth + 1) parent

theorem firstBlock_zero : firstBlock 0 = 4 := by rfl

theorem firstBlock_succ (depth : Nat) :
    firstBlock (depth + 1) = 4 * firstBlock depth := by
  simp [firstBlock, pow_succ, Nat.mul_comm]

theorem blockCount_eq (depth : Nat) : blockCount depth = 2 * 4 ^ (depth + 1) := rfl

theorem centerBlock_zero : centerBlock 0 = 9 := by rfl

theorem centerOrigin_succ (depth : Nat) :
    centerBlock (depth + 1) - 1 = 4 * (centerBlock depth - 1) := by
  rw [centerBlock, centerBlock, firstBlock_succ]
  omega

theorem verticalWindowAt_zero (parent : Index) (blockX : Nat) :
    verticalWindowAt 0 parent blockX = windowAt parent blockX 9 := by
  rfl

theorem horizontalWindowAt_zero (parent : Index) (blockY : Nat) :
    horizontalWindowAt 0 parent blockY = windowAt parent 9 blockY := by
  rfl

theorem verticalWindowAt_eq (depth : Nat) (parent : Index) (blockX : Nat) :
    verticalWindowAt depth parent blockX =
      [oldGrid depth parent (blockX - 1) (centerBlock depth - 1),
       oldGrid depth parent (blockX - 1 + 1) (centerBlock depth - 1),
       oldGrid depth parent (blockX - 1 + 2) (centerBlock depth - 1),
       oldGrid depth parent (blockX - 1) (centerBlock depth - 1 + 1),
       oldGrid depth parent (blockX - 1 + 1) (centerBlock depth - 1 + 1),
       oldGrid depth parent (blockX - 1 + 2) (centerBlock depth - 1 + 1),
       oldGrid depth parent (blockX - 1) (centerBlock depth - 1 + 2),
       oldGrid depth parent (blockX - 1 + 1) (centerBlock depth - 1 + 2),
       oldGrid depth parent (blockX - 1 + 2) (centerBlock depth - 1 + 2)] := by
  rfl

theorem horizontalWindowAt_eq (depth : Nat) (parent : Index) (blockY : Nat) :
    horizontalWindowAt depth parent blockY =
      [oldGrid depth parent (centerBlock depth - 1) (blockY - 1),
       oldGrid depth parent (centerBlock depth - 1 + 1) (blockY - 1),
       oldGrid depth parent (centerBlock depth - 1 + 2) (blockY - 1),
       oldGrid depth parent (centerBlock depth - 1) (blockY - 1 + 1),
       oldGrid depth parent (centerBlock depth - 1 + 1) (blockY - 1 + 1),
       oldGrid depth parent (centerBlock depth - 1 + 2) (blockY - 1 + 1),
       oldGrid depth parent (centerBlock depth - 1) (blockY - 1 + 2),
       oldGrid depth parent (centerBlock depth - 1 + 1) (blockY - 1 + 2),
       oldGrid depth parent (centerBlock depth - 1 + 2) (blockY - 1 + 2)] := by
  rfl

theorem windowGrid_verticalWindowAt
    (depth : Nat) (parent : Index) (blockX x y : Nat)
    (hx : x < 3) (hy : y < 3) :
    windowGrid (verticalWindowAt depth parent blockX) x y =
      oldGrid depth parent (blockX - 1 + x) (centerBlock depth - 1 + y) := by
  rw [verticalWindowAt_eq]
  interval_cases x <;> interval_cases y <;> simp [windowGrid]

theorem windowGrid_horizontalWindowAt
    (depth : Nat) (parent : Index) (blockY x y : Nat)
    (hx : x < 3) (hy : y < 3) :
    windowGrid (horizontalWindowAt depth parent blockY) x y =
      oldGrid depth parent (centerBlock depth - 1 + x) (blockY - 1 + y) := by
  rw [horizontalWindowAt_eq]
  interval_cases x <;> interval_cases y <;> simp [windowGrid]

theorem iterateRefine_two_congr_at
    {first second : Nat → Nat → Index} {x y : Nat}
    (hcell : first (x / 2 / 2) (y / 2 / 2) =
      second (x / 2 / 2) (y / 2 / 2)) :
    iterateRefine 2 first x y = iterateRefine 2 second x y := by
  simp only [iterateRefine, refineIndexGrid]
  rw [hcell]

set_option maxHeartbeats 1000000 in
-- Normalizing the translated two-refinement window requires extra elaboration.
/-- Every successor row window is a residue slice of a predecessor window. -/
theorem verticalWindowAt_succ
    (depth : Nat) (parent : Index) (blockX : Nat) :
    verticalWindowAt (depth + 1) parent blockX =
      refineWindow
        (verticalWindowAt depth parent ((blockX - 1) / 4 + 1))
        ((blockX - 1) % 4) 0 := by
  rw [verticalWindowAt, refineWindow, oldGrid_succ, centerOrigin_succ]
  have hmodlt := Nat.mod_lt (blockX - 1) (by decide : 0 < 4)
  have horigin : blockX - 1 =
      4 * ((blockX - 1) / 4) + (blockX - 1) % 4 := by
    have := Nat.mod_add_div (blockX - 1) 4
    omega
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  rw [horigin]
  have hdiv :
      (4 * ((blockX - 1) / 4) + (blockX - 1) % 4) / 4 =
        (blockX - 1) / 4 := by omega
  have hmod :
      (4 * ((blockX - 1) / 4) + (blockX - 1) % 4) % 4 =
        (blockX - 1) % 4 := by omega
  rw [hdiv, hmod]
  have hshift := iterateRefine_shift 2 (oldGrid depth parent)
    ((blockX - 1) / 4) (centerBlock depth - 1)
    ((blockX - 1) % 4 + x) y
  norm_num at hshift
  rw [← Nat.add_assoc] at hshift
  rw [← hshift]
  simp only [Nat.zero_add]
  apply iterateRefine_two_congr_at
  rw [windowGrid_verticalWindowAt]
  · simp [shiftGrid]
  · omega
  · omega

set_option maxHeartbeats 1000000 in
-- Normalizing the translated two-refinement window requires extra elaboration.
/-- Every successor column window is a residue slice of a predecessor window. -/
theorem horizontalWindowAt_succ
    (depth : Nat) (parent : Index) (blockY : Nat) :
    horizontalWindowAt (depth + 1) parent blockY =
      refineWindow
        (horizontalWindowAt depth parent ((blockY - 1) / 4 + 1))
        0 ((blockY - 1) % 4) := by
  rw [horizontalWindowAt, refineWindow, oldGrid_succ, centerOrigin_succ]
  have hmodlt := Nat.mod_lt (blockY - 1) (by decide : 0 < 4)
  have horigin : blockY - 1 =
      4 * ((blockY - 1) / 4) + (blockY - 1) % 4 := by
    have := Nat.mod_add_div (blockY - 1) 4
    omega
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  rw [horigin]
  have hdiv :
      (4 * ((blockY - 1) / 4) + (blockY - 1) % 4) / 4 =
        (blockY - 1) / 4 := by omega
  have hmod :
      (4 * ((blockY - 1) / 4) + (blockY - 1) % 4) % 4 =
        (blockY - 1) % 4 := by omega
  rw [hdiv, hmod]
  have hshift := iterateRefine_shift 2 (oldGrid depth parent)
    (centerBlock depth - 1) ((blockY - 1) / 4)
    x ((blockY - 1) % 4 + y)
  norm_num at hshift
  rw [← Nat.add_assoc] at hshift
  rw [← hshift]
  simp only [Nat.zero_add]
  apply iterateRefine_two_congr_at
  rw [windowGrid_horizontalWindowAt]
  · simp [shiftGrid]
  · omega
  · omega

end SparseFreeLineEvenExtraCreatedWindowClosure
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
