/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentAuditDefs

/-!
# Classify adjacent refined cells for the created-seam audit

The last substitution address bit puts neighboring cells in one of two cases:
siblings under one parent, or opposite child classes across a parent boundary.
After canonicalizing the graph-invisible component, these are precisely the
finite pair states checked by the adjacent audit.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedAdjacentClassification

open RedCycles SparseFreeLineLocalStates
  PairCoverSeamCreatedAdjacentAudit

theorem canonicalPair_mem_crossPairs
    {first second : List Index} {a b : Index}
    (ha : a ∈ first) (hb : b ∈ second) :
    canonicalPair (a, b) ∈ crossPairs first second := by
  simp only [crossPairs, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

theorem vertical_siblings_mem (parent : Index) (horizontal : Fin 2) :
    canonicalPair
        (childBlock parent horizontal 0, childBlock parent horizontal 1) ∈
      verticalPairs := by
  simp only [verticalPairs, List.mem_eraseDups, List.mem_append]
  left
  simp only [verticalSiblingPairs, List.mem_eraseDups, List.mem_flatMap,
    List.mem_map]
  exact ⟨parent, by simp, horizontal, by simp, rfl⟩

theorem horizontal_siblings_mem (parent : Index) (vertical : Fin 2) :
    canonicalPair
        (childBlock parent 0 vertical, childBlock parent 1 vertical) ∈
      horizontalPairs := by
  simp only [horizontalPairs, List.mem_eraseDups, List.mem_append]
  left
  simp only [horizontalSiblingPairs, List.mem_eraseDups, List.mem_flatMap,
    List.mem_map]
  exact ⟨parent, by simp, vertical, by simp, rfl⟩

/-- Every vertically adjacent pair after a positive number of refinements is
one of the finitely audited vertical states. -/
theorem verticalPair_mem (depth : Nat) (grid : Nat → Nat → Index)
    (x y : Nat) :
    canonicalPair
        (iterateRefine (depth + 1) grid x y,
          iterateRefine (depth + 1) grid x (y + 1)) ∈
      verticalPairs := by
  have hmod : y % 2 = 0 ∨ y % 2 = 1 := by
    have := Nat.mod_lt y (by decide : 0 < 2)
    omega
  rcases hmod with heven | hodd
  · have hy : parityOffset y = 0 := by
      apply Fin.ext
      simpa [parityOffset] using heven
    have hysucc : parityOffset (y + 1) = 1 := by
      apply Fin.ext
      change (y + 1) % 2 = 1
      omega
    have hdiv : (y + 1) / 2 = y / 2 := by omega
    change canonicalPair
        (childBlock (iterateRefine depth grid (x / 2) (y / 2))
            (parityOffset x) (parityOffset y),
          childBlock (iterateRefine depth grid (x / 2) ((y + 1) / 2))
            (parityOffset x) (parityOffset (y + 1))) ∈ verticalPairs
    rw [hy, hysucc, hdiv]
    exact vertical_siblings_mem _ _
  · have hy : parityOffset y = 1 := by
      apply Fin.ext
      simpa [parityOffset] using hodd
    have hysucc : parityOffset (y + 1) = 0 := by
      apply Fin.ext
      change (y + 1) % 2 = 0
      omega
    apply List.mem_eraseDups.mpr
    apply List.mem_append_right
    apply canonicalPair_mem_crossPairs
    · rw [← hy]
      exact iterateRefine_succ_mem_rowChildren depth grid x y
    · rw [← hysucc]
      exact iterateRefine_succ_mem_rowChildren depth grid x (y + 1)

/-- Horizontal dual of `verticalPair_mem`. -/
theorem horizontalPair_mem (depth : Nat) (grid : Nat → Nat → Index)
    (x y : Nat) :
    canonicalPair
        (iterateRefine (depth + 1) grid x y,
          iterateRefine (depth + 1) grid (x + 1) y) ∈
      horizontalPairs := by
  have hmod : x % 2 = 0 ∨ x % 2 = 1 := by
    have := Nat.mod_lt x (by decide : 0 < 2)
    omega
  rcases hmod with heven | hodd
  · have hx : parityOffset x = 0 := by
      apply Fin.ext
      simpa [parityOffset] using heven
    have hxsucc : parityOffset (x + 1) = 1 := by
      apply Fin.ext
      change (x + 1) % 2 = 1
      omega
    have hdiv : (x + 1) / 2 = x / 2 := by omega
    change canonicalPair
        (childBlock (iterateRefine depth grid (x / 2) (y / 2))
            (parityOffset x) (parityOffset y),
          childBlock (iterateRefine depth grid ((x + 1) / 2) (y / 2))
            (parityOffset (x + 1)) (parityOffset y)) ∈ horizontalPairs
    rw [hx, hxsucc, hdiv]
    exact horizontal_siblings_mem _ _
  · have hx : parityOffset x = 1 := by
      apply Fin.ext
      simpa [parityOffset] using hodd
    have hxsucc : parityOffset (x + 1) = 0 := by
      apply Fin.ext
      change (x + 1) % 2 = 0
      omega
    apply List.mem_eraseDups.mpr
    apply List.mem_append_right
    apply canonicalPair_mem_crossPairs
    · rw [← hx]
      exact iterateRefine_succ_mem_columnChildren depth grid x y
    · rw [← hxsucc]
      exact iterateRefine_succ_mem_columnChildren depth grid (x + 1) y

end PairCoverSeamCreatedAdjacentClassification
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
