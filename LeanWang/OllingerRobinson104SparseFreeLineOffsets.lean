/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageOffsets

/-!
# A reduced unbounded free-line pattern

The exact Robinson recurrence retains every child of every old free line.  For
the scaffold reduction, it is enough to retain an unbounded subfamily.  We keep
only even offsets: each old offset refines to its first child `4 * offset`, and
each level adds the new even right-side line.  Consequently the family grows by
one line per level, while every persistent child's physical coordinate is
exactly the sparse copy of its parent coordinate in both phases.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOffsets

open RedShadeCycles RedShadeGraphRefinement ShadedFreeLineOffsets
  ShadedFreeLineRecurrence BorderCoverageOffsets

def offsets : Nat → List Nat
  | 0 => [2]
  | depth + 1 =>
      (offsets depth).map (fun offset => 4 * offset) ++
        [4 ^ (depth + 2) - 2]

@[simp] theorem offsets_zero : offsets 0 = [2] := rfl

@[simp] theorem offsets_succ (depth : Nat) :
    offsets (depth + 1) =
      (offsets depth).map (fun offset => 4 * offset) ++
        [4 ^ (depth + 2) - 2] := rfl

theorem rightOffset_even (depth : Nat) :
    (4 ^ (depth + 2) - 2) % 2 = 0 := by
  rw [show 4 ^ (depth + 2) = 4 * 4 ^ (depth + 1) by
    simp [pow_succ, mul_comm]]
  have hpositive : 0 < 4 ^ (depth + 1) := pow_pos (by decide) _
  have heq : 4 * 4 ^ (depth + 1) - 2 =
      2 * (2 * 4 ^ (depth + 1) - 1) := by omega
  rw [heq]
  simp

theorem offsets_even (depth : Nat) :
    ∀ offset ∈ offsets depth, offset % 2 = 0 := by
  induction depth with
  | zero => simp [offsets]
  | succ depth ih =>
      intro offset hoffset
      rw [offsets_succ, List.mem_append] at hoffset
      rcases hoffset with hoffset | hoffset
      · rcases List.mem_map.1 hoffset with ⟨oldOffset, hold, rfl⟩
        omega
      · simp only [List.mem_singleton] at hoffset
        subst offset
        exact rightOffset_even depth

theorem rightOffset_mem_freeOffsets (depth : Nat) :
    4 ^ (depth + 2) - 2 ∈ freeOffsets (depth + 1) := by
  rw [freeOffsets_succ_decompose]
  simp

theorem offsets_mem_freeOffsets (depth : Nat) :
    ∀ offset ∈ offsets depth, offset ∈ freeOffsets depth := by
  induction depth with
  | zero =>
      intro offset hoffset
      simp only [offsets_zero, List.mem_singleton] at hoffset
      rcases hoffset with rfl
      norm_num [freeOffsets, extendedOffsets]
  | succ depth ih =>
      intro offset hoffset
      rw [offsets_succ, List.mem_append] at hoffset
      rcases hoffset with hoffset | hoffset
      · rcases List.mem_map.1 hoffset with ⟨oldOffset, hold, rfl⟩
        apply mem_freeOffsets_succ_of_child depth (ih oldOffset hold)
        have heven := offsets_even depth oldOffset hold
        simp [expandOffset, heven]
      · simp only [List.mem_singleton] at hoffset
        subst offset
        exact rightOffset_mem_freeOffsets depth

theorem offsets_length (depth : Nat) :
    (offsets depth).length = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [offsets_succ, ih]

theorem offsets_pairwise (depth : Nat) :
    (offsets depth).Pairwise (· < ·) := by
  induction depth with
  | zero => simp [offsets]
  | succ depth ih =>
      rw [offsets_succ, List.pairwise_append]
      refine ⟨?_, by simp, ?_⟩
      · rw [List.pairwise_map]
        exact ih.imp fun hlt => by omega
      · intro mapped hmapped right hright
        simp only [List.mem_map] at hmapped
        rcases hmapped with ⟨oldOffset, hold, rfl⟩
        simp only [List.mem_singleton] at hright
        subst right
        have hbound := mem_freeOffsets_lt_last depth
          (offsets_mem_freeOffsets depth oldOffset hold)
        rw [show 4 ^ (depth + 2) = 4 * 4 ^ (depth + 1) by
          simp [pow_succ, mul_comm]]
        omega

theorem offsets_nodup (depth : Nat) : (offsets depth).Nodup :=
  (offsets_pairwise depth).imp fun hlt => Nat.ne_of_lt hlt

theorem lineCoordinate_evenOffset_sparse
    (phase : Phase) (depth offset : Nat) (heven : offset % 2 = 0) :
    lineCoordinate phase (depth + 1) (4 * offset) =
      sparseCoordinate (lineCoordinate phase depth offset) := by
  cases phase
  · have hcoordinate : (lineCoordinate .even depth offset) % 2 = 1 := by
      rw [lineCoordinate_even]
      omega
    have hsparse := sparseCoordinate_of_odd hcoordinate
    rw [lineCoordinate_even] at hsparse
    rw [lineCoordinate_even (depth + 1) (4 * offset),
      lineCoordinate_even depth offset, pow_succ]
    omega
  · have hcoordinate : (lineCoordinate .odd depth offset) % 2 = 1 := by
      rw [lineCoordinate_odd]
      omega
    have hsparse := sparseCoordinate_of_odd hcoordinate
    rw [lineCoordinate_odd] at hsparse
    rw [lineCoordinate_odd (depth + 1) (4 * offset),
      lineCoordinate_odd depth offset, pow_succ]
    omega

theorem lineCoordinate_mem_sparse
    (phase : Phase) (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) :
    lineCoordinate phase (depth + 1) (4 * offset) =
      sparseCoordinate (lineCoordinate phase depth offset) :=
  lineCoordinate_evenOffset_sparse phase depth offset
    (offsets_even depth offset hoffset)

end SparseFreeLineOffsets
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
