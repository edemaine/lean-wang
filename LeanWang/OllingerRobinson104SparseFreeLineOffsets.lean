/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageOffsets

/-!
# A reduced unbounded free-line pattern

The exact Robinson recurrence retains both children of every old free line.
For the scaffold reduction, it is enough to retain an unbounded subfamily.  An
even offset retains both children; an odd offset retains only its second child.
There is exactly one even offset at every level, so this boundary-free family
grows by one line per refinement.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOffsets

open RedShadeCycles RedShadeGraphRefinement ShadedFreeLineOffsets
  ShadedFreeLineRecurrence BorderCoverageOffsets

def children (offset : Nat) : List Nat :=
  if offset % 2 = 0 then [4 * offset, 4 * offset + 1]
  else [4 * offset + 3]

def mainChild (offset : Nat) : Nat :=
  if offset % 2 = 0 then 4 * offset else 4 * offset + 3

def extraChild (offset : Nat) : Nat := 4 * offset + 1

def evenCount : List Nat → Nat
  | [] => 0
  | offset :: rest => (if offset % 2 = 0 then 1 else 0) + evenCount rest

def offsets : Nat → List Nat
  | 0 => [2]
  | depth + 1 => (offsets depth).flatMap children

def pivot (depth : Nat) : Nat := 2 * 4 ^ depth

@[simp] theorem offsets_zero : offsets 0 = [2] := rfl

@[simp] theorem offsets_succ (depth : Nat) :
    offsets (depth + 1) =
      (offsets depth).flatMap children := rfl

theorem children_subset_expandOffset (offset : Nat) :
    ∀ child ∈ children offset, child ∈ expandOffset offset := by
  intro child hchild
  by_cases heven : offset % 2 = 0
  · simpa [children, expandOffset, heven] using hchild
  · simp only [children, heven, if_false, List.mem_singleton] at hchild
    subst child
    simp [expandOffset, heven]

theorem mem_children_cases {offset child : Nat}
    (hchild : child ∈ children offset) :
    child = mainChild offset ∨
      offset % 2 = 0 ∧ child = extraChild offset := by
  by_cases heven : offset % 2 = 0
  · simp only [children, mainChild, extraChild, heven, if_true,
      List.mem_cons, List.not_mem_nil, or_false] at hchild ⊢
    rcases hchild with hchild | hchild
    · exact Or.inl hchild
    · exact Or.inr ⟨trivial, hchild⟩
  · simp only [children, mainChild, heven, if_false,
      List.mem_singleton] at hchild ⊢
    exact Or.inl hchild

theorem mainChild_mem_children (offset : Nat) :
    mainChild offset ∈ children offset := by
  by_cases heven : offset % 2 = 0 <;>
    simp [mainChild, children, heven]

theorem extraChild_mem_children {offset : Nat} (heven : offset % 2 = 0) :
    extraChild offset ∈ children offset := by
  simp [extraChild, children, heven]

theorem children_length (offset : Nat) :
    (children offset).length = if offset % 2 = 0 then 2 else 1 := by
  by_cases heven : offset % 2 = 0 <;> simp [children, heven]

theorem evenCount_children (offset : Nat) :
    evenCount (children offset) = if offset % 2 = 0 then 1 else 0 := by
  by_cases heven : offset % 2 = 0 <;>
    simp [children, evenCount, heven, Nat.add_mod, Nat.mul_mod]

theorem evenCount_append (first second : List Nat) :
    evenCount (first ++ second) = evenCount first + evenCount second := by
  induction first with
  | nil => simp [evenCount]
  | cons value values ih =>
      simp [evenCount, ih, Nat.add_assoc]

theorem evenCount_flatMap_children (values : List Nat) :
    evenCount (values.flatMap children) = evenCount values := by
  induction values with
  | nil => rfl
  | cons offset rest ih =>
      simp only [List.flatMap_cons]
      rw [evenCount_append]
      rw [evenCount_children, ih]
      rfl

theorem length_flatMap_children (values : List Nat) :
    (values.flatMap children).length = values.length + evenCount values := by
  induction values with
  | nil => rfl
  | cons offset rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [children_length, ih]
      by_cases heven : offset % 2 = 0 <;>
        simp [evenCount, heven] <;> omega

theorem offsets_evenCount (depth : Nat) : evenCount (offsets depth) = 1 := by
  induction depth with
  | zero => simp [offsets, evenCount]
  | succ depth ih =>
      rw [offsets_succ, evenCount_flatMap_children, ih]

theorem offsets_length (depth : Nat) :
    (offsets depth).length = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [offsets_succ, length_flatMap_children, offsets_evenCount, ih]

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
      rw [offsets_succ, List.mem_flatMap] at hoffset
      rcases hoffset with ⟨oldOffset, hold, hchild⟩
      exact mem_freeOffsets_succ_of_child depth (ih oldOffset hold)
        (children_subset_expandOffset oldOffset offset hchild)

theorem offsets_pairwise (depth : Nat) :
    (offsets depth).Pairwise (· < ·) := by
  induction depth with
  | zero => simp [offsets]
  | succ depth ih =>
      rw [offsets_succ, List.pairwise_flatMap]
      constructor
      · intro offset _
        by_cases heven : offset % 2 = 0 <;>
          simp [children, heven]
      · exact ih.imp fun hlt first hfirst second hsecond =>
          expandOffset_separated hlt first
            (children_subset_expandOffset _ _ hfirst) second
            (children_subset_expandOffset _ _ hsecond)

theorem offsets_nodup (depth : Nat) : (offsets depth).Nodup :=
  (offsets_pairwise depth).imp fun hlt => Nat.ne_of_lt hlt

/-- Every successor offset is one of the retained children of an old offset. -/
theorem mem_offsets_succ_cases (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets (depth + 1)) :
    ∃ oldOffset ∈ offsets depth, offset ∈ children oldOffset := by
  simpa [offsets_succ, List.mem_flatMap] using hoffset

theorem mem_offsets_succ_of_child (depth : Nat)
    {oldOffset child : Nat} (hold : oldOffset ∈ offsets depth)
    (hchild : child ∈ children oldOffset) :
    child ∈ offsets (depth + 1) := by
  rw [offsets_succ, List.mem_flatMap]
  exact ⟨oldOffset, hold, hchild⟩

theorem pivot_even (depth : Nat) : pivot depth % 2 = 0 := by
  simp [pivot]

theorem pivot_mem_offsets (depth : Nat) : pivot depth ∈ offsets depth := by
  induction depth with
  | zero => simp [pivot, offsets]
  | succ depth ih =>
      apply mem_offsets_succ_of_child depth ih
      have heven := pivot_even depth
      have hpivot : pivot (depth + 1) = 4 * pivot depth := by
        simp only [pivot, pow_succ]
        ac_rfl
      rw [hpivot]
      simp [children, heven]

theorem even_offset_eq_pivot (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) (heven : offset % 2 = 0) :
    offset = pivot depth := by
  induction depth generalizing offset with
  | zero => simpa [offsets, pivot] using hoffset
  | succ depth ih =>
      rcases mem_offsets_succ_cases depth hoffset with
        ⟨oldOffset, hold, hchild⟩
      by_cases holdEven : oldOffset % 2 = 0
      · simp only [children, holdEven, if_true, List.mem_cons,
          List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl
        · rw [ih hold holdEven]
          simp only [pivot, pow_succ]
          ac_rfl
        · simp [Nat.add_mod, Nat.mul_mod] at heven
      · simp only [children, holdEven, if_false,
          List.mem_singleton] at hchild
        subst offset
        simp [Nat.add_mod, Nat.mul_mod] at heven

theorem even_pivot_coordinate (depth : Nat) :
    lineCoordinate .even depth (pivot depth) = 4 * 4 ^ depth + 1 := by
  simp [pivot, lineCoordinate_even]
  omega

theorem odd_pivot_coordinate (depth : Nat) :
    lineCoordinate .odd depth (pivot depth) = 8 * 4 ^ depth + 1 := by
  simp [pivot, lineCoordinate_odd]
  omega

theorem even_extra_coordinate (depth : Nat) :
    lineCoordinate .even (depth + 1) (extraChild (pivot depth)) =
      16 * 4 ^ depth + 2 := by
  simp [extraChild, pivot, lineCoordinate_even, pow_succ]
  omega

theorem odd_extra_coordinate (depth : Nat) :
    lineCoordinate .odd (depth + 1) (extraChild (pivot depth)) =
      32 * 4 ^ depth + 3 := by
  simp [extraChild, pivot, lineCoordinate_odd, pow_succ]
  omega

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

theorem exitCoordinate_eq_sparse_add_six {coordinate : Nat}
    (hodd : coordinate % 2 = 1) :
    exitCoordinate coordinate = sparseCoordinate coordinate + 6 := by
  simp [exitCoordinate, localCoordinate, hodd, sparseCoordinate, macroOrigin]

/-- In the even phase a retained child is at the sparse row or its successor. -/
theorem even_child_coordinate
    (depth offset child : Nat) (hchild : child ∈ children offset) :
    lineCoordinate .even (depth + 1) child =
        sparseCoordinate (lineCoordinate .even depth offset) ∨
      lineCoordinate .even (depth + 1) child =
        sparseCoordinate (lineCoordinate .even depth offset) + 1 := by
  by_cases heven : offset % 2 = 0
  · simp only [children, heven, if_true, List.mem_cons,
      List.not_mem_nil, or_false] at hchild
    rcases hchild with rfl | rfl
    · exact Or.inl (lineCoordinate_evenOffset_sparse .even depth offset heven)
    · right
      have hsparse := lineCoordinate_evenOffset_sparse .even depth offset heven
      rw [lineCoordinate_even, lineCoordinate_even, pow_succ] at hsparse ⊢
      omega
  · have hodd : offset % 2 = 1 := by omega
    simp only [children, heven, if_false, List.mem_singleton] at hchild
    subst child
    left
    have hcoordinate : (lineCoordinate .even depth offset) % 2 = 0 := by
      rw [lineCoordinate_even]
      omega
    have hsparse := sparseCoordinate_of_even hcoordinate
    rw [lineCoordinate_even] at hsparse
    rw [lineCoordinate_even (depth + 1) (4 * offset + 3),
      lineCoordinate_even depth offset, pow_succ]
    omega

/-- In the odd phase retained children use the sparse, near, or exit row. -/
theorem odd_child_coordinate
    (depth offset child : Nat) (hchild : child ∈ children offset) :
    lineCoordinate .odd (depth + 1) child =
        sparseCoordinate (lineCoordinate .odd depth offset) ∨
      lineCoordinate .odd (depth + 1) child =
        sparseCoordinate (lineCoordinate .odd depth offset) + 2 ∨
      lineCoordinate .odd (depth + 1) child =
        exitCoordinate (lineCoordinate .odd depth offset) := by
  have hcoordinate : (lineCoordinate .odd depth offset) % 2 = 1 := by
    rw [lineCoordinate_odd]
    omega
  have hsparse := sparseCoordinate_of_odd hcoordinate
  by_cases heven : offset % 2 = 0
  · simp only [children, heven, if_true, List.mem_cons,
      List.not_mem_nil, or_false] at hchild
    rcases hchild with rfl | rfl
    · exact Or.inl (lineCoordinate_evenOffset_sparse .odd depth offset heven)
    · right
      left
      rw [lineCoordinate_odd] at hsparse
      rw [lineCoordinate_odd (depth + 1) (4 * offset + 1),
        lineCoordinate_odd depth offset, pow_succ]
      omega
  · simp only [children, heven, if_false, List.mem_singleton] at hchild
    subst child
    right
    right
    rw [exitCoordinate_eq_sparse_add_six hcoordinate]
    rw [lineCoordinate_odd] at hsparse
    rw [lineCoordinate_odd (depth + 1) (4 * offset + 3),
      lineCoordinate_odd depth offset, pow_succ]
    omega

theorem even_mainChild_coordinate (depth offset : Nat) :
    lineCoordinate .even (depth + 1) (mainChild offset) =
      sparseCoordinate (lineCoordinate .even depth offset) := by
  by_cases heven : offset % 2 = 0
  · simpa [mainChild, heven] using
      lineCoordinate_evenOffset_sparse .even depth offset heven
  · have hodd : offset % 2 = 1 := by omega
    have hcoordinate : (lineCoordinate .even depth offset) % 2 = 0 := by
      rw [lineCoordinate_even]
      omega
    have hsparse := sparseCoordinate_of_even hcoordinate
    rw [lineCoordinate_even] at hsparse
    simp only [mainChild, heven, if_false]
    rw [lineCoordinate_even (depth + 1) (4 * offset + 3),
      lineCoordinate_even depth offset, pow_succ]
    omega

theorem odd_mainChild_coordinate (depth offset : Nat) :
    lineCoordinate .odd (depth + 1) (mainChild offset) =
        sparseCoordinate (lineCoordinate .odd depth offset) ∨
      lineCoordinate .odd (depth + 1) (mainChild offset) =
        exitCoordinate (lineCoordinate .odd depth offset) := by
  by_cases heven : offset % 2 = 0
  · left
    simpa [mainChild, heven] using
      lineCoordinate_evenOffset_sparse .odd depth offset heven
  · right
    have hcoordinate : (lineCoordinate .odd depth offset) % 2 = 1 := by
      rw [lineCoordinate_odd]
      omega
    have hsparse := sparseCoordinate_of_odd hcoordinate
    rw [exitCoordinate_eq_sparse_add_six hcoordinate]
    rw [lineCoordinate_odd] at hsparse
    simp only [mainChild, heven, if_false]
    rw [lineCoordinate_odd (depth + 1) (4 * offset + 3),
      lineCoordinate_odd depth offset, pow_succ]
    omega

end SparseFreeLineOffsets
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
