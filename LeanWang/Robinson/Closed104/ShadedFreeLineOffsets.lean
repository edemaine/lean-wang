/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeGrid
import Mathlib.Tactic.IntervalCases

/-!
The arithmetic free-line pattern visible in Figure 18.

It is convenient to retain the two enclosing border coordinates during the
recurrence.  Every coarse offset `x` then produces two ordered fine offsets:
`4x, 4x+1` when `x` is even and `4x+2, 4x+3` when `x` is odd.  Removing the
first and last offsets leaves the actual interior free-line candidates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineOffsets

open RedShadeCycles RedShadePaths ShadedFreeGrid ShadedPlaneSignalGrid

def expandOffset (offset : Nat) : List Nat :=
  if offset % 2 = 0 then [4 * offset, 4 * offset + 1]
  else [4 * offset + 2, 4 * offset + 3]

def extendedOffsets : Nat → List Nat
  | 0 => [0, 1, 2, 3]
  | depth + 1 => (extendedOffsets depth).flatMap expandOffset

def freeOffsets (depth : Nat) : List Nat :=
  ((extendedOffsets depth).drop 1).dropLast

theorem expandOffset_length (offset : Nat) :
    (expandOffset offset).length = 2 := by
  by_cases heven : offset % 2 = 0 <;> simp [expandOffset, heven]

theorem flatMap_expandOffset_length (offsets : List Nat) :
    (offsets.flatMap expandOffset).length = 2 * offsets.length := by
  induction offsets with
  | nil => simp
  | cons offset offsets ih =>
      simp [expandOffset_length, ih]
      omega

theorem extendedOffsets_length (depth : Nat) :
    (extendedOffsets depth).length = 2 ^ (depth + 2) := by
  induction depth with
  | zero => norm_num [extendedOffsets]
  | succ depth ih =>
      rw [extendedOffsets, flatMap_expandOffset_length, ih]
      calc
        2 * 2 ^ (depth + 2) = 2 ^ (depth + 2) * 2 := by omega
        _ = 2 ^ ((depth + 2) + 1) := (pow_succ _ _).symm
        _ = 2 ^ (depth + 1 + 2) := by congr 1

theorem freeOffsets_length (depth : Nat) :
    (freeOffsets depth).length = 2 ^ (depth + 2) - 2 := by
  simp only [freeOffsets, List.length_dropLast, List.length_drop,
    extendedOffsets_length]
  have hpositive : 0 < 2 ^ depth := pow_pos (by decide) _
  rw [show depth + 2 = depth + 2 by rfl, pow_add]
  norm_num
  omega

theorem freeOffsets_length_succ (depth : Nat) :
    (freeOffsets (depth + 1)).length =
      2 * (freeOffsets depth).length + 2 := by
  rw [freeOffsets_length, freeOffsets_length]
  have hpositive : 0 < 2 ^ depth := pow_pos (by decide) _
  rw [show depth + 1 + 2 = depth + 3 by omega,
    show depth + 2 = depth + 2 by rfl, pow_add, pow_add]
  norm_num
  omega

theorem expandOffset_pairwise (offset : Nat) :
    (expandOffset offset).Pairwise (· < ·) := by
  by_cases heven : offset % 2 = 0 <;> simp [expandOffset, heven]

set_option linter.flexible false in
theorem expandOffset_separated {first second : Nat} (hlt : first < second) :
    ∀ firstChild ∈ expandOffset first,
      ∀ secondChild ∈ expandOffset second, firstChild < secondChild := by
  intro firstChild hfirst secondChild hsecond
  by_cases hfirstEven : first % 2 = 0 <;>
    by_cases hsecondEven : second % 2 = 0 <;>
      simp [expandOffset, hfirstEven, hsecondEven] at hfirst hsecond <;>
      rcases hfirst with rfl | rfl <;> rcases hsecond with rfl | rfl <;> omega

theorem flatMap_expandOffset_pairwise {offsets : List Nat}
    (ordered : offsets.Pairwise (· < ·)) :
    (offsets.flatMap expandOffset).Pairwise (· < ·) := by
  rw [List.pairwise_flatMap]
  constructor
  · intro offset _
    exact expandOffset_pairwise offset
  · exact ordered.imp fun hlt => expandOffset_separated hlt

theorem extendedOffsets_pairwise (depth : Nat) :
    (extendedOffsets depth).Pairwise (· < ·) := by
  induction depth with
  | zero => norm_num [extendedOffsets]
  | succ depth ih =>
      exact flatMap_expandOffset_pairwise ih

theorem freeOffsets_pairwise (depth : Nat) :
    (freeOffsets depth).Pairwise (· < ·) := by
  exact ((extendedOffsets_pairwise depth).drop).sublist
    (List.dropLast_sublist _)

theorem freeOffsets_nodup (depth : Nat) :
    (freeOffsets depth).Nodup :=
  (freeOffsets_pairwise depth).imp fun hlt => Nat.ne_of_lt hlt

set_option linter.style.nativeDecide false in
theorem freeOffsets_one :
    freeOffsets 1 = [1, 6, 7, 8, 9, 14] := by
  native_decide

set_option linter.style.nativeDecide false in
theorem freeOffsets_two :
    freeOffsets 2 = [1, 6, 7, 24, 25, 30, 31,
      32, 33, 38, 39, 56, 57, 62] := by
  native_decide

theorem extendedOffsets_starts_zero (depth : Nat) :
    ∃ rest : List Nat, extendedOffsets depth = 0 :: rest := by
  induction depth with
  | zero => exact ⟨[1, 2, 3], rfl⟩
  | succ depth ih =>
      rcases ih with ⟨rest, hrest⟩
      rw [extendedOffsets, hrest]
      simp [expandOffset]

set_option linter.flexible false in
theorem extendedOffsets_decompose (depth : Nat) :
    extendedOffsets depth =
      0 :: (freeOffsets depth ++ [4 ^ (depth + 1) - 1]) := by
  induction depth with
  | zero => decide
  | succ depth ih =>
      change (extendedOffsets depth).flatMap expandOffset =
        0 :: freeOffsets (depth + 1) ++ [4 ^ (depth + 2) - 1]
      rw [freeOffsets]
      change (extendedOffsets depth).flatMap expandOffset =
        0 :: (((extendedOffsets depth).flatMap expandOffset).drop 1).dropLast ++
          [4 ^ (depth + 2) - 1]
      rw [ih]
      have hpow : 4 ^ (depth + 1) = 4 * 4 ^ depth := by
        simp [pow_succ, mul_comm]
      have hodd : (4 ^ (depth + 1) - 1) % 2 ≠ 0 := by
        rw [hpow]
        have hpositive : 0 < 4 ^ depth := pow_pos (by decide) _
        have heq : 4 * 4 ^ depth - 1 = 2 * (2 * 4 ^ depth - 1) + 1 := by
          omega
        rw [heq]
        simp
      simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil]
      simp [expandOffset, hodd]
      rw [show 4 ^ (depth + 2) = 4 * 4 ^ (depth + 1) by
        simp [pow_succ, mul_comm]]
      have hpositive : 0 < 4 ^ (depth + 1) := pow_pos (by decide) _
      conv_rhs =>
        rw [show
          1 :: ((freeOffsets depth).flatMap expandOffset ++
            [4 * (4 ^ (depth + 1) - 1) + 2,
              4 * (4 ^ (depth + 1) - 1) + 3]) =
            ((1 :: (freeOffsets depth).flatMap expandOffset) ++
              [4 * (4 ^ (depth + 1) - 1) + 2]) ++
                [4 * (4 ^ (depth + 1) - 1) + 3] by simp,
          List.dropLast_concat]
      simp only [List.cons_append, List.append_assoc, List.append_cancel_left_eq,
        List.cons.injEq]
      simp only [true_and, List.nil_append, List.cons.injEq, and_true]
      rw [Nat.mul_sub_left_distrib]
      omega

set_option linter.flexible false in
/-- One recurrence step adds the two side lines and expands every old line. -/
theorem freeOffsets_succ_decompose (depth : Nat) :
    freeOffsets (depth + 1) =
      1 :: (freeOffsets depth).flatMap expandOffset ++
        [4 ^ (depth + 2) - 2] := by
  rw [freeOffsets, extendedOffsets, extendedOffsets_decompose depth]
  have hpow : 4 ^ (depth + 1) = 4 * 4 ^ depth := by
    simp [pow_succ, mul_comm]
  have hodd : (4 ^ (depth + 1) - 1) % 2 ≠ 0 := by
    rw [hpow]
    have hpositive : 0 < 4 ^ depth := pow_pos (by decide) _
    have heq : 4 * 4 ^ depth - 1 = 2 * (2 * 4 ^ depth - 1) + 1 := by
      omega
    rw [heq]
    simp
  simp [expandOffset, hodd]
  rw [show 4 ^ (depth + 2) = 4 * 4 ^ (depth + 1) by
    simp [pow_succ, mul_comm]]
  have hpositive : 0 < 4 ^ (depth + 1) := pow_pos (by decide) _
  rw [show
    1 :: ((freeOffsets depth).flatMap expandOffset ++
      [4 * (4 ^ (depth + 1) - 1) + 2,
        4 * (4 ^ (depth + 1) - 1) + 3]) =
      ((1 :: (freeOffsets depth).flatMap expandOffset) ++
        [4 * (4 ^ (depth + 1) - 1) + 2]) ++
          [4 * (4 ^ (depth + 1) - 1) + 3] by simp,
    List.dropLast_concat]
  simp only [List.cons_append, List.append_cancel_left_eq,
    List.cons.injEq]
  simp only [true_and, and_true]
  rw [Nat.mul_sub_left_distrib]
  omega

/-- Every successor offset is a side line or a child of an old free offset. -/
theorem mem_freeOffsets_succ_cases (depth : Nat) {offset : Nat}
    (hmem : offset ∈ freeOffsets (depth + 1)) :
    offset = 1 ∨
      (∃ oldOffset ∈ freeOffsets depth,
        offset ∈ expandOffset oldOffset) ∨
      offset = 4 ^ (depth + 2) - 2 := by
  rw [freeOffsets_succ_decompose] at hmem
  simpa [List.mem_flatMap] using hmem

/-- Conversely, every child of an old free offset survives in the successor list. -/
theorem mem_freeOffsets_succ_of_child (depth : Nat)
    {oldOffset child : Nat} (hold : oldOffset ∈ freeOffsets depth)
    (hchild : child ∈ expandOffset oldOffset) :
    child ∈ freeOffsets (depth + 1) := by
  rw [freeOffsets_succ_decompose]
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨oldOffset, hold, hchild⟩)

set_option linter.flexible false in
theorem mem_extendedOffsets_lt (depth : Nat) {offset : Nat}
    (hmem : offset ∈ extendedOffsets depth) :
    offset < 4 ^ (depth + 1) := by
  induction depth generalizing offset with
  | zero =>
      simp [extendedOffsets] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> norm_num
  | succ depth ih =>
      rw [extendedOffsets, List.mem_flatMap] at hmem
      rcases hmem with ⟨parent, hparent, hchild⟩
      have hparentBound := ih hparent
      by_cases heven : parent % 2 = 0 <;>
        simp [expandOffset, heven] at hchild <;>
        rcases hchild with rfl | rfl <;>
        rw [show depth + 1 + 1 = depth + 2 by omega,
          show 4 ^ (depth + 2) = 4 * 4 ^ (depth + 1) by
            simp [pow_succ, mul_comm]] <;>
        omega

theorem mem_freeOffsets_bounds (depth : Nat) {offset : Nat}
    (hmem : offset ∈ freeOffsets depth) :
    0 < offset ∧ offset < 4 ^ (depth + 1) := by
  have hextended : offset ∈ extendedOffsets depth := by
    exact List.mem_of_mem_drop (List.mem_of_mem_dropLast hmem)
  refine ⟨?_, mem_extendedOffsets_lt depth hextended⟩
  rcases extendedOffsets_starts_zero depth with ⟨rest, hrest⟩
  have htail : offset ∈ rest := by
    rw [freeOffsets, hrest] at hmem
    simpa using List.mem_of_mem_dropLast hmem
  have hordered := extendedOffsets_pairwise depth
  rw [hrest, List.pairwise_cons] at hordered
  exact hordered.1 offset htail

theorem mem_freeOffsets_lt_last (depth : Nat) {offset : Nat}
    (hmem : offset ∈ freeOffsets depth) :
    offset < 4 ^ (depth + 1) - 1 := by
  have hordered := extendedOffsets_pairwise depth
  rw [extendedOffsets_decompose] at hordered
  have htail : (freeOffsets depth ++ [4 ^ (depth + 1) - 1]).Pairwise (· < ·) := by
    simpa only [List.tail_cons] using hordered.tail
  rw [List.pairwise_append] at htail
  exact htail.2.2 offset hmem (4 ^ (depth + 1) - 1) (by simp)

def offsetAtDepth (depth : Nat)
    (index : Fin (freeOffsets depth).length) : Nat :=
  (freeOffsets depth).get index

theorem offsetAtDepth_mem (depth : Nat)
    (index : Fin (freeOffsets depth).length) :
    offsetAtDepth depth index ∈ freeOffsets depth :=
  List.get_mem _ _

theorem offsetAtDepth_strictMono (depth : Nat)
    {first second : Fin (freeOffsets depth).length} (hlt : first < second) :
    offsetAtDepth depth first < offsetAtDepth depth second :=
  (freeOffsets_pairwise depth).rel_get_of_lt hlt

theorem offsetAtDepth_bounds (depth : Nat)
    (index : Fin (freeOffsets depth).length) :
    0 < offsetAtDepth depth index ∧
      offsetAtDepth depth index < 4 ^ (depth + 1) :=
  mem_freeOffsets_bounds depth (offsetAtDepth_mem depth index)

theorem offsetAtDepth_lt_last (depth : Nat)
    (index : Fin (freeOffsets depth).length) :
    offsetAtDepth depth index < 4 ^ (depth + 1) - 1 :=
  mem_freeOffsets_lt_last depth (offsetAtDepth_mem depth index)

theorem depth_le_freeOffsets_length (depth : Nat) :
    depth ≤ (freeOffsets depth).length := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [show depth + 1 = depth + 1 by rfl,
        freeOffsets_length_succ]
      omega

/-- Package semantic freedom of all Figure 18 offsets as an ordered grid. -/
def freeGridOfOffsets
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north depth : Nat)
    (column_east : ∀ index : Fin (freeOffsets depth).length,
      quarterWest west + offsetAtDepth depth index < quarterEast east)
    (row_north : ∀ index : Fin (freeOffsets depth).length,
      quarterSouth south + offsetAtDepth depth index < quarterNorth north)
    (freeColumn : ∀ index : Fin (freeOffsets depth).length,
      IsFreeColumn indexGrid shadeGrid south north
        (quarterWest west + offsetAtDepth depth index))
    (freeRow : ∀ index : Fin (freeOffsets depth).length,
      IsFreeRow indexGrid shadeGrid west east
        (quarterSouth south + offsetAtDepth depth index)) :
    FreeGrid indexGrid shadeGrid west east south north
      (freeOffsets depth).length where
  columnAt := fun index => quarterWest west + offsetAtDepth depth index
  rowAt := fun index => quarterSouth south + offsetAtDepth depth index
  column_strictMono := by
    intro first second hlt
    exact Nat.add_lt_add_left (offsetAtDepth_strictMono depth hlt) _
  row_strictMono := by
    intro first second hlt
    exact Nat.add_lt_add_left (offsetAtDepth_strictMono depth hlt) _
  column_west := by
    intro index
    have := (offsetAtDepth_bounds depth index).1
    omega
  column_east := by
    intro index
    exact column_east index
  row_south := by
    intro index
    have := (offsetAtDepth_bounds depth index).1
    omega
  row_north := by
    intro index
    exact row_north index
  freeColumn := freeColumn
  freeRow := freeRow

end ShadedFreeLineOffsets
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
