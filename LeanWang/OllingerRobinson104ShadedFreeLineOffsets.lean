/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineBase

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

end ShadedFreeLineOffsets
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
