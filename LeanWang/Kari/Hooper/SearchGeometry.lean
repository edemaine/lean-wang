/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FullTM0
import Mathlib.Tactic.Ring

/-!
# Geometry of searches on a full tape

Hooper's Basic Lemma is an induction on the distance from a search head to the
next marked cell.  This file records that geometry independently of the states
and transition table that will implement bounded, nested searches.

The tape coordinates in `FullTM0` are relative to the current head.  Thus the
tape after finding a marker at distance `k` is `T.moveN direction k`: its cell
contents are unchanged in absolute coordinates, but the marker has become the
new head cell.
-/

namespace LeanWang
namespace Kari
namespace Hooper

open Turing

namespace FullTM0.Tape

universe u

variable {Γ : Type u}

/-- The signed displacement of one head move. -/
def delta : Turing.Dir → Int
  | .left => -1
  | .right => 1

/-- The signed displacement after `n` moves in one direction. -/
def offset (d : Turing.Dir) (n : Nat) : Int :=
  (n : Int) * delta d

/-- Move a head-relative tape `n` cells in one direction. -/
def moveN (T : FullTM0.Tape Γ) (d : Turing.Dir) (n : Nat) : FullTM0.Tape Γ :=
  fun i => T (i + offset d n)

@[simp]
theorem delta_left : delta .left = -1 :=
  rfl

@[simp]
theorem delta_right : delta .right = 1 :=
  rfl

@[simp]
theorem offset_zero (d : Turing.Dir) : offset d 0 = 0 := by
  simp [offset]

@[simp]
theorem offset_left (n : Nat) : offset .left n = -(n : Int) := by
  simp [offset]

@[simp]
theorem offset_right (n : Nat) : offset .right n = n := by
  simp [offset]

@[simp]
theorem offset_succ (d : Turing.Dir) (n : Nat) :
    offset d (n + 1) = offset d n + delta d := by
  cases d <;> simp [offset, add_comm]

@[simp]
theorem offset_add (d : Turing.Dir) (m n : Nat) :
    offset d (m + n) = offset d m + offset d n := by
  simp [offset, add_mul]

@[simp]
theorem moveN_apply (T : FullTM0.Tape Γ) (d : Turing.Dir) (n : Nat) (i : Int) :
    T.moveN d n i = T (i + offset d n) :=
  rfl

@[simp]
theorem moveN_zero (T : FullTM0.Tape Γ) (d : Turing.Dir) :
    T.moveN d 0 = T := by
  funext i
  simp [moveN]

@[simp]
theorem read_moveN (T : FullTM0.Tape Γ) (d : Turing.Dir) (n : Nat) :
    (T.moveN d n).read = T (offset d n) := by
  simp [moveN, FullTM0.Tape.read]

@[simp]
theorem move_apply_delta (T : FullTM0.Tape Γ) (d : Turing.Dir) (i : Int) :
    T.move d i = T (i + delta d) := by
  cases d <;> simp [FullTM0.Tape.move, delta, sub_eq_add_neg]

@[simp]
theorem move_apply_offset (T : FullTM0.Tape Γ) (d : Turing.Dir) (n : Nat) :
    (T.move d) (offset d n) = T (offset d (n + 1)) := by
  cases d <;> simp [FullTM0.Tape.move, offset, add_comm, sub_eq_add_neg]

/-- Moving once and then `n` more times is the same as moving `n+1` times. -/
theorem move_moveN (T : FullTM0.Tape Γ) (d : Turing.Dir) (n : Nat) :
    (T.move d).moveN d n = T.moveN d (n + 1) := by
  funext i
  simp only [moveN_apply, move_apply_delta, offset_succ]
  congr 1
  ring

/-- Consecutive runs of moves in the same direction add their lengths. -/
theorem moveN_add (T : FullTM0.Tape Γ) (d : Turing.Dir) (m n : Nat) :
    (T.moveN d m).moveN d n = T.moveN d (m + n) := by
  funext i
  simp only [moveN_apply, offset_add]
  congr 1
  ring

end FullTM0.Tape

universe u

variable {Γ : Type u}

/-- There are exactly `k` blank cells from the head through the cell just
before a marked target, in direction `d`.  Distance zero means that the current
head cell is already marked. -/
def SearchGap (IsBlank IsMark : Γ → Prop) (T : FullTM0.Tape Γ)
    (d : Turing.Dir) (k : Nat) : Prop :=
  (∀ i < k, IsBlank (T (FullTM0.Tape.offset d i))) ∧
    IsMark (T (FullTM0.Tape.offset d k))

namespace SearchGap

variable {IsBlank IsMark : Γ → Prop}
variable {T : FullTM0.Tape Γ} {d : Turing.Dir} {k : Nat}

@[simp]
theorem zero :
    SearchGap IsBlank IsMark T d 0 ↔ IsMark (T 0) := by
  simp [SearchGap]

theorem blank (h : SearchGap IsBlank IsMark T d k) {i : Nat} (hi : i < k) :
    IsBlank (T (FullTM0.Tape.offset d i)) :=
  h.1 i hi

theorem marked (h : SearchGap IsBlank IsMark T d k) :
    IsMark (T (FullTM0.Tape.offset d k)) :=
  h.2

/-- After one move toward a target at distance `k+1`, the remaining search gap
has distance `k`. -/
theorem tail (h : SearchGap IsBlank IsMark T d (k + 1)) :
    SearchGap IsBlank IsMark (T.move d) d k := by
  constructor
  · intro i hi
    simpa using h.blank (Nat.succ_lt_succ hi)
  · simpa using h.marked

end SearchGap

end Hooper
end Kari
end LeanWang
