/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Dynamics
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Full-tape semantics for Post-Turing machines

Mathlib's `Turing.TM0.Cfg` uses a tape that is blank outside a finite interval.
Hooper's immortality problem instead quantifies over arbitrary configurations on
arbitrary bi-infinite tapes.  This file gives the same `Turing.TM0.Machine` an
alternative semantics whose tape is an unrestricted function `Int → Γ`.

Coordinates are relative to the head: coordinate `0` is the cell currently
being scanned.  Moving the head therefore shifts the coordinate system.  The
last part of the file embeds Mathlib configurations into full configurations
and proves that the two step semantics, finite iterates, survival, and
immortality agree on embedded configurations.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FullTM0

open Turing

universe u v

/-- An unrestricted bi-infinite tape, in coordinates relative to the head. -/
abbrev Tape (Γ : Type u) := Int → Γ

namespace Tape

variable {Γ : Type u}

/-- The symbol currently scanned by the head. -/
def read (T : Tape Γ) : Γ :=
  T 0

/-- Shift head-relative tape coordinates after moving the machine head. -/
def move (d : Turing.Dir) (T : Tape Γ) : Tape Γ :=
  match d with
  | .left => fun i => T (i - 1)
  | .right => fun i => T (i + 1)

/-- Replace the symbol under the head. -/
def write (a : Γ) (T : Tape Γ) : Tape Γ :=
  fun i => if i = 0 then a else T i

@[simp]
theorem read_eq (T : Tape Γ) : T.read = T 0 :=
  rfl

@[simp]
theorem move_left_apply (T : Tape Γ) (i : Int) :
    (T.move .left) i = T (i - 1) :=
  rfl

@[simp]
theorem move_right_apply (T : Tape Γ) (i : Int) :
    (T.move .right) i = T (i + 1) :=
  rfl

@[simp]
theorem move_left_right (T : Tape Γ) :
    (T.move .left).move .right = T := by
  funext i
  simp

@[simp]
theorem move_right_left (T : Tape Γ) :
    (T.move .right).move .left = T := by
  funext i
  simp

@[simp]
theorem write_apply (a : Γ) (T : Tape Γ) (i : Int) :
    (T.write a) i = if i = 0 then a else T i :=
  rfl

@[simp]
theorem read_write (a : Γ) (T : Tape Γ) :
    (T.write a).read = a := by
  simp [read, write]

@[simp]
theorem write_apply_of_ne (a : Γ) (T : Tape Γ) {i : Int} (hi : i ≠ 0) :
    (T.write a) i = T i := by
  simp [write, hi]

/-- Regard Mathlib's finitely supported tape as a full tape. -/
def ofMathlib [Inhabited Γ] (T : Turing.Tape Γ) : Tape Γ :=
  T.nth

@[simp]
theorem ofMathlib_apply [Inhabited Γ] (T : Turing.Tape Γ) (i : Int) :
    ofMathlib T i = T.nth i :=
  rfl

@[simp]
theorem ofMathlib_move [Inhabited Γ] (T : Turing.Tape Γ) (d : Turing.Dir) :
    ofMathlib (T.move d) = (ofMathlib T).move d := by
  funext i
  cases d <;> simp [ofMathlib, move]

@[simp]
theorem ofMathlib_write [Inhabited Γ] (T : Turing.Tape Γ) (a : Γ) :
    ofMathlib (T.write a) = (ofMathlib T).write a := by
  funext i
  simp [ofMathlib, write]

theorem ofMathlib_injective [Inhabited Γ] :
    Function.Injective (ofMathlib : Turing.Tape Γ → Tape Γ) := by
  intro T U h
  rcases T with ⟨headT, leftT, rightT⟩
  rcases U with ⟨headU, leftU, rightU⟩
  have hhead : headT = headU := by
    simpa [ofMathlib, Turing.Tape.nth] using congrFun h 0
  have hleft : leftT = leftU := by
    apply Turing.ListBlank.ext
    intro n
    simpa [ofMathlib, Turing.Tape.nth] using
      congrFun h (Int.negSucc n)
  have hright : rightT = rightU := by
    apply Turing.ListBlank.ext
    intro n
    simpa [ofMathlib, Turing.Tape.nth] using
      congrFun h ((n + 1 : Nat) : Int)
  cases hhead
  cases hleft
  cases hright
  rfl

end Tape

/-- A machine state together with an arbitrary bi-infinite tape. -/
structure Cfg (Γ : Type u) (Λ : Type v) where
  q : Λ
  tape : Tape Γ

namespace Cfg

variable {Γ : Type u} {Λ : Type v}

/-- Embed a Mathlib finite-support configuration into the full-tape semantics. -/
def ofMathlib [Inhabited Γ] (c : Turing.TM0.Cfg Γ Λ) : Cfg Γ Λ :=
  ⟨c.q, Tape.ofMathlib c.Tape⟩

@[simp]
theorem ofMathlib_q [Inhabited Γ] (c : Turing.TM0.Cfg Γ Λ) :
    (ofMathlib c).q = c.q :=
  rfl

@[simp]
theorem ofMathlib_tape [Inhabited Γ] (c : Turing.TM0.Cfg Γ Λ) :
    (ofMathlib c).tape = Tape.ofMathlib c.Tape :=
  rfl

theorem ofMathlib_injective [Inhabited Γ] :
    Function.Injective (ofMathlib : Turing.TM0.Cfg Γ Λ → Cfg Γ Λ) := by
  intro c d h
  have hq : c.q = d.q := congrArg Cfg.q h
  have ht : Tape.ofMathlib c.Tape = Tape.ofMathlib d.Tape :=
    congrArg Cfg.tape h
  cases c
  cases d
  simp only at hq ht ⊢
  cases hq
  cases Tape.ofMathlib_injective ht
  rfl

end Cfg

variable {Γ : Type u} {Λ : Type v}
variable [Inhabited Γ] [Inhabited Λ]

/-- Execute one `TM0` instruction on an unrestricted tape. -/
def step (M : Turing.TM0.Machine Γ Λ) (c : Cfg Γ Λ) : Option (Cfg Γ Λ) :=
  (M c.q c.tape.read).map fun ⟨q', action⟩ =>
    ⟨q', match action with
      | .move d => c.tape.move d
      | .write a => c.tape.write a⟩

/-- Reachability for the full-tape execution semantics. -/
def Reaches (M : Turing.TM0.Machine Γ Λ) : Cfg Γ Λ → Cfg Γ Λ → Prop :=
  StateTransition.Reaches (step M)

/-- Every finite execution prefix from `c` is defined. -/
def ImmortalFrom (M : Turing.TM0.Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  Dynamics.ImmortalFrom (step M) c

/-- The machine has an immortal configuration on some arbitrary full tape. -/
def Immortal (M : Turing.TM0.Machine Γ Λ) : Prop :=
  Dynamics.Immortal (step M)

/-- The full semantics agrees for one step with Mathlib's semantics. -/
theorem step_ofMathlib (M : Turing.TM0.Machine Γ Λ) (c : Turing.TM0.Cfg Γ Λ) :
    (Turing.TM0.step M c).map Cfg.ofMathlib = step M (Cfg.ofMathlib c) := by
  rcases c with ⟨q, T⟩
  simp only [Turing.TM0.step, step, Cfg.ofMathlib, Tape.read_eq,
    Tape.ofMathlib_apply, Turing.Tape.nth_zero]
  cases h : M q T.head with
  | none => simp
  | some result =>
      rcases result with ⟨q', action⟩
      cases action <;> simp [Cfg.ofMathlib]

/-- The full semantics agrees with Mathlib's semantics for every finite iterate. -/
theorem iterate_step_ofMathlib (M : Turing.TM0.Machine Γ Λ)
    (n : Nat) (c : Turing.TM0.Cfg Γ Λ) :
    (Dynamics.iterate (Turing.TM0.step M) n c).map Cfg.ofMathlib =
      Dynamics.iterate (step M) n (Cfg.ofMathlib c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Dynamics.iterate_succ, Dynamics.iterate_succ]
      rw [← ih]
      cases h : Dynamics.iterate (Turing.TM0.step M) n c with
      | none => simp
      | some d => simpa [h] using step_ofMathlib M d

/-- A finite-support configuration survives exactly when its full-tape image survives. -/
theorem survives_step_ofMathlib_iff (M : Turing.TM0.Machine Γ Λ)
    (c : Turing.TM0.Cfg Γ Λ) (n : Nat) :
    Dynamics.Survives (Turing.TM0.step M) c n ↔
      Dynamics.Survives (step M) (Cfg.ofMathlib c) n := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨Cfg.ofMathlib d, ?_⟩
    have h := iterate_step_ofMathlib M n c
    simpa [hd] using h.symm
  · rintro ⟨d, hd⟩
    cases hfinite : Dynamics.iterate (Turing.TM0.step M) n c with
    | none =>
        have h := iterate_step_ofMathlib M n c
        rw [hfinite] at h
        simp only [Option.map_none] at h
        rw [← h] at hd
        simp at hd
    | some e => exact ⟨e, hfinite⟩

/-- On a finite-support initial configuration, immortality is unchanged by
passing to the unrestricted full-tape semantics. -/
theorem immortalFrom_step_ofMathlib_iff (M : Turing.TM0.Machine Γ Λ)
    (c : Turing.TM0.Cfg Γ Λ) :
    Dynamics.ImmortalFrom (Turing.TM0.step M) c ↔
      ImmortalFrom M (Cfg.ofMathlib c) := by
  simp only [Dynamics.ImmortalFrom, ImmortalFrom]
  exact forall_congr' fun n => survives_step_ofMathlib_iff M c n

end FullTM0
end Hooper
end Kari
end LeanWang
