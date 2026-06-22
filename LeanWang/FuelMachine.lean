/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
A minimal fuel-enumerating machine model.

This is an intermediate reduction target: it repeatedly tests a decidable
predicate at fuel values `0, 1, 2, ...` and halts at the first successful fuel.
The remaining reduction bridge is to implement this counter/search behavior in
the concrete one-tape `Machine` model, by compiling it to finite machine data.
-/

namespace LeanWang

namespace FuelMachine

/-- State of a fuel search: either still testing fuel `k`, or halted. -/
inductive State where
  | running (fuel : Nat)
  | halt
deriving DecidableEq, Repr

/-- One step of fuel search for a Boolean predicate `P`. -/
def step (P : Nat → Bool) : State → State
  | State.halt => State.halt
  | State.running k => if P k then State.halt else State.running (k + 1)

/-- State after `n` steps of fuel search. -/
def run (P : Nat → Bool) (n : Nat) : State :=
  Nat.iterate (step P) n (State.running 0)

/-- The fuel search eventually reaches the halt state. -/
def Halts (P : Nat → Bool) : Prop :=
  ∃ n : Nat, run P n = State.halt

@[simp]
theorem run_zero (P : Nat → Bool) :
    run P 0 = State.running 0 := by
  rfl

@[simp]
theorem run_succ (P : Nat → Bool) (n : Nat) :
    run P (n + 1) = step P (run P n) := by
  unfold run
  rw [Function.iterate_succ_apply']

theorem exists_true_of_run_halt {P : Nat → Bool} :
    ∀ {n : Nat}, run P n = State.halt → ∃ k : Nat, P k = true
  | 0, h => by
      simp [run] at h
  | n + 1, h => by
      rw [run_succ] at h
      cases hr : run P n with
      | halt =>
          exact exists_true_of_run_halt hr
      | running k =>
          by_cases hk : P k = true
          · exact ⟨k, hk⟩
          · simp [step, hr, hk] at h

theorem run_eq_running_of_all_false {P : Nat → Bool} :
    ∀ n : Nat, (∀ k : Nat, k < n → P k = false) →
      run P n = State.running n
  | 0, _ => by
      rfl
  | n + 1, hfalse => by
      rw [run_succ, run_eq_running_of_all_false n (by
        intro k hk
        exact hfalse k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
      have hn : P n = false := hfalse n (Nat.lt_succ_self n)
      simp [step, hn]

theorem run_halt_of_true {P : Nat → Bool} :
    ∀ {k : Nat}, P k = true → ∃ n : Nat, run P n = State.halt
  | 0, h0 => by
      exact ⟨1, by simp [step, h0]⟩
  | k + 1, hk => by
      by_cases hearlier : ∃ j : Nat, j < k + 1 ∧ P j = true
      · rcases hearlier with ⟨j, hj, htrue⟩
        exact run_halt_of_true htrue
      · have hfalse : ∀ j : Nat, j < k + 1 → P j = false := by
          intro j hj
          cases h : P j
          · rfl
          · exact False.elim (hearlier ⟨j, hj, h⟩)
        refine ⟨k + 1 + 1, ?_⟩
        rw [run_succ, run_eq_running_of_all_false (k + 1) hfalse]
        simp [step, hk]

theorem halts_iff_exists_true (P : Nat → Bool) :
    Halts P ↔ ∃ k : Nat, P k = true := by
  constructor
  · rintro ⟨n, hn⟩
    exact exists_true_of_run_halt hn
  · rintro ⟨k, hk⟩
    exact run_halt_of_true hk

end FuelMachine

end LeanWang
