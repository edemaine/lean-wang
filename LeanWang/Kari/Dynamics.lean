/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.StateTransition

/-!
# Partial dynamics for the Kari construction

Section 5.4 of Jeandel and Vanier's presentation of Kari's construction uses
the terminology that a point is *immortal* when every finite prefix of its
forward orbit under a partial map is defined, and that the partial map is
immortal when it has such a point.  This module packages those notions for an
arbitrary transition function `step : α → Option α`.

Mathlib's `StateTransition.eval step x` runs the same partial dynamics until it
reaches a point where `step` is `none`.  The main theorem below identifies its
nontermination exactly with immortality from `x`.
-/

namespace LeanWang
namespace Kari
namespace Dynamics

universe u

variable {α : Type u}

/-- The state after exactly `n` defined transitions, if all of them exist. -/
def iterate (step : α → Option α) : Nat → α → Option α
  | 0, x => some x
  | n + 1, x => (iterate step n x).bind step

@[simp]
theorem iterate_zero (step : α → Option α) (x : α) :
    iterate step 0 x = some x :=
  rfl

@[simp]
theorem iterate_succ (step : α → Option α) (n : Nat) (x : α) :
    iterate step (n + 1) x = (iterate step n x).bind step :=
  rfl

/-- The orbit from `x` remains defined for `n` transitions. -/
def Survives (step : α → Option α) (x : α) (n : Nat) : Prop :=
  ∃ y, iterate step n x = some y

/-- Every finite prefix of the forward orbit from `x` is defined. -/
def ImmortalFrom (step : α → Option α) (x : α) : Prop :=
  ∀ n, Survives step x n

/-- The partial dynamics has at least one immortal starting point. -/
def Immortal (step : α → Option α) : Prop :=
  ∃ x, ImmortalFrom step x

@[simp]
theorem survives_zero (step : α → Option α) (x : α) :
    Survives step x 0 :=
  ⟨x, rfl⟩

/-- An exact finite iterate gives the corresponding reflexive-transitive path. -/
theorem reaches_of_iterate_eq_some {step : α → Option α} {n : Nat} {x y : α}
    (h : iterate step n x = some y) :
    StateTransition.Reaches step x y := by
  induction n generalizing x y with
  | zero =>
      simp only [iterate_zero] at h
      cases Option.some.inj h
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      rw [iterate_succ] at h
      cases hiterate : iterate step n x with
      | none => simp [hiterate] at h
      | some z =>
          have hstep : step z = some y := by
            simpa [hiterate] using h
          exact Relation.ReflTransGen.tail (ih hiterate) (by simp [hstep])

/-- Every finite path of deterministic transitions is an exact iterate. -/
theorem exists_iterate_eq_some_of_reaches {step : α → Option α} {x y : α}
    (h : StateTransition.Reaches step x y) :
    ∃ n, iterate step n x = some y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      simp only [iterate_succ, hn, Option.bind_some]
      simpa using hstep

/-- `StateTransition.eval` diverges exactly at immortal starting points. -/
theorem not_eval_dom_iff_immortalFrom (step : α → Option α) (x : α) :
    ¬ (StateTransition.eval step x).Dom ↔ ImmortalFrom step x := by
  constructor
  · intro hdiverges n
    induction n with
    | zero => exact survives_zero step x
    | succ n ih =>
        rcases ih with ⟨y, hy⟩
        cases hstep : step y with
        | none =>
            exfalso
            apply hdiverges
            apply Part.dom_iff_mem.2
            exact ⟨y, StateTransition.mem_eval.2
              ⟨reaches_of_iterate_eq_some hy, hstep⟩⟩
        | some z =>
            exact ⟨z, by simp [hy, hstep]⟩
  · intro himmortal hdom
    rcases Part.dom_iff_mem.1 hdom with ⟨terminal, hterminal⟩
    rcases StateTransition.mem_eval.1 hterminal with ⟨hreaches, hnone⟩
    rcases exists_iterate_eq_some_of_reaches hreaches with ⟨n, hn⟩
    rcases himmortal (n + 1) with ⟨y, hy⟩
    simp [hn, hnone] at hy

/-- The partial dynamics is immortal iff `eval` diverges from some point. -/
theorem immortal_iff_exists_not_eval_dom (step : α → Option α) :
    Immortal step ↔ ∃ x, ¬ (StateTransition.eval step x).Dom := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (not_eval_dom_iff_immortalFrom step x).2 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (not_eval_dom_iff_immortalFrom step x).1 hx⟩

end Dynamics
end Kari
end LeanWang
