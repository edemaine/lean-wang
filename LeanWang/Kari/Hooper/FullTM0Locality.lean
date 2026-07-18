/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FullTM0

/-!
# Finite-run locality for full-tape machines

A Post-Turing machine can inspect only one new tape cell per transition.
Consequently, two full configurations that agree in a radius-`steps + radius`
window have `steps`-step iterates that either are both undefined or still
agree in the remaining radius-`radius` window.  In particular, tape contents
outside radius `steps` cannot affect whether the machine halts after exactly
`steps` transitions, or at any earlier time.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FullTM0

open Turing

universe u v

namespace Tape

variable {Γ : Type u}

/-- Two head-relative tapes agree throughout the closed integer interval
`[-radius, radius]`. -/
def Agree (radius : Nat) (T U : Tape Γ) : Prop :=
  ∀ position : Int,
    -(radius : Int) ≤ position → position ≤ (radius : Int) →
      T position = U position

namespace Agree

/-- Agreement on a larger window implies agreement on every smaller window. -/
theorem mono {small large : Nat} {T U : Tape Γ}
    (h : Agree large T U) (hle : small ≤ large) :
    Agree small T U := by
  intro position hlower hupper
  have hcast : (small : Int) ≤ (large : Int) := by exact_mod_cast hle
  exact h position (by omega) (by omega)

/-- Window agreement includes equality of the currently scanned symbols. -/
theorem read {radius : Nat} {T U : Tape Γ} (h : Agree radius T U) :
    T.read = U.read := by
  exact h 0 (by simp) (by simp)

/-- After one head move, agreement on radius `r + 1` leaves agreement on
radius `r`. -/
theorem move {radius : Nat} {T U : Tape Γ}
    (h : Agree (radius + 1) T U) (direction : Turing.Dir) :
    Agree radius (T.move direction) (U.move direction) := by
  intro position hlower hupper
  cases direction with
  | left =>
      exact h (position - 1) (by push_cast; omega) (by push_cast; omega)
  | right =>
      exact h (position + 1) (by push_cast; omega) (by push_cast; omega)

/-- Writing the same symbol under both heads preserves every existing
agreement window. -/
theorem write {radius : Nat} {T U : Tape Γ}
    (h : Agree radius T U) (symbol : Γ) :
    Agree radius (T.write symbol) (U.write symbol) := by
  intro position hlower hupper
  by_cases hposition : position = 0
  · subst position
    simp
  · simp [Tape.write, hposition, h position hlower hupper]

end Agree
end Tape

namespace Cfg

variable {Γ : Type u} {Λ : Type v}

/-- Two configurations have the same control state and locally equal tapes. -/
def Agree (radius : Nat) (first second : Cfg Γ Λ) : Prop :=
  first.q = second.q ∧ Tape.Agree radius first.tape second.tape

namespace Agree

/-- Configuration agreement is monotone in the window radius. -/
theorem mono {small large : Nat} {first second : Cfg Γ Λ}
    (h : Agree large first second) (hle : small ≤ large) :
    Agree small first second :=
  ⟨h.1, h.2.mono hle⟩

/-- Locally agreeing configurations present the same state and scanned symbol
to the transition function. -/
theorem inputs {radius : Nat} {first second : Cfg Γ Λ}
    (h : Agree radius first second) :
    (first.q, first.tape.read) = (second.q, second.tape.read) :=
  Prod.ext h.1 h.2.read

end Agree
end Cfg

variable {Γ : Type u} {Λ : Type v}
variable [Inhabited Γ] [Inhabited Λ]

omit [Inhabited Γ] in
/-- One machine transition consumes at most one cell of locality radius. -/
theorem step_rel (M : Turing.TM0.Machine Γ Λ) {radius : Nat}
    {first second : Cfg Γ Λ}
    (hagree : Cfg.Agree (radius + 1) first second) :
    Option.Rel (Cfg.Agree radius) (step M first) (step M second) := by
  rcases first with ⟨firstState, firstTape⟩
  rcases second with ⟨secondState, secondTape⟩
  rcases hagree with ⟨hstate, htape⟩
  change firstState = secondState at hstate
  change Tape.Agree (radius + 1) firstTape secondTape at htape
  subst secondState
  have hread : firstTape.read = secondTape.read := htape.read
  simp only [step, hread]
  cases hmachine : M firstState secondTape.read with
  | none => exact Option.Rel.none
  | some result =>
      rcases result with ⟨nextState, action⟩
      cases action with
      | move direction =>
          exact Option.Rel.some ⟨rfl, htape.move direction⟩
      | write symbol =>
          exact Option.Rel.some ⟨rfl,
            (htape.mono (Nat.le_add_right radius 1)).write symbol⟩

omit [Inhabited Γ] in
/-- Whether the next transition is undefined depends only on the current
state and scanned symbol. -/
theorem step_eq_none_iff_of_agree (M : Turing.TM0.Machine Γ Λ)
    {first second : Cfg Γ Λ} (hagree : Cfg.Agree 0 first second) :
    step M first = none ↔ step M second = none := by
  rcases first with ⟨firstState, firstTape⟩
  rcases second with ⟨secondState, secondTape⟩
  rcases hagree with ⟨hstate, htape⟩
  change firstState = secondState at hstate
  change Tape.Agree 0 firstTape secondTape at htape
  subst secondState
  have hread : firstTape.read = secondTape.read := htape.read
  simp only [step, hread]
  cases M firstState secondTape.read <;> simp

omit [Inhabited Γ] in
/-- Relational bind for the shrinking locality invariant. -/
private theorem optionRel_bind_step (M : Turing.TM0.Machine Γ Λ)
    {radius : Nat} {first second : Option (Cfg Γ Λ)}
    (hrel : Option.Rel (Cfg.Agree (radius + 1)) first second) :
    Option.Rel (Cfg.Agree radius)
      (first.bind (step M)) (second.bind (step M)) := by
  cases hrel with
  | none => exact Option.Rel.none
  | some hagree => exact step_rel M hagree

omit [Inhabited Γ] [Inhabited Λ] in
/-- A relation from a defined option supplies a defined related option. -/
private theorem exists_of_optionRel_some_left
    {R : Cfg Γ Λ → Cfg Γ Λ → Prop} {first : Cfg Γ Λ}
    {second : Option (Cfg Γ Λ)}
    (hrel : Option.Rel R (some first) second) :
    ∃ other, second = some other ∧ R first other := by
  cases hrel with
  | some h => exact ⟨_, rfl, h⟩

omit [Inhabited Γ] [Inhabited Λ] in
/-- Related options are defined simultaneously. -/
private theorem exists_some_iff_of_optionRel
    {R : Cfg Γ Λ → Cfg Γ Λ → Prop}
    {first second : Option (Cfg Γ Λ)} (hrel : Option.Rel R first second) :
    (∃ value, first = some value) ↔ ∃ value, second = some value := by
  cases hrel with
  | none => simp
  | some _ => simp

omit [Inhabited Γ] in
/-- **Finite-run locality.** After `steps` transitions, an initial agreement
window of radius `steps + radius` leaves a radius-`radius` agreement window.
The two iterates are related only when both are undefined or both are defined,
so this also preserves survival through the given number of transitions. -/
theorem iterate_rel (M : Turing.TM0.Machine Γ Λ)
    (steps radius : Nat) {first second : Cfg Γ Λ}
    (hagree : Cfg.Agree (steps + radius) first second) :
    Option.Rel (Cfg.Agree radius)
      (Dynamics.iterate (step M) steps first)
      (Dynamics.iterate (step M) steps second) := by
  induction steps generalizing first second radius with
  | zero =>
      exact Option.Rel.some (by simpa using hagree)
  | succ steps ih =>
      have hpref : Option.Rel (Cfg.Agree (radius + 1))
          (Dynamics.iterate (step M) steps first)
          (Dynamics.iterate (step M) steps second) := by
        apply ih
        simpa [Nat.succ_add, Nat.add_assoc] using hagree
      rw [Dynamics.iterate_succ, Dynamics.iterate_succ]
      exact optionRel_bind_step M hpref

omit [Inhabited Γ] in
/-- A defined exact iterate transfers to every tape with the same initial
radius-`steps` window, and the resulting state, head position, and scanned
symbol agree. -/
theorem iterate_eq_some_of_agree (M : Turing.TM0.Machine Γ Λ)
    (steps : Nat) {first second finish : Cfg Γ Λ}
    (hagree : Cfg.Agree steps first second)
    (hiterate : Dynamics.iterate (step M) steps first = some finish) :
    ∃ otherFinish,
      Dynamics.iterate (step M) steps second = some otherFinish ∧
        Cfg.Agree 0 finish otherFinish := by
  have hrel := iterate_rel M steps 0 (by simpa using hagree)
  rw [hiterate] at hrel
  rcases exists_of_optionRel_some_left hrel with
    ⟨otherFinish, hother, hfinish⟩
  exact ⟨otherFinish, hother, hfinish⟩

omit [Inhabited Γ] in
/-- Exact survival for `steps` transitions is unaffected by tape contents
outside the initial radius-`steps` window. -/
theorem survives_iff_of_agree (M : Turing.TM0.Machine Γ Λ)
    (steps : Nat) {first second : Cfg Γ Λ}
    (hagree : Cfg.Agree steps first second) :
    Dynamics.Survives (step M) first steps ↔
      Dynamics.Survives (step M) second steps := by
  have hrel := iterate_rel M steps 0 (by simpa using hagree)
  simpa [Dynamics.Survives] using exists_some_iff_of_optionRel hrel

/-- The machine halts after exactly `steps` successful transitions. -/
def HaltsAt (M : Turing.TM0.Machine Γ Λ) (start : Cfg Γ Λ)
    (steps : Nat) : Prop :=
  ∃ terminal,
    Dynamics.iterate (step M) steps start = some terminal ∧
      step M terminal = none

omit [Inhabited Γ] in
/-- Halting after exactly `steps` transitions is determined by the initial
radius-`steps` window. -/
theorem haltsAt_iff_of_agree (M : Turing.TM0.Machine Γ Λ)
    (steps : Nat) {first second : Cfg Γ Λ}
    (hagree : Cfg.Agree steps first second) :
    HaltsAt M first steps ↔ HaltsAt M second steps := by
  constructor
  · rintro ⟨terminal, hiterate, hhalt⟩
    rcases iterate_eq_some_of_agree M steps hagree hiterate with
      ⟨otherTerminal, hotherIterate, hterminal⟩
    exact ⟨otherTerminal, hotherIterate,
      (step_eq_none_iff_of_agree M hterminal).1 hhalt⟩
  · rintro ⟨terminal, hiterate, hhalt⟩
    have hagree' : Cfg.Agree steps second first :=
      ⟨hagree.1.symm, fun position hlower hupper =>
        (hagree.2 position hlower hupper).symm⟩
    rcases iterate_eq_some_of_agree M steps hagree' hiterate with
      ⟨otherTerminal, hotherIterate, hterminal⟩
    exact ⟨otherTerminal, hotherIterate,
      (step_eq_none_iff_of_agree M hterminal).1 hhalt⟩

/-- The machine halts after at most `steps` successful transitions. -/
def HaltsWithin (M : Turing.TM0.Machine Γ Λ) (start : Cfg Γ Λ)
    (steps : Nat) : Prop :=
  ∃ runtime ≤ steps, HaltsAt M start runtime

omit [Inhabited Γ] in
/-- Halting anywhere within `steps` transitions is unaffected by tape
contents outside the initial radius-`steps` window. -/
theorem haltsWithin_iff_of_agree (M : Turing.TM0.Machine Γ Λ)
    (steps : Nat) {first second : Cfg Γ Λ}
    (hagree : Cfg.Agree steps first second) :
    HaltsWithin M first steps ↔ HaltsWithin M second steps := by
  constructor
  · rintro ⟨runtime, hruntime, hhalt⟩
    exact ⟨runtime, hruntime,
      (haltsAt_iff_of_agree M runtime (hagree.mono hruntime)).1 hhalt⟩
  · rintro ⟨runtime, hruntime, hhalt⟩
    exact ⟨runtime, hruntime,
      (haltsAt_iff_of_agree M runtime (hagree.mono hruntime)).2 hhalt⟩

end FullTM0
end Hooper
end Kari
end LeanWang
