/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FullTM0
import Mathlib.Data.Fintype.Sets

/-!
# Restricting a supported `TM0` machine to finite control

Mathlib permits a `Turing.TM0.Machine` to use an infinite ambient label type and
records effective finiteness through `Turing.TM0.Supports`.  That is enough for
a designated initial computation, but not for Hooper's immortality problem:
an arbitrary configuration could start at an out-of-support label and create a
spurious immortal orbit.

This file restricts a supported machine to the subtype of labels in its finite
support.  The restricted machine has a genuine `Fintype` of control states.
For full-tape execution, forgetting the subtype commutes with every finite
iterate, so immortality of a restricted configuration is exactly immortality
of its supported ambient image.
-/

namespace LeanWang
namespace Kari
namespace Hooper

open Turing

universe u v

/-- A `TM0` machine together with a finite transition-closed set containing its
default initial label. -/
structure SupportedMachine (Γ : Type u) (Λ : Type v)
    [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ] where
  machine : Turing.TM0.Machine Γ Λ
  states : Finset Λ
  supports : Turing.TM0.Supports machine (states : Set Λ)

namespace SupportedMachine

variable {Γ : Type u} {Λ : Type v}
variable [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]

/-- The genuine finite control-state type of a supported machine. -/
def State (S : SupportedMachine Γ Λ) :=
  {q : Λ // q ∈ S.states}

instance (S : SupportedMachine Γ Λ) : Inhabited S.State :=
  ⟨⟨default, S.supports.1⟩⟩

instance (S : SupportedMachine Γ Λ) : Fintype S.State := by
  change Fintype {q : Λ // q ∈ S.states}
  infer_instance

instance (S : SupportedMachine Γ Λ) : DecidableEq S.State :=
  fun a b => decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm

/-- Restrict every transition target to the support subtype. -/
def restrict (S : SupportedMachine Γ Λ) : Turing.TM0.Machine Γ S.State :=
  fun q a =>
    match S.machine q.1 a with
    | none => none
    | some (q', action) =>
        if hq' : q' ∈ S.states then some (⟨q', hq'⟩, action) else none

/-- Forget the proof that a restricted state belongs to the support. -/
def forgetState (S : SupportedMachine Γ Λ) : S.State → Λ :=
  Subtype.val

/-- Forget support proofs in a full-tape configuration. -/
def forgetCfg (S : SupportedMachine Γ Λ) (c : FullTM0.Cfg Γ S.State) :
    FullTM0.Cfg Γ Λ :=
  ⟨c.q.1, c.tape⟩

/-- Lift a supported ambient configuration to the restricted machine. -/
def liftCfg (S : SupportedMachine Γ Λ) (c : FullTM0.Cfg Γ Λ)
    (hq : c.q ∈ S.states) : FullTM0.Cfg Γ S.State :=
  ⟨⟨c.q, hq⟩, c.tape⟩

@[simp]
theorem forgetCfg_liftCfg (S : SupportedMachine Γ Λ) (c : FullTM0.Cfg Γ Λ)
    (hq : c.q ∈ S.states) :
    S.forgetCfg (S.liftCfg c hq) = c := by
  cases c
  rfl

/-- Forgetting finite-control proofs commutes with one full-tape step. -/
theorem step_forgetCfg (S : SupportedMachine Γ Λ)
    (c : FullTM0.Cfg Γ S.State) :
    (FullTM0.step S.restrict c).map S.forgetCfg =
      FullTM0.step S.machine (S.forgetCfg c) := by
  rcases c with ⟨q, T⟩
  simp only [FullTM0.step, forgetCfg, FullTM0.Tape.read_eq]
  cases h : S.machine q.1 (T 0) with
  | none => simp [restrict, h]
  | some result =>
      rcases result with ⟨q', action⟩
      have htransition : (q', action) ∈ S.machine q.1 (T 0) := h
      have hq' : q' ∈ S.states := S.supports.2 htransition q.2
      cases action <;> simp [restrict, h, hq', forgetCfg]

/-- Forgetting finite-control proofs commutes with every finite iterate. -/
theorem iterate_forgetCfg (S : SupportedMachine Γ Λ)
    (n : Nat) (c : FullTM0.Cfg Γ S.State) :
    (Dynamics.iterate (FullTM0.step S.restrict) n c).map S.forgetCfg =
      Dynamics.iterate (FullTM0.step S.machine) n (S.forgetCfg c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Dynamics.iterate_succ, Dynamics.iterate_succ, ← ih]
      cases h : Dynamics.iterate (FullTM0.step S.restrict) n c with
      | none => simp
      | some d => simpa [h] using S.step_forgetCfg d

/-- A restricted configuration survives `n` steps exactly when its ambient
image does. -/
theorem survives_forgetCfg_iff (S : SupportedMachine Γ Λ)
    (c : FullTM0.Cfg Γ S.State) (n : Nat) :
    Dynamics.Survives (FullTM0.step S.restrict) c n ↔
      Dynamics.Survives (FullTM0.step S.machine) (S.forgetCfg c) n := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨S.forgetCfg d, ?_⟩
    have h := S.iterate_forgetCfg n c
    simpa [hd] using h.symm
  · rintro ⟨d, hd⟩
    cases hrestricted : Dynamics.iterate (FullTM0.step S.restrict) n c with
    | none =>
        have h := S.iterate_forgetCfg n c
        rw [hrestricted] at h
        simp only [Option.map_none] at h
        rw [← h] at hd
        simp at hd
    | some e => exact ⟨e, hrestricted⟩

/-- Restricting finite control preserves immortality from each supported
configuration. -/
theorem immortalFrom_forgetCfg_iff (S : SupportedMachine Γ Λ)
    (c : FullTM0.Cfg Γ S.State) :
    FullTM0.ImmortalFrom S.restrict c ↔
      FullTM0.ImmortalFrom S.machine (S.forgetCfg c) := by
  simp only [FullTM0.ImmortalFrom, Dynamics.ImmortalFrom]
  exact forall_congr' fun n => S.survives_forgetCfg_iff c n

/-- The restricted machine is immortal exactly when the ambient machine has an
immortal configuration whose initial label belongs to the chosen support. -/
theorem immortal_restrict_iff (S : SupportedMachine Γ Λ) :
    FullTM0.Immortal S.restrict ↔
      ∃ c : FullTM0.Cfg Γ Λ,
        c.q ∈ S.states ∧ FullTM0.ImmortalFrom S.machine c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨S.forgetCfg c, c.q.2, (S.immortalFrom_forgetCfg_iff c).1 hc⟩
  · rintro ⟨c, hq, hc⟩
    let lifted := S.liftCfg c hq
    refine ⟨lifted, (S.immortalFrom_forgetCfg_iff lifted).2 ?_⟩
    simpa [lifted] using hc

end SupportedMachine

end Hooper
end Kari
end LeanWang
