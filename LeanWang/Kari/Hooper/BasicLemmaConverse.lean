/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.BasicLemma

/-!
# The converse to Hooper's Basic Lemma

For the converse direction of Hooper's construction, an immortal computation
must not be able to remain forever inside a bounded-search controller.  The
argument in Appendix VII is again a strong induction on the finite search gap,
but its conclusion is a dichotomy: the search reaches its exact success
configuration, or the whole machine reaches a terminal configuration.

This file isolates that induction from the concrete transition table.
`ConverseNestingLaws` records the four local obligations.  Nearby targets are
found directly; a distant target launches a nested frame; the nested core
either restores that frame at its boundary or halts, provided every strictly
shorter search already resolves; and a restored boundary unwinds to the
outer search one cell closer to its target.
-/

namespace LeanWang
namespace Kari
namespace Hooper

open Turing

universe u v w

namespace FullTM0

variable {Γ : Type u} {Λ : Type v}
variable [Inhabited Γ] [Inhabited Λ]

/-- The full-tape machine reaches a configuration with no outgoing step. -/
def HaltsFrom (M : Turing.TM0.Machine Γ Λ) (start : Cfg Γ Λ) : Prop :=
  ∃ terminal, Reaches M start terminal ∧ step M terminal = none

namespace HaltsFrom

omit [Inhabited Γ] in
/-- Prepending a finite execution prefix to a halting computation preserves
halting. -/
theorem of_reaches {M : Turing.TM0.Machine Γ Λ} {start current : Cfg Γ Λ}
    (hprefix : Reaches M start current) (hhalts : HaltsFrom M current) :
    HaltsFrom M start := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  exact ⟨terminal, hprefix.trans hterminalReach, hterminal⟩

omit [Inhabited Γ] in
/-- Every full-tape computation either reaches a terminal configuration or
survives for arbitrarily many steps. -/
theorem or_immortalFrom (M : Turing.TM0.Machine Γ Λ) (start : Cfg Γ Λ) :
    HaltsFrom M start ∨ ImmortalFrom M start := by
  classical
  by_cases hdom : (StateTransition.eval (step M) start).Dom
  · left
    rcases Part.dom_iff_mem.mp hdom with ⟨terminal, hterminal⟩
    rcases StateTransition.mem_eval.mp hterminal with ⟨hreach, hstep⟩
    exact ⟨terminal, hreach, hstep⟩
  · right
    exact (Dynamics.not_eval_dom_iff_immortalFrom _ _).mp hdom

omit [Inhabited Γ] in
/-- Full-tape immortality from a fixed configuration is exactly the absence
of a reachable terminal configuration. -/
theorem immortalFrom_iff_not (M : Turing.TM0.Machine Γ Λ)
    (start : Cfg Γ Λ) :
    ImmortalFrom M start ↔ ¬ HaltsFrom M start := by
  constructor
  · intro himmortal
    rintro ⟨terminal, hreach, hterminal⟩
    rcases Dynamics.exists_iterate_eq_some_of_reaches hreach with ⟨n, hn⟩
    rcases himmortal (n + 1) with ⟨next, hnext⟩
    simp [Dynamics.iterate_succ, hn, hterminal] at hnext
  · intro hnot
    rcases or_immortalFrom M start with hhalts | himmortal
    · exact False.elim (hnot hhalts)
    · exact himmortal

end HaltsFrom

/-- A finite execution either reaches the advertised continuation or exposes
a terminal configuration reachable from its starting point.  This is the
common outcome type of the converse bounded-search proofs. -/
abbrev ResolvesTo (M : Turing.TM0.Machine Γ Λ)
    (start finish : Cfg Γ Λ) : Prop :=
  Reaches M start finish ∨ HaltsFrom M start

namespace ResolvesTo

omit [Inhabited Γ] in
/-- An ordinary finite execution is a resolving execution. -/
theorem of_reaches {M : Turing.TM0.Machine Γ Λ} {start finish : Cfg Γ Λ}
    (h : Reaches M start finish) : ResolvesTo M start finish :=
  Or.inl h

omit [Inhabited Γ] in
/-- A terminal outcome resolves toward every advertised continuation. -/
theorem of_halts {M : Turing.TM0.Machine Γ Λ} {start finish : Cfg Γ Λ}
    (h : HaltsFrom M start) : ResolvesTo M start finish :=
  Or.inr h

omit [Inhabited Γ] in
/-- Resolving executions compose like ordinary reachability. -/
theorem trans {M : Turing.TM0.Machine Γ Λ}
    {start middle finish : Cfg Γ Λ}
    (h₁ : ResolvesTo M start middle) (h₂ : ResolvesTo M middle finish) :
    ResolvesTo M start finish := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr (HaltsFrom.of_reaches h₁ h₂)
  · exact Or.inr h₁

omit [Inhabited Γ] in
/-- Prepending an ordinary finite execution to a resolving execution. -/
theorem trans_reaches {M : Turing.TM0.Machine Γ Λ}
    {start middle finish : Cfg Γ Λ}
    (h₁ : Reaches M start middle) (h₂ : ResolvesTo M middle finish) :
    ResolvesTo M start finish :=
  trans (of_reaches h₁) h₂

omit [Inhabited Γ] in
/-- Attach stable data to the successful side of a resolving execution. -/
theorem and_right {M : Turing.TM0.Machine Γ Λ}
    {start finish : Cfg Γ Λ} {P : Prop}
    (h : ResolvesTo M start finish) (hP : P) :
    (Reaches M start finish ∧ P) ∨ HaltsFrom M start :=
  h.imp (fun hreach => ⟨hreach, hP⟩) id

end ResolvesTo
end FullTM0

namespace SearchSystem

variable {Γ : Type u} {Λ : Type v} {Search : Type w}
variable [Inhabited Γ] [Inhabited Λ]

/-- Every genuine search gap of size `k` either reaches the exact successful
configuration without changing the absolute tape contents, or reaches a
terminal configuration of the whole machine. -/
def Resolves (S : SearchSystem Γ Λ Search) (k : Nat) : Prop :=
  ∀ (s : Search) (T : FullTM0.Tape Γ),
    SearchGap S.isBlank (S.isMark s) T (S.direction s) k →
      FullTM0.ResolvesTo S.machine (S.startCfg s T) (S.successCfg s T k)

end SearchSystem

variable {Γ : Type u} {Λ : Type v} {Search : Type w}
variable [Inhabited Γ] [Inhabited Λ]

/-- Local obligations for the converse bounded-search induction.

Unlike `NestingLaws.grow`, `core` makes no immortality assumption.  It says
that once every strictly shorter search is known to resolve, a launched nested
computation either restores its saved frame at the far boundary or halts. -/
structure ConverseNestingLaws (S : SearchSystem Γ Λ Search) where
  /-- A target within the local radius is found without nesting. -/
  direct : ∀ {s T k},
    SearchGap S.isBlank (S.isMark s) T (S.direction s) k →
      k ≤ S.radius s →
        FullTM0.Reaches S.machine (S.startCfg s T) (S.successCfg s T k)
  /-- A target outside the local radius launches a well-formed nested frame. -/
  launch : ∀ {s T k},
    SearchGap S.isBlank (S.isMark s) T (S.direction s) k →
      S.radius s < k →
        ∃ c, FullTM0.Reaches S.machine (S.startCfg s T) c ∧
          S.nestedAt ⟨s, T, k⟩ c
  /-- Assuming all shorter searches resolve, the nested core either reaches
  the saved frame's far boundary or reaches a terminal configuration. -/
  core : ∀ {frame c},
    (∀ j < frame.distance, S.Resolves j) →
      S.nestedAt frame c →
        (∃ boundary, FullTM0.Reaches S.machine c boundary ∧
          S.boundaryAt frame boundary) ∨
        FullTM0.HaltsFrom S.machine c
  /-- Boundary cleanup restores the outer tape and resumes the saved search
  exactly one cell closer to its target. -/
  unwind : ∀ {frame boundary},
    S.boundaryAt frame boundary →
      FullTM0.Reaches S.machine boundary
        (S.startCfg frame.saved
          (frame.outer.move (S.direction frame.saved)))

namespace ConverseNestingLaws

variable {S : SearchSystem Γ Λ Search}

/-- **Converse to Hooper's Basic Lemma.** Every finite search either finds its
target exactly or halts.  Thus no immortal orbit can remain forever inside a
bounded-search controller entered on a genuine finite gap. -/
theorem resolves (L : ConverseNestingLaws S) : ∀ k, S.Resolves k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro s T hgap
      by_cases hnear : k ≤ S.radius s
      · exact Or.inl (L.direct hgap hnear)
      · have hfar : S.radius s < k := Nat.lt_of_not_ge hnear
        rcases L.launch hgap hfar with ⟨nested, hlaunch, hnested⟩
        rcases L.core (fun j hj => ih j hj) hnested with
          (⟨boundary, hcore, hboundary⟩ | hcoreHalts)
        · have hunwind := L.unwind hboundary
          have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hfar
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
          have htail : SearchGap S.isBlank (S.isMark s)
              (T.move (S.direction s)) (S.direction s) j :=
            hgap.tail
          rcases ih j (Nat.lt_succ_self j) s
              (T.move (S.direction s)) htail with hsuccess | htailHalts
          · left
            have hall := hlaunch.trans (hcore.trans (hunwind.trans hsuccess))
            simpa [FullTM0.Reaches, StateTransition.Reaches,
              SearchSystem.successCfg, FullTM0.Tape.move_moveN] using hall
          · right
            exact FullTM0.HaltsFrom.of_reaches
              (hlaunch.trans (hcore.trans hunwind)) htailHalts
        · right
          exact FullTM0.HaltsFrom.of_reaches hlaunch hcoreHalts

end ConverseNestingLaws

end Hooper
end Kari
end LeanWang
