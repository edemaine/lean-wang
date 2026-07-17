/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SearchGeometry

/-!
# Hooper's Basic Lemma

Appendix VII of Hooper's immortality construction replaces every unbounded
search by a bounded search.  When the bound is exhausted, the machine launches
a nested canonical computation in the remaining gap.  Reaching the far
boundary unwinds that computation, restores the outer tape, and resumes the
original search one cell closer to its target.

This file isolates the induction behind that argument from the eventual
transition table.  `NestingLaws` states the four local obligations of a
concrete implementation: nearby searches succeed directly; distant searches
launch a frame; an immortal canonical computation grows a well-formed frame to
its boundary, assuming all strictly shorter searches work; and boundary
cleanup restores the outer search one cell closer.  The theorem
`NestingLaws.basicLemma` proves that every finite search succeeds by strong
induction on its gap.

Storing an entire outer tape in `Frame` is only proof bookkeeping.  The
compiled machine will store a finite return tag and recover the tape through
the concrete frame invariant.
-/

namespace LeanWang
namespace Kari
namespace Hooper

open Turing

universe u v w

/-- Logical data saved about one suspended outer search. -/
structure Frame (Γ : Type u) (Search : Type w) where
  saved : Search
  outer : FullTM0.Tape Γ
  distance : Nat

/-- The typed interface between Hooper's search induction and a concrete
full-tape Turing machine. -/
structure SearchSystem (Γ : Type u) (Λ : Type v) (Search : Type w)
    [Inhabited Γ] [Inhabited Λ] where
  machine : Turing.TM0.Machine Γ Λ
  searchState : Search → Λ
  successState : Search → Λ
  direction : Search → Turing.Dir
  radius : Search → Nat
  isBlank : Γ → Prop
  isMark : Γ → Prop
  nestedAt : Frame Γ Search → FullTM0.Cfg Γ Λ → Prop
  boundaryAt : Frame Γ Search → FullTM0.Cfg Γ Λ → Prop

namespace SearchSystem

variable {Γ : Type u} {Λ : Type v} {Search : Type w}
variable [Inhabited Γ] [Inhabited Λ]

/-- A search poised at the first cell of its gap. -/
def startCfg (S : SearchSystem Γ Λ Search) (s : Search)
    (T : FullTM0.Tape Γ) : FullTM0.Cfg Γ Λ :=
  ⟨S.searchState s, T⟩

/-- The successful configuration after moving the head to the target marker. -/
def successCfg (S : SearchSystem Γ Λ Search) (s : Search)
    (T : FullTM0.Tape Γ) (k : Nat) : FullTM0.Cfg Γ Λ :=
  ⟨S.successState s, T.moveN (S.direction s) k⟩

/-- Every search with a gap of exactly `k` reaches its target without changing
the absolute tape contents. -/
def Solves (S : SearchSystem Γ Λ Search) (k : Nat) : Prop :=
  ∀ (s : Search) (T : FullTM0.Tape Γ),
    SearchGap S.isBlank S.isMark T (S.direction s) k →
      FullTM0.Reaches S.machine (S.startCfg s T) (S.successCfg s T k)

end SearchSystem

variable {Γ : Type u} {Λ : Type v} {Search : Type w}
variable [Inhabited Γ] [Inhabited Λ]

/-- The local correctness obligations for Hooper's nested bounded-search
transformation.  `CoreImmortal` says that the canonical computation launched
inside a failed search grows forever. -/
structure NestingLaws (S : SearchSystem Γ Λ Search) (CoreImmortal : Prop) where
  /-- A target within the local radius is found without nesting. -/
  direct : ∀ {s T k},
    SearchGap S.isBlank S.isMark T (S.direction s) k →
      k ≤ S.radius s →
        FullTM0.Reaches S.machine (S.startCfg s T) (S.successCfg s T k)
  /-- A more distant target causes a well-formed nested computation to be
  launched inside the outer gap. -/
  launch : ∀ {s T k},
    SearchGap S.isBlank S.isMark T (S.direction s) k →
      S.radius s < k →
        ∃ c, FullTM0.Reaches S.machine (S.startCfg s T) c ∧
          S.nestedAt ⟨s, T, k⟩ c
  /-- Assuming all shorter searches succeed, an immortal canonical computation
  eventually reaches the saved frame's far boundary. -/
  grow : ∀ {frame c},
    CoreImmortal →
      (∀ j < frame.distance, S.Solves j) →
        S.nestedAt frame c →
          ∃ boundary, FullTM0.Reaches S.machine c boundary ∧
            S.boundaryAt frame boundary
  /-- Cleanup restores the outer tape and resumes the saved search exactly one
  cell closer to its target. -/
  unwind : ∀ {frame boundary},
    S.boundaryAt frame boundary →
      FullTM0.Reaches S.machine boundary
        (S.startCfg frame.saved
          (frame.outer.move (S.direction frame.saved)))

namespace NestingLaws

variable {S : SearchSystem Γ Λ Search} {CoreImmortal : Prop}

/-- **Hooper's Basic Lemma.** Under the four nesting laws, immortality of the
canonical computation makes every finite left- or right-moving search find its
target.  The proof is the simultaneous strong induction on search distance
described in Appendix VII. -/
theorem basicLemma (L : NestingLaws S CoreImmortal) (hcore : CoreImmortal) :
    ∀ k, S.Solves k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro s T hgap
      by_cases hnear : k ≤ S.radius s
      · exact L.direct hgap hnear
      · have hfar : S.radius s < k := Nat.lt_of_not_ge hnear
        rcases L.launch hgap hfar with ⟨nested, hlaunch, hnested⟩
        rcases L.grow hcore (fun j hj => ih j hj) hnested with
          ⟨boundary, hgrow, hboundary⟩
        have hunwind := L.unwind hboundary
        have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hfar
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
        have htail : SearchGap S.isBlank S.isMark
            (T.move (S.direction s)) (S.direction s) j :=
          hgap.tail
        have hshort := ih j (Nat.lt_succ_self j) s
          (T.move (S.direction s)) htail
        have hall := hlaunch.trans (hgrow.trans (hunwind.trans hshort))
        simpa [FullTM0.Reaches, StateTransition.Reaches, SearchSystem.successCfg,
          FullTM0.Tape.move_moveN] using hall

end NestingLaws

end Hooper
end Kari
end LeanWang
