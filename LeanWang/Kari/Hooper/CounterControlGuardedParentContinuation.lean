/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedResume
import LeanWang.Kari.Hooper.CounterControlGuardedUnnesting
import LeanWang.Kari.Hooper.CounterControlParentContinuation

/-!
# Found-state continuation of a guarded parent search

A guarded generated search first resolves to its exact advertised found
configuration.  Its finite raw-command continuation has two useful outcomes:

* it reaches a represented logical core which strictly contains the old gap;
* it reaches another guarded returned search with a strictly larger gap.

The first outcome is converted to the second by finite-prefix totality.  This
file performs that common assembly once, leaving command-family modules to
prove only the exact found-state classification.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedParentContinuation

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedResume CounterControlGuardedUnnesting
open CounterControlParentEmbedding CounterControlParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- Useful continuations measured from the exact found configuration of a
guarded generated search. -/
inductive FoundGuardedParentOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) : Type where
  | logical (core : LogicalCore base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current) core.cfg)
      (strictly_inside : current.current.distance <
        FramedMarkerTape.layoutEnd core.registers)
  | nextSearch (next : GuardedSearch base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current) next.current.cfg)
      (distance_lt : current.current.distance < next.current.distance)

/-- A found-state strict escape may either already have the structured
parent outcome above or stop at a strictly larger intermediate genuine
search (for example the matching outward validation replay). -/
inductive FoundGuardedEscapeOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) : Type where
  | parent (outcome : FoundGuardedParentOutcome current)
  | nextSearch (next : GenuineSearch base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current) next.cfg)
      (distance_lt : current.current.distance < next.distance)

/-- Exact finite-continuation obligation for every guarded generated command.
Search resolution itself is excluded from the law. -/
def FoundGuardedParentContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GuardedSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) →
      Nonempty (FoundGuardedParentOutcome current)

/-- The weaker first-entry classification starts from an arbitrary genuine
search.  A containing inequality is unnecessary here: reaching either a
represented logical core or a shared-return guard is enough to enter the
stable guarded phase. -/
inductive FoundGuardedEntryOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
  | logical (core : LogicalCore base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) core.cfg)
  | nextSearch (next : GuardedSearch base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) next.current.cfg)

/-- Exact finite-continuation obligation for the first, possibly unguarded,
generated search on an immortal orbit. -/
def FoundGuardedEntryContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GenuineSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      (foundCfg current) →
      Nonempty (FoundGuardedEntryOutcome current)

/-- First-entry outcome retaining the comparison needed to alternate with a
strict but temporarily unguarded replay search. -/
inductive FoundMonotoneGuardedEntryOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
  | logical (core : LogicalCore base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) core.cfg)
      (inside : current.distance ≤
        FramedMarkerTape.layoutEnd core.registers)
  | nextSearch (next : GuardedSearch base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) next.current.cfg)
      (distance_le : current.distance ≤ next.current.distance)

/-- Exact monotone continuation obligation for an arbitrary genuine search. -/
def FoundMonotoneGuardedEntryContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GenuineSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      (foundCfg current) →
      Nonempty (FoundMonotoneGuardedEntryOutcome current)

/-- A found-state outcome supplies one strict guarded unnesting step.  In the
logical branch, finite-prefix totality cleans the represented core, resumes
its saved caller, and the shared return supplies the guard. -/
theorem guardedUnnests_of_foundOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.current.cfg)
    (outcome : FoundGuardedParentOutcome current) :
    ∃ next : GuardedSearch base c, GuardedUnnests current next := by
  have hfound := reaches_foundCfg_of_immortal current.current himmortal
  cases outcome with
  | nextSearch next htail hdistance =>
      exact ⟨next, ⟨hfound.trans htail, hdistance⟩⟩
  | logical core htail hinside =>
      have himmortalFound := immortalFrom_of_reaches base c
        himmortal hfound
      have himmortalCore := immortalFrom_of_reaches base c
        himmortalFound htail
      rcases core.reaches_resumed_of_immortal base c hmortal
          himmortalCore with ⟨resumed⟩
      let next : GuardedSearch base c :=
        CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
      refine ⟨next, ⟨hfound.trans (htail.trans resumed.reaches), ?_⟩⟩
      exact hinside.trans_le (core.layoutEnd_le_resumedDistance resumed)

/-- The exact found-state continuation law implies the stable guarded
unnesting law consumed by the global iteration theorem. -/
theorem guardedUnnestingLaw_of_foundGuardedParentContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : FoundGuardedParentContinuationLaw base c) :
    GuardedUnnestingLaw base c := by
  intro current himmortal
  have himmortalFound := immortalFrom_foundCfg current.current himmortal
  rcases hlaw current himmortalFound with ⟨outcome⟩
  exact guardedUnnests_of_foundOutcome base c hmortal current
    himmortal outcome

/-- Either form of found-state escape supplies a strict genuine search from
the guarded entry. -/
theorem guardedEscapes_of_foundOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.current.cfg)
    (outcome : FoundGuardedEscapeOutcome current) :
    ∃ next : GenuineSearch base c, GuardedEscapes current next := by
  cases outcome with
  | nextSearch next htail hdistance =>
      have hfound := reaches_foundCfg_of_immortal current.current himmortal
      exact ⟨next, ⟨hfound.trans htail, hdistance⟩⟩
  | parent parent =>
      rcases guardedUnnests_of_foundOutcome base c hmortal current
          himmortal parent with ⟨next, hnext⟩
      exact ⟨next.current, ⟨hnext.reaches, hnext.distance_lt⟩⟩

/-- A found-state escape law implies the local strict escape law consumed by
the alternating global theorem. -/
theorem guardedEscapeLaw_of_foundContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : ∀ current : GuardedSearch base c,
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
        (foundCfg current.current) →
        Nonempty (FoundGuardedEscapeOutcome current)) :
    GuardedEscapeLaw base c := by
  intro current himmortal
  have himmortalFound := immortalFrom_foundCfg current.current himmortal
  rcases hlaw current himmortalFound with ⟨outcome⟩
  exact guardedEscapes_of_foundOutcome base c hmortal current
    himmortal outcome

/-- A first-entry found-state outcome reaches the stable guarded phase. -/
theorem entersGuardedSearch_of_foundEntryOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg)
    (outcome : FoundGuardedEntryOutcome current) :
    ∃ next : GuardedSearch base c, EntersGuardedSearch current next := by
  have hfound := reaches_foundCfg_of_immortal current himmortal
  cases outcome with
  | nextSearch next htail =>
      exact ⟨next, ⟨hfound.trans htail⟩⟩
  | logical core htail =>
      have himmortalFound := immortalFrom_of_reaches base c
        himmortal hfound
      have himmortalCore := immortalFrom_of_reaches base c
        himmortalFound htail
      rcases core.reaches_resumed_of_immortal base c hmortal
          himmortalCore with ⟨resumed⟩
      let next : GuardedSearch base c :=
        CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
      exact ⟨next, ⟨hfound.trans (htail.trans resumed.reaches)⟩⟩

/-- The weaker exact found-state law supplies the initial guarded-entry law
consumed by global iteration. -/
theorem guardedEntryLaw_of_foundGuardedEntryContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : FoundGuardedEntryContinuationLaw base c) :
    GuardedEntryLaw base c := by
  intro current himmortal
  have himmortalFound := immortalFrom_foundCfg current himmortal
  rcases hlaw current himmortalFound with ⟨outcome⟩
  exact entersGuardedSearch_of_foundEntryOutcome base c hmortal current
    himmortal outcome

/-- A comparison-preserving found-state outcome reaches the guarded phase
without decreasing the known gap. -/
theorem monotoneGuardedEntry_of_foundOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg)
    (outcome : FoundMonotoneGuardedEntryOutcome current) :
    ∃ next : GuardedSearch base c, MonotoneGuardedEntry current next := by
  have hfound := reaches_foundCfg_of_immortal current himmortal
  cases outcome with
  | nextSearch next htail hdistance =>
      exact ⟨next, ⟨hfound.trans htail, hdistance⟩⟩
  | logical core htail hinside =>
      have himmortalFound := immortalFrom_of_reaches base c
        himmortal hfound
      have himmortalCore := immortalFrom_of_reaches base c
        himmortalFound htail
      rcases core.reaches_resumed_of_immortal base c hmortal
          himmortalCore with ⟨resumed⟩
      let next : GuardedSearch base c :=
        CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
      refine ⟨next, ⟨hfound.trans (htail.trans resumed.reaches), ?_⟩⟩
      exact hinside.trans (core.layoutEnd_le_resumedDistance resumed)

/-- The exact comparison-preserving continuation law supplies monotone
guarded re-entry. -/
theorem monotoneGuardedEntryLaw_of_foundContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : FoundMonotoneGuardedEntryContinuationLaw base c) :
    MonotoneGuardedEntryLaw base c := by
  intro current himmortal
  have himmortalFound := immortalFrom_foundCfg current himmortal
  rcases hlaw current himmortalFound with ⟨outcome⟩
  exact monotoneGuardedEntry_of_foundOutcome base c hmortal current
    himmortal outcome

end

end CounterControlGuardedParentContinuation
end Hooper
end Kari
end LeanWang
