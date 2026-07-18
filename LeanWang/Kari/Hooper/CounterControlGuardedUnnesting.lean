/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedSearch
import LeanWang.Kari.Hooper.CounterControlLongSearchMortality

/-!
# Global unnesting through guarded returned searches

The shared return dispatcher supplies a stable one-cell guard behind every
generated search which it resumes.  This file factors the remaining global
argument through that invariant.

There are two local operational obligations.  An arbitrary immortal genuine
search must eventually reach some guarded returned search, and an immortal
guarded search must eventually reach a guarded search with a strictly larger
gap.  Neither obligation mentions iteration or the uniform long-search bound.
Once they are available, strict guarded unnesting can be iterated and the
long-search mortality theorem rules out every arbitrary immortal orbit.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedUnnesting

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch

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

/-! ## The two local laws -/

/-- A guarded returned search reached from an arbitrary genuine search. -/
structure EntersGuardedSearch
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (next : GuardedSearch base c) : Prop where
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    current.cfg next.current.cfg

/-- Normalization obligation for the first, possibly unguarded, generated
search on an arbitrary immortal orbit.  No distance comparison is needed at
this first transition. -/
def GuardedEntryLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GenuineSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      current.cfg →
      ∃ next : GuardedSearch base c, EntersGuardedSearch current next

/-- A first-entry transition which does not lose the genuine gap already
seen.  This stronger form is stable enough to alternate an unguarded replay
search with the next shared-return guard. -/
structure MonotoneGuardedEntry
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (next : GuardedSearch base c) : Prop where
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    current.cfg next.current.cfg
  distance_le : current.distance ≤ next.current.distance

/-- Every immortal genuine search eventually returns to the guarded phase
without decreasing its known finite gap. -/
def MonotoneGuardedEntryLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GenuineSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      current.cfg →
      ∃ next : GuardedSearch base c, MonotoneGuardedEntry current next

/-- Forgetting the distance comparison gives the ordinary guarded-entry
law. -/
theorem guardedEntryLaw_of_monotoneGuardedEntryLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaw : MonotoneGuardedEntryLaw base c) :
    GuardedEntryLaw base c := by
  intro current himmortal
  rcases hlaw current himmortal with ⟨next, hnext⟩
  exact ⟨next, ⟨hnext.reaches⟩⟩

/-- A guarded search exposes a strictly larger genuine search, which may be
an intermediate replay search rather than a shared-return search. -/
structure GuardedEscapes
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) (next : GenuineSearch base c) : Prop where
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    current.current.cfg next.cfg
  distance_lt : current.current.distance < next.distance

/-- Local strict-progress obligation before restoring the shared-return
guard. -/
def GuardedEscapeLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GuardedSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      current.current.cfg →
      ∃ next : GenuineSearch base c, GuardedEscapes current next

/-- One strict unnesting transition between guarded returned searches. -/
structure GuardedUnnests
    {base : Nat} {c : Nat.Partrec.Code}
    (current next : GuardedSearch base c) : Prop where
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    current.current.cfg next.current.cfg
  distance_lt : current.current.distance < next.current.distance

/-- Stable local unnesting obligation after the first shared return. -/
def GuardedUnnestingLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GuardedSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      current.current.cfg →
      ∃ next : GuardedSearch base c, GuardedUnnests current next

/-- Strict escape followed by monotone guarded re-entry is one stable
guarded unnesting step. -/
theorem guardedUnnestingLaw_of_escape_and_monotoneEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hentry : MonotoneGuardedEntryLaw base c)
    (hescape : GuardedEscapeLaw base c) :
    GuardedUnnestingLaw base c := by
  intro current himmortal
  rcases hescape current himmortal with ⟨middle, hmiddle⟩
  have himmortalMiddle := immortalFrom_of_reaches base c
    himmortal hmiddle.reaches
  rcases hentry middle himmortalMiddle with ⟨next, hnext⟩
  exact ⟨next, ⟨hmiddle.reaches.trans hnext.reaches,
    hmiddle.distance_lt.trans_le hnext.distance_le⟩⟩

/-! ## Iteration -/

/-- Iterating strict guarded unnesting increases the gap by any prescribed
number of cells. -/
theorem exists_iterated_guardedUnnesting
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaw : GuardedUnnestingLaw base c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.current.cfg) :
    ∀ steps : Nat, ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        current.current.cfg next.current.cfg ∧
      current.current.distance + steps ≤ next.current.distance := by
  intro steps
  induction steps with
  | zero =>
      exact ⟨current, Relation.ReflTransGen.refl, by omega⟩
  | succ steps ih =>
      rcases ih with ⟨middle, hmiddle, hdistance⟩
      have himmortalMiddle := immortalFrom_of_reaches base c
        himmortal hmiddle
      rcases hlaw middle himmortalMiddle with ⟨next, hnext⟩
      refine ⟨next, hmiddle.trans hnext.reaches, ?_⟩
      change Nat.succ (current.current.distance + steps) ≤
        next.current.distance
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt hdistance hnext.distance_lt)

/-- Every arbitrary immortal orbit first reaches a guarded returned search,
provided the entry law holds. -/
theorem exists_reached_guardedSearch_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hentry : GuardedEntryLaw base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start next.current.cfg := by
  rcases exists_reachedGenuineSearch_of_immortalFrom
      base c hmortal start himmortal with ⟨first⟩
  have himmortalFirst := immortalFrom_of_reaches base c
    himmortal first.reaches
  rcases hentry first.toGenuineSearch himmortalFirst with ⟨next, hnext⟩
  exact ⟨next, first.reaches.trans hnext.reaches⟩

/-- Entry followed by strict guarded iteration reaches genuine searches of
unbounded distance on every arbitrary immortal orbit. -/
theorem reaches_unbounded_guardedSearch_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hentry : GuardedEntryLaw base c)
    (hlaw : GuardedUnnestingLaw base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∀ bound : Nat, ∃ current : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start current.current.cfg ∧
      bound < current.current.distance := by
  intro bound
  rcases exists_reached_guardedSearch_of_immortalFrom
      base c hmortal hentry start himmortal with ⟨first, hfirst⟩
  have himmortalFirst := immortalFrom_of_reaches base c himmortal hfirst
  rcases exists_iterated_guardedUnnesting base c hlaw first
      himmortalFirst (bound + 1) with ⟨current, htail, hdistance⟩
  refine ⟨current, hfirst.trans htail, ?_⟩
  omega

/-- The two guarded operational laws imply mortality of every arbitrary
controller configuration whenever the fixed source computation halts. -/
theorem haltsFrom_of_guardedUnnestingLaws
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hentry : GuardedEntryLaw base c)
    (hlaw : GuardedUnnestingLaw base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start := by
  rcases FullTM0.HaltsFrom.or_immortalFrom
      (CounterControlNestingBridge.machine base c) start with
    hhalts | himmortal
  · exact hhalts
  · rcases CounterControlLongSearchMortality.exists_bound_halts_search
        base c hmortal with ⟨bound, hbound⟩
    rcases reaches_unbounded_guardedSearch_of_immortalFrom
        base c hmortal hentry hlaw start himmortal bound with
      ⟨current, hreach, hlarge⟩
    have hsearchHalts : FullTM0.HaltsFrom
        (CounterControlNestingBridge.machine base c) current.current.cfg :=
      hbound hlarge current.current.gap
    have hstartHalts := FullTM0.HaltsFrom.of_reaches hreach hsearchHalts
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c) start).mp
          himmortal hstartHalts)

/-- Consumer-facing form of the alternating argument: monotone guarded
re-entry supplies both the initial guard and guard restoration after every
strict intermediate replay. -/
theorem haltsFrom_of_escape_and_monotoneEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hentry : MonotoneGuardedEntryLaw base c)
    (hescape : GuardedEscapeLaw base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start :=
  haltsFrom_of_guardedUnnestingLaws base c hmortal
    (guardedEntryLaw_of_monotoneGuardedEntryLaw base c hentry)
    (guardedUnnestingLaw_of_escape_and_monotoneEntry
      base c hentry hescape) start

end

end CounterControlGuardedUnnesting
end Hooper
end Kari
end LeanWang
