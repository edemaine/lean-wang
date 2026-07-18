/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlParentEmbedding
import LeanWang.Kari.Hooper.CounterControlFiniteConverse

/-!
# Continuing a resumed parent command from its exact found state

The parent-embedding law starts at a resumed generated search.  Its search
phase is not part of the remaining Hooper-specific geometry: the converse
Basic Lemma already says that every finite generated search either reaches
its exact advertised found configuration or halts.  On an immortal orbit,
the halting branch is impossible.

This file removes that search phase from the outstanding obligation.  A
`FoundParentEmbeddingOutcome` starts at the exact `successCfg`, with the same
outer tape moved by the known gap and with no normalization in between.  The
remaining `FoundParentContinuationLaw` therefore asks only for the finite raw
command continuation and its tape-coordinate classification:

* reach a bounded logical core which strictly contains the resumed gap; or
* finish an already-running cleanup chain at a strictly larger search.

Either outcome composes with exact search resolution to give
`ResumedParentEmbeddingLaw`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlParentContinuation

open Turing
open BoundedMarkerProgram CounterControlPlan FramedMarkerTape
open CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlPrefixResume
open CounterControlParentEmbedding
open CounterControlPrefixInstructionResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The exact advertised endpoint of a genuine generated search.  Its tape
is the original outer tape moved by the known finite gap, without any write. -/
def foundCfg {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  (searchSystem base c).successCfg
    current.search current.outer current.distance

/-- On an immortal orbit, the converse Basic Lemma resolves every genuine
generated search to its exact advertised found configuration. -/
theorem reaches_foundCfg_of_immortal
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      current.cfg (foundCfg current) := by
  rcases CounterControlFiniteConverse.resolves_all
      base c current.distance current.search current.outer current.gap with
    hfound | hhalts
  · simpa [GenuineSearch.cfg, foundCfg, searchSystem] using hfound
  · have hnot :=
      (FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c) current.cfg).mp himmortal
    exact False.elim (hnot (by
      simpa [GenuineSearch.cfg, searchSystem] using hhalts))

/-- Exact search resolution also transports immortality to the found state,
so the finite continuation may eliminate its own terminal branches. -/
theorem immortalFrom_foundCfg
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg) :
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      (foundCfg current) := by
  have hreach := reaches_foundCfg_of_immortal current himmortal
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-! ## The finite continuation obligation -/

/-- Parent-embedding outcomes measured from the exact found configuration of
the resumed search.  This differs from `ParentEmbeddingOutcome` only in the
starting point of its reachability witnesses. -/
inductive FoundParentEmbeddingOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
  | logical (core : LogicalCore base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) core.cfg)
      (strictly_inside : current.distance < layoutEnd core.registers)
  | nextSearch (next : GenuineSearch base c)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) next.cfg)
      (distance_lt : current.distance < next.distance)

namespace FoundParentEmbeddingOutcome

/-- Prepending exact search resolution turns a found-state classification
into the parent-embedding classification expected by prefix totality. -/
def toParentEmbeddingOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    (outcome : FoundParentEmbeddingOutcome current)
    (hfound : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      current.cfg (foundCfg current)) :
    ParentEmbeddingOutcome current := by
  cases outcome with
  | logical core htail hinside =>
      exact .logical ⟨core, hfound.trans htail, hinside⟩
  | nextSearch next htail hdistance =>
      exact .resumed next ⟨hfound.trans htail, hdistance⟩

end FoundParentEmbeddingOutcome

/-- The remaining operational theorem after the generic search phase has
been discharged.  The structured resume remains in the quantification so a
proof can use its represented collision core, selected tag, direction, and
exact `limit - 1` gap.  Only the reachability witnesses begin at the exact
found state. -/
def FoundParentContinuationLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ {frame : PrefixEnvelope}
      {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
      (resumed : PrefixResumedSearch base c frame start),
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next) →
      Nonempty (FoundParentEmbeddingOutcome resumed.next)

/-- A proof of the finite found-state continuation law supplies the original
resumed-parent embedding law. -/
theorem resumedParentEmbeddingLaw_of_foundParentContinuationLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaw : FoundParentContinuationLaw base c) :
    ResumedParentEmbeddingLaw base c := by
  intro frame start resumed himmortal
  have hfound := reaches_foundCfg_of_immortal resumed.next himmortal
  have himmortalFound := immortalFrom_foundCfg resumed.next himmortal
  rcases hlaw resumed himmortalFound with ⟨outcome⟩
  exact ⟨outcome.toParentEmbeddingOutcome hfound⟩

end

end CounterControlParentContinuation
end Hooper
end Kari
end LeanWang
