/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGlobalFrontier
import LeanWang.Kari.Hooper.CounterControlValidationRoundtrip
import LeanWang.Kari.Hooper.CounterControlLongSearchMortality

/-!
# Global unnesting on arbitrary immortal controller orbits

Validation reconstructs a tag-free finite counter prefix.  Its first
obstruction is enough to run the counter body and erase the core, but the
saved return tag is deliberately not assumed until the shared return
dispatcher reads it.  The first part of this file records the tape invariant
at that point: after the dispatcher erases the tag, the operational cleanup
tape has one genuine blank search gap all the way to the old obstruction.

The second part separates the remaining global argument from that local tape
geometry.  A `ClearedPrefixUnnestingLaw` says that an immortal generated
search eventually reaches a generated search with strictly larger gap.  Once
the body/cleanup theorem and the finite command continuations establish this
single law, ordinary induction makes reached genuine gaps unbounded.  The
uniform long-search mortality theorem then rules out the immortal orbit.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGlobalUnnesting

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlCleanupSemantics
open CounterControlArbitraryMortality
open CounterControlCommandContinuationMortality
open CounterControlGlobalFrontier

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## The cleared-prefix tape invariant -/

/-- Installing an arbitrary dummy tag at logical coordinate `0` does not
change the cleanup tape, because cleanup erases that coordinate.  This lets
the existing framed cleanup theorem be used without asserting that the
original tag-free core already carries the dummy tag. -/
private theorem afterTag_eq_afterTag_writeTag
    {spec : Spec numTags} (T : FullTM0.Tape (Symbol numTags)) :
    afterTag spec
        (writeLogical spec.growth T 0 (tagSymbol spec.returnTag)) =
      afterTag spec T := by
  funext position
  by_cases hposition : position = 0
  · subst position
    simp [afterTag, writeLogical, Function.update]
  simp only [afterTag, afterZero, afterOne, afterTwo, afterThree, afterFour,
    clearBoundary, writeLogical]
  simp [Function.update, hposition]

/-- A tag-free core, runway, and target can temporarily be tagged at logical
coordinate `0`.  The change is used only to invoke framed cleanup geometry;
the operational cleanup immediately erases it again. -/
private theorem represents_writeTag
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents spec.registers spec.growth T)
    (hrunway : ∀ position, layoutEnd spec.registers < position →
      position < spec.outerDistance →
        logicalTape spec.growth T position = blankSymbol)
    (htarget : spec.outerTarget.Matches
      (logicalTape spec.growth T spec.outerDistance)) :
    Represents spec
      (writeLogical spec.growth T 0 (tagSymbol spec.returnTag)) := by
  let U := writeLogical spec.growth T 0 (tagSymbol spec.returnTag)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [U] using
      (writeLogical_at spec.growth T 0 (tagSymbol spec.returnTag))
  · intro position hposition
    have hne : position + 1 ≠ 0 := by omega
    rw [show logicalTape spec.growth U (position + 1) =
        logicalTape spec.growth T (position + 1) by
      simpa [U] using writeLogical_of_ne spec.growth T 0 (position + 1)
        (tagSymbol spec.returnTag) hne]
    exact hcore.core position hposition
  · intro position hpast hbefore
    have hne : position ≠ 0 := by
      have hendPositive : 0 < layoutEnd spec.registers := by
        simp [layoutEnd]
      omega
    rw [show logicalTape spec.growth U position =
        logicalTape spec.growth T position by
      simpa [U] using writeLogical_of_ne spec.growth T 0 position
        (tagSymbol spec.returnTag) hne]
    exact hrunway position hpast hbefore
  · have hne : spec.outerDistance ≠ 0 := by
      have hpast := spec.core_before_target
      omega
    rw [show logicalTape spec.growth U spec.outerDistance =
        logicalTape spec.growth T spec.outerDistance by
      simpa [U] using writeLogical_of_ne spec.growth T 0 spec.outerDistance
        (tagSymbol spec.returnTag) hne]
    exact htarget

/-- Tag-free version of the operational cleanup identity.  Clearing the five
boundaries and then coordinate `0` is extensionally the same as clearing the
whole represented core prefix, even when coordinate `0` was arbitrary. -/
theorem afterTag_eq_cleanupTape_of_coreTarget
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents spec.registers spec.growth T)
    (hrunway : ∀ position, layoutEnd spec.registers < position →
      position < spec.outerDistance →
        logicalTape spec.growth T position = blankSymbol)
    (htarget : spec.outerTarget.Matches
      (logicalTape spec.growth T spec.outerDistance)) :
    afterTag spec T = cleanupTape spec T := by
  let U := writeLogical spec.growth T 0 (tagSymbol spec.returnTag)
  have hrep : Represents spec U :=
    represents_writeTag hcore hrunway htarget
  have hcleanup := afterTag_eq_cleanupTape hrep
  have hafter : afterTag spec U = afterTag spec T := by
    exact afterTag_eq_afterTag_writeTag T
  have hcleanupTape : cleanupTape spec U = cleanupTape spec T := by
    unfold cleanupTape
    apply congrArg (logicalTape spec.growth)
    funext position
    by_cases hprefix :
        0 ≤ position ∧ position ≤ layoutEnd spec.registers
    · simp [clearLogicalPrefix, hprefix]
    · have hposition : position ≠ 0 := by
        intro hzero
        subst position
        exact hprefix (by simp)
      have hphysical : physicalCoord spec.growth position ≠
          physicalCoord spec.growth 0 := by
        intro heq
        exact hposition (physicalCoord_injective spec.growth heq)
      have hphysicalZero : physicalCoord spec.growth position ≠ 0 := by
        simpa using hphysical
      simp [clearLogicalPrefix, hprefix, U, logicalTape_apply,
        writeLogical, Function.update, hphysicalZero]
  exact hafter.symm.trans (hcleanup.trans hcleanupTape)

/-- Once the shared return dispatcher erases the arbitrary tag cell, cleanup
exposes a genuine search gap from that cell to the old first obstruction.
This is the tape-level bridge needed by global unnesting. -/
theorem afterTag_searchGap_of_coreTarget
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents spec.registers spec.growth T)
    (hrunway : ∀ position, layoutEnd spec.registers < position →
      position < spec.outerDistance →
        logicalTape spec.growth T position = blankSymbol)
    (htarget : spec.outerTarget.Matches
      (logicalTape spec.growth T spec.outerDistance)) :
    SearchGap (fun symbol => symbol = blankSymbol) spec.outerTarget.Matches
      (afterTag spec T) spec.growth spec.outerDistance := by
  let U := writeLogical spec.growth T 0 (tagSymbol spec.returnTag)
  have hrep : Represents spec U :=
    represents_writeTag hcore hrunway htarget
  have hgap := afterTag_searchGap hrep
  rw [afterTag_eq_afterTag_writeTag T] at hgap
  exact hgap

/-! ## Reached genuine searches -/

/-- A generated search entry together with its exact finite matching gap. -/
structure GenuineSearch (base : Nat) (c : Nat.Partrec.Code) : Type where
  search : Search
  outer : FullTM0.Tape (Symbol numTags)
  distance : Nat
  gap : SearchGap (fun symbol => symbol = blankSymbol)
    (command base c search).target.Matches outer
    (command base c search).searchDirection distance

namespace GenuineSearch

/-- Concrete entry configuration of a packaged genuine generated search. -/
def cfg {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  (searchSystem base c).startCfg current.search current.outer

end GenuineSearch

/-- A genuine generated search known to lie on the orbit from `start`. -/
structure ReachedGenuineSearch (base : Nat) (c : Nat.Partrec.Code)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Type extends
    GenuineSearch base c where
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    start toGenuineSearch.cfg

/-- The older existential frontier is equivalent to the packaged reached
search used by the unnesting induction. -/
theorem reachedGenuineSearch_iff_frontier
    (base : Nat) (c : Nat.Partrec.Code)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) :
    Nonempty (ReachedGenuineSearch base c start) ↔
      GenuineSearchFrontier base c start := by
  constructor
  · rintro ⟨current⟩
    exact ⟨current.search, current.outer, current.distance,
      current.reaches, current.gap⟩
  · rintro ⟨search, outer, distance, hreach, hgap⟩
    exact ⟨ReachedGenuineSearch.mk
      ⟨search, outer, distance, hgap⟩ hreach⟩

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start finish) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) finish := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- The global frontier already guarantees at least one reached genuine
generated search on every arbitrary immortal orbit with mortal source. -/
theorem exists_reachedGenuineSearch_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    Nonempty (ReachedGenuineSearch base c start) := by
  rcases reaches_frontier_of_immortalFrom base c hmortal start himmortal with
    ⟨finish, hreach, hfrontier⟩
  cases hfrontier with
  | logical growth state hstate T =>
      have hsearch :=
        genuine_validationSearch_of_reachable_bounded_logical
          base c hmortal himmortal growth state hstate T hreach
      exact (reachedGenuineSearch_iff_frontier base c start).2 hsearch
  | search raw hraw T =>
      let search : Search := CounterControlCommandAt.rawTag raw hraw
      have hget : rawCommands.get search = raw :=
        CounterControlCommandAt.rawCommands_get_rawTag raw hraw
      have hsearchReach : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) start
          ((searchSystem base c).startCfg search T) := by
        change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          start ⟨CounterControlSearchSystem.commandOffset base c search, T⟩
        unfold CounterControlSearchSystem.commandOffset
        rw [hget]
        exact hreach
      rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
          base c hmortal
          (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
          himmortal hsearchReach with ⟨distance, hgap⟩
      exact ⟨ReachedGenuineSearch.mk
        ⟨search, T, distance, hgap⟩ hsearchReach⟩

/-! ## The one remaining local-to-global law -/

/-- One unnesting step clears the current finite core, resumes its generated
caller, and reaches a generated search whose genuine gap is strictly larger.
The reachability field, rather than mere global existence, lets the law be
iterated from any point of an immortal orbit. -/
structure ClearedPrefixUnnests {base : Nat} {c : Nat.Partrec.Code}
    (current next : GenuineSearch base c) : Prop where
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    current.cfg next.cfg
  distance_lt : current.distance < next.distance

/-- The precise operational obligation still to be discharged by the
tag-free prefix body/cleanup semantics and finite command-continuation
normalization. -/
def ClearedPrefixUnnestingLaw (base : Nat) (c : Nat.Partrec.Code) : Prop :=
  ∀ current : GenuineSearch base c,
    FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
      current.cfg →
      ∃ next : GenuineSearch base c, ClearedPrefixUnnests current next

/-- Iterating strict unnesting produces a later genuine search whose distance
has increased by any prescribed number. -/
theorem exists_iterated_unnesting
    (base : Nat) (c : Nat.Partrec.Code)
    (hlaw : ClearedPrefixUnnestingLaw base c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg) :
    ∀ steps : Nat, ∃ next : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        current.cfg next.cfg ∧
      current.distance + steps ≤ next.distance := by
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
      change Nat.succ (current.distance + steps) ≤ next.distance
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt hdistance hnext.distance_lt)

/-- Under the local unnesting law, every arbitrary immortal orbit with mortal
source reaches generated genuine searches of unbounded distance. -/
theorem reaches_unbounded_genuineSearch_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : ClearedPrefixUnnestingLaw base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∀ bound : Nat, ∃ current : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start current.cfg ∧
      bound < current.distance := by
  intro bound
  rcases exists_reachedGenuineSearch_of_immortalFrom
      base c hmortal start himmortal with ⟨first⟩
  have himmortalFirst := immortalFrom_of_reaches base c
    himmortal first.reaches
  rcases exists_iterated_unnesting base c hlaw first.toGenuineSearch
      himmortalFirst (bound + 1) with ⟨current, htail, hdistance⟩
  refine ⟨current, first.reaches.trans htail, ?_⟩
  omega

/-- The uniform long-search bound contradicts the unbounded gaps supplied by
global unnesting.  Thus the local unnesting law is the only remaining semantic
obligation for mortality of every arbitrary controller configuration. -/
theorem haltsFrom_of_clearedPrefixUnnestingLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hlaw : ClearedPrefixUnnestingLaw base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) start := by
  rcases FullTM0.HaltsFrom.or_immortalFrom
      (CounterControlNestingBridge.machine base c) start with
    hhalts | himmortal
  · exact hhalts
  · rcases CounterControlLongSearchMortality.exists_bound_halts_search
        base c hmortal with ⟨bound, hbound⟩
    rcases reaches_unbounded_genuineSearch_of_immortalFrom
        base c hmortal hlaw start himmortal bound with
      ⟨current, hreach, hlarge⟩
    have hsearchHalts : FullTM0.HaltsFrom
        (CounterControlNestingBridge.machine base c) current.cfg :=
      hbound hlarge current.gap
    have hstartHalts := FullTM0.HaltsFrom.of_reaches hreach hsearchHalts
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c) start).mp
          himmortal hstartHalts)

end

end CounterControlGlobalUnnesting
end Hooper
end Kari
end LeanWang
