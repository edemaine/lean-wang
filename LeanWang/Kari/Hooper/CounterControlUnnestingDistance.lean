/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCleanupResume

/-!
# The strict distance comparison for global unnesting

Cleanup of a represented core ending at `layoutEnd registers` exposes its
first obstruction at `outerDistance`.  The return transition then restarts a
generated search at distance `outerDistance - 1`.  For this resumed gap to be
strictly longer than an earlier triggering gap `currentDistance`, the exact
missing geometric premise is

`currentDistance < layoutEnd registers`.

Indeed, the represented prefix supplies
`layoutEnd registers < outerDistance`, and these two strict inequalities are
equivalent to the desired one-cell-shifted comparison.  This module packages
that arithmetic fact together with the operational cleanup/resume theorem as
a conditional `ClearedPrefixUnnests` constructor.  Establishing the premise
for an incoming arbitrary generated search is intentionally left to the
command-success-to-logical reconstruction layer; it is not a consequence of
tag-free prefix cleanup alone.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlUnnestingDistance

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlCleanupSemantics
open CounterControlGlobalUnnesting

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The exact arithmetic comparison needed after the return transition's
one-cell move. -/
theorem lt_outerDistance_sub_one
    {currentDistance coreEnd outerDistance : Nat}
    (hcurrent : currentDistance < coreEnd)
    (hcore : coreEnd < outerDistance) :
    currentDistance < outerDistance - 1 := by
  omega

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

/-- Conditional operational form of one strict global-unnesting step.

The body/cleanup layer supplies `hreturn`; the cleanup/resume layer supplies
the exact next gap.  The sole comparison premise not supplied by those layers
is `hcurrent`: the triggering gap must lie strictly inside the reconstructed
core. -/
theorem clearedPrefixUnnests_of_reaches_cleaned_return
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents spec.registers spec.growth T)
    (hrunway : ∀ position, layoutEnd spec.registers < position →
      position < spec.outerDistance →
        logicalTape spec.growth T position = blankSymbol)
    (htarget : spec.outerTarget.Matches
      (logicalTape spec.growth T spec.outerDistance))
    (hcurrent : current.distance < layoutEnd spec.registers)
    (hreturn : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) current.cfg
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth (afterZero spec T) 0⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg) :
    ∃ next : GenuineSearch base c, ClearedPrefixUnnests current next := by
  let returnCfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
    ⟨controllerReturn base c spec.growth,
      atLogical spec.growth (afterZero spec T) 0⟩
  have himmortalReturn : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) returnCfg :=
    immortalFrom_of_reaches base c himmortal
      (by simpa [returnCfg] using hreturn)
  rcases CounterControlCleanupResume.reaches_resumed_search_at_first_obstruction_sub_one
      base c hmortal hcore hrunway htarget
      (by simpa [returnCfg] using himmortalReturn) with
    ⟨search, distance, hresume, hdirection, hgap, hdistance⟩
  let outer := (afterTag spec T).move spec.growth
  let next : GenuineSearch base c := {
    search := search
    outer := outer
    distance := distance
    gap := by
      rw [hdirection]
      simpa [outer] using hgap }
  refine ⟨next, ?_⟩
  constructor
  · change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      current.cfg ((searchSystem base c).startCfg search outer)
    exact hreturn.trans hresume
  · change current.distance < distance
    rw [hdistance]
    exact lt_outerDistance_sub_one hcurrent spec.core_before_target

end

end CounterControlUnnestingDistance
end Hooper
end Kari
end LeanWang
