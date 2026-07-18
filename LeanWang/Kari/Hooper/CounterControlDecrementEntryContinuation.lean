/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementPositiveEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementZeroEmbedding
import LeanWang.Kari.Hooper.CounterControlPositiveGuarding
import LeanWang.Kari.Hooper.CounterControlGenuineDecrementEntry

/-!
# Completed decrement-entry continuations

An immortal guarded caller selected inside `routeToDecrementStart` reaches
one of the two exact decrement branches.  The positive branch is compared
with the reverse marker-shift schedule, while the zero branch is compared
with its recovery route.  Both therefore give the same strict guarded-parent
outcome for the original route caller.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlDecrementEntryContinuation

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGuardedDecrementBranchSearch

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

/-- Every guarded decrement-entry route caller completes at a logical core
which strictly contains its original search gap. -/
theorem foundGuardedParentOutcome_of_decrementEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases searchOutcome_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨outcome⟩
  cases outcome with
  | positive entry =>
      exact
        CounterControlGuardedDecrementPositiveEmbedding.positiveOriginal_foundGuardedParentOutcome
          base c entry hmortal himmortal
  | zero entry =>
      exact
        CounterControlGuardedDecrementZeroEmbedding.zeroRecovery_foundGuardedParentOutcome
          base c entry hmortal himmortal

/-- Consumer-facing strict escape form of the guarded decrement-entry
continuation. -/
theorem foundGuardedEscapeOutcome_of_decrementEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases foundGuardedParentOutcome_of_decrementEntry base c hmortal current
      growth source register ifZero ifPositive hrule hcommand himmortal with
    ⟨outcome⟩
  exact ⟨.parent outcome⟩

/-- A positive arbitrary decrement-entry gap consumes one blank cell and
reuses the strict guarded theorem.  The distance-zero arbitrary case needs
a genuinely unguarded entry argument and is deliberately not claimed here. -/
theorem foundMonotoneGuardedEntryOutcome_of_decrementEntry_positive
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (hpositive : 0 < current.distance)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  let guarded := CounterControlPositiveGuarding.guardedTail current hpositive
  have hselected : guarded.selectedRaw = current.selectedRaw := rfl
  have hcommand' : guarded.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register) := by
    simpa [hselected] using hcommand
  have hfound :=
    CounterControlPositiveGuarding.foundCfg_guardedTail current hpositive
  have himmortalGuarded : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg guarded.current) := by
    simpa [guarded, hfound] using himmortal
  rcases foundGuardedParentOutcome_of_decrementEntry base c hmortal guarded
      growth source register ifZero ifPositive hrule hcommand'
      himmortalGuarded with ⟨parent⟩
  exact ⟨CounterControlPositiveGuarding.monotone_of_guardedTail_parent
    current hpositive (by simpa [guarded] using parent)⟩

/-- At distance zero no guard is needed for the comparison.  Follow the
genuine route through the test and branch, then transport the completed
branch endpoint back to the original found configuration. -/
theorem foundMonotoneGuardedEntryOutcome_of_decrementEntry_zero
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (hzero : current.distance = 0)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  rcases
      CounterControlGenuineDecrementEntry.branchSearchOutcome_of_rule
        base c hmortal current himmortal growth source register ifZero
        ifPositive hrule hcommand with
    ⟨branch⟩
  cases branch with
  | positive entry =>
      rcases entry.logicalHandoff_of_immortal hmortal himmortal with
        ⟨handoff⟩
      have himmortalNext : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          handoff.entry.next.current.cfg :=
        immortalFrom_of_reaches base c himmortal handoff.entry.reaches
      have himmortalFound := immortalFrom_foundCfg
        handoff.entry.next.current himmortalNext
      rcases CounterControlGuardedShiftEmbedding.decrementPositiveCenteredEnd
          base c hmortal handoff.entry.next himmortalFound growth source
          register ifZero ifPositive handoff.direct with
        ⟨endpoint⟩
      have hfound := reaches_foundCfg_of_immortal
        handoff.entry.next.current himmortalNext
      have hreaches := handoff.entry.reaches.trans
        (hfound.trans endpoint.reaches)
      exact ⟨FoundMonotoneGuardedEntryOutcome.logical endpoint.core
        hreaches (by simp [hzero])⟩
  | zero entry =>
      have himmortalNext : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c) entry.next.cfg :=
        immortalFrom_of_reaches base c himmortal entry.reaches
      have hfound := reaches_foundCfg_of_immortal entry.next himmortalNext
      rcases entry.monotoneOutcome_of_immortal hmortal himmortal with
        ⟨outcome⟩
      cases outcome with
      | logical core reaches _inside =>
          exact ⟨FoundMonotoneGuardedEntryOutcome.logical core
            (entry.reaches.trans (hfound.trans reaches)) (by simp [hzero])⟩
      | nextSearch next reaches _distance =>
          exact ⟨FoundMonotoneGuardedEntryOutcome.nextSearch next
            (entry.reaches.trans (hfound.trans reaches)) (by simp [hzero])⟩

/-- Total weak monotone continuation for an arbitrary genuine
decrement-entry caller. -/
theorem foundMonotoneGuardedEntryOutcome_of_decrementEntry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  by_cases hzero : current.distance = 0
  · exact foundMonotoneGuardedEntryOutcome_of_decrementEntry_zero base c
      hmortal current hzero growth source register ifZero ifPositive hrule
      hcommand himmortal
  · exact foundMonotoneGuardedEntryOutcome_of_decrementEntry_positive
      base c hmortal current (Nat.pos_of_ne_zero hzero) growth source register
      ifZero ifPositive hrule hcommand himmortal

end

end CounterControlDecrementEntryContinuation
end Hooper
end Kari
end LeanWang
