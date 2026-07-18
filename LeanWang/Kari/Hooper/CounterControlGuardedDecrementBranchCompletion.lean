/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementBranchSearch
import LeanWang.Kari.Hooper.CounterControlGuardedShiftEmbedding
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding

/-!
# Completing the two guarded decrement branches

The positive distance-zero guarded search is run through the complete
decrement-shift schedule and final direct rule.  The zero distance-zero
genuine search is run through the guard-free recovery-route embedding.
Both packages retain the original guarded decrement-entry route; this is the
geometry needed to turn containment of the distance-zero branch search into
strict containment of the original guarded caller.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedDecrementBranchCompletion

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGuardedDecrementBranchSearch
open CounterControlGuardedShiftCompletion

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Fully discharged positive-decrement direct endpoint, still indexed by
the original guarded decrement-entry caller through `entry`. -/
structure PositiveLogicalHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  entry : PositiveSearchHandoff current growth source register
    ifZero ifPositive
  direct : DecrementPositiveDirectHandoff entry.next growth source register
    ifZero ifPositive
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨logicalState base c growth ifPositive,
      decrementPositiveTape direct.suffix⟩

/-- Run the positive branch through every shift and the final direct rule. -/
theorem positiveLogicalHandoff_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : PositiveSearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (PositiveLogicalHandoff current growth source register
      ifZero ifPositive) := by
  have himmortalEntry := positive_immortalFrom base c entry himmortal
  have himmortalFound := immortalFrom_foundCfg entry.next.current
    himmortalEntry
  rcases CounterControlGuardedSearch.GuardedSearch.decrementShift_suffix_of_immortal
      base c hmortal entry.next growth source register ifZero ifPositive
      entry.route.rule_mem (positive_command_mem entry) himmortalFound with
    ⟨suffix⟩
  rcases decrementPositiveDirectHandoff base c entry.next growth source
      register ifZero ifPositive entry.route.rule_mem suffix with
    ⟨direct⟩
  have hfound := reaches_foundCfg_of_immortal entry.next.current
    himmortalEntry
  exact ⟨⟨entry, direct,
    entry.reaches.trans (hfound.trans direct.reaches)⟩⟩

/-- Completed zero-recovery embedding, retaining both the original route and
the exact distance-zero search against which the monotone outcome is stated. -/
structure ZeroRecoveryHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  entry : ZeroSearchHandoff current growth source register ifZero ifPositive
  outcome : FoundMonotoneGuardedEntryOutcome entry.next
  reaches_found : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    (foundCfg current.current) (foundCfg entry.next)

/-- Run the zero branch through the complete guard-free recovery route. -/
theorem zeroRecoveryHandoff_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : ZeroSearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (ZeroRecoveryHandoff current growth source register
      ifZero ifPositive) := by
  have himmortalEntry := zero_immortalFrom base c entry himmortal
  have himmortalFound := immortalFrom_foundCfg entry.next himmortalEntry
  rcases CounterControlGenuineRouteEmbedding.zeroRecovery_logical_of_rule
      base c hmortal entry.next himmortalFound growth source register ifZero
      ifPositive entry.route.rule_mem (zero_command_mem entry) with
    ⟨outcome⟩
  exact ⟨⟨entry, outcome,
    entry.reaches.trans
      (reaches_foundCfg_of_immortal entry.next himmortalEntry)⟩⟩

/-- Fully executed branch continuation before the final original-gap
containment comparison. -/
inductive CompletionOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  | positive (handoff : PositiveLogicalHandoff current growth source register
      ifZero ifPositive)
  | zero (handoff : ZeroRecoveryHandoff current growth source register
      ifZero ifPositive)

/-- Complete either exact branch-search package through its entire generated
positive-shift or zero-recovery continuation. -/
theorem completionOutcome_of_searchOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (outcome : SearchOutcome current growth source register
      ifZero ifPositive) :
    Nonempty (CompletionOutcome current growth source register
      ifZero ifPositive) := by
  cases outcome with
  | positive entry =>
      rcases positiveLogicalHandoff_of_immortal base c entry hmortal
          himmortal with ⟨handoff⟩
      exact ⟨CompletionOutcome.positive handoff⟩
  | zero entry =>
      rcases zeroRecoveryHandoff_of_immortal base c entry hmortal himmortal
          with ⟨handoff⟩
      exact ⟨CompletionOutcome.zero handoff⟩

/-- End-to-end completion from a selected guarded decrement-entry caller. -/
theorem completionOutcome_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (CompletionOutcome current growth source register
      ifZero ifPositive) := by
  rcases searchOutcome_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨outcome⟩
  exact completionOutcome_of_searchOutcome base c hmortal himmortal outcome

end

end CounterControlGuardedDecrementBranchCompletion
end Hooper
end Kari
end LeanWang
