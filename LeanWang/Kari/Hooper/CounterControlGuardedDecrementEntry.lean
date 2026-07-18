/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlDecrementEntry
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Guarded conditional-decrement entry

A generated caller inside `routeToDecrementStart` first completes that
preserving route, then executes the decrement test and its two-way direct
branch.  This file retains the exact endpoint tape.  On an immortal orbit,
the branch cell is forced to be either blank, entering the positive shift
schedule, or the preceding labelled boundary, entering zero recovery.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedDecrementEntry

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedRouteEmbedding
open CounterControlDecrementEntry
open CounterControlRouteSuffixMortality CounterControlValidationMortality
open CounterControlParentContinuation

noncomputable section

set_option maxRecDepth 10000

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Shared route and test handoff -/

/-- Tape after a guarded route's test rule moves into the register gap. -/
abbrev branchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GuardedRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    FullTM0.Tape (Symbol numTags) :=
  CounterControlDecrementEntry.branchTape progress

/-- A guarded caller's shared decrement-test certificate. -/
abbrev TestHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type :=
  CounterControlDecrementEntry.TestHandoff current.current growth source
    register ifZero ifPositive

/-- The guarded route endpoint is centered on the tested boundary. -/
theorem decrementEntry_finish_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GuardedRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    progress.suffix.finish.read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register) :=
  CounterControlDecrementEntry.decrementEntry_finish_read progress

/-- Complete a guarded decrement-entry route and execute its boundary test. -/
theorem testHandoff_of_rule
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
    Nonempty (TestHandoff current growth source register ifZero ifPositive) := by
  exact CounterControlDecrementEntry.testHandoff_of_rule base c hmortal
    current.current himmortal growth source register ifZero ifPositive hrule
    hcommand

/-- Exact branch selected after the decrement test. -/
inductive BranchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  | positive (handoff : TestHandoff current growth source register
      ifZero ifPositive)
      (read_blank : (branchTape handoff.route).read = blankSymbol)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩)
  | zero (handoff : TestHandoff current growth source register
      ifZero ifPositive)
      (read_boundary : (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current)
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩)

/-- Immortality forces the decrement branch cell to carry exactly one of
the two symbols for which this instruction generated an outgoing rule. -/
theorem branchRead_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    (branchTape handoff.route).read = blankSymbol ∨
      (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc :=
  CounterControlDecrementEntry.branchRead_of_reaches base c
    handoff.rule_mem (foundCfg current.current) (branchTape handoff.route)
    handoff.reaches himmortal

/-- Given the symbol selected at the branch cell, execute the corresponding
generated direct rule to the first positive-shift or zero-recovery search. -/
theorem branchOutcome_of_read
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (hread : (branchTape handoff.route).read = blankSymbol ∨
      (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc) :
    Nonempty (BranchOutcome current growth source register
      ifZero ifPositive) := by
  rcases CounterControlDecrementEntry.branchStep_of_read base c
      handoff.rule_mem (branchTape handoff.route) hread with ⟨step⟩
  cases step with
  | positive hblank hstep =>
      exact ⟨BranchOutcome.positive handoff hblank
        (handoff.reaches.trans hstep)⟩
  | zero hboundary hstep =>
      exact ⟨BranchOutcome.zero handoff hboundary
        (handoff.reaches.trans hstep)⟩

/-- Complete a guarded decrement-entry caller and select its exact generated
branch.  Immortality excludes every disabled branch symbol. -/
theorem branchOutcome_of_rule
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
    Nonempty (BranchOutcome current growth source register
      ifZero ifPositive) := by
  rcases testHandoff_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨handoff⟩
  exact branchOutcome_of_read base c handoff
    (branchRead_of_immortal base c handoff himmortal)

end

end CounterControlGuardedDecrementEntry
end Hooper
end Kari
end LeanWang
