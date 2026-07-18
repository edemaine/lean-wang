/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Conditional-decrement route handoff

This module contains the proof-neutral part of conditional-decrement entry.
It completes a genuine preserving-route endpoint with the decrement test.
Guarded and guard-free callers share this certificate and differ only in how
they obtain the route endpoint and use the subsequent branch.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlDecrementEntry

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting
open CounterControlGenuineRouteEmbedding
open CounterControlRouteSuffixMortality CounterControlValidationMortality
open CounterControlParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## The final target of a retained route suffix -/

/-- Last target of a route suffix, including the already found current leg. -/
def lastRouteTarget (current : MarkerValidation.Leg)
    (remaining : List MarkerValidation.Leg) : Fin 5 :=
  ((current :: remaining).getLast (by simp)).target

@[simp] theorem lastRouteTarget_nil (current : MarkerValidation.Leg) :
    lastRouteTarget current [] = current.target := by
  rfl

/-- A complete nonempty route trace finishes on its final labelled target. -/
theorem routeGaps_finish_read
    {growth : Turing.Dir} {route : List MarkerValidation.Leg}
    {outer finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteGaps growth route outer finish)
    (hne : route ≠ []) :
    finish.read = boundarySymbol ((route.getLast hne).target) := by
  induction trace with
  | last leg outer distance gap =>
      have hmarked := gap.marked
      change outer (FullTM0.Tape.offset
        (orient growth leg.direction) distance) =
          boundarySymbol leg.target at hmarked
      simpa [FullTM0.Tape.read_moveN] using hmarked
  | cons leg next rest outer distance gap finish tail ih =>
      simpa using ih (by simp)

/-- Starting at the already found current leg, a route tail finishes on the
last target of `current :: remaining`. -/
theorem routeTailGaps_finish_read
    {growth : Turing.Dir} {remaining : List MarkerValidation.Leg}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteTailGaps growth remaining start finish)
    (current : MarkerValidation.Leg)
    (hcurrent : start.read = boundarySymbol current.target) :
    finish.read = boundarySymbol (lastRouteTarget current remaining) := by
  cases trace with
  | nil => simpa using hcurrent
  | cons next rest start finish tail =>
      simpa [lastRouteTarget] using routeGaps_finish_read tail (by simp)

/-- The final leg of a nonempty decrement-entry route targets the boundary
immediately after the selected register. -/
theorem decrementEntry_lastTarget
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    lastRouteTarget progress.suffix.current progress.suffix.remaining =
      MarkerSchedule.decrementStartBoundary register := by
  cases register with
  | clock =>
      have himpossible := progress.suffix.route_eq
      simp [AnchoredCounterGeometry.routeToDecrementStart] at himpossible
  | left =>
      have hlast := congrArg List.getLast? progress.suffix.route_eq
      rw [List.getLast?_append_cons,
        List.getLast?_eq_some_getLast (by
          simp [AnchoredCounterGeometry.routeToDecrementStart]),
        List.getLast?_eq_some_getLast (by simp)] at hlast
      have htarget := congrArg MarkerValidation.Leg.target
        (Option.some.inj hlast).symm
      change lastRouteTarget progress.suffix.current
        progress.suffix.remaining = 1 at htarget
      exact htarget
  | right =>
      have hlast := congrArg List.getLast? progress.suffix.route_eq
      rw [List.getLast?_append_cons,
        List.getLast?_eq_some_getLast (by
          simp [AnchoredCounterGeometry.routeToDecrementStart]),
        List.getLast?_eq_some_getLast (by simp)] at hlast
      have htarget := congrArg MarkerValidation.Leg.target
        (Option.some.inj hlast).symm
      change lastRouteTarget progress.suffix.current
        progress.suffix.remaining = 2 at htarget
      exact htarget
  | temp =>
      have hlast := congrArg List.getLast? progress.suffix.route_eq
      rw [List.getLast?_append_cons,
        List.getLast?_eq_some_getLast (by
          simp [AnchoredCounterGeometry.routeToDecrementStart]),
        List.getLast?_eq_some_getLast (by simp)] at hlast
      have htarget := congrArg MarkerValidation.Leg.target
        (Option.some.inj hlast).symm
      change lastRouteTarget progress.suffix.current
        progress.suffix.remaining = 3 at htarget
      exact htarget

/-- The completed route is centered on the boundary tested by the decrement
instruction. -/
theorem decrementEntry_finish_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    progress.suffix.finish.read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register) := by
  have hread := routeTailGaps_finish_read progress.suffix.tailGaps
    progress.suffix.current progress.current_read
  rw [decrementEntry_lastTarget progress] at hread
  exact hread

/-! ## Exact test handoff -/

/-- Tape after the test rule moves left into the selected register gap. -/
def branchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    FullTM0.Tape (Symbol numTags) :=
  progress.suffix.finish.move (orient growth .left)

/-- Exact completion of a decrement-entry route and its test rule. -/
structure TestHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  rule_mem : (source, .decrement register ifZero ifPositive) ∈
    GlobalSourceProgram.program
  route : GenuineRouteEnd current growth source bodySearchBase
    (bodyDirectBase + 1) (directRef growth source testDirectSlot)
    (AnchoredCounterGeometry.routeToDecrementStart register)
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    ⟨resolve base c (directRef growth source branchDirectSlot),
      branchTape route⟩

/-- Execute the exact boundary test after a completed decrement-entry route. -/
theorem testHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (TestHandoff current growth source register ifZero ifPositive) := by
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot,
      .boundary (MarkerSchedule.decrementStartBoundary register),
      directRef growth source branchDirectSlot, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches progress.suffix.finish.read := by
    simpa [raw, RawRead.Matches] using decrementEntry_finish_read progress
  have htest := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw progress.suffix.finish hmatch
  have htest' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        progress.suffix.finish⟩
      ⟨resolve base c (directRef growth source branchDirectSlot),
        branchTape progress⟩ := by
    change FullTM0.Reaches (FiniteTM0.machine
      (CounterControlPlan.table base c)) _ _
    simpa [raw, branchTape] using htest
  exact ⟨⟨hrule, progress, progress.reaches.trans htest'⟩⟩

/-- Complete a selected decrement-entry route and execute its boundary test. -/
theorem testHandoff_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (TestHandoff current growth source register ifZero ifPositive) := by
  have hcommands : ∀ command,
      command ∈ routeCommandsAux growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) →
        command ∈ rawCommands := by
    intro command hmem
    exact CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth hrule (by simp [commandsForRule, decrementCommands, hmem])
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source bodySearchBase
          (bodyDirectBase + 1)
          (AnchoredCounterGeometry.routeToDecrementStart register) →
        rule ∈ rawDirectRules := by
    intro rule hmem
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    simp [directRulesForRule, decrementRules, hmem]
  rcases progressedRoute base c hmortal current himmortal growth source
      bodySearchBase (bodyDirectBase + 1)
      (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register) hcommand
      hcommands hcontinuations with ⟨progress⟩
  exact testHandoff base c current growth source register ifZero ifPositive
    hrule progress

end

end CounterControlDecrementEntry
end Hooper
end Kari
end LeanWang
