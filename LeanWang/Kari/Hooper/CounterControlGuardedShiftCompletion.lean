/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedShiftCoordinates

/-!
# Direct-control completion after guarded marker shifts

A guarded marker-shift caller can occur partway through an increment or a
positive-decrement schedule.  `CounterControlGuardedShiftCoordinates`
advances the remaining generated shifts and stops at the schedule's final
direct-control state.  This file executes the final direct glue exactly.

For an increment, the glue moves right from the vacated old boundary cell to
the shifted boundary.  It selects either the increment-recovery route or,
when that route is empty, the logical successor itself.  For a positive
decrement, the glue moves left from the vacated old boundary cell directly to
the positive logical successor.  Both handoffs retain the source rule, its
logical-target bound, the exact final tape, and reachability from the original
guarded found configuration.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedShiftCompletion

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlGuardedSearch
open CounterControlGuardedSearch.GuardedSearch
open CounterControlResumedShiftCoordinates
open CounterControlGlobalUnnesting
open CounterControlParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Tape facts retained by a shift suffix -/

/-- Every marker-shift handoff is centered on the vacated old source cell,
which is blank.  Consequently a complete suffix also finishes on a blank. -/
theorem shiftTailGaps_finish_read_blank
    {direction : Turing.Dir} {labels : List (Fin 5)}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : ShiftTailGaps direction labels start finish)
    (hblank : start.read = blankSymbol) :
    finish.read = blankSymbol := by
  induction trace with
  | nil => exact hblank
  | cons expected remaining outer distance gap positive finish tail ih =>
      apply ih
      cases direction <;>
        simp [shiftStepTape, FullTM0.Tape.read, FullTM0.Tape.move,
          FullTM0.Tape.write]

/-- Last boundary moved by a suffix which starts immediately after moving
`current`. -/
def lastShiftExpected (current : Fin 5) (remaining : List (Fin 5)) : Fin 5 :=
  (current :: remaining).getLast (by simp)

@[simp] theorem lastShiftExpected_nil (current : Fin 5) :
    lastShiftExpected current [] = current := by
  rfl

private theorem shiftStepTape_opposite_read
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (expected : Fin 5) :
    ((shiftStepTape direction outer distance expected).move
      (NestingMachine.opposite direction)).read = boundarySymbol expected := by
  cases direction <;>
    simp [shiftStepTape, NestingMachine.opposite, FullTM0.Tape.read,
      FullTM0.Tape.move, FullTM0.Tape.write]

/-- The cell behind the final suffix head contains the last boundary moved
by the whole prefix-plus-suffix schedule. -/
theorem shiftTailGaps_finish_opposite_read
    {direction : Turing.Dir} {labels : List (Fin 5)}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : ShiftTailGaps direction labels start finish)
    (current : Fin 5)
    (hcurrent : (start.move
      (NestingMachine.opposite direction)).read = boundarySymbol current) :
    (finish.move (NestingMachine.opposite direction)).read =
      boundarySymbol (lastShiftExpected current labels) := by
  induction trace generalizing current with
  | nil => simpa using hcurrent
  | cons expected remaining outer distance gap positive finish tail ih =>
      have hnext := shiftStepTape_opposite_read direction outer distance
        expected
      have hfinish := ih expected hnext
      simpa [lastShiftExpected] using hfinish

/-! ## Exact endpoint descriptions -/

/-- Symbolic endpoint selected by the direct blank rule after an increment
shift schedule. -/
def incrementAfterShiftRef (growth : Turing.Dir) (source : Nat)
    (register : Register) (next : Nat) : ControlRef :=
  match AnchoredCounterGeometry.routeFromIncrement register with
  | [] => .logical growth next
  | _ :: _ => directRef growth source (bodyDirectBase + 1)

/-- Exact tape after the post-increment blank rule moves right onto the
shifted boundary. -/
def incrementAfterShiftTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : IncrementShiftSuffixReached current growth source register) :
    FullTM0.Tape (Symbol numTags) :=
  suffix.finish.move (orient growth .right)

/-- Exact tape after the positive-decrement finish rule moves left onto the
new boundary `4`. -/
def decrementPositiveTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : DecrementShiftSuffixReached current growth source register) :
    FullTM0.Tape (Symbol numTags) :=
  suffix.finish.move (orient growth .left)

/-- The retained position decomposition still identifies the final boundary
of a complete increment schedule. -/
theorem incrementShiftSuffix_lastExpected
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : IncrementShiftSuffixReached current growth source register) :
    lastShiftExpected suffix.position.current suffix.position.remaining =
      MarkerSchedule.decrementStartBoundary register := by
  have hlast := congrArg List.getLast? suffix.position.labels_eq
  rw [List.getLast?_append_cons] at hlast
  have hright := List.getLast?_eq_some_getLast
    (l := suffix.position.current :: suffix.position.remaining) (by simp)
  change (suffix.position.current :: suffix.position.remaining).getLast? =
    some (lastShiftExpected suffix.position.current
      suffix.position.remaining) at hright
  rw [hright] at hlast
  cases register <;>
    simpa [MarkerShift.incrementOrder, lastShiftExpected,
      MarkerSchedule.decrementStartBoundary] using hlast.symm

/-- After the increment blank rule moves right, the scanned symbol is the
boundary from which the recovery route starts. -/
theorem incrementAfterShiftTape_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : IncrementShiftSuffixReached current growth source register) :
    (incrementAfterShiftTape suffix).read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register) := by
  have hdirection : current.direction = orient growth .left := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [suffix.position.raw_eq] at hdirection
    exact hdirection.symm
  have hcurrent := suffix.handoff.destination_boundary
  rw [hdirection] at hcurrent
  have hread := shiftTailGaps_finish_opposite_read suffix.tailGaps
    suffix.position.current hcurrent
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  rw [hopposite] at hread
  rw [incrementShiftSuffix_lastExpected suffix] at hread
  simpa [incrementAfterShiftTape] using hread

/-- The retained position decomposition still identifies boundary `4` as
the final boundary of every positive-decrement shift schedule. -/
theorem decrementShiftSuffix_lastExpected
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : DecrementShiftSuffixReached current growth source register) :
    lastShiftExpected suffix.position.current suffix.position.remaining = 4 := by
  have hlast := congrArg List.getLast? suffix.position.labels_eq
  rw [List.getLast?_append_cons] at hlast
  have hright := List.getLast?_eq_some_getLast
    (l := suffix.position.current :: suffix.position.remaining) (by simp)
  change (suffix.position.current :: suffix.position.remaining).getLast? =
    some (lastShiftExpected suffix.position.current
      suffix.position.remaining) at hright
  rw [hright] at hlast
  cases register <;>
    simpa [MarkerShift.decrementOrder, lastShiftExpected] using hlast.symm

/-- The positive-decrement finish rule moves left onto the newly placed
boundary `4`. -/
theorem decrementPositiveTape_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : DecrementShiftSuffixReached current growth source register) :
    (decrementPositiveTape suffix).read = boundarySymbol 4 := by
  have hdirection : current.direction = orient growth .right := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection]
      at hdirection
    rw [suffix.position.raw_eq] at hdirection
    exact hdirection.symm
  have hcurrent := suffix.handoff.destination_boundary
  rw [hdirection] at hcurrent
  have hread := shiftTailGaps_finish_opposite_read suffix.tailGaps
    suffix.position.current hcurrent
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  rw [hopposite] at hread
  rw [decrementShiftSuffix_lastExpected suffix] at hread
  simpa [decrementPositiveTape] using hread

/-- Completed direct handoff after a guarded increment-shift suffix.  A
nonempty recovery route stops at its entry direct state; the empty clock
route stops at the logical successor. -/
structure IncrementDirectHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat) : Type where
  rule_mem : (source, .increment register next) ∈
    GlobalSourceProgram.program
  target_lt : next < logicalSpan
  suffix : IncrementShiftSuffixReached current growth source register
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨resolve base c (incrementAfterShiftRef growth source register next),
      incrementAfterShiftTape suffix⟩

/-- Completed direct handoff after a guarded positive-decrement suffix. -/
structure DecrementPositiveDirectHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  rule_mem : (source, .decrement register ifZero ifPositive) ∈
    GlobalSourceProgram.program
  target_lt : ifPositive < logicalSpan
  suffix : DecrementShiftSuffixReached current growth source register
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨logicalState base c growth ifPositive,
      decrementPositiveTape suffix⟩

/-- Exact tape at the first generated search of a nonempty increment
recovery route. -/
def incrementRecoverySearchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (suffix : IncrementShiftSuffixReached current growth source register)
    (first : MarkerValidation.Leg) : FullTM0.Tape (Symbol numTags) :=
  (incrementAfterShiftTape suffix).move (orient growth first.direction)

/-- Completed direct-control prefix for a nonempty increment recovery.  The
endpoint is the first generated search of the recovery route, so all direct
glue following the marker-shift schedule has been discharged. -/
structure IncrementRecoverySearchHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat) (first : MarkerValidation.Leg)
    (rest : List MarkerValidation.Leg) : Type where
  direct : IncrementDirectHandoff current growth source register next
  route_eq : AnchoredCounterGeometry.routeFromIncrement register =
    first :: rest
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨resolve base c (searchRef growth source secondarySearchBase),
      incrementRecoverySearchTape direct.suffix first⟩

/-- Exhaustive exact endpoint after all direct control following a guarded
increment-shift suffix has run. -/
inductive IncrementDirectCompletion
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat) : Type where
  | logical
      (direct : IncrementDirectHandoff current growth source register next)
      (route_eq : AnchoredCounterGeometry.routeFromIncrement register = [])
  | recovery (first : MarkerValidation.Leg)
      (rest : List MarkerValidation.Leg)
      (handoff : IncrementRecoverySearchHandoff current growth source
        register next first rest)

/-! ## Executing the direct glue -/

/-- Execute the exact post-increment blank rule after any completed guarded
shift suffix. -/
theorem incrementDirectHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (suffix : IncrementShiftSuffixReached current growth source register) :
    Nonempty (IncrementDirectHandoff current growth source register next) := by
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source bodyDirectBase, .blank,
      incrementAfterShiftRef growth source register next, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change raw ∈ validationRules growth source ++
      incrementRules growth source next register
    apply List.mem_append_right
    simp only [incrementRules, List.mem_append]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    simp only [List.mem_singleton]
    rfl
  have hblank : raw.read.Matches suffix.finish.read := by
    change suffix.finish.read = blankSymbol
    exact shiftTailGaps_finish_read_blank suffix.tailGaps
      suffix.handoff.source_blank
  have hdirect := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw suffix.finish hblank
  have hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (incrementAfterShiftRef growth source register next),
        incrementAfterShiftTape suffix⟩ := by
    exact suffix.reaches.trans hdirect
  have hnext : next < logicalSpan :=
    state_lt_logicalSpan
      (CounterControlAbstractTrace.target_mem_programStates hrule
        (by simp [instructionTargets]))
  exact ⟨⟨hrule, hnext, suffix, hreach⟩⟩

/-- If the increment recovery route is empty, the exact direct handoff is
already at bounded logical control. -/
theorem IncrementDirectHandoff.reachesLogical_of_route_eq_nil
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register} {next : Nat}
    (handoff : IncrementDirectHandoff current growth source register next)
    (hroute : AnchoredCounterGeometry.routeFromIncrement register = []) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨logicalState base c growth next,
        incrementAfterShiftTape handoff.suffix⟩ := by
  have hrun := handoff.reaches
  have href : incrementAfterShiftRef growth source register next =
      .logical growth next := by
    simp [incrementAfterShiftRef, hroute]
  rw [href] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨logicalState base c growth next,
      incrementAfterShiftTape handoff.suffix⟩ at hrun
  exact hrun

/-- Execute the recovery-route entry rule after the post-increment blank
rule.  The result is centered at the route's first generated search with the
exact two-move tape. -/
theorem incrementRecoverySearchHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (suffix : IncrementShiftSuffixReached current growth source register)
    (first : MarkerValidation.Leg) (rest : List MarkerValidation.Leg)
    (hroute : AnchoredCounterGeometry.routeFromIncrement register =
      first :: rest) :
    Nonempty (IncrementRecoverySearchHandoff current growth source register
      next first rest) := by
  rcases incrementDirectHandoff base c current growth source register next
      hrule suffix with ⟨direct⟩
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source (bodyDirectBase + 1),
      .boundary (MarkerSchedule.decrementStartBoundary register),
      searchRef growth source secondarySearchBase, first.direction⟩
  have hraw : raw ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change raw ∈ validationRules growth source ++
      incrementRules growth source next register
    apply List.mem_append_right
    simp [raw, incrementRules, hroute, routeEntryRules]
  have hmatch : raw.read.Matches
      (incrementAfterShiftTape direct.suffix).read := by
    change (incrementAfterShiftTape direct.suffix).read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register)
    exact incrementAfterShiftTape_read direct.suffix
  have hentry := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (incrementAfterShiftTape direct.suffix) hmatch
  have hentry' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source (bodyDirectBase + 1)),
        incrementAfterShiftTape direct.suffix⟩
      ⟨resolve base c (searchRef growth source secondarySearchBase),
        incrementRecoverySearchTape direct.suffix first⟩ := by
    simpa [BoundedMarkerProgram.machine, CounterControlPlan.table, raw,
      incrementRecoverySearchTape] using hentry
  have href : incrementAfterShiftRef growth source register next =
      directRef growth source (bodyDirectBase + 1) := by
    simp [incrementAfterShiftRef, hroute]
  have hbefore := direct.reaches
  rw [href] at hbefore
  have hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (searchRef growth source secondarySearchBase),
        incrementRecoverySearchTape direct.suffix first⟩ := by
    exact hbefore.trans hentry'
  exact ⟨⟨direct, hroute, hreach⟩⟩

/-- Split the finite register-dependent recovery route and produce its exact
fully discharged direct-control endpoint. -/
theorem incrementDirectCompletion
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (suffix : IncrementShiftSuffixReached current growth source register) :
    Nonempty (IncrementDirectCompletion current growth source register
      next) := by
  cases hroute : AnchoredCounterGeometry.routeFromIncrement register with
  | nil =>
      rcases incrementDirectHandoff base c current growth source register
          next hrule suffix with ⟨direct⟩
      exact ⟨IncrementDirectCompletion.logical direct hroute⟩
  | cons first rest =>
      rcases incrementRecoverySearchHandoff base c current growth source
          register next hrule suffix first rest hroute with ⟨handoff⟩
      exact ⟨IncrementDirectCompletion.recovery first rest handoff⟩

/-- Execute the exact finish rule after any completed guarded
positive-decrement shift suffix. -/
theorem decrementPositiveDirectHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (suffix : DecrementShiftSuffixReached current growth source register) :
    Nonempty (DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) := by
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source finishDirectSlot, .blank,
      .logical growth ifPositive, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hblank : raw.read.Matches suffix.finish.read := by
    change suffix.finish.read = blankSymbol
    exact shiftTailGaps_finish_read_blank suffix.tailGaps
      suffix.handoff.source_blank
  have hdirect := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw suffix.finish hblank
  have hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨logicalState base c growth ifPositive,
        decrementPositiveTape suffix⟩ := by
    exact suffix.reaches.trans hdirect
  have htarget : ifPositive < logicalSpan :=
    state_lt_logicalSpan
      (CounterControlAbstractTrace.target_mem_programStates hrule
        (by simp [instructionTargets]))
  exact ⟨⟨hrule, htarget, suffix, hreach⟩⟩

/-! ## Endpoint facts -/

/-- The rule provenance retained by an increment handoff bounds its eventual
logical successor in the allocated logical-state block. -/
theorem IncrementDirectHandoff.target_bounds
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register} {next : Nat}
    (handoff : IncrementDirectHandoff current growth source register next) :
    logicalBase base c growth ≤ logicalState base c growth next ∧
      logicalState base c growth next <
        logicalBase base c growth + logicalSpan :=
  logicalState_bounds base c growth handoff.target_lt

/-- The positive-decrement endpoint is centered on boundary `4`. -/
theorem DecrementPositiveDirectHandoff.endpoint_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) :
    (decrementPositiveTape handoff.suffix).read = boundarySymbol 4 :=
  decrementPositiveTape_read handoff.suffix

/-- The retained decrement rule bounds its positive successor in the
allocated logical-state block. -/
theorem DecrementPositiveDirectHandoff.target_bounds
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : DecrementPositiveDirectHandoff current growth source register
      ifZero ifPositive) :
    logicalBase base c growth ≤ logicalState base c growth ifPositive ∧
      logicalState base c growth ifPositive <
        logicalBase base c growth + logicalSpan :=
  logicalState_bounds base c growth handoff.target_lt

end

end CounterControlGuardedShiftCompletion
end Hooper
end Kari
end LeanWang
