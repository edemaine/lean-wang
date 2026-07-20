/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlIncrementSchedule

/-!
# Increment-instruction semantics

This module composes the shared validation prefix with collision-free
increment schedules and recovery routes.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge
open CounterControlScheduleSemantics CounterControlCleanupSemantics
  CounterControlFrameBacking CounterControlCoreRoutes

noncomputable section
/-! ## Solved increment schedule -/

/-- Reinstalling any incremented register layout absorbs a previous
increment installation.  All incremented layouts have the same endpoint,
so the later canonical installation covers everything written by the
earlier one. -/
theorem install_incrementTape_eq
    (spec : Spec numTags) (T : FullTM0.Tape (Symbol numTags))
    (earlier later : Register) :
    install (spec.registers.increment later) spec.growth spec.returnTag
        (incrementTape spec earlier T) =
      incrementTape spec later T := by
  change install (spec.registers.increment later) spec.growth spec.returnTag
      (install (spec.registers.increment earlier) spec.growth
        spec.returnTag T) =
    install (spec.registers.increment later) spec.growth spec.returnTag T
  apply install_over_install
  simp only [layoutEnd_increment]
  omega

/-- The two primitive increment shifts needed by the register-independent
schedule.  The successful and halting-aware developments instantiate the
same runner with different shorter-search hypotheses and failure predicates.
-/
structure IncrementScheduleRunner
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop) where
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  clock : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat)
      (success : ControlRef) (collision : Option ControlRef)
      {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T →
      layoutEnd (spec.registers.increment .clock) < spec.outerDistance →
      0 < limit →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ 4 .left .right
        success (some .left) collision ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨resolve base c success,
          atLogical spec.growth (incrementTape spec .clock T)
            (layoutEnd spec.registers)⟩
  internal : ∀ (limit : Nat), Short limit →
    ∀ (counterState searchSlot : Nat)
      (success : ControlRef) (collision : Option ControlRef)
      {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)},
      Represents spec T → ∀ (next : Registers) (i : Fin 4),
      0 < RegisterLayout.values spec.registers i →
      RegisterLayout.values spec.registers i < limit →
      layoutEnd next < spec.outerDistance →
      layoutEnd next = layoutEnd spec.registers →
      MarkerMachine.moveAt .right
          (MarkerTape.canonicalTape spec.registers)
          (MarkerTape.boundaryPosition spec.registers i.castSucc) i.castSucc =
        MarkerTape.canonicalTape next →
      RawCommand.markerShift
        ⟨spec.growth, counterState, searchSlot⟩ i.castSucc .left .right
        success (some .left) collision ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨spec.growth, counterState, searchSlot⟩,
          atLogical spec.growth T (lastGapOffset spec.registers i)⟩
        ⟨resolve base c success,
          atLogical spec.growth
            (install next spec.growth spec.returnTag T)
            (boundaryOffset spec.registers i.castSucc)⟩

/-- Register-independent increment scheduling, parameterized by the outcome
of each constituent bounded search. -/
theorem machine_reaches_incrementSchedule_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : IncrementScheduleRunner base c Short Failure)
    (source : Nat) (register : Register)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : Short spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  have hlimit : 0 < spec.outerDistance := by
    omega
  let prefixRunner : IncrementPrefixRunner base c Failure spec.growth
      spec.registers T := {
    stageTape := fun stage => incrementTape spec stage T
    pullback := runner.pullback
    clock := by
      intro counterState searchSlot success collision hraw
      have hclockRoom : layoutEnd (spec.registers.increment .clock) <
          spec.outerDistance := by
        simpa only [layoutEnd_increment] using hroom
      exact runner.clock spec.outerDistance hshort counterState searchSlot
        success collision h hclockRoom hlimit hraw
    internal := by
      intro counterState searchSlot success current next hnext hraw
      have hcurrentRoom : layoutEnd (spec.registers.increment current) <
          spec.outerDistance := by
        simpa only [layoutEnd_increment] using hroom
      let currentSpec := incrementSpec spec current hcurrentRoom
      let currentTape := incrementTape spec current T
      have hcurrentRep : Represents currentSpec currentTape :=
        incrementTape_represents h current hcurrentRoom
      have hrun := runner.internal spec.outerDistance hshort counterState
        searchSlot success none hcurrentRep
        (spec.registers.increment next) (incrementStageIndex next)
        (by
          simpa only [currentSpec, incrementSpec, updateSpec] using
            incrementStage_positive spec.registers hnext)
        (by
          simpa [currentSpec, incrementSpec, updateSpec] using
            registerValue_lt_outerDistance hcurrentRep
              (incrementStageIndex next))
        (by simpa [currentSpec, incrementSpec, updateSpec,
          layoutEnd_increment] using hroom)
        (by simp [currentSpec, incrementSpec, updateSpec,
          layoutEnd_increment])
        (by
          simpa only [currentSpec, incrementSpec, updateSpec] using
            incrementStage_move spec.registers hnext)
        hraw
      have htape : install (spec.registers.increment next) spec.growth
          spec.returnTag currentTape = incrementTape spec next T := by
        simpa [currentTape] using
          install_incrementTape_eq spec T current next
      simp only [currentSpec, incrementSpec, updateSpec] at hrun
      rw [htape] at hrun
      exact hrun }
  exact machine_reaches_incrementPrefix_with base c Failure prefixRunner
    source register hcommands

/-- All collision-free shifts of one generated increment execute exactly.
The endpoint is the blank old source cell of the last shifted boundary; the
following direct rule moves right onto the new boundary. -/
theorem machine_reaches_incrementSchedule_solved
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    (register : Register)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let runner : IncrementScheduleRunner base c (ShortSearches base c)
      (fun _ => False) := {
    pullback := by
      intro _ _ _ failure
      exact failure.elim
    clock := by
      intro limit hshort counterState searchSlot success collision spec T
        h hroom hlimit hraw
      exact Or.inl (machine_reaches_incrementClock_solved base c limit hshort
        counterState searchSlot success collision h hroom hlimit hraw)
    internal := by
      intro limit hshort counterState searchSlot success collision spec T
        h next i hpositive hdistance hnextCore hsameEnd hmove hraw
      exact Or.inl (machine_reaches_incrementInternal_solved base c limit hshort
        counterState searchSlot success collision h next i hpositive hdistance
        hnextCore hsameEnd hmove hraw) }
  rcases machine_reaches_incrementSchedule_with base c (ShortSearches base c)
      (fun _ => False) runner source register h hroom hshort hcommands with
    result | failure
  · exact result
  · exact failure.elim

theorem incrementSchedule_source_blank
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T) (register : Register)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    logicalTape spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register)) =
      blankSymbol := by
  exact (CounterControlCoreFrame.PrefixRepresents.ofFramed
      (incrementTape_represents h register hroom)).toCoreRepresents
    |>.increment_source_blank spec.registers register

/-- Recovery from the blank old source cell to boundary `4` after a complete
increment schedule. -/
theorem machine_reaches_incrementRecovery_solved
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical spec.growth next
          | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
        atLogical spec.growth T
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨logicalState base c spec.growth next,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
  have hcommands : ∀ raw,
      raw ∈ routeCommandsAux spec.growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical spec.growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hrules : ∀ raw,
      raw ∈ routeEntryRules spec.growth source
            (match AnchoredCounterGeometry.routeFromIncrement register with
            | [] => .logical spec.growth next
            | _ :: _ => directRef spec.growth source (bodyDirectBase + 1))
            (MarkerSchedule.decrementStartBoundary register)
            secondarySearchBase
            (AnchoredCounterGeometry.routeFromIncrement register) ++
          routeContinuationRules spec.growth source secondarySearchBase
            (bodyDirectBase + 2)
            (AnchoredCounterGeometry.routeFromIncrement register) →
        raw ∈ rawDirectRules := by
    intro raw hraw
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      incrementRules spec.growth source next register
    apply List.mem_append_right
    have hraw' : raw ∈
        routeEntryRules spec.growth source
            (directRef spec.growth source (bodyDirectBase + 1))
            (MarkerSchedule.decrementStartBoundary register)
            secondarySearchBase
            (AnchoredCounterGeometry.routeFromIncrement register) ++
          routeContinuationRules spec.growth source secondarySearchBase
            (bodyDirectBase + 2)
            (AnchoredCounterGeometry.routeFromIncrement register) := by
      generalize hroute : AnchoredCounterGeometry.routeFromIncrement register =
        route at hraw ⊢
      cases route with
      | nil => simp [routeEntryRules, routeContinuationRules] at hraw
      | cons first rest => exact hraw
    rcases List.mem_append.mp hraw' with hentry | hcontinuation
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hentry))
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inr hcontinuation)
  exact route_reaches_solved_at_maybe_empty base c spec.outerDistance hshort
    spec.growth source secondarySearchBase (bodyDirectBase + 2)
    (match AnchoredCounterGeometry.routeFromIncrement register with
    | [] => .logical spec.growth next
    | _ :: _ => directRef spec.growth source (bodyDirectBase + 1))
    (.logical spec.growth next)
    (MarkerSchedule.decrementStartBoundary register)
    (AnchoredCounterGeometry.routeFromIncrement register)
    (by
      intro hnil
      simp [hnil])
    T
    (boundaryOffset spec.registers
      (MarkerSchedule.decrementStartBoundary register))
    (layoutEnd spec.registers)
    (by rw [atLogical_read]; exact h.boundary _)
    (routeFromIncrement_executesWithin h register) hcommands hrules

/-- The direct blank rule after the final increment shift moves onto the new
boundary and selects either the recovery route or (for clock) the logical
successor directly. -/
theorem machine_reaches_incrementHandoff
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical spec.growth next
          | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset (spec.registers.increment register)
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  let route := AnchoredCounterGeometry.routeFromIncrement register
  let afterShift : ControlRef := match route with
    | [] => .logical spec.growth next
    | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)
  let raw : RawDirectRule :=
    ⟨spec.growth, directRef spec.growth source bodyDirectBase, .blank,
      afterShift, .right⟩
  have hraw : raw ∈ rawDirectRules := by
    apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
    change raw ∈ validationRules spec.growth source ++
      incrementRules spec.growth source next register
    apply List.mem_append_right
    simp only [incrementRules, List.mem_append]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    simp only [List.mem_singleton]
    exact rfl
  have hblank : raw.read.Matches
      (atLogical spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))).read := by
    change (atLogical spec.growth (incrementTape spec register T)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))).read = blankSymbol
    rw [atLogical_read]
    exact incrementSchedule_source_blank h register hroom
  have hrun := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw (atLogical spec.growth (incrementTape spec register T)
      (boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register))) hblank
  have hcoord : boundaryOffset spec.registers
        (MarkerSchedule.decrementStartBoundary register) + 1 =
      boundaryOffset (spec.registers.increment register)
        (MarkerSchedule.decrementStartBoundary register) :=
    AnchoredCounterGeometry.incrementStartBoundary_add_one
      spec.registers register
  rw [show orient spec.growth .right =
    OrientedMarkerTape.orientDirection spec.growth .right by
      exact orient_eq_orientDirection spec.growth .right,
    atLogical_move_right, hcoord] at hrun
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨resolve base c (directRef spec.growth source bodyDirectBase),
      atLogical spec.growth (incrementTape spec register T)
        (boundaryOffset spec.registers
          (MarkerSchedule.decrementStartBoundary register))⟩
    ⟨resolve base c
        (match AnchoredCounterGeometry.routeFromIncrement register with
        | [] => .logical spec.growth next
        | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
      atLogical spec.growth (incrementTape spec register T)
        (boundaryOffset (spec.registers.increment register)
          (MarkerSchedule.decrementStartBoundary register))⟩ at hrun
  exact hrun

/-- Recovery specialized to the frame and tape produced by a successful
increment.  Keeping this transport next to the recovery proof hides the
proof-dependent `incrementSpec` bookkeeping from later clients. -/
theorem machine_reaches_incrementRecovery_after_increment
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c
          (match AnchoredCounterGeometry.routeFromIncrement register with
          | [] => .logical spec.growth next
          | _ :: _ => directRef spec.growth source (bodyDirectBase + 1)),
        atLogical spec.growth (incrementTape spec register T)
          (boundaryOffset (spec.registers.increment register)
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨logicalState base c spec.growth next,
        atLogical spec.growth (incrementTape spec register T)
          (layoutEnd (spec.registers.increment register))⟩ := by
  let nextSpec := incrementSpec spec register hroom
  have hnext : Represents nextSpec (incrementTape spec register T) :=
    incrementTape_represents h register hroom
  have hrun := machine_reaches_incrementRecovery_solved base c source next
    register hrule hnext (by
      simpa [nextSpec, incrementSpec, updateSpec] using hshort)
  simpa [nextSpec, incrementSpec, updateSpec] using hrun

/-- Exact successful semantics of one compiled increment instruction on a
backed frame. -/
theorem machine_reaches_incrementInstruction_solved
    (base : Nat) (c : Nat.Partrec.Code) (source next : Nat)
    (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hroom : layoutEnd (spec.registers.increment register) <
      spec.outerDistance)
    (hshort : ShortSearches base c spec.outerDistance) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c spec.growth source,
          atLogical spec.growth T (layoutEnd spec.registers)⟩
        ⟨logicalState base c spec.growth next,
          atLogical spec.growth (incrementTape spec register T)
            (layoutEnd (spec.registers.increment register))⟩ ∧
      BackedBy (incrementSpec spec register hroom)
        (incrementTape spec register T) outer := by
  have h := hback.represents
  have hvalidation := machine_reaches_validation_solved base c spec.growth
    source (.increment register next) hrule h rfl hshort
  have hcommands : ∀ raw,
      raw ∈ incrementShiftCommands spec.growth source register →
        raw ∈ rawCommands := by
    intro raw hraw
    apply command_mem_rawCommands_of_rule spec.growth hrule
    simp [commandsForRule, incrementCommands, hraw]
  have hschedule := machine_reaches_incrementSchedule_solved base c source
    register h hroom hshort hcommands
  have hhandoff := machine_reaches_incrementHandoff base c source next
    register hrule h hroom
  have hrecovery := machine_reaches_incrementRecovery_after_increment base c
    source next register hrule h hroom hshort
  have hvalidation' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c spec.growth source,
        atLogical spec.growth T (layoutEnd spec.registers)⟩
      ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
        atLogical spec.growth T (layoutEnd spec.registers)⟩ := by
    simpa [bodyEntry, searchRef, CounterControlPlan.resolve] using hvalidation
  constructor
  · exact hvalidation'.trans
      (hschedule.trans (hhandoff.trans hrecovery))
  · exact incrementTape_backedBy hback register hroom

end

end CounterControlInstructionSemantics
end Hooper
end Kari
end LeanWang
