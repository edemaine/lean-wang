/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionSearchSemantics

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

/- The increment schedule visits boundaries 4, 3, 2, and 1 in order.
These equations isolate its fixed geometry from the execution proof. -/
theorem incrementSchedule_clock_start (registers : Registers) :
    layoutEnd registers =
      lastGapOffset (registers.increment .clock) 3 := by
  simp [lastGapOffset, CounterLayout.boundaryPos, layoutEnd,
    RegisterLayout.clockBoundary_eq, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]
  omega

theorem incrementSchedule_clock_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .temp) 2 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

theorem incrementSchedule_temp_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .right) 1 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

theorem incrementSchedule_finish_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      boundaryOffset registers 3 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

theorem incrementSchedule_finish_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      boundaryOffset registers 2 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

theorem incrementSchedule_finish_left (registers : Registers) :
    boundaryOffset (registers.increment .right) ((1 : Fin 4).castSucc) =
      boundaryOffset registers 1 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

/-! ## Generic increment prefixes -/

/-- Consecutive stages in the fixed clock-to-left increment order. -/
inductive IncrementStageNext : Register → Register → Prop
  | clock : IncrementStageNext .clock .temp
  | temp : IncrementStageNext .temp .right
  | right : IncrementStageNext .right .left

/-- The internal boundary index used to install a non-clock stage. -/
def incrementStageIndex : Register → Fin 4
  | .clock => 3
  | .temp => 3
  | .right => 2
  | .left => 1

/-- The stages following the mandatory clock shift, through the selected
target register. -/
def incrementStages : Register → List Register
  | .clock => []
  | .temp => [.temp]
  | .right => [.temp, .right]
  | .left => [.temp, .right, .left]

/-- A tail follows the fixed increment order and ends at its target. -/
inductive IncrementStageChain : Register → Register →
    List Register → Prop
  | done (stage : Register) : IncrementStageChain stage stage []
  | cons {current next target : Register} {tail : List Register}
      (hnext : IncrementStageNext current next)
      (hrest : IncrementStageChain next target tail) :
      IncrementStageChain current target (next :: tail)

theorem incrementStages_chain (register : Register) :
    IncrementStageChain .clock register (incrementStages register) := by
  cases register with
  | clock => exact .done .clock
  | temp => exact .cons .clock (.done .temp)
  | right => exact .cons .clock (.cons .temp (.done .right))
  | left =>
      exact .cons .clock (.cons .temp (.cons .right (.done .left)))

theorem incrementStages_labels (register : Register) :
    4 :: (incrementStages register).map
        (fun stage => (incrementStageIndex stage).castSucc) =
      MarkerShift.incrementOrder register := by
  cases register <;> rfl

theorem incrementStage_positive (registers : Registers)
    {current next : Register} (hnext : IncrementStageNext current next) :
    0 < RegisterLayout.values (registers.increment current)
      (incrementStageIndex next) := by
  cases hnext <;>
    simp [incrementStageIndex, RegisterLayout.values, Registers.increment,
      Registers.set, Registers.get]

theorem incrementStage_move (registers : Registers)
    {current next : Register} (hnext : IncrementStageNext current next) :
    MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape (registers.increment current))
        (MarkerTape.boundaryPosition (registers.increment current)
          (incrementStageIndex next).castSucc)
        (incrementStageIndex next).castSucc =
      MarkerTape.canonicalTape (registers.increment next) := by
  cases hnext with
  | clock => exact MarkerSchedule.moveTempBoundary_after_clock registers
  | temp => exact MarkerSchedule.moveRightBoundary_after_temp registers
  | right => exact MarkerSchedule.moveLeftBoundary_after_right registers

theorem incrementStage_head (registers : Registers)
    {current next after : Register}
    (hnext : IncrementStageNext current next)
    (hafter : IncrementStageNext next after) :
    boundaryOffset (registers.increment current)
        (incrementStageIndex next).castSucc =
      lastGapOffset (registers.increment next) (incrementStageIndex after) := by
  cases hnext <;> cases hafter
  · exact incrementSchedule_clock_temp registers
  · exact incrementSchedule_temp_right registers

theorem incrementStage_finish (registers : Registers)
    {current next : Register} (hnext : IncrementStageNext current next) :
    boundaryOffset (registers.increment current)
        (incrementStageIndex next).castSucc =
      boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary next) := by
  cases hnext with
  | clock => exact incrementSchedule_finish_temp registers
  | temp => exact incrementSchedule_finish_right registers
  | right => exact incrementSchedule_finish_left registers

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

/-- Fold the non-clock tail of an increment prefix. -/
private theorem incrementTail_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Short : Nat → Prop)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (runner : IncrementScheduleRunner base c Short Failure)
    (source searchSlot : Nat)
    {current next target : Register} {tail : List Register}
    (hnext : IncrementStageNext current next)
    (hrest : IncrementStageChain next target tail)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : Represents spec T)
    (hroom : layoutEnd (spec.registers.increment target) <
      spec.outerDistance)
    (hshort : Short spec.outerDistance)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommandsAux spec.growth source searchSlot false
        ((next :: tail).map
          (fun stage => (incrementStageIndex stage).castSucc)) →
      raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨spec.growth, source, searchSlot⟩,
        atLogical spec.growth (incrementTape spec current T)
          (lastGapOffset (spec.registers.increment current)
            (incrementStageIndex next))⟩
      ⟨resolve base c (directRef spec.growth source bodyDirectBase),
        atLogical spec.growth (incrementTape spec target T)
          (boundaryOffset spec.registers
            (MarkerSchedule.decrementStartBoundary target))⟩ := by
  induction hrest generalizing current searchSlot with
  | done stage =>
      have hcurrentRoom : layoutEnd (spec.registers.increment current) <
          spec.outerDistance := by
        simpa only [layoutEnd_increment] using hroom
      let currentSpec := incrementSpec spec current hcurrentRoom
      let currentTape := incrementTape spec current T
      have hcurrentRep : Represents currentSpec currentTape :=
        incrementTape_represents h current hcurrentRoom
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, searchSlot⟩
          (incrementStageIndex stage).castSucc .left .right
          (directRef spec.growth source bodyDirectBase) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommandsAux]
      have hrun := runner.internal spec.outerDistance hshort source searchSlot
        (directRef spec.growth source bodyDirectBase) none hcurrentRep
        (spec.registers.increment stage) (incrementStageIndex stage)
        (by
          simpa only [currentSpec, incrementSpec, updateSpec] using
            incrementStage_positive spec.registers hnext)
        (by
          simpa [currentSpec, incrementSpec, updateSpec] using
            registerValue_lt_outerDistance hcurrentRep
              (incrementStageIndex stage))
        (by simpa [currentSpec, incrementSpec, updateSpec,
          layoutEnd_increment] using hroom)
        (by simp [currentSpec, incrementSpec, updateSpec,
          layoutEnd_increment])
        (by
          simpa only [currentSpec, incrementSpec, updateSpec] using
            incrementStage_move spec.registers hnext)
        hraw
      have htape : install (spec.registers.increment stage) spec.growth
          spec.returnTag currentTape = incrementTape spec stage T := by
        simpa [currentTape] using
          install_incrementTape_eq spec T current stage
      simp only [currentSpec, incrementSpec, updateSpec] at hrun
      rw [htape, incrementStage_finish spec.registers
        (current := current) (next := stage) hnext] at hrun
      exact hrun
  | @cons next after target tail hafter htail ih =>
      have hcurrentRoom : layoutEnd (spec.registers.increment current) <
          spec.outerDistance := by
        simpa only [layoutEnd_increment] using hroom
      let currentSpec := incrementSpec spec current hcurrentRoom
      let currentTape := incrementTape spec current T
      have hcurrentRep : Represents currentSpec currentTape :=
        incrementTape_represents h current hcurrentRoom
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, searchSlot⟩
          (incrementStageIndex next).castSucc .left .right
          (searchRef spec.growth source (searchSlot + 1))
          (some .left) none ∈ rawCommands := by
        apply hcommands
        simp [incrementShiftCommandsAux]
      have hrun := runner.internal spec.outerDistance hshort source searchSlot
        (searchRef spec.growth source (searchSlot + 1)) none hcurrentRep
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
      rw [htape, incrementStage_head spec.registers
        (current := current) (next := next) (after := after)
        hnext hafter] at hrun
      simp only [searchRef, CounterControlPlan.resolve] at hrun
      have hnextCommands : ∀ raw,
          raw ∈ incrementShiftCommandsAux spec.growth source
            (searchSlot + 1) false
            ((after :: tail).map
              (fun stage => (incrementStageIndex stage).castSucc)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simpa [incrementShiftCommandsAux] using List.mem_cons_of_mem _ hraw'
      have htailRun := ih (current := next) (searchSlot := searchSlot + 1)
        hafter hroom hnextCommands
      exact FullTM0.CompletesOr.trans runner.pullback hrun htailRun

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
  have hclockRoom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  generalize hstages : incrementStages register = stages
  have hlabels :
      4 :: stages.map
          (fun stage => (incrementStageIndex stage).castSucc) =
        MarkerShift.incrementOrder register :=
    by rw [← hstages]; exact incrementStages_labels register
  have hchain : IncrementStageChain .clock register stages := by
    rw [← hstages]
    exact incrementStages_chain register
  clear hstages
  revert hlabels
  cases hchain with
  | done =>
      intro hlabels
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (directRef spec.growth source bodyDirectBase) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      simpa [MarkerSchedule.decrementStartBoundary] using
        runner.clock spec.outerDistance hshort source bodySearchBase
          (directRef spec.growth source bodyDirectBase)
          (some (directRef spec.growth source testDirectSlot)) h hclockRoom
          hlimit hraw
  | @cons _ next _ tail hnext hrest =>
      intro hlabels
      have hraw : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp only [incrementShiftCommands]
        rw [← hlabels]
        simp [incrementShiftCommandsAux]
      have hclock := runner.clock spec.outerDistance hshort source
        bodySearchBase (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hraw
      have hclock' : FullTM0.CompletesOr
          (CounterControlNestingBridge.machine base c) Failure
          ⟨searchState base c ⟨spec.growth, source, bodySearchBase⟩,
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨searchState base c
              ⟨spec.growth, source, bodySearchBase + 1⟩,
            atLogical spec.growth (incrementTape spec .clock T)
              (lastGapOffset (spec.registers.increment .clock)
                (incrementStageIndex next))⟩ := by
        cases hnext
        simpa [searchRef, CounterControlPlan.resolve, incrementStageIndex,
          incrementSchedule_clock_start spec.registers] using hclock
      have htailCommands : ∀ raw,
          raw ∈ incrementShiftCommandsAux spec.growth source
            (bodySearchBase + 1) false
            ((next :: tail).map
              (fun stage => (incrementStageIndex stage).castSucc)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simp only [incrementShiftCommands]
        rw [← hlabels]
        exact List.mem_cons_of_mem _ hraw'
      have htailRun := incrementTail_with base c Short Failure runner source
        (bodySearchBase + 1) hnext hrest h hroom hshort htailCommands
      exact FullTM0.CompletesOr.trans runner.pullback hclock' htailRun
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
