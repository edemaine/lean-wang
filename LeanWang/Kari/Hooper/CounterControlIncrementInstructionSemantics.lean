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
private theorem incrementSchedule_clock_start (registers : Registers) :
    layoutEnd registers =
      lastGapOffset (registers.increment .clock) 3 := by
  simp [lastGapOffset, CounterLayout.boundaryPos, layoutEnd,
    RegisterLayout.clockBoundary_eq, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]
  omega

private theorem incrementSchedule_clock_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .temp) 2 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

private theorem incrementSchedule_temp_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .right) 1 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

private theorem incrementSchedule_finish_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      boundaryOffset registers 3 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

private theorem incrementSchedule_finish_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      boundaryOffset registers 2 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

private theorem incrementSchedule_finish_left (registers : Registers) :
    boundaryOffset (registers.increment .right) ((1 : Fin 4).castSucc) =
      boundaryOffset registers 1 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

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
    have := hroom
    omega
  have hclockRoom : layoutEnd (spec.registers.increment .clock) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have htempRoom : layoutEnd (spec.registers.increment .temp) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have hrightRoom : layoutEnd (spec.registers.increment .right) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  have hleftRoom : layoutEnd (spec.registers.increment .left) <
      spec.outerDistance := by
    simpa only [layoutEnd_increment] using hroom
  cases register with
  | clock =>
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
  | temp =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hfour := runner.clock spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (directRef clockSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hthree := runner.internal spec.outerDistance hshort source (bodySearchBase + 1)
        (directRef clockSpec.growth source bodyDirectBase) none hclockRep
        (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htape : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = incrementTape spec .temp T := by
        simpa [clockTape] using
          install_incrementTape_eq spec T .clock .temp
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htape] at hthree
      rw [← incrementSchedule_clock_start spec.registers,
        incrementSchedule_finish_temp spec.registers] at hthree
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact FullTM0.CompletesOr.trans runner.pullback hfour hthree
  | right =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      let tempTape := incrementTape spec .temp T
      let tempSpec := incrementSpec spec .temp htempRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have htempRep : Represents tempSpec tempTape :=
        incrementTape_represents h .temp htempRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef clockSpec.growth source (bodySearchBase + 2))
          (some .left) none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (searchRef spec.growth source (bodySearchBase + 2))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawTwo : RawCommand.markerShift
          ⟨tempSpec.growth, source, bodySearchBase + 2⟩ 2 .left .right
          (directRef tempSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [tempSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 2⟩ 2 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hfour := runner.clock spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := runner.internal spec.outerDistance hshort source (bodySearchBase + 1)
        (searchRef clockSpec.growth source (bodySearchBase + 2)) none
        hclockRep (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htwo := runner.internal spec.outerDistance hshort source (bodySearchBase + 2)
        (directRef tempSpec.growth source bodyDirectBase) none htempRep
        (spec.registers.increment .right) (2 : Fin 4)
        (by simp [tempSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance htempRep (2 : Fin 4))
        (by simpa [tempSpec, incrementSpec, updateSpec] using hrightRoom)
        (by simp [tempSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveRightBoundary_after_temp spec.registers)
        hrawTwo
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        simpa [clockTape, tempTape] using
          install_incrementTape_eq spec T .clock .temp
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = incrementTape spec .right T := by
        simpa [tempTape] using
          install_incrementTape_eq spec T .temp .right
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      rw [← incrementSchedule_clock_start spec.registers,
        incrementSchedule_clock_temp spec.registers] at hthree
      rw [incrementSchedule_finish_right spec.registers] at htwo
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree
      exact FullTM0.CompletesOr.trans runner.pullback hfour
        (FullTM0.CompletesOr.trans runner.pullback hthree htwo)
  | left =>
      let clockTape := incrementTape spec .clock T
      let clockSpec := incrementSpec spec .clock hclockRoom
      let tempTape := incrementTape spec .temp T
      let tempSpec := incrementSpec spec .temp htempRoom
      let rightTape := incrementTape spec .right T
      let rightSpec := incrementSpec spec .right hrightRoom
      have hclockRep : Represents clockSpec clockTape :=
        incrementTape_represents h .clock hclockRoom
      have htempRep : Represents tempSpec tempTape :=
        incrementTape_represents h .temp htempRoom
      have hrightRep : Represents rightSpec rightTape :=
        incrementTape_represents h .right hrightRoom
      have hrawFour : RawCommand.markerShift
          ⟨spec.growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef spec.growth source (bodySearchBase + 1)) (some .left)
          (some (directRef spec.growth source testDirectSlot)) ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      have hrawThree : RawCommand.markerShift
          ⟨clockSpec.growth, source, bodySearchBase + 1⟩ 3 .left .right
          (searchRef clockSpec.growth source (bodySearchBase + 2))
          (some .left) none ∈ rawCommands := by
        simpa [clockSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 1⟩ 3 .left .right
            (searchRef spec.growth source (bodySearchBase + 2))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawTwo : RawCommand.markerShift
          ⟨tempSpec.growth, source, bodySearchBase + 2⟩ 2 .left .right
          (searchRef tempSpec.growth source (bodySearchBase + 3))
          (some .left) none ∈ rawCommands := by
        simpa [tempSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 2⟩ 2 .left .right
            (searchRef spec.growth source (bodySearchBase + 3))
            (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hrawOne : RawCommand.markerShift
          ⟨rightSpec.growth, source, bodySearchBase + 3⟩ 1 .left .right
          (directRef rightSpec.growth source bodyDirectBase) (some .left)
          none ∈ rawCommands := by
        simpa [rightSpec, incrementSpec, updateSpec] using hcommands
          (.markerShift
            ⟨spec.growth, source, bodySearchBase + 3⟩ 1 .left .right
            (directRef spec.growth source bodyDirectBase) (some .left) none)
          (by simp [incrementShiftCommands, incrementShiftCommandsAux,
            MarkerShift.incrementOrder])
      have hfour := runner.clock spec.outerDistance hshort source bodySearchBase
        (searchRef spec.growth source (bodySearchBase + 1))
        (some (directRef spec.growth source testDirectSlot)) h hclockRoom
        hlimit hrawFour
      have hthree := runner.internal spec.outerDistance hshort source (bodySearchBase + 1)
        (searchRef clockSpec.growth source (bodySearchBase + 2)) none
        hclockRep (spec.registers.increment .temp) (3 : Fin 4)
        (by simp [clockSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hclockRep (3 : Fin 4))
        (by simpa [clockSpec, incrementSpec, updateSpec] using htempRoom)
        (by simp [clockSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [clockSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveTempBoundary_after_clock spec.registers)
        hrawThree
      have htwo := runner.internal spec.outerDistance hshort source (bodySearchBase + 2)
        (searchRef tempSpec.growth source (bodySearchBase + 3)) none
        htempRep (spec.registers.increment .right) (2 : Fin 4)
        (by simp [tempSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance htempRep (2 : Fin 4))
        (by simpa [tempSpec, incrementSpec, updateSpec] using hrightRoom)
        (by simp [tempSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [tempSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveRightBoundary_after_temp spec.registers)
        hrawTwo
      have hone := runner.internal spec.outerDistance hshort source (bodySearchBase + 3)
        (directRef rightSpec.growth source bodyDirectBase) none hrightRep
        (spec.registers.increment .left) (1 : Fin 4)
        (by simp [rightSpec, incrementSpec, updateSpec,
          RegisterLayout.values, Registers.increment, Registers.set,
          Registers.get])
        (by simpa [rightSpec, incrementSpec, updateSpec] using
          registerValue_lt_outerDistance hrightRep (1 : Fin 4))
        (by simpa [rightSpec, incrementSpec, updateSpec] using hleftRoom)
        (by simp [rightSpec, incrementSpec, updateSpec, layoutEnd_increment])
        (by simpa [rightSpec, incrementSpec, updateSpec] using
          MarkerSchedule.moveLeftBoundary_after_right spec.registers)
        hrawOne
      have htapeThree : install (spec.registers.increment .temp) spec.growth
          spec.returnTag clockTape = tempTape := by
        simpa [clockTape, tempTape] using
          install_incrementTape_eq spec T .clock .temp
      simp only [clockSpec, incrementSpec, updateSpec] at hthree
      rw [htapeThree] at hthree
      have htapeTwo : install (spec.registers.increment .right) spec.growth
          spec.returnTag tempTape = rightTape := by
        simpa [tempTape, rightTape] using
          install_incrementTape_eq spec T .temp .right
      simp only [tempSpec, incrementSpec, updateSpec] at htwo
      rw [htapeTwo] at htwo
      have htapeOne : install (spec.registers.increment .left) spec.growth
          spec.returnTag rightTape = incrementTape spec .left T := by
        simpa [rightTape] using
          install_incrementTape_eq spec T .right .left
      simp only [rightSpec, incrementSpec, updateSpec] at hone
      rw [htapeOne] at hone
      rw [← incrementSchedule_clock_start spec.registers,
        incrementSchedule_clock_temp spec.registers] at hthree
      rw [incrementSchedule_temp_right spec.registers] at htwo
      rw [incrementSchedule_finish_left spec.registers] at hone
      simp only [searchRef, CounterControlPlan.resolve] at hfour hthree htwo
      exact FullTM0.CompletesOr.trans runner.pullback hfour
        (FullTM0.CompletesOr.trans runner.pullback hthree
          (FullTM0.CompletesOr.trans runner.pullback htwo hone))

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
            (directRef spec.growth source (bodyDirectBase + 1))
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
    rcases List.mem_append.mp hraw with hentry | hcontinuation
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hentry))
    · simp only [incrementRules, List.mem_append]
      exact Or.inl (Or.inr hcontinuation)
  cases register with
  | clock =>
      exact Relation.ReflTransGen.refl
  | temp =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 3
        (AnchoredCounterGeometry.routeFromIncrement .temp)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 3) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 3)
        (routeFromIncrement_executesWithin h .temp)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | right =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 2
        (AnchoredCounterGeometry.routeFromIncrement .right)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 2) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 2)
        (routeFromIncrement_executesWithin h .right)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun
  | left =>
      have hrun := route_reaches_solved_at_of_ne_nil base c
        spec.outerDistance hshort
        spec.growth source secondarySearchBase (bodyDirectBase + 2)
        (directRef spec.growth source (bodyDirectBase + 1))
        (.logical spec.growth next) 1
        (AnchoredCounterGeometry.routeFromIncrement .left)
        (by simp [AnchoredCounterGeometry.routeFromIncrement]) T
        (boundaryOffset spec.registers 1) (layoutEnd spec.registers)
        (by rw [atLogical_read]; exact h.boundary 1)
        (routeFromIncrement_executesWithin h .left)
        (by intro raw hraw; exact hcommands raw hraw)
        (by intro raw hraw; exact hrules raw hraw)
      simpa [AnchoredCounterGeometry.routeFromIncrement, logicalState,
        CounterControlPlan.resolve,
        MarkerSchedule.decrementStartBoundary] using hrun

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
