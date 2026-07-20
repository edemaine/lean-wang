/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionSearchSemantics
import LeanWang.Kari.Hooper.CounterControlScheduleStages

/-!
# Representation-independent increment-prefix scheduling

This module folds the fixed clock-to-register increment prefix independently
of whether each primitive shift is justified by a finite framed tape or an
open core.  Those representations need only provide the two normalized shift
operations below.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlScheduleSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlBridge

noncomputable section

/-- Normalized operational interface for an increment prefix.  Each stage
tape is expressed over the original register layout, hiding the distinct
finite-frame and open-core installation lemmas from the structural fold. -/
structure IncrementPrefixRunner
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (growth : Turing.Dir) (registers : Registers)
    (T : FullTM0.Tape (Symbol numTags)) where
  stageTape : Register → FullTM0.Tape (Symbol numTags)
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  clock : ∀ (source searchSlot : Nat) (success : ControlRef)
      (collision : Option ControlRef),
    RawCommand.markerShift
        ⟨growth, source, searchSlot⟩ 4 .left .right success
        (some .left) collision ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth T (layoutEnd registers)⟩
        ⟨resolve base c success,
          atLogical growth (stageTape .clock) (layoutEnd registers)⟩
  internal : ∀ (source searchSlot : Nat) (success : ControlRef)
      {current next : Register}, IncrementStageNext current next →
    RawCommand.markerShift
        ⟨growth, source, searchSlot⟩
        (incrementStageIndex next).castSucc .left .right success
        (some .left) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth (stageTape current)
            (lastGapOffset (registers.increment current)
              (incrementStageIndex next))⟩
        ⟨resolve base c success,
          atLogical growth (stageTape next)
            (boundaryOffset (registers.increment current)
              (incrementStageIndex next).castSucc)⟩

/-- Fold the non-clock tail of a normalized increment prefix. -/
private theorem incrementPrefixTail
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    {growth : Turing.Dir} {registers : Registers}
    {T : FullTM0.Tape (Symbol numTags)}
    (runner : IncrementPrefixRunner base c Failure growth registers T)
    (source searchSlot : Nat)
    {current next target : Register} {tail : List Register}
    (hnext : IncrementStageNext current next)
    (hrest : IncrementStageChain next target tail)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommandsAux growth source searchSlot false
        ((next :: tail).map
          (fun stage => (incrementStageIndex stage).castSucc)) →
      raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, source, searchSlot⟩,
        atLogical growth (runner.stageTape current)
          (lastGapOffset (registers.increment current)
            (incrementStageIndex next))⟩
      ⟨resolve base c (directRef growth source bodyDirectBase),
        atLogical growth (runner.stageTape target)
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary target))⟩ := by
  induction hrest generalizing current searchSlot with
  | done stage =>
      have hraw : RawCommand.markerShift
          ⟨growth, source, searchSlot⟩
          (incrementStageIndex stage).castSucc .left .right
          (directRef growth source bodyDirectBase) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommandsAux]
      have hrun := runner.internal source searchSlot
        (directRef growth source bodyDirectBase) hnext hraw
      rw [incrementStage_finish registers
        (current := current) (next := stage) hnext] at hrun
      exact hrun
  | @cons next after target tail hafter htail ih =>
      have hraw : RawCommand.markerShift
          ⟨growth, source, searchSlot⟩
          (incrementStageIndex next).castSucc .left .right
          (searchRef growth source (searchSlot + 1)) (some .left) none ∈
            rawCommands := by
        apply hcommands
        simp [incrementShiftCommandsAux]
      have hrun := runner.internal source searchSlot
        (searchRef growth source (searchSlot + 1)) hnext hraw
      rw [incrementStage_head registers
        (current := current) (next := next) (after := after)
        hnext hafter] at hrun
      simp only [searchRef, CounterControlPlan.resolve] at hrun
      have hnextCommands : ∀ raw,
          raw ∈ incrementShiftCommandsAux growth source
            (searchSlot + 1) false
            ((after :: tail).map
              (fun stage => (incrementStageIndex stage).castSucc)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simpa [incrementShiftCommandsAux] using List.mem_cons_of_mem _ hraw'
      have htailRun := ih (current := next) (searchSlot := searchSlot + 1)
        hafter hnextCommands
      exact FullTM0.CompletesOr.trans runner.pullback hrun htailRun

/-- Run the complete prefix through the selected register. -/
theorem machine_reaches_incrementPrefix_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    {growth : Turing.Dir} {registers : Registers}
    {T : FullTM0.Tape (Symbol numTags)}
    (runner : IncrementPrefixRunner base c Failure growth registers T)
    (source : Nat) (register : Register)
    (hcommands : ∀ raw,
      raw ∈ incrementShiftCommands growth source register →
        raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        atLogical growth T (layoutEnd registers)⟩
      ⟨resolve base c (directRef growth source bodyDirectBase),
        atLogical growth (runner.stageTape register)
          (boundaryOffset registers
            (MarkerSchedule.decrementStartBoundary register))⟩ := by
  generalize hstages : incrementStages register = stages
  have hlabels :
      4 :: stages.map
          (fun stage => (incrementStageIndex stage).castSucc) =
        MarkerShift.incrementOrder register := by
    rw [← hstages]
    exact incrementStages_labels register
  have hchain : IncrementStageChain .clock register stages := by
    rw [← hstages]
    exact incrementStages_chain register
  clear hstages
  revert hlabels
  cases hchain with
  | done =>
      intro _
      have hraw : RawCommand.markerShift
          ⟨growth, source, bodySearchBase⟩ 4 .left .right
          (directRef growth source bodyDirectBase) (some .left)
          (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
        apply hcommands
        simp [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder]
      simpa [MarkerSchedule.decrementStartBoundary] using
        runner.clock source bodySearchBase
          (directRef growth source bodyDirectBase)
          (some (directRef growth source testDirectSlot)) hraw
  | @cons _ next _ tail hnext hrest =>
      intro hlabels
      have hraw : RawCommand.markerShift
          ⟨growth, source, bodySearchBase⟩ 4 .left .right
          (searchRef growth source (bodySearchBase + 1)) (some .left)
          (some (directRef growth source testDirectSlot)) ∈ rawCommands := by
        apply hcommands
        simp only [incrementShiftCommands]
        rw [← hlabels]
        simp [incrementShiftCommandsAux]
      have hclock := runner.clock source bodySearchBase
        (searchRef growth source (bodySearchBase + 1))
        (some (directRef growth source testDirectSlot)) hraw
      have hclock' : FullTM0.CompletesOr
          (CounterControlNestingBridge.machine base c) Failure
          ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
            atLogical growth T (layoutEnd registers)⟩
          ⟨searchState base c ⟨growth, source, bodySearchBase + 1⟩,
            atLogical growth (runner.stageTape .clock)
              (lastGapOffset (registers.increment .clock)
                (incrementStageIndex next))⟩ := by
        cases hnext
        simpa [searchRef, CounterControlPlan.resolve, incrementStageIndex,
          incrementSchedule_clock_start registers] using hclock
      have htailCommands : ∀ raw,
          raw ∈ incrementShiftCommandsAux growth source
            (bodySearchBase + 1) false
            ((next :: tail).map
              (fun stage => (incrementStageIndex stage).castSucc)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simp only [incrementShiftCommands]
        rw [← hlabels]
        exact List.mem_cons_of_mem _ hraw'
      have htailRun := incrementPrefixTail base c Failure runner source
        (bodySearchBase + 1) hnext hrest htailCommands
      exact FullTM0.CompletesOr.trans runner.pullback hclock' htailRun

end

end CounterControlScheduleSemantics
end Hooper
end Kari
end LeanWang
