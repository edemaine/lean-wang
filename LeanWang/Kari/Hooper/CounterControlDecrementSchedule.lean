/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionSearchSemantics
import LeanWang.Kari.Hooper.CounterControlScheduleStages

/-!
# Representation-independent positive-decrement scheduling

This module folds the fixed register-to-clock decrement suffix independently
of the tape representation used to justify its primitive shifts.  A runner
normalizes those shifts to one tape per intermediate stage and one final tape;
the controller trace is then shared by finite frames, open cores, and finite
tag-free prefixes.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlScheduleSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlBridge

noncomputable section

/-- Normalized operational interface for a positive-decrement suffix.  The
first boundary shift starts on the tested boundary; later shifts start at the
first cell of their represented gap. -/
structure DecrementSuffixRunner
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    (growth : Turing.Dir) (origin final : Registers) (start : Register)
    (original result : FullTM0.Tape (Symbol numTags)) where
  stageTape : Register → FullTM0.Tape (Symbol numTags)
  aligned : origin = decrementStageRegisters final start
  pullback : ∀ {start current},
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start current →
      Failure current → Failure start
  firstStep : ∀ (source searchSlot : Nat) (success : ControlRef)
      {current next : Register}, current = start →
    DecrementStageNext current next →
    RawCommand.markerShift
        ⟨growth, source, searchSlot⟩ (decrementStageIndex current).succ
        .right .left success (some .right) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth original
            (boundaryOffset origin (decrementStageIndex current).succ)⟩
        ⟨resolve base c success,
          atLogical growth (stageTape next)
            (boundaryOffset origin (decrementStageIndex current).succ)⟩
  followingStep : ∀ (source searchSlot : Nat) (success : ControlRef)
      {current next : Register}, DecrementStageNext current next →
    RawCommand.markerShift
        ⟨growth, source, searchSlot⟩ (decrementStageIndex current).succ
        .right .left success (some .right) none ∈ rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth (stageTape current)
            (firstGapOffset (decrementStageRegisters final current)
              (decrementStageIndex current))⟩
        ⟨resolve base c success,
          atLogical growth (stageTape next)
            (boundaryOffset (decrementStageRegisters final current)
              (decrementStageIndex current).succ)⟩
  firstFinish : ∀ (source searchSlot : Nat), start = .clock →
    RawCommand.markerShift
        ⟨growth, source, searchSlot⟩ 4 .right .left
        (directRef growth source finishDirectSlot) (some .right) none ∈
          rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth original (boundaryOffset origin 4)⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth result (layoutEnd origin)⟩
  followingFinish : ∀ (source searchSlot : Nat),
    RawCommand.markerShift
        ⟨growth, source, searchSlot⟩ 4 .right .left
        (directRef growth source finishDirectSlot) (some .right) none ∈
          rawCommands →
      FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
        ⟨searchState base c ⟨growth, source, searchSlot⟩,
          atLogical growth (stageTape .clock)
            (firstGapOffset (decrementStageRegisters final .clock) 3)⟩
        ⟨resolve base c (directRef growth source finishDirectSlot),
          atLogical growth result (layoutEnd origin)⟩

/-- Fold all shifts after the first shift of a decrement suffix. -/
private theorem decrementSuffixTail
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    {growth : Turing.Dir} {origin final : Registers} {start : Register}
    {original result : FullTM0.Tape (Symbol numTags)}
    (runner : DecrementSuffixRunner base c Failure growth origin final start
      original result)
    (source searchSlot : Nat) {stage : Register} {stages : List Register}
    (hchain : DecrementStageChain stage stages)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommandsAux growth source searchSlot
        (stages.map (fun current => (decrementStageIndex current).succ)) →
      raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, source, searchSlot⟩,
        atLogical growth (runner.stageTape stage)
          (firstGapOffset (decrementStageRegisters final stage)
            (decrementStageIndex stage))⟩
      ⟨resolve base c (directRef growth source finishDirectSlot),
        atLogical growth result (layoutEnd origin)⟩ := by
  induction hchain generalizing searchSlot with
  | clock =>
      apply runner.followingFinish source searchSlot
      apply hcommands
      simp [decrementShiftCommandsAux, decrementStageIndex]
  | @cons stage next tail hnext hrest ih =>
      have hraw : RawCommand.markerShift
          ⟨growth, source, searchSlot⟩
          (decrementStageIndex stage).succ .right .left
          (searchRef growth source (searchSlot + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommandsAux]
      have hstep := runner.followingStep source searchSlot
        (searchRef growth source (searchSlot + 1)) hnext hraw
      have htarget :
          (⟨resolve base c (searchRef growth source (searchSlot + 1)),
            atLogical growth (runner.stageTape next)
              (boundaryOffset (decrementStageRegisters final stage)
                (decrementStageIndex stage).succ)⟩ :
              FullTM0.Cfg (Symbol numTags) FiniteTM0.State) =
          ⟨resolve base c (searchRef growth source (searchSlot + 1)),
            atLogical growth (runner.stageTape next)
              (firstGapOffset (decrementStageRegisters final next)
                (decrementStageIndex next))⟩ := by
        rw [decrementStage_head (final := final) hnext]
      rw [htarget] at hstep
      simp only [searchRef, CounterControlPlan.resolve] at hstep
      have hnextCommands : ∀ raw,
          raw ∈ decrementShiftCommandsAux growth source (searchSlot + 1)
            ((next :: tail).map
              (fun current => (decrementStageIndex current).succ)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simpa [decrementShiftCommandsAux] using
          List.mem_cons_of_mem _ hraw'
      have htail := ih (searchSlot := searchSlot + 1) hnextCommands
      exact FullTM0.CompletesOr.trans runner.pullback hstep htail

/-- Use the first-stage entry convention once, then run the shared tail. -/
private theorem decrementSuffix
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    {growth : Turing.Dir} {origin final : Registers} {start : Register}
    {original result : FullTM0.Tape (Symbol numTags)}
    (runner : DecrementSuffixRunner base c Failure growth origin final start
      original result)
    (source : Nat) {stages : List Register}
    (hchain : DecrementStageChain start stages)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommandsAux growth source secondarySearchBase
        (stages.map (fun current => (decrementStageIndex current).succ)) →
      raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
        atLogical growth original
          (boundaryOffset origin (decrementStageIndex start).succ)⟩
      ⟨resolve base c (directRef growth source finishDirectSlot),
        atLogical growth result (layoutEnd origin)⟩ := by
  cases hchain with
  | clock =>
      apply runner.firstFinish source secondarySearchBase rfl
      apply hcommands
      simp [decrementShiftCommandsAux, decrementStageIndex]
  | @cons _ next tail hnext hrest =>
      have hraw : RawCommand.markerShift
          ⟨growth, source, secondarySearchBase⟩
          (decrementStageIndex start).succ .right .left
          (searchRef growth source (secondarySearchBase + 1))
          (some .right) none ∈ rawCommands := by
        apply hcommands
        simp [decrementShiftCommandsAux]
      have hfirst := runner.firstStep source secondarySearchBase
        (searchRef growth source (secondarySearchBase + 1)) rfl hnext hraw
      have hhead : boundaryOffset origin
            (decrementStageIndex start).succ =
          firstGapOffset (decrementStageRegisters final next)
            (decrementStageIndex next) := by
        rw [runner.aligned]
        exact decrementStage_head (final := final) hnext
      have htarget :
          (⟨resolve base c
              (searchRef growth source (secondarySearchBase + 1)),
            atLogical growth (runner.stageTape next)
              (boundaryOffset origin (decrementStageIndex start).succ)⟩ :
              FullTM0.Cfg (Symbol numTags) FiniteTM0.State) =
          ⟨resolve base c
              (searchRef growth source (secondarySearchBase + 1)),
            atLogical growth (runner.stageTape next)
              (firstGapOffset (decrementStageRegisters final next)
                (decrementStageIndex next))⟩ := by
        rw [hhead]
      rw [htarget] at hfirst
      simp only [searchRef, CounterControlPlan.resolve] at hfirst
      have htailCommands : ∀ raw,
          raw ∈ decrementShiftCommandsAux growth source
            (secondarySearchBase + 1)
            ((next :: tail).map
              (fun current => (decrementStageIndex current).succ)) →
          raw ∈ rawCommands := by
        intro raw hraw'
        apply hcommands raw
        simpa [decrementShiftCommandsAux] using
          List.mem_cons_of_mem _ hraw'
      have htail := decrementSuffixTail base c Failure runner source
        (secondarySearchBase + 1) hrest htailCommands
      exact FullTM0.CompletesOr.trans runner.pullback hfirst htail

/-- Run the complete positive-decrement suffix selected by `register`. -/
theorem machine_reaches_decrementSuffix_with
    (base : Nat) (c : Nat.Partrec.Code)
    (Failure : FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop)
    {growth : Turing.Dir} {origin final : Registers} {register : Register}
    {original result : FullTM0.Tape (Symbol numTags)}
    (runner : DecrementSuffixRunner base c Failure growth origin final register
      original result)
    (source : Nat)
    (hcommands : ∀ raw,
      raw ∈ decrementShiftCommands growth source register →
        raw ∈ rawCommands) :
    FullTM0.CompletesOr (CounterControlNestingBridge.machine base c) Failure
      ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
        atLogical growth original
          (boundaryOffset origin
            (MarkerSchedule.decrementStartBoundary register))⟩
      ⟨resolve base c (directRef growth source finishDirectSlot),
        atLogical growth result (layoutEnd origin)⟩ := by
  have hcommandList :
      (decrementStages register).map
          (fun current => (decrementStageIndex current).succ) =
        MarkerShift.decrementOrder register :=
    decrementStages_labels register
  have hsuffixCommands : ∀ raw,
      raw ∈ decrementShiftCommandsAux growth source secondarySearchBase
        ((decrementStages register).map
          (fun current => (decrementStageIndex current).succ)) →
      raw ∈ rawCommands := by
    intro raw hraw
    apply hcommands raw
    simpa [decrementShiftCommands, hcommandList] using hraw
  have hrun := decrementSuffix base c Failure runner source
    (decrementStages_chain register) hsuffixCommands
  have hstart : (decrementStageIndex register).succ =
      MarkerSchedule.decrementStartBoundary register := by
    cases register <;> rfl
  simpa [hstart] using hrun

end

end CounterControlScheduleSemantics
end Hooper
end Kari
end LeanWang
