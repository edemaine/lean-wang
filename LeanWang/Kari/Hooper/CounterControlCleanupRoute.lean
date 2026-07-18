/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlRawCallerClassification
import LeanWang.Kari.Hooper.CounterControlExactCommandContinuation
import LeanWang.Kari.Hooper.CounterControlCleanupSemantics

/-!
# Exact finite-control route through collision cleanup

The geometric cleanup theorems run all four boundary erases at once.  A
resumed parent caller may instead re-enter at any one of those searches, so
the caller-side proof needs the table-level links between individual cleanup
blocks.  This file names the four commands and packages their exact compiled
forms, success states, found-target tapes, and final shared-return dispatch.

No search-resolution or progress argument is used here.  Each found-target
step is a direct specialization of the exact generated-command continuation,
and the last link composes the existing shared-return rule with the selected
command's private one-cell resume rule.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupRoute

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlCommandAt
open CounterControlCommandContinuationMortality
open CounterControlExactCommandContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## The four exact raw commands -/

/-- Position in the fixed four-command cleanup suffix. -/
inductive Stage where
  | three
  | two
  | one
  | zero
  deriving DecidableEq

/-- Generated search slot of one cleanup stage. -/
def Stage.slot : Stage → Nat
  | .three => cleanupSearchBase
  | .two => cleanupSearchBase + 1
  | .one => cleanupSearchBase + 2
  | .zero => cleanupSearchBase + 3

/-- Boundary erased by one cleanup stage. -/
def Stage.expected : Stage → Fin 5
  | .three => 3
  | .two => 2
  | .one => 1
  | .zero => 0

/-- Symbolic continuation after one successful erase. -/
def Stage.successRef (growth : Turing.Dir) (source : Nat) :
    Stage → ControlRef
  | .three => searchRef growth source (cleanupSearchBase + 1)
  | .two => searchRef growth source (cleanupSearchBase + 2)
  | .one => searchRef growth source (cleanupSearchBase + 3)
  | .zero => .sharedReturn growth

/-- The raw erasing boundary command at one cleanup stage. -/
def command (growth : Turing.Dir) (source : Nat)
    (stage : Stage) : RawCommand :=
  .boundaryNavigation ⟨growth, source, stage.slot⟩ stage.expected .left
    (stage.successRef growth source) (.erase (some .left))

@[simp] theorem command_address
    (growth : Turing.Dir) (source : Nat) (stage : Stage) :
    (command growth source stage).address =
      ⟨growth, source, stage.slot⟩ := by
  cases stage <;> rfl

@[simp] theorem command_mem_cleanupCommands
    (growth : Turing.Dir) (source : Nat) (stage : Stage) :
    command growth source stage ∈ cleanupCommands growth source := by
  cases stage <;> simp [command, Stage.slot, Stage.expected,
    Stage.successRef, cleanupCommands]

/-- Conversely, every member of the fixed cleanup list is exactly one of
the four indexed stages. -/
theorem exists_stage_of_mem_cleanupCommands
    {raw : RawCommand} {growth : Turing.Dir} {source : Nat}
    (hraw : raw ∈ cleanupCommands growth source) :
    ∃ stage, raw = command growth source stage := by
  rcases
      (CounterControlRawCallerClassification.mem_cleanupCommands_iff
        raw growth source).mp hraw with
    h | h | h | h
  · exact ⟨.three, h⟩
  · exact ⟨.two, h⟩
  · exact ⟨.one, h⟩
  · exact ⟨.zero, h⟩

/-- Existential, stage-indexed form of cleanup-list membership. -/
theorem mem_cleanupCommands_iff_exists_stage
    (raw : RawCommand) (growth : Turing.Dir) (source : Nat) :
    raw ∈ cleanupCommands growth source ↔
      ∃ stage, raw = command growth source stage := by
  constructor
  · exact exists_stage_of_mem_cleanupCommands
  · rintro ⟨stage, rfl⟩
    exact command_mem_cleanupCommands growth source stage

/-- Every increment rule contributes all four cleanup commands to the global
enumeration. -/
theorem command_mem_rawCommands_of_increment
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program) (stage : Stage) :
    command growth source stage ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, incrementCommands,
    command_mem_cleanupCommands growth source stage]

/-! ## Compilation and exact successors -/

/-- Constructor-level compilation retains the cleanup boundary, physical
inward direction, symbolic successor, and the stage's own return tag. -/
theorem compile_command
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands) :
    compileRawCommand base c (command growth source stage) hraw =
      .boundaryNavigation stage.expected (orient growth .left)
        (resolve base c (stage.successRef growth source))
        (rawTag (command growth source stage) hraw)
        (.erase (some (orient growth .left))) := by
  rw [compileRawCommand_spec]
  cases stage <;> rfl

@[simp] theorem compile_command_target
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands) :
    (compileRawCommand base c (command growth source stage) hraw).target =
      .boundary stage.expected := by
  rw [compile_command]
  rfl

@[simp] theorem compile_command_searchDirection
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands) :
    (compileRawCommand base c (command growth source stage) hraw).searchDirection =
      orient growth .left := by
  rw [compile_command]
  rfl

@[simp] theorem compile_command_successState
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands) :
    (compileRawCommand base c (command growth source stage) hraw).successState =
      resolve base c (stage.successRef growth source) := by
  rw [compile_command]
  rfl

@[simp] theorem compile_command_returnTag
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands) :
    (compileRawCommand base c (command growth source stage) hraw).returnTag =
      rawTag (command growth source stage) hraw := by
  exact CounterControlCommandAt.compileRawCommand_returnTag
    base c (command growth source stage) hraw

/-- Cleanup searches physically inward, opposite the orientation in which
the erased counter core grows. -/
theorem compile_command_searchDirection_eq_opposite
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands) :
    (compileRawCommand base c (command growth source stage) hraw).searchDirection =
      NestingMachine.opposite growth := by
  rw [compile_command_searchDirection base c growth source stage hraw]
  cases growth <;> rfl

@[simp] theorem resolve_success_three
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) :
    resolve base c (Stage.three.successRef growth source) =
      searchState base c ⟨growth, source, Stage.two.slot⟩ := rfl

@[simp] theorem resolve_success_two
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) :
    resolve base c (Stage.two.successRef growth source) =
      searchState base c ⟨growth, source, Stage.one.slot⟩ := rfl

@[simp] theorem resolve_success_one
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) :
    resolve base c (Stage.one.successRef growth source) =
      searchState base c ⟨growth, source, Stage.zero.slot⟩ := rfl

@[simp] theorem resolve_success_zero
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) :
    resolve base c (Stage.zero.successRef growth source) =
      controllerReturn base c growth := rfl

/-- Once a cleanup search has found its advertised boundary, the generated
table erases it, moves one logical cell inward, and enters the exact next
cleanup block (or the directional shared return after boundary `0`). -/
theorem found_reaches_success
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (stage : Stage)
    (hraw : command growth source stage ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol stage.expected) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩), T⟩
      ⟨resolve base c (stage.successRef growth source),
        (T.write blankSymbol).move (orient growth .left)⟩ := by
  have hmatch :
      (compileRawCommand base c (command growth source stage) hraw).target.Matches
        T.read := by
    rw [compile_command_target]
    simpa [Target.Matches] using hread
  have outcome := exact_found_continuation base c
    (command growth source stage) hraw T hmatch
  have hreach := outcome.reachesSuccess_of_destinationFree (by
    simp [ShiftDestinationOccupied, command])
  simpa [command, RawCommand.address, rawSuccessRef, exactSuccessTape] using
    hreach

/-- Boundary `3` cleanup enters the boundary-`2` search on the exact erased
and inward-moved tape. -/
theorem found_three_reaches_two
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hraw : command growth source .three ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 3) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, cleanupSearchBase⟩), T⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase + 1⟩,
        (T.write blankSymbol).move (orient growth .left)⟩ := by
  simpa [Stage.slot, Stage.expected, Stage.successRef, searchRef, resolve] using
    found_reaches_success base c growth source .three hraw T hread

/-- Boundary `2` cleanup enters the boundary-`1` search. -/
theorem found_two_reaches_one
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hraw : command growth source .two ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 2) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, cleanupSearchBase + 1⟩), T⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase + 2⟩,
        (T.write blankSymbol).move (orient growth .left)⟩ := by
  simpa [Stage.slot, Stage.expected, Stage.successRef, searchRef, resolve] using
    found_reaches_success base c growth source .two hraw T hread

/-- Boundary `1` cleanup enters the boundary-`0` search. -/
theorem found_one_reaches_zero
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hraw : command growth source .one ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 1) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, cleanupSearchBase + 2⟩), T⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase + 3⟩,
        (T.write blankSymbol).move (orient growth .left)⟩ := by
  simpa [Stage.slot, Stage.expected, Stage.successRef, searchRef, resolve] using
    found_reaches_success base c growth source .one hraw T hread

/-- Boundary `0` cleanup enters the directional shared-return dispatcher. -/
theorem found_zero_reaches_return
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hraw : command growth source .zero ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 0) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, cleanupSearchBase + 3⟩), T⟩
      ⟨controllerReturn base c growth,
        (T.write blankSymbol).move (orient growth .left)⟩ := by
  simpa [Stage.slot, Stage.expected, Stage.successRef, resolve] using
    found_reaches_success base c growth source .zero hraw T hread

/-! ## Exact shared-return dispatch -/

/-- Reading the tag of an actual generated command clears it, enters that
command's private resume state, advances one cell in its search direction,
and restarts the exact selected search. -/
theorem return_restarts_command
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (U : FullTM0.Tape (Symbol numTags))
    (hread : U.read = tagSymbol (rawTag raw hraw)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c
          (compileRawCommand base c raw hraw).searchDirection, U⟩
      ⟨searchState base c raw.address,
        (U.write blankSymbol).move
          (compileRawCommand base c raw hraw).searchDirection⟩ := by
  have hdispatch :=
    CounterControlCleanupSemantics.machine_sharedReturn_reaches_resume
      base c (rawTag raw hraw) U hread
  have hdispatch' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c
          (compileRawCommand base c raw hraw).searchDirection, U⟩
      ⟨resumeState (CanonicalInitializer.radius c)
          (searchState base c raw.address), U.write blankSymbol⟩ := by
    change FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c
          (compileCommand base c (rawTag raw hraw)).searchDirection, U⟩
      ⟨resumeState (CanonicalInitializer.radius c)
          (searchState base c
            (rawCommands.get (rawTag raw hraw)).address),
        U.write blankSymbol⟩ at hdispatch
    rw [CounterControlCommandAt.rawCommands_get_rawTag raw hraw] at hdispatch
    simpa only [compileRawCommand] using hdispatch
  have hresume := BoundedMarkerProgram.machine_resume_reaches
    (coreTable base c) (CommandAt.compileRawCommand base c raw hraw)
    (U.write blankSymbol) (FullTM0.Tape.read_write blankSymbol U)
  have hresume' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resumeState (CanonicalInitializer.radius c)
          (searchState base c raw.address), U.write blankSymbol⟩
      ⟨searchState base c raw.address,
        (U.write blankSymbol).move
          (compileRawCommand base c raw hraw).searchDirection⟩ := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.entryState] using hresume
  exact hdispatch'.trans hresume'

/-- The last boundary erase and the dispatcher compose without losing the
two exact tag erasures or either physical head move. -/
theorem found_zero_dispatches_command
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hzero : command growth source .zero ∈ rawCommands)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hboundary : T.read = boundarySymbol 0)
    (hdirection :
      (compileRawCommand base c raw hraw).searchDirection = growth)
    (htag : ((T.write blankSymbol).move (orient growth .left)).read =
      tagSymbol (rawTag raw hraw)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, cleanupSearchBase + 3⟩), T⟩
      ⟨searchState base c raw.address,
        ((((T.write blankSymbol).move (orient growth .left)).write
          blankSymbol).move growth)⟩ := by
  have herase := found_zero_reaches_return
    base c growth source hzero T hboundary
  have hdispatch := return_restarts_command base c raw hraw
    ((T.write blankSymbol).move (orient growth .left)) htag
  rw [hdirection] at hdispatch
  exact herase.trans hdispatch

end

end CounterControlCleanupRoute
end Hooper
end Kari
end LeanWang
