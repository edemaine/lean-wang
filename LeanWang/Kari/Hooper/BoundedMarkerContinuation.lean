/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgram

/-!
# Concrete continuations for bounded marker commands

This module packages the exact finite executions that begin after a bounded
search has reached its `foundState`.  Navigation preserves its target, erase
commands clear it, successful marker shifts clear the old boundary and write
the new one, and colliding marker shifts preserve the occupied destination.
The local executions are also lifted through a complete command table and the
whole linked bounded-marker machine.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace BoundedMarkerContinuation

open Turing
open BoundedMarkerProgram

/-! ## Finite indexing and the nonblank alphabet -/

/-- `nonblankSymbols` enumerates exactly the complement of the embedded blank
in the complete tagged alphabet. -/
theorem mem_nonblankSymbols_iff {numTags : Nat}
    (symbol : Symbol numTags) :
    symbol ∈ nonblankSymbols numTags ↔ symbol ≠ blankSymbol := by
  constructor
  · intro hmem heq
    subst symbol
    exact blankSymbol_not_mem_nonblankSymbols hmem
  · intro hne
    simp only [nonblankSymbols, List.mem_append, List.mem_map,
      List.mem_finRange]
    by_cases hbase : symbol.val < MarkerMachine.AlphabetSize
    · left
      change symbol.val < 6 at hbase
      have hnonzero : symbol.val ≠ 0 := by
        intro hzero
        apply hne
        apply Fin.ext
        simpa [blankSymbol, baseSymbol, MarkerMachine.blankSymbol,
          MarkerMachine.encodeSymbol] using hzero
      have hpositive : 0 < symbol.val := Nat.pos_of_ne_zero hnonzero
      let label : Fin 5 := ⟨symbol.val - 1, by omega⟩
      refine ⟨label, by simp, ?_⟩
      apply Fin.ext
      simp [label, boundarySymbol, baseSymbol,
        MarkerMachine.boundarySymbol, MarkerMachine.encodeSymbol]
      omega
    · right
      let tag : Fin numTags := ⟨symbol.val - MarkerMachine.AlphabetSize, by
        have hsymbol := symbol.isLt
        simp only [AlphabetSize] at hsymbol
        omega⟩
      refine ⟨tag, by simp, ?_⟩
      apply Fin.ext
      simp [tag, tagSymbol]
      omega

/-- The command selected by a `Fin` index occupies the corresponding uniform
block offset. -/
theorem commandAt_get {numTags radius base : Nat}
    (commands : List (Command numTags)) (index : Fin commands.length) :
    CommandAt radius base (commandOffset base radius index.val)
      (commands.get index) commands := by
  induction commands generalizing base with
  | nil => exact Fin.elim0 index
  | cons first commands ih =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simpa [commandOffset] using
          (CommandAt.head (radius := radius) base first commands)
      · have htail := ih (base := base + blockWidth radius) tailIndex
        simpa [commandOffset, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          (CommandAt.tail (radius := radius) (offset := base)
            (commandOffset := commandOffset
              (base + blockWidth radius) radius tailIndex.val)
            (first := first) (command := commands.get tailIndex)
            (commands := commands) htail)

/-- Namespace-form alias for selecting a linked command by its finite list
index. -/
theorem CommandAt.get {numTags radius base : Nat}
    (commands : List (Command numTags)) (index : Fin commands.length) :
    CommandAt radius base (commandOffset base radius index.val)
      (commands.get index) commands :=
  commandAt_get commands index

/-! ## One-rule execution helper -/

private theorem reaches_rule {numTags : Nat}
    (rules : FiniteTM0.Table (AlphabetSize numTags))
    (hdet : FiniteTM0.Deterministic rules)
    (source : FiniteTM0.State) (read : Symbol numTags)
    (target : FiniteTM0.State)
    (action : FiniteTM0.Action (AlphabetSize numTags))
    (hrule : FiniteTM0.Rule.mk source read target action ∈ rules)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = read) :
    FullTM0.Reaches (FiniteTM0.machine rules) ⟨source, T⟩
      ⟨target, match action with
        | .moveLeft => T.move .left
        | .moveRight => T.move .right
        | .write symbol => T.write symbol⟩ := by
  have hlookup : FiniteTM0.lookupAction rules source read =
      some (target, action) :=
    (FiniteTM0.lookupAction_eq_some_iff_of_deterministic hdet).2 hrule
  apply Relation.ReflTransGen.single
  simp only [FullTM0.step]
  rw [hread]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some]
  cases action <;> rfl

private theorem reaches_write_rule {numTags : Nat}
    (rules : FiniteTM0.Table (AlphabetSize numTags))
    (hdet : FiniteTM0.Deterministic rules)
    (source : FiniteTM0.State) (read : Symbol numTags)
    (target : FiniteTM0.State) (written : Symbol numTags)
    (hrule : FiniteTM0.Rule.mk source read target (.write written) ∈ rules)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = read) :
    FullTM0.Reaches (FiniteTM0.machine rules) ⟨source, T⟩
      ⟨target, T.write written⟩ := by
  exact reaches_rule rules hdet source read target (.write written) hrule
    T hread

private theorem reaches_move_rule {numTags : Nat}
    (rules : FiniteTM0.Table (AlphabetSize numTags))
    (hdet : FiniteTM0.Deterministic rules)
    (source : FiniteTM0.State) (read : Symbol numTags)
    (target : FiniteTM0.State) (direction : Turing.Dir)
    (hrule : FiniteTM0.Rule.mk source read target
      (liftAction (MarkerMachine.moveAction direction)) ∈ rules)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = read) :
    FullTM0.Reaches (FiniteTM0.machine rules) ⟨source, T⟩
      ⟨target, T.move direction⟩ := by
  cases direction <;>
    exact reaches_rule rules hdet source read target _ hrule T hread

private theorem write_read_self {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) : T.write T.read = T := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.read, FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

/-! ## Lifting a continuation through the linked tables -/

/-- An execution using only a command's continuation rules is also an
execution of its complete private command table. -/
theorem command_reaches_of_continuation {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreach : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      start finish) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTable radius offset sharedCore command))
      start finish := by
  simpa [commandTable] using FiniteTM0Program.reaches_append_left
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command) hreach

/-- An execution using only a selected command's continuation rules remains
valid in the entire linked machine. -/
theorem machine_reaches_of_continuation {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreach : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius commandOffset
          (coreEntry base radius commands) command))
      start finish) :
    FullTM0.Reaches (machine base radius commands core) start finish := by
  exact table_reaches_of_commandAt core hat
    (command_reaches_of_continuation radius commandOffset
      (coreEntry base radius commands) command hreach)

/-! ## Navigation and erasure -/

/-- Whole-command navigation from `foundState` preserves the target and the
entire tape. -/
theorem command_reaches_navigation_native {numTags : Nat}
    (radius offset sharedCore : Nat) (target : Target numTags)
    (direction : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (T : FullTM0.Tape (Symbol numTags))
    (hmatch : target.Matches T.read) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius offset sharedCore
          (Command.navigateTarget target direction successState returnTag)))
      ⟨foundState radius offset, T⟩ ⟨successState, T⟩ := by
  exact command_reaches_of_continuation radius offset sharedCore _
    (continuation_reaches_navigation_native radius offset sharedCore target
      direction successState returnTag T hmatch)

/-- Linked-machine navigation from `foundState` preserves the target and the
entire tape. -/
theorem machine_reaches_navigation_native {numTags : Nat}
    {base radius commandOffset : Nat}
    {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (target : Target numTags) (direction : Turing.Dir)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (hat : CommandAt radius base commandOffset
      (Command.navigateTarget target direction successState returnTag)
      commands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : target.Matches T.read) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨foundState radius commandOffset, T⟩ ⟨successState, T⟩ := by
  exact machine_reaches_of_continuation core hat
    (continuation_reaches_navigation_native radius commandOffset
      (coreEntry base radius commands) target direction successState
      returnTag T hmatch)

/-- Erasing a found boundary with no departure clears exactly the head cell. -/
theorem continuation_reaches_erase_none_native {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol expected) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.erase expected direction successState returnTag none)))
      ⟨foundState radius offset, T⟩
      ⟨successState, T.write blankSymbol⟩ := by
  apply reaches_write_rule _
    (continuationTable_deterministic radius offset sharedCore _)
    (foundState radius offset) (boundarySymbol expected) successState
    blankSymbol _ T hread
  simp [continuationTable, Command.erase]

/-- Erasing a found boundary with a departure clears the head cell and then
moves once in the requested direction. -/
theorem continuation_reaches_erase_some_native {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (direction departure : Turing.Dir)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol expected) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.erase expected direction successState returnTag
            (some departure))))
      ⟨foundState radius offset, T⟩
      ⟨successState, (T.write blankSymbol).move departure⟩ := by
  let command : Command numTags :=
    Command.erase expected direction successState returnTag (some departure)
  have hclear : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨foundState radius offset, T⟩
      ⟨departState radius offset, T.write blankSymbol⟩ := by
    apply reaches_write_rule _
      (continuationTable_deterministic radius offset sharedCore command)
      (foundState radius offset) (boundarySymbol expected)
      (departState radius offset) blankSymbol _ T hread
    simp [command, continuationTable, Command.erase]
  have hdepart : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨departState radius offset, T.write blankSymbol⟩
      ⟨successState, (T.write blankSymbol).move departure⟩ := by
    apply reaches_move_rule _
      (continuationTable_deterministic radius offset sharedCore command)
      (departState radius offset) blankSymbol successState departure _
      (T.write blankSymbol) (by simp)
    simp [command, continuationTable, Command.erase]
  exact hclear.trans hdepart

/-- Uniform erasure theorem, with its exact optional-departure endpoint. -/
theorem continuation_reaches_erase_native {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol expected) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.erase expected direction successState returnTag departure)))
      ⟨foundState radius offset, T⟩
      ⟨successState, match departure with
        | none => T.write blankSymbol
        | some departure => (T.write blankSymbol).move departure⟩ := by
  cases departure with
  | none =>
      simpa using continuation_reaches_erase_none_native
        radius offset sharedCore expected direction successState returnTag T
        hread
  | some departure =>
      simpa using continuation_reaches_erase_some_native
        radius offset sharedCore expected direction departure successState
        returnTag T hread

/-- Whole-command form of exact erasure from `foundState`. -/
theorem command_reaches_erase_native {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol expected) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius offset sharedCore
          (Command.erase expected direction successState returnTag departure)))
      ⟨foundState radius offset, T⟩
      ⟨successState, match departure with
        | none => T.write blankSymbol
        | some departure => (T.write blankSymbol).move departure⟩ := by
  exact command_reaches_of_continuation radius offset sharedCore _
    (continuation_reaches_erase_native radius offset sharedCore expected
      direction successState returnTag departure T hread)

/-- Linked-machine form of exact erasure from `foundState`. -/
theorem machine_reaches_erase_native {numTags : Nat}
    {base radius commandOffset : Nat} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (expected : Fin 5) (direction : Turing.Dir)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (hat : CommandAt radius base commandOffset
      (Command.erase expected direction successState returnTag departure)
      commands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol expected) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨foundState radius commandOffset, T⟩
      ⟨successState, match departure with
        | none => T.write blankSymbol
        | some departure => (T.write blankSymbol).move departure⟩ := by
  cases departure with
  | none =>
      apply machine_reaches_of_continuation core hat
      exact continuation_reaches_erase_none_native radius commandOffset
        (coreEntry base radius commands) expected direction successState
        returnTag T hread
  | some departure =>
      apply machine_reaches_of_continuation core hat
      exact continuation_reaches_erase_some_native radius commandOffset
        (coreEntry base radius commands) expected direction departure
        successState returnTag T hread

/-- Cleanup is navigation to an arbitrary physical tag, so it preserves the
tag and enters the shared return dispatcher. -/
theorem continuation_cleanup_reaches_return_native {numTags : Nat}
    (radius offset sharedCore sharedReturn : Nat)
    (direction : Turing.Dir) (returnTag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (Target.anyTag : Target numTags).Matches T.read) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.cleanup direction sharedReturn returnTag)))
      ⟨foundState radius offset, T⟩ ⟨sharedReturn, T⟩ := by
  simpa only [Command.cleanup, Command.navigateTarget] using
    continuation_reaches_navigation_native radius offset sharedCore
      (Target.anyTag : Target numTags) direction sharedReturn returnTag T hmatch

/-- Whole-command cleanup from `foundState` preserves the physical tag and
enters the requested shared dispatcher. -/
theorem command_cleanup_from_found_reaches_return_native {numTags : Nat}
    (radius offset sharedCore sharedReturn : Nat)
    (direction : Turing.Dir) (returnTag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (Target.anyTag : Target numTags).Matches T.read) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius offset sharedCore
          (Command.cleanup direction sharedReturn returnTag)))
      ⟨foundState radius offset, T⟩ ⟨sharedReturn, T⟩ := by
  exact command_reaches_of_continuation radius offset sharedCore _
    (continuation_cleanup_reaches_return_native radius offset sharedCore
      sharedReturn direction returnTag T hmatch)

/-- Linked-machine cleanup from `foundState` preserves the physical tag and
enters the shared dispatcher. -/
theorem machine_cleanup_from_found_reaches_return_native {numTags : Nat}
    {base radius commandOffset : Nat} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (direction : Turing.Dir) (returnTag : Fin numTags)
    (hat : CommandAt radius base commandOffset
      (Command.cleanup direction
        (returnState base radius commands direction) returnTag)
      commands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (Target.anyTag : Target numTags).Matches T.read) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨foundState radius commandOffset, T⟩
      ⟨returnState base radius commands direction, T⟩ := by
  exact machine_reaches_of_continuation core hat
    (continuation_cleanup_reaches_return_native radius commandOffset
      (coreEntry base radius commands)
      (returnState base radius commands direction)
      direction returnTag T hmatch)

/-! ## Marker-shift success and collision -/

private theorem continuation_shift_reaches_verify_native {numTags : Nat}
    (radius offset sharedCore : Nat) (move : MarkerProgram.Move)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (collisionState : Option FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.move move successState returnTag departure collisionState)))
      ⟨foundState radius offset, T⟩
      ⟨verifyState radius offset,
        (T.write blankSymbol).move move.shiftDirection⟩ := by
  let command : Command numTags :=
    Command.move move successState returnTag departure collisionState
  have hclear : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨foundState radius offset, T⟩
      ⟨clearState radius offset, T.write blankSymbol⟩ := by
    apply reaches_write_rule _
      (continuationTable_deterministic radius offset sharedCore command)
      (foundState radius offset) (boundarySymbol move.expected)
      (clearState radius offset) blankSymbol _ T hread
    simp [command, continuationTable, Command.move]
  have hmove : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨clearState radius offset, T.write blankSymbol⟩
      ⟨verifyState radius offset,
        (T.write blankSymbol).move move.shiftDirection⟩ := by
    apply reaches_move_rule _
      (continuationTable_deterministic radius offset sharedCore command)
      (clearState radius offset) blankSymbol (verifyState radius offset)
      move.shiftDirection _ (T.write blankSymbol) (by simp)
    simp [command, continuationTable, Command.move]
  exact hclear.trans hmove

/-- Linked-machine prefix common to successful and blocked marker shifts:
clear the found boundary and move to the destination-verification state.
This endpoint is useful when a command has no collision exit and an occupied
destination must be shown terminal. -/
theorem machine_reaches_shift_verify_native {numTags : Nat}
    {base radius commandOffset : Nat} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (move : MarkerProgram.Move)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (collisionState : Option FiniteTM0.State)
    (hat : CommandAt radius base commandOffset
      (Command.move move successState returnTag departure collisionState)
      commands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨foundState radius commandOffset, T⟩
      ⟨verifyState radius commandOffset,
        (T.write blankSymbol).move move.shiftDirection⟩ := by
  exact machine_reaches_of_continuation core hat
    (continuation_shift_reaches_verify_native radius commandOffset
      (coreEntry base radius commands) move successState returnTag departure
      collisionState T hread)

/-- A collision-free shift clears the old boundary, moves to its blank
destination, writes the same labelled boundary, and performs the optional
departure exactly once. -/
theorem continuation_reaches_shift_success_native {numTags : Nat}
    (radius offset sharedCore : Nat) (move : MarkerProgram.Move)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (collisionState : Option FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected)
    (hblank : ((T.write blankSymbol).move move.shiftDirection).read =
      blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.move move successState returnTag departure collisionState)))
      ⟨foundState radius offset, T⟩
      ⟨successState, match departure with
        | none =>
            ((T.write blankSymbol).move move.shiftDirection).write
              (boundarySymbol move.expected)
        | some departure =>
            (((T.write blankSymbol).move move.shiftDirection).write
              (boundarySymbol move.expected)).move departure⟩ := by
  let destination := (T.write blankSymbol).move move.shiftDirection
  have hverify := continuation_shift_reaches_verify_native radius offset
    sharedCore move successState returnTag departure collisionState T hread
  cases departure with
  | none =>
      have hwrite : FullTM0.Reaches
          (FiniteTM0.machine
            (continuationTable radius offset sharedCore
              (Command.move move successState returnTag none collisionState)))
          ⟨verifyState radius offset, destination⟩
          ⟨successState,
            destination.write (boundarySymbol move.expected)⟩ := by
        apply reaches_write_rule _
          (continuationTable_deterministic radius offset sharedCore _)
          (verifyState radius offset) blankSymbol successState
          (boundarySymbol move.expected) _ destination (by
            simpa [destination] using hblank)
        simp [continuationTable, Command.move]
      exact hverify.trans hwrite
  | some departure =>
      have hwrite : FullTM0.Reaches
          (FiniteTM0.machine
            (continuationTable radius offset sharedCore
              (Command.move move successState returnTag (some departure)
                collisionState)))
          ⟨verifyState radius offset, destination⟩
          ⟨departState radius offset,
            destination.write (boundarySymbol move.expected)⟩ := by
        apply reaches_write_rule _
          (continuationTable_deterministic radius offset sharedCore _)
          (verifyState radius offset) blankSymbol (departState radius offset)
          (boundarySymbol move.expected) _ destination (by
            simpa [destination] using hblank)
        simp [continuationTable, Command.move]
      have hdepart : FullTM0.Reaches
          (FiniteTM0.machine
            (continuationTable radius offset sharedCore
              (Command.move move successState returnTag (some departure)
                collisionState)))
          ⟨departState radius offset,
            destination.write (boundarySymbol move.expected)⟩
          ⟨successState,
            (destination.write
              (boundarySymbol move.expected)).move departure⟩ := by
        apply reaches_move_rule _
          (continuationTable_deterministic radius offset sharedCore _)
          (departState radius offset) (boundarySymbol move.expected)
          successState departure _
          (destination.write (boundarySymbol move.expected)) (by simp)
        simp [continuationTable, Command.move]
      exact hverify.trans (hwrite.trans hdepart)

/-- Whole-command form of a successful exact marker shift. -/
theorem command_reaches_shift_success_native {numTags : Nat}
    (radius offset sharedCore : Nat) (move : MarkerProgram.Move)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (collisionState : Option FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected)
    (hblank : ((T.write blankSymbol).move move.shiftDirection).read =
      blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius offset sharedCore
          (Command.move move successState returnTag departure collisionState)))
      ⟨foundState radius offset, T⟩
      ⟨successState, match departure with
        | none =>
            ((T.write blankSymbol).move move.shiftDirection).write
              (boundarySymbol move.expected)
        | some departure =>
            (((T.write blankSymbol).move move.shiftDirection).write
              (boundarySymbol move.expected)).move departure⟩ := by
  exact command_reaches_of_continuation radius offset sharedCore _
    (continuation_reaches_shift_success_native radius offset sharedCore move
      successState returnTag departure collisionState T hread hblank)

/-- Linked-machine form of a successful exact marker shift. -/
theorem machine_reaches_shift_success_native {numTags : Nat}
    {base radius commandOffset : Nat} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (move : MarkerProgram.Move) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (collisionState : Option FiniteTM0.State)
    (hat : CommandAt radius base commandOffset
      (Command.move move successState returnTag departure collisionState)
      commands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected)
    (hblank : ((T.write blankSymbol).move move.shiftDirection).read =
      blankSymbol) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨foundState radius commandOffset, T⟩
      ⟨successState, match departure with
        | none =>
            ((T.write blankSymbol).move move.shiftDirection).write
              (boundarySymbol move.expected)
        | some departure =>
            (((T.write blankSymbol).move move.shiftDirection).write
              (boundarySymbol move.expected)).move departure⟩ := by
  cases departure with
  | none =>
      apply machine_reaches_of_continuation core hat
      exact continuation_reaches_shift_success_native radius commandOffset
        (coreEntry base radius commands) move successState returnTag none
        collisionState T hread hblank
  | some departure =>
      apply machine_reaches_of_continuation core hat
      exact continuation_reaches_shift_success_native radius commandOffset
        (coreEntry base radius commands) move successState returnTag
        (some departure) collisionState T hread hblank

/-- An occupied marker-shift destination takes the configured collision exit.
The old boundary has already been cleared, but the observed destination symbol
and every other cell are preserved. -/
theorem continuation_reaches_shift_collision_native {numTags : Nat}
    (radius offset sharedCore : Nat) (move : MarkerProgram.Move)
    (successState collisionState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected)
    (hnonblank : ((T.write blankSymbol).move move.shiftDirection).read ≠
      blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.move move successState returnTag departure
            (some collisionState))))
      ⟨foundState radius offset, T⟩
      ⟨collisionState,
        (T.write blankSymbol).move move.shiftDirection⟩ := by
  let destination := (T.write blankSymbol).move move.shiftDirection
  have hverify := continuation_shift_reaches_verify_native radius offset
    sharedCore move successState returnTag departure (some collisionState)
    T hread
  have hmem : destination.read ∈ nonblankSymbols numTags :=
    (mem_nonblankSymbols_iff destination.read).2 (by
      simpa [destination] using hnonblank)
  have hcollisionRule :
      FiniteTM0.Rule.mk (verifyState radius offset) destination.read
          collisionState (.write destination.read) ∈
        collisionRules (verifyState radius offset) collisionState := by
    simp only [collisionRules, List.mem_map]
    exact ⟨destination.read, hmem, rfl⟩
  have hcollision : FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.move move successState returnTag departure
            (some collisionState))))
      ⟨verifyState radius offset, destination⟩
      ⟨collisionState, destination⟩ := by
    have hrule :
        FiniteTM0.Rule.mk (verifyState radius offset) destination.read
            collisionState (.write destination.read) ∈
          continuationTable radius offset sharedCore
            (Command.move move successState returnTag departure
              (some collisionState)) := by
      cases departure <;>
        simp only [Command.move, continuationTable, List.mem_append,
          List.mem_cons, List.not_mem_nil]
      all_goals aesop
    have hstep := reaches_write_rule _
      (continuationTable_deterministic radius offset sharedCore _)
      (verifyState radius offset) destination.read collisionState
      destination.read hrule destination rfl
    simpa only [write_read_self] using hstep
  exact hverify.trans hcollision

/-- Whole-command form of the exact marker-shift collision exit. -/
theorem command_reaches_shift_collision_native {numTags : Nat}
    (radius offset sharedCore : Nat) (move : MarkerProgram.Move)
    (successState collisionState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected)
    (hnonblank : ((T.write blankSymbol).move move.shiftDirection).read ≠
      blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius offset sharedCore
          (Command.move move successState returnTag departure
            (some collisionState))))
      ⟨foundState radius offset, T⟩
      ⟨collisionState,
        (T.write blankSymbol).move move.shiftDirection⟩ := by
  exact command_reaches_of_continuation radius offset sharedCore _
    (continuation_reaches_shift_collision_native radius offset sharedCore
      move successState collisionState returnTag departure T hread hnonblank)

/-- Linked-machine form of the exact marker-shift collision exit. -/
theorem machine_reaches_shift_collision_native {numTags : Nat}
    {base radius commandOffset : Nat} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (move : MarkerProgram.Move)
    (successState collisionState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (hat : CommandAt radius base commandOffset
      (Command.move move successState returnTag departure
        (some collisionState)) commands)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol move.expected)
    (hnonblank : ((T.write blankSymbol).move move.shiftDirection).read ≠
      blankSymbol) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨foundState radius commandOffset, T⟩
      ⟨collisionState,
        (T.write blankSymbol).move move.shiftDirection⟩ := by
  exact machine_reaches_of_continuation core hat
    (continuation_reaches_shift_collision_native radius commandOffset
      (coreEntry base radius commands) move successState collisionState
      returnTag departure T hread hnonblank)

end BoundedMarkerContinuation
end Hooper
end Kari
end LeanWang
