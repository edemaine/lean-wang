/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.NestingMachine

/-!
# Tagged bounded searches for finite marker programs

This module links a finite family of Hooper bounded-search controllers around
one shared nested-core entry.  Every command carries its expected boundary
label, search direction, external success state, and a finite return tag.
The found action is either search-only navigation or a guarded one-cell marker
shift.  A shift may explicitly depart from the newly written boundary before
entering its success state; this is essential when chaining suffix shifts,
because the next bounded search accepts a blank head cell rather than the
previous command's boundary.

On a failed bounded search, the controller writes the command's tag at the
prefix boundary and jumps to one shared core-entry state.  The only abstract
obligation left to the eventual canonical simulation is to grow while
preserving that tag and restore the outer tape around it.  A shared return
state dispatches on the tag, clears it, and enters the correct finite unwind
routine.  Thus command identity is physically represented even after control
has entered the shared core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace BoundedMarkerProgram

open Turing

/-! ## General command descriptors -/

/-- What to do after the expected marker has been found. -/
inductive FoundAction where
  /-- Search-only navigation: leave the marker and head in place. -/
  | stay
  /-- Move the marker one cell in `shiftDirection`.  If `departure` is
  present, take that head step after rewriting the marker and only then enter
  the external success state. -/
  | shift (shiftDirection : Turing.Dir) (departure : Option Turing.Dir)
  deriving DecidableEq

/-- One bounded-search command.  `returnTag` is written before entering the
shared nested core and is consumed by the shared return dispatcher. -/
structure Command (numTags : Nat) where
  expected : Fin 5
  searchDirection : Turing.Dir
  successState : FiniteTM0.State
  returnTag : Fin numTags
  foundAction : FoundAction
  deriving DecidableEq

/-- Search-only descriptor. -/
def Command.navigate {numTags : Nat} (expected : Fin 5)
    (searchDirection : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) : Command numTags :=
  ⟨expected, searchDirection, successState, returnTag, .stay⟩

/-- Marker-shift descriptor with an explicit optional departure step. -/
def Command.move {numTags : Nat} (move : MarkerProgram.Move)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir := none) : Command numTags :=
  ⟨move.expected, move.searchDirection, successState, returnTag,
    .shift move.shiftDirection departure⟩

/-! ## Enlarged finite alphabet and physical return tags -/

/-- Six marker symbols plus one distinct physical symbol per return tag. -/
def AlphabetSize (numTags : Nat) : Nat :=
  MarkerMachine.AlphabetSize + numTags

/-- Explicit alphabet used by the tagged controller. -/
abbrev Symbol (numTags : Nat) := FiniteTM0.Symbol (AlphabetSize numTags)

/-- Embed the original six-symbol marker alphabet. -/
def baseSymbol {numTags : Nat} (a : MarkerMachine.Symbol) : Symbol numTags :=
  ⟨a.val, lt_of_lt_of_le a.isLt
    (Nat.le_add_right MarkerMachine.AlphabetSize numTags)⟩

/-- Physical symbol representing one return tag. -/
def tagSymbol {numTags : Nat} (tag : Fin numTags) : Symbol numTags :=
  ⟨MarkerMachine.AlphabetSize + tag.val, by
    simp only [AlphabetSize]
    omega⟩

/-- Embedded blank. -/
def blankSymbol {numTags : Nat} : Symbol numTags :=
  baseSymbol MarkerMachine.blankSymbol

/-- Embedded marker boundary. -/
def boundarySymbol {numTags : Nat} (label : Fin 5) : Symbol numTags :=
  baseSymbol (MarkerMachine.boundarySymbol label)

theorem blankSymbol_eq_baseSymbol {numTags : Nat} :
    (blankSymbol : Symbol numTags) =
      baseSymbol MarkerMachine.blankSymbol :=
  rfl

theorem boundarySymbol_eq_baseSymbol {numTags : Nat} (label : Fin 5) :
    (boundarySymbol label : Symbol numTags) =
      baseSymbol (MarkerMachine.boundarySymbol label) :=
  rfl

theorem baseSymbol_injective {numTags : Nat} :
    Function.Injective (@baseSymbol numTags) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Symbol numTags => x.val) h

theorem tagSymbol_injective {numTags : Nat} :
    Function.Injective (@tagSymbol numTags) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [tagSymbol] at hv
  omega

theorem baseSymbol_ne_tagSymbol {numTags : Nat}
    (a : MarkerMachine.Symbol) (tag : Fin numTags) :
    baseSymbol a ≠ tagSymbol tag := by
  intro h
  have hv := congrArg Fin.val h
  simp only [baseSymbol, tagSymbol] at hv
  have ha := a.isLt
  omega

theorem blankSymbol_ne_boundarySymbol {numTags : Nat} (label : Fin 5) :
    (blankSymbol : Symbol numTags) ≠ boundarySymbol label := by
  exact fun h => MarkerMachine.blankSymbol_ne_boundarySymbol label
    (baseSymbol_injective h)

theorem blankSymbol_ne_tagSymbol {numTags : Nat} (tag : Fin numTags) :
    (blankSymbol : Symbol numTags) ≠ tagSymbol tag :=
  baseSymbol_ne_tagSymbol _ _

theorem boundarySymbol_ne_tagSymbol {numTags : Nat}
    (label : Fin 5) (tag : Fin numTags) :
    (boundarySymbol label : Symbol numTags) ≠ tagSymbol tag :=
  baseSymbol_ne_tagSymbol _ _

@[simp]
theorem boundarySymbol_injective {numTags : Nat} (i j : Fin 5) :
    (boundarySymbol i : Symbol numTags) = boundarySymbol j ↔ i = j := by
  constructor
  · intro h
    exact MarkerMachine.boundarySymbol_injective (baseSymbol_injective h)
  · exact congrArg boundarySymbol

/-- Encode a base marker tape pointwise. -/
def encodeTape {numTags : Nat} (T : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.Tape (Symbol numTags) :=
  fun i => baseSymbol (T i)

@[simp]
theorem encodeTape_apply {numTags : Nat}
    (T : FullTM0.Tape MarkerMachine.Symbol) (i : Int) :
    encodeTape (numTags := numTags) T i = baseSymbol (T i) :=
  rfl

@[simp]
theorem encodeTape_move {numTags : Nat}
    (T : FullTM0.Tape MarkerMachine.Symbol) (direction : Turing.Dir) :
    encodeTape (numTags := numTags) (T.move direction) =
      (encodeTape T).move direction := by
  funext i
  cases direction <;> rfl

@[simp]
theorem encodeTape_moveN {numTags : Nat}
    (T : FullTM0.Tape MarkerMachine.Symbol) (direction : Turing.Dir)
    (distance : Nat) :
    encodeTape (numTags := numTags) (T.moveN direction distance) =
      (encodeTape T).moveN direction distance := by
  funext i
  rfl

@[simp]
theorem encodeTape_write {numTags : Nat}
    (T : FullTM0.Tape MarkerMachine.Symbol) (a : MarkerMachine.Symbol) :
    encodeTape (numTags := numTags) (T.write a) =
      (encodeTape T).write (baseSymbol a) := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

/-! ## Lifting six-symbol finite tables -/

/-- Lift one explicit marker action to the tagged alphabet. -/
def liftAction {numTags : Nat} :
    FiniteTM0.Action MarkerMachine.AlphabetSize →
      FiniteTM0.Action (AlphabetSize numTags)
  | .moveLeft => .moveLeft
  | .moveRight => .moveRight
  | .write a => .write (baseSymbol a)

/-- Lift one explicit marker rule without changing control states. -/
def liftRule {numTags : Nat}
    (rule : FiniteTM0.Rule MarkerMachine.AlphabetSize) :
    FiniteTM0.Rule (AlphabetSize numTags) :=
  FiniteTM0.Rule.mk rule.1.1 (baseSymbol rule.1.2)
    rule.2.1 (liftAction rule.2.2)

/-- Lift a complete explicit marker table to the tagged alphabet. -/
def liftTable {numTags : Nat}
    (rules : FiniteTM0.Table MarkerMachine.AlphabetSize) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  rules.map liftRule

/-- Lift an explicit lookup result. -/
def liftResult {numTags : Nat}
    (result : FiniteTM0.Result MarkerMachine.AlphabetSize) :
    FiniteTM0.Result (AlphabetSize numTags) :=
  (result.1, liftAction result.2)

theorem lookupAction_liftTable {numTags : Nat}
    (rules : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (state : FiniteTM0.State) (a : MarkerMachine.Symbol) :
    FiniteTM0.lookupAction (liftTable (numTags := numTags) rules)
        state (baseSymbol a) =
      (FiniteTM0.lookupAction rules state a).map liftResult := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      rcases rule with ⟨⟨source, read⟩, ⟨target, action⟩⟩
      by_cases hkey : (state, a) = (source, read)
      · rcases hkey with ⟨rfl, rfl⟩
        simp [liftTable, liftRule, liftResult, FiniteTM0.lookupAction,
          FiniteTM0.Rule.mk]
      · have hlifted :
          (state, (baseSymbol a : Symbol numTags)) ≠
            (source, (baseSymbol read : Symbol numTags)) := by
          intro h
          apply hkey
          have hstate : state = source :=
            congrArg (fun p : FiniteTM0.State × Symbol numTags => p.1) h
          have hread : baseSymbol (numTags := numTags) a =
              baseSymbol read :=
            congrArg (fun p : FiniteTM0.State × Symbol numTags => p.2) h
          exact Prod.ext hstate
            (baseSymbol_injective (numTags := numTags) hread)
        change FiniteTM0.lookupAction
            (FiniteTM0.Rule.mk source (baseSymbol read) target
                (liftAction action) ::
              liftTable rules) state (baseSymbol a) =
          (FiniteTM0.lookupAction
            (FiniteTM0.Rule.mk source read target action :: rules)
            state a).map liftResult
        rw [FiniteTM0.lookupAction_cons_ne hlifted]
        rw [FiniteTM0.lookupAction_cons_ne hkey]
        exact ih

/-- Lift only the tape alphabet of a full configuration. -/
def encodeCfg {numTags : Nat}
    (cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨cfg.q, encodeTape cfg.tape⟩

/-- One semantic step commutes with alphabet lifting. -/
theorem step_liftTable {numTags : Nat}
    (rules : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State) :
    FullTM0.step (FiniteTM0.machine (liftTable (numTags := numTags) rules))
        (encodeCfg cfg) =
      (FullTM0.step (FiniteTM0.machine rules) cfg).map encodeCfg := by
  simp only [FullTM0.step, FiniteTM0.machine, encodeCfg,
    FullTM0.Tape.read_eq, encodeTape_apply]
  rw [lookupAction_liftTable]
  cases hlookup : FiniteTM0.lookupAction rules cfg.q (cfg.tape 0) with
  | none => simp
  | some result =>
      rcases result with ⟨target, action⟩
      cases action <;> simp [liftResult, liftAction, encodeCfg]

/-- Every finite execution of a base table lifts pointwise. -/
theorem reaches_liftTable {numTags : Nat}
    (rules : FiniteTM0.Table MarkerMachine.AlphabetSize)
    {start finish : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine rules) start finish) :
    FullTM0.Reaches
      (FiniteTM0.machine (liftTable (numTags := numTags) rules))
      (encodeCfg start) (encodeCfg finish) := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
      apply Relation.ReflTransGen.tail ih
      rw [step_liftTable]
      simpa using Option.mem_map_of_mem encodeCfg hstep

/-! ## State layout and executable command tables -/

/-- Three private continuation states suffice for clearing, verifying, and
optionally departing from a rewritten boundary. -/
def continuationWidth : Nat := 3

/-- Uniform interval reserved for one command. -/
def blockWidth (radius : Nat) : Nat :=
  NestingMachine.localWidth radius + continuationWidth

/-- Start of command number `index`. -/
def commandOffset (base radius index : Nat) : FiniteTM0.State :=
  base + index * blockWidth radius

/-- Local state after clearing a found marker. -/
def clearState (radius offset : Nat) : FiniteTM0.State :=
  offset + NestingMachine.localWidth radius

/-- Local state that verifies the marker's destination is blank. -/
def verifyState (radius offset : Nat) : FiniteTM0.State :=
  clearState radius offset + 1

/-- Local state that departs from the marker just written. -/
def departState (radius offset : Nat) : FiniteTM0.State :=
  clearState radius offset + 2

/-- Shared return dispatcher after all private command blocks. -/
def returnState (base radius : Nat) {numTags : Nat}
    (commands : List (Command numTags)) : FiniteTM0.State :=
  commandOffset base radius commands.length

/-- One shared entry for the eventual canonical nested computation. -/
def coreEntry (base radius : Nat) {numTags : Nat}
    (commands : List (Command numTags)) : FiniteTM0.State :=
  returnState base radius commands + 1

/-- Source state of one bounded command. -/
def entryState (_radius offset : Nat) : FiniteTM0.State := offset

/-- Command-specific failed-search state before writing the return tag. -/
def launchState (radius offset : Nat) : FiniteTM0.State :=
  offset + NestingMachine.localLaunchState radius

/-- Command-specific finite-unwind entry selected by the return tag. -/
def unwindState (radius offset : Nat) : FiniteTM0.State :=
  offset + NestingMachine.localUnwindState radius

/-- Command-specific state reached after finding its expected marker. -/
def foundState (radius offset : Nat) : FiniteTM0.State :=
  offset + NestingMachine.localSuccessState radius

private theorem clear_ne_launch (radius offset : Nat) :
    clearState radius offset ≠ launchState radius offset := by
  simp [clearState, launchState, NestingMachine.localWidth,
    NestingMachine.localLaunchState, NestingMachine.bound]
  omega

private theorem clear_ne_found (radius offset : Nat) :
    clearState radius offset ≠ foundState radius offset := by
  simp [clearState, foundState, NestingMachine.localWidth,
    NestingMachine.localSuccessState, NestingMachine.bound]
  omega

private theorem verify_ne_launch (radius offset : Nat) :
    verifyState radius offset ≠ launchState radius offset := by
  intro h
  change offset + (2 * (radius + 1) + 3) + 1 =
    offset + (radius + 1 + 2) at h
  omega

private theorem verify_ne_found (radius offset : Nat) :
    verifyState radius offset ≠ foundState radius offset := by
  intro h
  change offset + (2 * (radius + 1) + 3) + 1 =
    offset + (radius + 1 + 1) at h
  omega

private theorem verify_ne_clear (radius offset : Nat) :
    verifyState radius offset ≠ clearState radius offset := by
  simp [verifyState]

private theorem depart_ne_launch (radius offset : Nat) :
    departState radius offset ≠ launchState radius offset := by
  intro h
  change offset + (2 * (radius + 1) + 3) + 2 =
    offset + (radius + 1 + 2) at h
  omega

private theorem depart_ne_found (radius offset : Nat) :
    departState radius offset ≠ foundState radius offset := by
  intro h
  change offset + (2 * (radius + 1) + 3) + 2 =
    offset + (radius + 1 + 1) at h
  omega

private theorem depart_ne_clear (radius offset : Nat) :
    departState radius offset ≠ clearState radius offset := by
  simp [departState]

private theorem depart_ne_verify (radius offset : Nat) :
    departState radius offset ≠ verifyState radius offset := by
  simp [departState, verifyState]

/-- Explicit continuation and failed-launch rules for one command.  These
rules precede the lifted bounded controller in `commandTable`; their source
states are reserved holes in or immediately after that controller. -/
def continuationTable {numTags : Nat} (radius offset sharedCore : Nat)
    (command : Command numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  let launchRule := FiniteTM0.Rule.mk (launchState radius offset)
    blankSymbol sharedCore (.write (tagSymbol command.returnTag))
  match command.foundAction with
  | .stay =>
      [ launchRule
      , FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol command.expected) command.successState
          (.write (boundarySymbol command.expected))
      ]
  | .shift shiftDirection none =>
      [ launchRule
      , FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol command.expected) (clearState radius offset)
          (.write blankSymbol)
      , FiniteTM0.Rule.mk (clearState radius offset) blankSymbol
          (verifyState radius offset)
          (liftAction (MarkerMachine.moveAction shiftDirection))
      , FiniteTM0.Rule.mk (verifyState radius offset) blankSymbol
          command.successState (.write (boundarySymbol command.expected))
      ]
  | .shift shiftDirection (some departure) =>
      [ launchRule
      , FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol command.expected) (clearState radius offset)
          (.write blankSymbol)
      , FiniteTM0.Rule.mk (clearState radius offset) blankSymbol
          (verifyState radius offset)
          (liftAction (MarkerMachine.moveAction shiftDirection))
      , FiniteTM0.Rule.mk (verifyState radius offset) blankSymbol
          (departState radius offset)
          (.write (boundarySymbol command.expected))
      , FiniteTM0.Rule.mk (departState radius offset)
          (boundarySymbol command.expected) command.successState
          (liftAction (MarkerMachine.moveAction departure))
      ]

/-- Lift and relocate the finite bounded controller used by one descriptor. -/
def privateControllerTable {numTags : Nat} (radius offset : Nat)
    (command : Command numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  FiniteTM0Program.relocate offset
    (liftTable (numTags := numTags)
      (NestingMachine.localTable radius command.expected
        command.searchDirection))

/-- One complete private command block. -/
def commandTable {numTags : Nat} (radius offset sharedCore : Nat)
    (command : Command numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  continuationTable radius offset sharedCore command ++
    privateControllerTable radius offset command

/-- Link private command blocks in consecutive disjoint intervals. -/
def commandTables {numTags : Nat} (radius sharedCore : Nat) :
    Nat → List (Command numTags) →
      FiniteTM0.Table (AlphabetSize numTags)
  | _, [] => []
  | offset, command :: commands =>
      commandTable radius offset sharedCore command ++
        commandTables radius sharedCore (offset + blockWidth radius) commands

/-- Shared return rules.  Distinct command tags give distinct rule keys even
though every rule has the same source state. -/
def returnTable {numTags : Nat} (radius sharedReturn : Nat) :
    Nat → List (Command numTags) →
      FiniteTM0.Table (AlphabetSize numTags)
  | _, [] => []
  | offset, command :: commands =>
      FiniteTM0.Rule.mk sharedReturn (tagSymbol command.returnTag)
          (unwindState radius offset) (.write blankSymbol) ::
        returnTable radius sharedReturn (offset + blockWidth radius) commands

/-- Entire generated controller, without the shared nested core itself. -/
def controllerTable {numTags : Nat} (base radius : Nat)
    (commands : List (Command numTags)) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  commandTables radius (coreEntry base radius commands) base commands ++
    returnTable radius (returnState base radius commands) base commands

/-- Append one shared finite nested-core table. -/
def table {numTags : Nat} (base radius : Nat)
    (commands : List (Command numTags))
    (core : FiniteTM0.Table (AlphabetSize numTags)) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  controllerTable base radius commands ++ core

/-- Semantic full-tape machine generated by `table`. -/
def machine {numTags : Nat} (base radius : Nat)
    (commands : List (Command numTags))
    (core : FiniteTM0.Table (AlphabetSize numTags)) :
    Turing.TM0.Machine (Symbol numTags) FiniteTM0.State :=
  FiniteTM0.machine (table base radius commands core)

/-! ## Exact command outcomes and guards -/

/-- Base marker tape after a command succeeds. -/
def resultTape {numTags : Nat} (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat) :
    FullTM0.Tape MarkerMachine.Symbol :=
  let found := T.moveN command.searchDirection distance
  match command.foundAction with
  | .stay => found
  | .shift shiftDirection departure =>
      let shifted := ((found.write MarkerMachine.blankSymbol).move
        shiftDirection).write (MarkerMachine.boundarySymbol command.expected)
      match departure with
      | none => shifted
      | some direction => shifted.move direction

/-- Runtime destination guard for a found action. -/
def FoundGuard {numTags : Nat} (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat) : Prop :=
  match command.foundAction with
  | .stay => True
  | .shift shiftDirection _ =>
      (((T.moveN command.searchDirection distance).write
        MarkerMachine.blankSymbol).move shiftDirection).read =
          MarkerMachine.blankSymbol

/-- Tape at the shared core entry after a failed bounded search. -/
def taggedFrameTape {numTags : Nat} (radius : Nat)
    (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.Tape (Symbol numTags) :=
  (encodeTape (T.moveN command.searchDirection
    (NestingMachine.bound radius))).write (tagSymbol command.returnTag)

/-! ## Exact continuation and shared-core handoff -/

/-- Package one successful semantic step as finite reachability. -/
private theorem reaches_of_step {numTags : Nat}
    {rules : FiniteTM0.Table (AlphabetSize numTags)}
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : FullTM0.step (FiniteTM0.machine rules) start = some finish) :
    FullTM0.Reaches (FiniteTM0.machine rules) start finish := by
  apply Relation.ReflTransGen.single
  simp [hstep]

@[simp]
private theorem liftAction_moveAction_toStmt {numTags : Nat}
    (direction : Turing.Dir) :
    (liftAction (numTags := numTags)
      (MarkerMachine.moveAction direction)).toStmt =
        Turing.TM0.Stmt.move direction := by
  cases direction <;> rfl

@[simp]
private theorem taggedTape_write_read {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) : T.write T.read = T := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.read, FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

/-- The fixed controller-state arithmetic keeps every continuation rule from
being shadowed by an earlier rule in the same table. -/
private theorem step_found_stay {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (searchDirection : Turing.Dir) (successState : Nat)
    (returnTag : Fin numTags) (F : FullTM0.Tape MarkerMachine.Symbol)
    (hread : F.read = MarkerMachine.boundarySymbol expected) :
    FullTM0.step (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          ⟨expected, searchDirection, successState, returnTag, .stay⟩))
      ⟨foundState radius offset, encodeTape F⟩ =
        some ⟨successState, encodeTape F⟩ := by
  have hencoded : (encodeTape (numTags := numTags) F).read =
      boundarySymbol expected := by
    change baseSymbol F.read =
      baseSymbol (MarkerMachine.boundarySymbol expected)
    exact congrArg (baseSymbol (numTags := numTags)) hread
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        ⟨expected, searchDirection, successState, returnTag, .stay⟩)
      (foundState radius offset) (boundarySymbol expected) =
        some (successState, .write (boundarySymbol expected)) := by
    simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
      foundState, launchState, NestingMachine.localSuccessState,
      NestingMachine.localLaunchState, NestingMachine.bound]
  have htape : (encodeTape (numTags := numTags) F).write
      (boundarySymbol expected) = encodeTape F := by
    rw [← hencoded]
    exact taggedTape_write_read _
  simp only [FullTM0.step]
  rw [hencoded]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    FiniteTM0.Action.toStmt_write]
  rw [htape]

private theorem step_found_clear {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (searchDirection shiftDirection : Turing.Dir)
    (successState : Nat) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (F : FullTM0.Tape MarkerMachine.Symbol)
    (hread : F.read = MarkerMachine.boundarySymbol expected) :
    FullTM0.step (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          ⟨expected, searchDirection, successState, returnTag,
            .shift shiftDirection departure⟩))
      ⟨foundState radius offset, encodeTape F⟩ =
        some ⟨clearState radius offset,
          encodeTape (F.write MarkerMachine.blankSymbol)⟩ := by
  have hencoded : (encodeTape (numTags := numTags) F).read =
      boundarySymbol expected := by
    change baseSymbol F.read =
      baseSymbol (MarkerMachine.boundarySymbol expected)
    exact congrArg (baseSymbol (numTags := numTags)) hread
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        ⟨expected, searchDirection, successState, returnTag,
          .shift shiftDirection departure⟩)
      (foundState radius offset) (boundarySymbol expected) =
        some (clearState radius offset, .write blankSymbol) := by
    cases departure <;>
      simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
        foundState, launchState, clearState, verifyState, departState,
        NestingMachine.localSuccessState, NestingMachine.localLaunchState,
        NestingMachine.localWidth, NestingMachine.bound]
  simp only [FullTM0.step]
  rw [hencoded]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some]
  rw [encodeTape_write]
  rfl

private theorem step_clear_move {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (searchDirection shiftDirection : Turing.Dir)
    (successState : Nat) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (F : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.step (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          ⟨expected, searchDirection, successState, returnTag,
            .shift shiftDirection departure⟩))
      ⟨clearState radius offset,
        encodeTape (F.write MarkerMachine.blankSymbol)⟩ =
        some ⟨verifyState radius offset,
          encodeTape ((F.write MarkerMachine.blankSymbol).move
            shiftDirection)⟩ := by
  have hencoded : (encodeTape (numTags := numTags)
      (F.write MarkerMachine.blankSymbol)).read = blankSymbol := by
    change baseSymbol MarkerMachine.blankSymbol =
      baseSymbol MarkerMachine.blankSymbol
    rfl
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        ⟨expected, searchDirection, successState, returnTag,
          .shift shiftDirection departure⟩)
      (clearState radius offset) blankSymbol =
        some (verifyState radius offset,
          liftAction (MarkerMachine.moveAction shiftDirection)) := by
    cases departure <;>
      simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
        blankSymbol_ne_boundarySymbol, clear_ne_launch, clear_ne_found]
  simp only [FullTM0.step]
  rw [hencoded]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    liftAction_moveAction_toStmt]
  rw [← encodeTape_move]

private theorem step_verify_write {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (searchDirection shiftDirection : Turing.Dir)
    (successState : Nat) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (F : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ((F.write MarkerMachine.blankSymbol).move
      shiftDirection).read = MarkerMachine.blankSymbol) :
    FullTM0.step (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          ⟨expected, searchDirection, successState, returnTag,
            .shift shiftDirection departure⟩))
      ⟨verifyState radius offset,
        encodeTape ((F.write MarkerMachine.blankSymbol).move
          shiftDirection)⟩ =
      some ⟨match departure with
        | none => successState
        | some _ => departState radius offset,
        encodeTape (((F.write MarkerMachine.blankSymbol).move
          shiftDirection).write (MarkerMachine.boundarySymbol expected))⟩ := by
  let shifted := (F.write MarkerMachine.blankSymbol).move shiftDirection
  have hencoded : (encodeTape (numTags := numTags) shifted).read =
      blankSymbol := by
    change baseSymbol shifted.read = baseSymbol MarkerMachine.blankSymbol
    exact congrArg (baseSymbol (numTags := numTags)) hblank
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        ⟨expected, searchDirection, successState, returnTag,
          .shift shiftDirection departure⟩)
      (verifyState radius offset) blankSymbol =
        some (match departure with
          | none => successState
          | some _ => departState radius offset,
          .write (boundarySymbol expected)) := by
    cases departure <;>
      simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
        blankSymbol_ne_boundarySymbol, verify_ne_launch, verify_ne_found,
        verify_ne_clear]
  simp only [FullTM0.step]
  rw [hencoded]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    FiniteTM0.Action.toStmt_write]
  rw [boundarySymbol_eq_baseSymbol]
  rw [encodeTape_write]

private theorem step_depart_move {numTags : Nat}
    (radius offset sharedCore : Nat) (expected : Fin 5)
    (searchDirection shiftDirection departure : Turing.Dir)
    (successState : Nat) (returnTag : Fin numTags)
    (F : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.step (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          ⟨expected, searchDirection, successState, returnTag,
            .shift shiftDirection (some departure)⟩))
      ⟨departState radius offset,
        encodeTape (((F.write MarkerMachine.blankSymbol).move
          shiftDirection).write (MarkerMachine.boundarySymbol expected))⟩ =
      some ⟨successState,
        encodeTape ((((F.write MarkerMachine.blankSymbol).move
          shiftDirection).write
            (MarkerMachine.boundarySymbol expected)).move departure)⟩ := by
  let written := ((F.write MarkerMachine.blankSymbol).move
    shiftDirection).write (MarkerMachine.boundarySymbol expected)
  have hencoded : (encodeTape (numTags := numTags) written).read =
      boundarySymbol expected := by
    change baseSymbol written.read =
      baseSymbol (MarkerMachine.boundarySymbol expected)
    simp [written]
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        ⟨expected, searchDirection, successState, returnTag,
          .shift shiftDirection (some departure)⟩)
      (departState radius offset) (boundarySymbol expected) =
        some (successState,
          liftAction (MarkerMachine.moveAction departure)) := by
    simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
      depart_ne_launch, depart_ne_found,
      depart_ne_clear, depart_ne_verify]
  simp only [FullTM0.step]
  rw [hencoded]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    liftAction_moveAction_toStmt]
  have hwritten : encodeTape (numTags := numTags) written =
      (((encodeTape F).write blankSymbol).move shiftDirection).write
        (boundarySymbol expected) := by
    simp [written, blankSymbol, boundarySymbol]
  rw [encodeTape_move, hwritten]

/-- Once the bounded scan has found its expected marker, the explicit
continuation performs exactly the descriptor's found action.  In particular,
an optional departure is a real head move made only after the shifted marker
has been written. -/
theorem continuation_reaches_success {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hmarked :
      (T.moveN command.searchDirection distance).read =
        MarkerMachine.boundarySymbol command.expected)
    (hguard : FoundGuard command T distance) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨foundState radius offset,
        encodeTape (T.moveN command.searchDirection distance)⟩
      ⟨command.successState, encodeTape (resultTape command T distance)⟩ := by
  rcases command with
    ⟨expected, searchDirection, successState, returnTag, foundAction⟩
  let F := T.moveN searchDirection distance
  cases foundAction with
  | stay =>
      exact reaches_of_step (step_found_stay radius offset sharedCore expected
        searchDirection successState returnTag F hmarked)
  | shift shiftDirection departure =>
      have hclear := reaches_of_step
        (step_found_clear radius offset sharedCore expected searchDirection
          shiftDirection successState returnTag departure F hmarked)
      have hmove := reaches_of_step
        (step_clear_move radius offset sharedCore expected searchDirection
          shiftDirection successState returnTag departure F)
      have hwrite := reaches_of_step
        (step_verify_write radius offset sharedCore expected searchDirection
          shiftDirection successState returnTag departure F hguard)
      cases departure with
      | none =>
          exact hclear.trans (hmove.trans hwrite)
      | some departure =>
          have hdepart := reaches_of_step
            (step_depart_move radius offset sharedCore expected searchDirection
              shiftDirection departure successState returnTag F)
          exact hclear.trans (hmove.trans (hwrite.trans hdepart))

/-- A failed bounded scan writes its command-specific physical return tag and
enters the one shared core state without otherwise modifying the exact frame
tape. -/
theorem continuation_reaches_core {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : (T.moveN command.searchDirection
      (NestingMachine.bound radius)).read = MarkerMachine.blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨launchState radius offset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩
      ⟨sharedCore, taggedFrameTape radius command T⟩ := by
  rcases command with
    ⟨expected, searchDirection, successState, returnTag, foundAction⟩
  let F := T.moveN searchDirection (NestingMachine.bound radius)
  have hencoded : (encodeTape (numTags := numTags) F).read = blankSymbol := by
    change baseSymbol F.read = baseSymbol MarkerMachine.blankSymbol
    exact congrArg (baseSymbol (numTags := numTags)) hblank
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        ⟨expected, searchDirection, successState, returnTag, foundAction⟩)
      (launchState radius offset) blankSymbol =
        some (sharedCore, .write (tagSymbol returnTag)) := by
    cases foundAction with
    | stay =>
        simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]
    | shift shiftDirection departure =>
        cases departure <;>
          simp [continuationTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]
  apply reaches_of_step
  simp only [FullTM0.step]
  rw [hencoded]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some]
  rfl

/-! ## Lifted private-controller semantics -/

/-- Nearby success of the lifted and relocated bounded controller. -/
theorem private_reaches_found {numTags : Nat} (radius offset : Nat)
    (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.expected)
      T command.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches
      (FiniteTM0.machine (privateControllerTable radius offset command))
      ⟨entryState radius offset, encodeTape T⟩
      ⟨foundState radius offset,
        encodeTape (T.moveN command.searchDirection distance)⟩ := by
  have hbase := NestingMachine.local_reaches_success radius command.expected
    command.searchDirection T distance hgap hnear
  have hlift := reaches_liftTable (numTags := numTags)
    (NestingMachine.localTable radius command.expected
      command.searchDirection) hbase
  have hrelocate := FiniteTM0Program.reaches_relocate offset
    (liftTable (numTags := numTags)
      (NestingMachine.localTable radius command.expected
        command.searchDirection)) hlift
  simpa [privateControllerTable, FiniteTM0Program.liftCfg, encodeCfg,
    entryState, foundState] using hrelocate

/-- Distant-search launch of the lifted and relocated bounded controller. -/
theorem private_reaches_launch {numTags : Nat} (radius offset : Nat)
    (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.expected)
      T command.searchDirection distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (privateControllerTable radius offset command))
      ⟨entryState radius offset, encodeTape T⟩
      ⟨launchState radius offset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩ := by
  have hbase := NestingMachine.local_reaches_launch radius command.expected
    command.searchDirection T distance hgap hfar
  have hlift := reaches_liftTable (numTags := numTags)
    (NestingMachine.localTable radius command.expected
      command.searchDirection) hbase
  have hrelocate := FiniteTM0Program.reaches_relocate offset
    (liftTable (numTags := numTags)
      (NestingMachine.localTable radius command.expected
        command.searchDirection)) hlift
  simpa [privateControllerTable, FiniteTM0Program.liftCfg, encodeCfg,
    entryState, launchState] using hrelocate

/-- Finite unwind of the lifted and relocated bounded controller. -/
theorem private_unwind_reaches {numTags : Nat} (radius offset : Nat)
    (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN command.searchDirection (NestingMachine.bound radius))
          (FullTM0.Tape.offset
            (NestingMachine.opposite command.searchDirection) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine (privateControllerTable radius offset command))
      ⟨unwindState radius offset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩
      ⟨entryState radius offset,
        encodeTape (T.move command.searchDirection)⟩ := by
  have hbase := NestingMachine.local_unwind_reaches radius command.expected
    command.searchDirection T hblank
  have hlift := reaches_liftTable (numTags := numTags)
    (NestingMachine.localTable radius command.expected
      command.searchDirection) hbase
  have hrelocate := FiniteTM0Program.reaches_relocate offset
    (liftTable (numTags := numTags)
      (NestingMachine.localTable radius command.expected
        command.searchDirection)) hlift
  simpa [privateControllerTable, FiniteTM0Program.liftCfg, encodeCfg,
    entryState, unwindState] using hrelocate

/-! ## Linking private controllers to their continuations -/

/-- Alphabet lifting preserves the source-state list exactly. -/
theorem sourceStates_liftTable {numTags : Nat}
    (rules : FiniteTM0.Table MarkerMachine.AlphabetSize) :
    FiniteTM0.sourceStates (liftTable (numTags := numTags) rules) =
      FiniteTM0.sourceStates rules := by
  simp [FiniteTM0.sourceStates, liftTable, liftRule, FiniteTM0.Rule.mk,
    List.map_map, Function.comp_def]

/-- Relocation adds the same offset to every source state. -/
theorem sourceStates_relocate {numSymbols : Nat} (offset : Nat)
    (rules : FiniteTM0.Table numSymbols) :
    FiniteTM0.sourceStates (FiniteTM0Program.relocate offset rules) =
      (FiniteTM0.sourceStates rules).map (offset + ·) := by
  simp [FiniteTM0.sourceStates, FiniteTM0Program.relocate,
    FiniteTM0Program.relocateRule, FiniteTM0.Rule.mk, List.map_map,
    Function.comp_def]

/-- A local source belongs either to the bounded scan prefix or to the later
unwind interval.  The success and launch states are the two holes between
those intervals. -/
theorem local_source_shape {radius : Nat} {expected : Fin 5}
    {direction : Turing.Dir} {state : Nat}
    (hstate : state ∈ FiniteTM0.sourceStates
      (NestingMachine.localTable radius expected direction)) :
    state ≤ NestingMachine.bound radius ∨
      NestingMachine.localUnwindState radius ≤ state := by
  simp only [NestingMachine.localTable, FiniteTM0.sourceStates,
    List.map_append, List.mem_append] at hstate
  rcases hstate with hscan | hunwind
  · left
    simpa [NestingMachine.scanTable] using
      (NestingMachine.source_mem_scanTableAux hscan).2
  · right
    simpa [NestingMachine.unwindTable] using
      (NestingMachine.source_mem_unwindTableAux hunwind).1

/-- Private controller sources occupy their reserved interval but avoid the
two continuation holes used for success and failed launch. -/
theorem source_mem_privateControllerTable {numTags : Nat}
    {radius offset state : Nat} {command : Command numTags}
    (hstate : state ∈ FiniteTM0.sourceStates
      (privateControllerTable radius offset command)) :
    offset ≤ state ∧ state < clearState radius offset ∧
      state ≠ foundState radius offset ∧
      state ≠ launchState radius offset := by
  simp only [privateControllerTable, sourceStates_relocate,
    sourceStates_liftTable, List.mem_map] at hstate
  rcases hstate with ⟨localState, hlocal, rfl⟩
  have hbound := NestingMachine.source_mem_localTable hlocal
  have hshape := local_source_shape hlocal
  refine ⟨Nat.le_add_right offset localState, ?_, ?_, ?_⟩
  · simpa [clearState] using Nat.add_lt_add_left hbound offset
  · intro heq
    have heq' : localState = NestingMachine.bound radius + 1 := by
      apply Nat.add_left_cancel (n := offset)
      simpa [foundState, NestingMachine.localSuccessState] using heq
    clear heq hbound
    rcases hshape with hscan | hunwind
    · omega
    · rw [heq'] at hunwind
      simp [NestingMachine.localUnwindState] at hunwind
  · intro heq
    have heq' : localState = NestingMachine.bound radius + 2 := by
      apply Nat.add_left_cancel (n := offset)
      simpa [launchState, NestingMachine.localLaunchState] using heq
    clear heq hbound
    rcases hshape with hscan | hunwind
    · omega
    · rw [heq'] at hunwind
      simp [NestingMachine.localUnwindState] at hunwind

/-- Every continuation source is one of the two private holes or lies at or
after the first state following the private controller. -/
theorem source_mem_continuationTable {numTags : Nat}
    {radius offset sharedCore state : Nat} {command : Command numTags}
    (hstate : state ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command)) :
    state = launchState radius offset ∨
      state = foundState radius offset ∨
      clearState radius offset ≤ state := by
  rcases command with
    ⟨expected, searchDirection, successState, returnTag, foundAction⟩
  cases foundAction with
  | stay =>
      simp [continuationTable, FiniteTM0.sourceStates,
        FiniteTM0.Rule.mk] at hstate
      rcases hstate with rfl | rfl <;> simp
  | shift shiftDirection departure =>
      cases departure with
      | none =>
          simp [continuationTable, FiniteTM0.sourceStates,
            FiniteTM0.Rule.mk] at hstate
          rcases hstate with rfl | rfl | rfl | rfl <;>
            simp [verifyState]
      | some departure =>
          simp [continuationTable, FiniteTM0.sourceStates,
            FiniteTM0.Rule.mk] at hstate
          rcases hstate with rfl | rfl | rfl | rfl | rfl <;>
            simp [verifyState, departState]

/-- Prefixing the private controller by its continuation rules cannot shadow
any private transition. -/
theorem private_continuation_source_disjoint {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    ∀ state,
      state ∈ FiniteTM0.sourceStates
        (privateControllerTable radius offset command) →
      state ∉ FiniteTM0.sourceStates
        (continuationTable radius offset sharedCore command) := by
  intro state hprivate hcontinuation
  have hp := source_mem_privateControllerTable hprivate
  rcases source_mem_continuationTable hcontinuation with
    hlaunch | hfound | hlate
  · exact hp.2.2.2 hlaunch
  · exact hp.2.2.1 hfound
  · exact (Nat.not_le_of_gt hp.2.1) hlate

/-- A step of a right-hand table is unchanged by a prefix with no rule at the
current state. -/
private theorem step_append_of_state_not_mem_left {numSymbols : Nat}
    (first second : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State)
    (hsource : cfg.q ∉ FiniteTM0.sourceStates first) :
    FullTM0.step (FiniteTM0.machine (first ++ second)) cfg =
      FullTM0.step (FiniteTM0.machine second) cfg := by
  have hlookup :
      FiniteTM0.lookupAction first cfg.q (cfg.tape 0) = none := by
    cases h : FiniteTM0.lookupAction first cfg.q (cfg.tape 0) with
    | none => rfl
    | some result =>
        rcases result with ⟨target, action⟩
        exfalso
        apply hsource
        have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some h
        exact List.mem_map.mpr
          ⟨FiniteTM0.Rule.mk cfg.q (cfg.tape 0) target action,
            hrule, rfl⟩
  simp only [FullTM0.step, FiniteTM0.machine, FullTM0.Tape.read_eq]
  rw [FiniteTM0Program.lookupAction_append, hlookup]

/-- A path through a right-hand table remains valid after prefixing a table
whose source states are disjoint from the right-hand source states. -/
private theorem reaches_append_right_of_source_disjoint {numSymbols : Nat}
    (first second : FiniteTM0.Table numSymbols)
    (hdisjoint : ∀ state,
      state ∈ FiniteTM0.sourceStates second →
      state ∉ FiniteTM0.sourceStates first)
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine second) start finish) :
    FullTM0.Reaches (FiniteTM0.machine (first ++ second)) start finish := by
  apply Relation.ReflTransGen.mono ?_ hreach
  intro current next hstep
  have hright : current.q ∈ FiniteTM0.sourceStates second := by
    by_contra hsource
    have hnone := FiniteTM0.machine_eq_none_of_state_not_mem
      hsource current.tape.read
    have hstepNone :
        FullTM0.step (FiniteTM0.machine second) current = none := by
      unfold FullTM0.step
      rw [hnone]
      rfl
    rw [hstepNone] at hstep
    simp at hstep
  rw [step_append_of_state_not_mem_left first second current
    (hdisjoint current.q hright)]
  exact hstep

/-- A nearby command executes its bounded controller and then its exact found
continuation inside the complete private command block. -/
theorem command_reaches_success {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.expected)
      T command.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius)
    (hguard : FoundGuard command T distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTable radius offset sharedCore command))
      ⟨entryState radius offset, encodeTape T⟩
      ⟨command.successState, encodeTape (resultTape command T distance)⟩ := by
  have hprivate := private_reaches_found radius offset command T distance
    hgap hnear
  have hprivate' := reaches_append_right_of_source_disjoint
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command)
    (private_continuation_source_disjoint radius offset sharedCore command)
    hprivate
  have hmarked :
      (T.moveN command.searchDirection distance).read =
        MarkerMachine.boundarySymbol command.expected := by
    simpa [FullTM0.Tape.read] using hgap.marked
  have hcontinuation := continuation_reaches_success radius offset sharedCore
    command T distance hmarked hguard
  have hcontinuation' := FiniteTM0Program.reaches_append_left
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command) hcontinuation
  exact hprivate'.trans hcontinuation'

/-- A distant command reaches the shared nested-core entry after writing its
physical return tag. -/
theorem command_reaches_core {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.expected)
      T command.searchDirection distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTable radius offset sharedCore command))
      ⟨entryState radius offset, encodeTape T⟩
      ⟨sharedCore, taggedFrameTape radius command T⟩ := by
  have hprivate := private_reaches_launch radius offset command T distance
    hgap hfar
  have hprivate' := reaches_append_right_of_source_disjoint
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command)
    (private_continuation_source_disjoint radius offset sharedCore command)
    hprivate
  have hblank :
      (T.moveN command.searchDirection
        (NestingMachine.bound radius)).read = MarkerMachine.blankSymbol := by
    simpa [FullTM0.Tape.read] using hgap.blank hfar
  have hcontinuation := continuation_reaches_core radius offset sharedCore
    command T hblank
  have hcontinuation' := FiniteTM0Program.reaches_append_left
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command) hcontinuation
  exact hprivate'.trans hcontinuation'

/-- Once dispatch has selected this command's private unwind state, its whole
command block resumes the outer search exactly one cell closer. -/
theorem command_unwind_reaches {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN command.searchDirection (NestingMachine.bound radius))
          (FullTM0.Tape.offset
            (NestingMachine.opposite command.searchDirection) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTable radius offset sharedCore command))
      ⟨unwindState radius offset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩
      ⟨entryState radius offset,
        encodeTape (T.move command.searchDirection)⟩ := by
  exact reaches_append_right_of_source_disjoint
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command)
    (private_continuation_source_disjoint radius offset sharedCore command)
    (private_unwind_reaches radius offset command T hblank)

/-! ## Linking a command occurrence into a finite command family -/

/-- A command occurrence together with the concrete offset of its private
block.  Carrying both the family base and the occurrence offset makes the
linker's state arithmetic explicit in semantic theorem statements. -/
inductive CommandAt {numTags : Nat} (radius : Nat) :
    Nat → Nat → Command numTags → List (Command numTags) → Prop
  | head (offset : Nat) (command : Command numTags)
      (commands : List (Command numTags)) :
      CommandAt radius offset offset command (command :: commands)
  | tail (offset commandOffset : Nat) (first command : Command numTags)
      (commands : List (Command numTags))
      (h : CommandAt radius (offset + blockWidth radius) commandOffset
        command commands) :
      CommandAt radius offset commandOffset command (first :: commands)

/-- A linked occurrence is an actual member of its command family. -/
theorem CommandAt.command_mem {numTags radius base commandOffset}
    {command : Command numTags} {commands : List (Command numTags)}
    (h : CommandAt radius base commandOffset command commands) :
    command ∈ commands := by
  induction h with
  | head => simp
  | tail _ _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- All rule sources in one command block lie in its advertised half-open
state interval. -/
theorem source_mem_commandTable {numTags : Nat}
    {radius offset sharedCore state : Nat} {command : Command numTags}
    (hstate : state ∈ FiniteTM0.sourceStates
      (commandTable radius offset sharedCore command)) :
    offset ≤ state ∧ state < offset + blockWidth radius := by
  simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hstate
  rcases hstate with hcontinuation | hprivate
  · rcases command with
      ⟨expected, searchDirection, successState, returnTag, foundAction⟩
    cases foundAction with
    | stay =>
        simp [continuationTable, FiniteTM0.sourceStates,
          FiniteTM0.Rule.mk] at hcontinuation
        rcases hcontinuation with rfl | rfl <;>
          constructor <;>
          simp [launchState, foundState, blockWidth, continuationWidth,
            NestingMachine.localLaunchState,
            NestingMachine.localSuccessState,
            NestingMachine.localWidth, NestingMachine.bound] <;>
          omega
    | shift shiftDirection departure =>
        cases departure with
        | none =>
            simp [continuationTable, FiniteTM0.sourceStates,
              FiniteTM0.Rule.mk] at hcontinuation
            rcases hcontinuation with rfl | rfl | rfl | rfl <;>
              constructor <;>
              simp [launchState, foundState, clearState, verifyState,
                blockWidth, continuationWidth,
                NestingMachine.localLaunchState,
                NestingMachine.localSuccessState,
                NestingMachine.localWidth, NestingMachine.bound] <;>
              omega
        | some departure =>
            simp [continuationTable, FiniteTM0.sourceStates,
              FiniteTM0.Rule.mk] at hcontinuation
            rcases hcontinuation with rfl | rfl | rfl | rfl | rfl <;>
              constructor <;>
              simp [launchState, foundState, clearState, verifyState,
                departState, blockWidth, continuationWidth,
                NestingMachine.localLaunchState,
                NestingMachine.localSuccessState,
                NestingMachine.localWidth, NestingMachine.bound] <;>
              omega
  · have hp := source_mem_privateControllerTable hprivate
    refine ⟨hp.1, Nat.lt_trans hp.2.1 ?_⟩
    simp [clearState, blockWidth, continuationWidth]

/-- Sources of a linked command family occupy the consecutive interval from
its base through the sum of its command-block widths. -/
theorem source_mem_commandTables {numTags : Nat}
    {radius sharedCore offset state : Nat}
    {commands : List (Command numTags)}
    (hstate : state ∈ FiniteTM0.sourceStates
      (commandTables radius sharedCore offset commands)) :
    offset ≤ state ∧
      state < offset + commands.length * blockWidth radius := by
  induction commands generalizing offset with
  | nil =>
      simp [commandTables, FiniteTM0.sourceStates] at hstate
  | cons first commands ih =>
      simp only [commandTables, FiniteTM0.sourceStates, List.map_append,
        List.mem_append] at hstate
      rcases hstate with hfirst | hrest
      · have hb := source_mem_commandTable hfirst
        constructor
        · exact hb.1
        · calc
            state < offset + blockWidth radius := hb.2
            _ ≤ offset + (commands.length + 1) * blockWidth radius := by
              simp [Nat.add_mul]
      · have hb := ih hrest
        constructor
        · exact Nat.le_trans (Nat.le_add_right _ _) hb.1
        · simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hb.2

/-- A semantic path through a selected command block remains valid after all
other command blocks are linked around it. -/
theorem commandTables_reaches_of_at {numTags : Nat}
    {radius sharedCore base commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    {start finish :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreach : FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius commandOffset sharedCore command))
      start finish) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTables radius sharedCore base commands))
      start finish := by
  induction hat with
  | head offset command commands =>
      exact FiniteTM0Program.reaches_append_left _ _ hreach
  | tail offset commandOffset first command commands hat ih =>
      apply reaches_append_right_of_source_disjoint
        (commandTable radius offset sharedCore first)
        (commandTables radius sharedCore (offset + blockWidth radius) commands)
        ?_ (ih hreach)
      intro state hrest hfirst
      have hrestBounds := source_mem_commandTables hrest
      have hfirstBounds := source_mem_commandTable hfirst
      exact (Nat.not_le_of_gt hfirstBounds.2) hrestBounds.1

/-! ## Physical return-tag dispatch -/

/-- Distinct command tags make the return dispatcher select the exact unwind
state belonging to a linked command occurrence. -/
theorem lookupAction_returnTable_of_at {numTags : Nat}
    {radius sharedReturn base commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (htags : (commands.map (·.returnTag)).Nodup) :
    FiniteTM0.lookupAction (returnTable radius sharedReturn base commands)
        sharedReturn (tagSymbol command.returnTag) =
      some (unwindState radius commandOffset, .write blankSymbol) := by
  induction hat with
  | head offset command commands =>
      simp [returnTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]
  | tail offset commandOffset first command commands hat ih =>
      simp only [List.map_cons, List.nodup_cons] at htags
      have htagMem : command.returnTag ∈ commands.map (·.returnTag) :=
        List.mem_map.mpr ⟨command, hat.command_mem, rfl⟩
      have htagNe : command.returnTag ≠ first.returnTag := by
        intro heq
        apply htags.1
        rw [← heq]
        exact htagMem
      have hkeyNe :
          (sharedReturn, tagSymbol command.returnTag) ≠
            (sharedReturn, tagSymbol first.returnTag) := by
        intro heq
        apply htagNe
        apply tagSymbol_injective
        exact congrArg Prod.snd heq
      change FiniteTM0.lookupAction
          (FiniteTM0.Rule.mk sharedReturn (tagSymbol first.returnTag)
              (unwindState radius offset) (.write blankSymbol) ::
            returnTable radius sharedReturn
              (offset + blockWidth radius) commands)
          sharedReturn (tagSymbol command.returnTag) = _
      rw [FiniteTM0.lookupAction_cons_ne hkeyNe]
      exact ih htags.2

/-- Dispatch consumes the physical tag, restores the known blank at the frame
boundary, and enters the selected finite unwind routine. -/
theorem returnTable_reaches_unwind {numTags : Nat}
    {radius sharedReturn base commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (htags : (commands.map (·.returnTag)).Nodup)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : (T.moveN command.searchDirection
      (NestingMachine.bound radius)).read = MarkerMachine.blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine (returnTable radius sharedReturn base commands))
      ⟨sharedReturn, taggedFrameTape radius command T⟩
      ⟨unwindState radius commandOffset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩ := by
  let F := T.moveN command.searchDirection (NestingMachine.bound radius)
  have hlookup := lookupAction_returnTable_of_at
    (sharedReturn := sharedReturn) hat htags
  have hread : (taggedFrameTape radius command T).read =
      tagSymbol command.returnTag := by
    simp [taggedFrameTape, FullTM0.Tape.read, FullTM0.Tape.write]
  have hrestore :
      (taggedFrameTape radius command T).write blankSymbol =
        encodeTape F := by
    funext i
    by_cases hi : i = 0
    · subst i
      change blankSymbol = baseSymbol (F 0)
      change baseSymbol MarkerMachine.blankSymbol = baseSymbol (F 0)
      exact congrArg (baseSymbol (numTags := numTags)) hblank.symm
    · simp [taggedFrameTape, F, FullTM0.Tape.write, hi]
  have hstep : FullTM0.Reaches
      (FiniteTM0.machine (returnTable radius sharedReturn base commands))
      ⟨sharedReturn, taggedFrameTape radius command T⟩
      ⟨unwindState radius commandOffset,
        (taggedFrameTape radius command T).write blankSymbol⟩ := by
    apply reaches_of_step
    simp only [FullTM0.step]
    rw [hread]
    simp only [FiniteTM0.machine_apply, hlookup, Option.map_some]
    rfl
  rw [hrestore] at hstep
  exact hstep

/-- Every return rule has exactly the shared dispatcher state as its source. -/
theorem source_mem_returnTable {numTags : Nat}
    {radius sharedReturn offset state : Nat}
    {commands : List (Command numTags)}
    (hstate : state ∈ FiniteTM0.sourceStates
      (returnTable radius sharedReturn offset commands)) :
    state = sharedReturn := by
  induction commands generalizing offset with
  | nil => simp [returnTable, FiniteTM0.sourceStates] at hstate
  | cons command commands ih =>
      simp only [returnTable, FiniteTM0.sourceStates, List.map_cons,
        List.mem_cons] at hstate
      rcases hstate with hfirst | hrest
      · exact hfirst
      · exact ih hrest

/-- Dispatch remains valid after prefixing all command blocks and appending
the shared nested-core table. -/
theorem table_return_reaches_unwind {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (htags : (commands.map (·.returnTag)).Nodup)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : (T.moveN command.searchDirection
      (NestingMachine.bound radius)).read = MarkerMachine.blankSymbol) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨returnState base radius commands, taggedFrameTape radius command T⟩
      ⟨unwindState radius commandOffset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩ := by
  have hreturn := returnTable_reaches_unwind
    (sharedReturn := returnState base radius commands) hat htags T hblank
  have hcontroller := reaches_append_right_of_source_disjoint
    (commandTables radius (coreEntry base radius commands) base commands)
    (returnTable radius (returnState base radius commands) base commands)
    (by
      intro state hreturnSource hcommandSource
      have hreturnEq := source_mem_returnTable hreturnSource
      have hcommandBounds := source_mem_commandTables hcommandSource
      have hupper : state < returnState base radius commands := by
        change state < base + commands.length * blockWidth radius
        exact hcommandBounds.2
      exact (Nat.ne_of_lt hupper) hreturnEq)
    hreturn
  exact FiniteTM0Program.reaches_append_left
    (controllerTable base radius commands) core
    (by simpa [controllerTable] using hcontroller)

/-! ## Whole-machine command interfaces -/

/-- Lift an execution of a selected command block through the command family,
return dispatcher, and appended core. -/
theorem table_reaches_of_commandAt {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    {start finish :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreach : FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius commandOffset
          (coreEntry base radius commands) command))
      start finish) :
    FullTM0.Reaches (machine base radius commands core) start finish := by
  have hcommands := commandTables_reaches_of_at hat hreach
  have hcontroller := FiniteTM0Program.reaches_append_left
    (commandTables radius (coreEntry base radius commands) base commands)
    (returnTable radius (returnState base radius commands) base commands)
    hcommands
  exact FiniteTM0Program.reaches_append_left
    (controllerTable base radius commands) core
    (by simpa [controllerTable] using hcontroller)

/-- Exact nearby-success interface of a selected command in the full table. -/
theorem machine_reaches_success {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.expected)
      T command.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius)
    (hguard : FoundGuard command T distance) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, encodeTape T⟩
      ⟨command.successState, encodeTape (resultTape command T distance)⟩ := by
  exact table_reaches_of_commandAt core hat
    (command_reaches_success radius commandOffset
      (coreEntry base radius commands) command T distance hgap hnear hguard)

/-- Exact failed-launch interface of a selected command in the full table. -/
theorem machine_reaches_core {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.expected)
      T command.searchDirection distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, encodeTape T⟩
      ⟨coreEntry base radius commands, taggedFrameTape radius command T⟩ := by
  exact table_reaches_of_commandAt core hat
    (command_reaches_core radius commandOffset
      (coreEntry base radius commands) command T distance hgap hfar)

/-- Exact finite-unwind interface after the return tag has been dispatched. -/
theorem machine_unwind_reaches {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN command.searchDirection (NestingMachine.bound radius))
          (FullTM0.Tape.offset
            (NestingMachine.opposite command.searchDirection) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨unwindState radius commandOffset,
        encodeTape (T.moveN command.searchDirection
          (NestingMachine.bound radius))⟩
      ⟨entryState radius commandOffset,
        encodeTape (T.move command.searchDirection)⟩ := by
  exact table_reaches_of_commandAt core hat
    (command_unwind_reaches radius commandOffset
      (coreEntry base radius commands) command T hblank)

/-! ## Determinism of the generated finite table -/

/-- Membership of a transition key implies membership of its source state. -/
private theorem key_mem_sourceStates {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols}
    {key : FiniteTM0.Key numSymbols}
    (hkey : key ∈ rules.map Prod.fst) :
    key.1 ∈ FiniteTM0.sourceStates rules := by
  rcases List.mem_map.mp hkey with ⟨rule, hrule, heq⟩
  exact List.mem_map.mpr
    ⟨rule, hrule, congrArg Prod.fst heq⟩

/-- The structurally unrolled bounded scan has unique transition keys. -/
theorem scanTableAux_deterministic (expected : Fin 5)
    (direction : Turing.Dir) (success launch state remaining : Nat) :
    FiniteTM0.Deterministic
      (NestingMachine.scanTableAux expected direction success launch
        remaining state) := by
  induction remaining generalizing state with
  | zero =>
      simpa [NestingMachine.scanTableAux, FiniteTM0.Deterministic,
        FiniteTM0.Rule.mk] using
        (MarkerMachine.blankSymbol_ne_boundarySymbol expected).symm
  | succ remaining ih =>
      simp only [NestingMachine.scanTableAux, FiniteTM0.Deterministic,
        List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | htail
        · exact (MarkerMachine.blankSymbol_ne_boundarySymbol expected)
            (congrArg Prod.snd heq).symm
        · have hsource : state ∈ FiniteTM0.sourceStates
              (NestingMachine.scanTableAux expected direction success launch
                remaining (state + 1)) :=
            key_mem_sourceStates htail
          have hbounds := NestingMachine.source_mem_scanTableAux hsource
          omega
      · constructor
        · intro htail
          have hsource : state ∈ FiniteTM0.sourceStates
              (NestingMachine.scanTableAux expected direction success launch
                remaining (state + 1)) :=
            key_mem_sourceStates htail
          have hbounds := NestingMachine.source_mem_scanTableAux hsource
          omega
        · exact ih (state + 1)

/-- The structurally unrolled finite unwind has unique transition keys. -/
theorem unwindTableAux_deterministic (direction : Turing.Dir)
    (search state remaining : Nat) :
    FiniteTM0.Deterministic
      (NestingMachine.unwindTableAux direction search remaining state) := by
  induction remaining generalizing state with
  | zero =>
      simp [NestingMachine.unwindTableAux, FiniteTM0.Deterministic,
        FiniteTM0.Rule.mk]
  | succ remaining ih =>
      simp only [NestingMachine.unwindTableAux, FiniteTM0.Deterministic,
        List.map_cons, List.nodup_cons]
      constructor
      · intro htail
        have hsource : state ∈ FiniteTM0.sourceStates
              (NestingMachine.unwindTableAux direction search remaining
                (state + 1)) :=
          key_mem_sourceStates htail
        have hbounds := NestingMachine.source_mem_unwindTableAux hsource
        omega
      · exact ih (state + 1)

/-- The complete local scan/unwind controller is deterministic. -/
theorem localTable_deterministic (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) :
    FiniteTM0.Deterministic
      (NestingMachine.localTable radius expected direction) := by
  simp only [NestingMachine.localTable, FiniteTM0.Deterministic,
    List.map_append]
  apply List.Nodup.append
    (scanTableAux_deterministic expected direction
      (NestingMachine.localSuccessState radius)
      (NestingMachine.localLaunchState radius) 0
      (NestingMachine.bound radius))
    (unwindTableAux_deterministic direction 0
      (NestingMachine.localUnwindState radius) radius)
  rw [List.disjoint_iff_ne]
  intro scanKey hscan unwindKey hunwind heq
  have hscanState := key_mem_sourceStates hscan
  have hunwindState := key_mem_sourceStates hunwind
  apply NestingMachine.scan_unwind_source_disjoint radius expected direction
    unwindKey.1 hunwindState
  rw [← congrArg Prod.fst heq]
  exact hscanState

/-- Alphabet lifting preserves uniqueness of transition keys. -/
theorem liftTable_deterministic {numTags : Nat}
    {rules : FiniteTM0.Table MarkerMachine.AlphabetSize}
    (hdet : FiniteTM0.Deterministic rules) :
    FiniteTM0.Deterministic (liftTable (numTags := numTags) rules) := by
  let liftKey := fun key : FiniteTM0.Key MarkerMachine.AlphabetSize =>
    (key.1, baseSymbol (numTags := numTags) key.2)
  have hinjective : Function.Injective liftKey := by
    intro first second heq
    change (first.1, baseSymbol first.2) =
      (second.1, baseSymbol second.2) at heq
    rcases Prod.mk.inj heq with ⟨hstate, hsymbol⟩
    exact Prod.ext hstate (baseSymbol_injective hsymbol)
  have hmapped := hdet.map hinjective
  simpa [FiniteTM0.Deterministic, liftTable, liftRule,
    FiniteTM0.Rule.mk, liftKey, Function.comp_def, List.map_map]
    using hmapped

/-- Relocation preserves uniqueness of transition keys. -/
theorem relocate_deterministic {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols}
    (hdet : FiniteTM0.Deterministic rules) (offset : Nat) :
    FiniteTM0.Deterministic
      (FiniteTM0Program.relocate offset rules) := by
  let relocateKey := fun key : FiniteTM0.Key numSymbols =>
    (offset + key.1, key.2)
  have hinjective : Function.Injective relocateKey := by
    intro first second heq
    change (offset + first.1, first.2) =
      (offset + second.1, second.2) at heq
    rcases Prod.mk.inj heq with ⟨hstate, hsymbol⟩
    exact Prod.ext (Nat.add_left_cancel hstate) hsymbol
  have hmapped := hdet.map hinjective
  simpa [FiniteTM0.Deterministic, FiniteTM0Program.relocate,
    FiniteTM0Program.relocateRule, FiniteTM0.Rule.mk, relocateKey,
    Function.comp_def, List.map_map] using hmapped

/-- Every private bounded controller is deterministic. -/
theorem privateControllerTable_deterministic {numTags : Nat}
    (radius offset : Nat) (command : Command numTags) :
    FiniteTM0.Deterministic
      (privateControllerTable radius offset command) := by
  exact relocate_deterministic
    (liftTable_deterministic
      (localTable_deterministic radius command.expected
        command.searchDirection)) offset

/-- The short explicit continuation of one command is deterministic. -/
theorem continuationTable_deterministic {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    FiniteTM0.Deterministic
      (continuationTable radius offset sharedCore command) := by
  rw [FiniteTM0.Deterministic]
  apply List.Nodup.of_map Prod.fst
  have hlaunchFound :
      launchState radius offset ≠ foundState radius offset := by
    intro h
    change offset + (radius + 1 + 2) =
      offset + (radius + 1 + 1) at h
    omega
  rcases command with
    ⟨expected, searchDirection, successState, returnTag, foundAction⟩
  cases foundAction with
  | stay =>
      simp [continuationTable, FiniteTM0.Rule.mk, hlaunchFound]
  | shift shiftDirection departure =>
      cases departure with
      | none =>
          simp [continuationTable, FiniteTM0.Rule.mk, hlaunchFound,
            (clear_ne_launch radius offset).symm,
            (clear_ne_found radius offset).symm,
            (verify_ne_launch radius offset).symm,
            (verify_ne_found radius offset).symm,
            (verify_ne_clear radius offset).symm]
      | some departure =>
          simp [continuationTable, FiniteTM0.Rule.mk, hlaunchFound,
            (clear_ne_launch radius offset).symm,
            (clear_ne_found radius offset).symm,
            (verify_ne_launch radius offset).symm,
            (verify_ne_found radius offset).symm,
            (verify_ne_clear radius offset).symm,
            (depart_ne_launch radius offset).symm,
            (depart_ne_found radius offset).symm,
            (depart_ne_clear radius offset).symm,
            (depart_ne_verify radius offset).symm]

/-- One complete command block has unique transition keys. -/
theorem commandTable_deterministic {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    FiniteTM0.Deterministic
      (commandTable radius offset sharedCore command) := by
  simp only [commandTable, FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append
    (continuationTable_deterministic radius offset sharedCore command)
    (privateControllerTable_deterministic radius offset command)
  rw [List.disjoint_iff_ne]
  intro continuationKey hcontinuation privateKey hprivate heq
  have hcontinuationState := key_mem_sourceStates hcontinuation
  have hprivateState := key_mem_sourceStates hprivate
  apply private_continuation_source_disjoint radius offset sharedCore command
    privateKey.1 hprivateState
  rw [← congrArg Prod.fst heq]
  exact hcontinuationState

/-- Consecutive command blocks remain deterministic because their source-state
intervals are disjoint. -/
theorem commandTables_deterministic {numTags : Nat}
    (radius sharedCore offset : Nat) (commands : List (Command numTags)) :
    FiniteTM0.Deterministic
      (commandTables radius sharedCore offset commands) := by
  induction commands generalizing offset with
  | nil => simp [commandTables, FiniteTM0.Deterministic]
  | cons command commands ih =>
      simp only [commandTables, FiniteTM0.Deterministic, List.map_append]
      apply List.Nodup.append
        (commandTable_deterministic radius offset sharedCore command)
        (ih (offset + blockWidth radius))
      rw [List.disjoint_iff_ne]
      intro firstKey hfirst restKey hrest heq
      have hfirstSource := key_mem_sourceStates hfirst
      have hrestSource := key_mem_sourceStates hrest
      have hfirstBounds := source_mem_commandTable hfirstSource
      have hrestBounds := source_mem_commandTables hrestSource
      apply (Nat.ne_of_lt
        (lt_of_lt_of_le hfirstBounds.2 hrestBounds.1))
      exact congrArg Prod.fst heq

/-- The transition-key list of the shared return dispatcher is the command-tag
list embedded at the one shared return state. -/
theorem returnTable_keys {numTags : Nat} (radius sharedReturn offset : Nat)
    (commands : List (Command numTags)) :
    (returnTable radius sharedReturn offset commands).map Prod.fst =
      commands.map fun command =>
        (sharedReturn, tagSymbol command.returnTag) := by
  induction commands generalizing offset with
  | nil => rfl
  | cons command commands ih =>
      simp [returnTable, FiniteTM0.Rule.mk, ih]

/-- Distinct return tags are exactly the condition needed for deterministic
shared dispatch. -/
theorem returnTable_deterministic {numTags : Nat}
    (radius sharedReturn offset : Nat) (commands : List (Command numTags))
    (htags : (commands.map (·.returnTag)).Nodup) :
    FiniteTM0.Deterministic
      (returnTable radius sharedReturn offset commands) := by
  let returnKey := fun tag : Fin numTags =>
    (sharedReturn, tagSymbol tag)
  have hinjective : Function.Injective returnKey := by
    intro first second heq
    apply tagSymbol_injective
    exact congrArg Prod.snd heq
  have hmapped := htags.map hinjective
  rw [FiniteTM0.Deterministic,
    returnTable_keys radius sharedReturn offset commands]
  simpa [returnKey, List.map_map, Function.comp_def] using hmapped

/-- All generated controller sources precede the shared core entry. -/
theorem source_mem_controllerTable {numTags : Nat}
    {base radius state : Nat} {commands : List (Command numTags)}
    (hstate : state ∈ FiniteTM0.sourceStates
      (controllerTable base radius commands)) :
    state < coreEntry base radius commands := by
  simp only [controllerTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hstate
  rcases hstate with hcommands | hreturn
  · have hbounds := source_mem_commandTables hcommands
    have hreturn : state < returnState base radius commands := by
      change state < base + commands.length * blockWidth radius
      exact hbounds.2
    simpa [coreEntry] using Nat.lt_succ_of_lt hreturn
  · have heq := source_mem_returnTable hreturn
    subst state
    simp [coreEntry]

/-- The generated controller is deterministic whenever command return tags
are pairwise distinct. -/
theorem controllerTable_deterministic {numTags : Nat}
    (base radius : Nat) (commands : List (Command numTags))
    (htags : (commands.map (·.returnTag)).Nodup) :
    FiniteTM0.Deterministic (controllerTable base radius commands) := by
  simp only [controllerTable, FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append
    (commandTables_deterministic radius (coreEntry base radius commands)
      base commands)
    (returnTable_deterministic radius (returnState base radius commands)
      base commands htags)
  rw [List.disjoint_iff_ne]
  intro commandKey hcommand returnKey hreturn heq
  have hcommandSource := key_mem_sourceStates hcommand
  have hreturnSource := key_mem_sourceStates hreturn
  have hcommandBounds := source_mem_commandTables hcommandSource
  have hreturnEq := source_mem_returnTable hreturnSource
  have hcommandUpper : commandKey.1 < returnState base radius commands := by
    change commandKey.1 < base + commands.length * blockWidth radius
    exact hcommandBounds.2
  apply Nat.ne_of_lt hcommandUpper
  rw [congrArg Prod.fst heq, hreturnEq]

/-- Appending a deterministic shared core in fresh states preserves
determinism of the complete executable table. -/
theorem table_deterministic {numTags : Nat}
    (base radius : Nat) (commands : List (Command numTags))
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (htags : (commands.map (·.returnTag)).Nodup)
    (hcore : FiniteTM0.Deterministic core)
    (hfresh : ∀ state ∈ FiniteTM0.sourceStates core,
      coreEntry base radius commands ≤ state) :
    FiniteTM0.Deterministic (table base radius commands core) := by
  simp only [table, FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append
    (controllerTable_deterministic base radius commands htags) hcore
  rw [List.disjoint_iff_ne]
  intro controllerKey hcontroller coreKey hcoreKey heq
  have hcontrollerSource := key_mem_sourceStates hcontroller
  have hcoreSource := key_mem_sourceStates hcoreKey
  have hcontrollerUpper := source_mem_controllerTable hcontrollerSource
  have hcoreLower := hfresh coreKey.1 hcoreSource
  apply Nat.ne_of_lt (lt_of_lt_of_le hcontrollerUpper hcoreLower)
  exact congrArg Prod.fst heq

end BoundedMarkerProgram
end Hooper
end Kari
end LeanWang
