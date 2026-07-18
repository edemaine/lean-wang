/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.AnchoredCounterGeometry
import LeanWang.Kari.Hooper.CanonicalInitializerProgram
import LeanWang.Kari.Hooper.GlobalSourceProgram

/-!
# Finite-control plan for the two oriented counter copies

This module is the symbolic linker between the fixed four-register program
and `BoundedMarkerProgram`.  It deliberately stops one layer short of the
counter-simulation proof: the output is already an executable list of bounded
commands and an executable finite table of the intervening one-cell moves,
but its semantic correctness is proved in later modules.

Each primitive counter instruction starts at boundary `4`, validates the
whole five-boundary layout, and then follows one of two finite plans.

* Increment shifts its boundary suffix right-to-left, recovers the
  boundary-`4` anchor, and provides the outward-collision cleanup path.
* Conditional decrement navigates to the tested gap, branches on the cell to
  its left, and either returns along the zero route or performs the positive
  left-to-right suffix shift.

The construction is duplicated in the two physical orientations.  Every
bounded search has an address, and the address's position in `rawCommands`
is its unique physical return tag.  The controller and canonical initializer
come first; four disjoint state intervals then hold right logical states,
right direct states, left logical states, and left direct states.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPlan

open Turing CounterMachine
open BoundedMarkerProgram

noncomputable section

/-! ## Physical orientation and symbolic addresses -/

/-- Interpret a logical direction in a copy whose registers grow in
`growth`. -/
def orient (growth logical : Turing.Dir) : Turing.Dir :=
  match growth with
  | .right => logical
  | .left => NestingMachine.opposite logical

@[simp] theorem orient_right (logical : Turing.Dir) :
    orient .right logical = logical := rfl

@[simp] theorem orient_left_left : orient .left .left = .right := rfl
@[simp] theorem orient_left_right : orient .left .right = .left := rfl

theorem orient_involutive (growth logical : Turing.Dir) :
    orient growth (orient growth logical) = logical := by
  cases growth <;> cases logical <;> rfl

/-- Address of one bounded search in the symbolic counter plan.  Slots are
private to a counter control state; the two orientations are distinguished
explicitly. -/
structure SearchAddress where
  growth : Turing.Dir
  counterState : CounterMachine.State
  slot : Nat
  deriving DecidableEq

/-- An internal direct-control state. -/
structure DirectAddress where
  growth : Turing.Dir
  counterState : CounterMachine.State
  slot : Nat
  deriving DecidableEq

/-- Symbolic target of a bounded command or direct rule. -/
inductive ControlRef where
  | logical (growth : Turing.Dir) (counterState : CounterMachine.State)
  | direct (address : DirectAddress)
  | search (address : SearchAddress)
  | sharedReturn
  deriving DecidableEq

def directRef (growth : Turing.Dir) (counterState slot : Nat) :
    ControlRef :=
  .direct ⟨growth, counterState, slot⟩

def searchRef (growth : Turing.Dir) (counterState slot : Nat) :
    ControlRef :=
  .search ⟨growth, counterState, slot⟩

/-! ## Raw bounded commands and direct rules -/

/-- Navigation actions before physical orientation is selected. -/
inductive RawNavigationAction where
  | preserve
  | erase (departure : Option Turing.Dir)
  deriving DecidableEq

/-- A bounded command with symbolic continuations and logical directions.
Its return tag is assigned only after all commands have been enumerated. -/
inductive RawCommand where
  | boundaryNavigation (address : SearchAddress) (expected : Fin 5)
      (searchDirection : Turing.Dir) (success : ControlRef)
      (action : RawNavigationAction)
  | tagNavigation (address : SearchAddress)
      (searchDirection : Turing.Dir) (success : ControlRef)
  | markerShift (address : SearchAddress) (expected : Fin 5)
      (searchDirection shiftDirection : Turing.Dir)
      (success : ControlRef) (departure : Option Turing.Dir)
      (collision : Option ControlRef)
  deriving DecidableEq

def RawCommand.address : RawCommand → SearchAddress
  | .boundaryNavigation address _ _ _ _ => address
  | .tagNavigation address _ _ => address
  | .markerShift address _ _ _ _ _ _ => address

def RawCommand.logicalSearchDirection : RawCommand → Turing.Dir
  | .boundaryNavigation _ _ direction _ _ => direction
  | .tagNavigation _ direction _ => direction
  | .markerShift _ _ direction _ _ _ _ => direction

def RawCommand.physicalSearchDirection (command : RawCommand) : Turing.Dir :=
  orient command.address.growth command.logicalSearchDirection

/-- Symbols inspected by direct finite-control rules. -/
inductive RawRead where
  | blank
  | boundary (label : Fin 5)
  | nonblank
  deriving DecidableEq

/-- Every direct rule is a single physical head move. -/
structure RawDirectRule where
  growth : Turing.Dir
  source : ControlRef
  read : RawRead
  target : ControlRef
  direction : Turing.Dir
  deriving DecidableEq

/-! ## Reusable navigation-route compiler -/

def routeCommandsAux (growth : Turing.Dir) (counterState : Nat)
    (searchSlot directSlot : Nat) (after : ControlRef) :
    List MarkerValidation.Leg → List RawCommand
  | [] => []
  | leg :: legs =>
      let success := match legs with
        | [] => after
        | _ :: _ => directRef growth counterState directSlot
      .boundaryNavigation ⟨growth, counterState, searchSlot⟩ leg.target
          leg.direction success .preserve ::
        routeCommandsAux growth counterState (searchSlot + 1)
          (directSlot + 1) after legs

def routeContinuationRulesFrom (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat) :
    MarkerValidation.Leg → List MarkerValidation.Leg →
      List RawDirectRule
  | _, [] => []
  | previous, next :: legs =>
      ⟨growth, directRef growth counterState directSlot,
        .boundary previous.target,
        searchRef growth counterState (searchSlot + 1), next.direction⟩ ::
      routeContinuationRulesFrom growth counterState (searchSlot + 1)
        (directSlot + 1) next legs

def routeContinuationRules (growth : Turing.Dir)
    (counterState searchSlot directSlot : Nat) :
    List MarkerValidation.Leg → List RawDirectRule
  | [] => []
  | first :: legs =>
      routeContinuationRulesFrom growth counterState searchSlot directSlot
        first legs

def routeEntryRules (growth : Turing.Dir) (counterState : Nat)
    (source : ControlRef) (sourceBoundary : Fin 5) (searchSlot : Nat) :
    List MarkerValidation.Leg → List RawDirectRule
  | [] => []
  | first :: _ =>
      [⟨growth, source, .boundary sourceBoundary,
        searchRef growth counterState searchSlot, first.direction⟩]

/-! ## Fixed slot layout -/

def validationSearchBase : Nat := 0
def validationDirectBase : Nat := 0

def bodySearchBase : Nat := 16
def secondarySearchBase : Nat := 24
def zeroSearchBase : Nat := 32
def cleanupSearchBase : Nat := 40

def bodyDirectBase : Nat := 16
def testDirectSlot : Nat := 24
def branchDirectSlot : Nat := 25
def finishDirectSlot : Nat := 26
def zeroDirectBase : Nat := 32

/-- A deliberately roomy fixed stride for all internal states of one source
counter state.  Generated direct slots occupy only the prefix below `40`. -/
def directStride : Nat := 64

theorem directStride_pos : 0 < directStride := by decide

/-! ## Validation prefix -/

def bodyEntry (growth : Turing.Dir) (source : Nat) :
    CounterMachine.Instruction → ControlRef
  | .increment _ _ => searchRef growth source bodySearchBase
  | .decrement register _ _ =>
      match AnchoredCounterGeometry.routeToDecrementStart register with
      | [] => directRef growth source testDirectSlot
      | _ :: _ => directRef growth source bodyDirectBase

def validationCommands (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : List RawCommand :=
  routeCommandsAux growth source validationSearchBase
    validationDirectBase (bodyEntry growth source instruction)
    MarkerValidation.sweep

def validationRules (growth : Turing.Dir) (source : Nat) :
    List RawDirectRule :=
  routeEntryRules growth source (.logical growth source) 4
      validationSearchBase MarkerValidation.sweep ++
    routeContinuationRules growth source validationSearchBase
      validationDirectBase MarkerValidation.sweep

/-! ## Increment body and collision cleanup -/

def incrementShiftCommandsAux (growth : Turing.Dir) (source : Nat)
    (searchSlot : Nat) (first : Bool) : List (Fin 5) → List RawCommand
  | [] => []
  | expected :: labels =>
      let success := match labels with
        | [] => directRef growth source bodyDirectBase
        | _ :: _ => searchRef growth source (searchSlot + 1)
      let collision := if first then
          some (directRef growth source testDirectSlot)
        else none
      .markerShift ⟨growth, source, searchSlot⟩ expected .left .right
          success (some .left) collision ::
        incrementShiftCommandsAux growth source (searchSlot + 1) false labels

def incrementShiftCommands (growth : Turing.Dir) (source : Nat)
    (register : Register) : List RawCommand :=
  incrementShiftCommandsAux growth source bodySearchBase true
    (MarkerShift.incrementOrder register)

def cleanupCommands (growth : Turing.Dir) (source : Nat) :
    List RawCommand :=
  [ .boundaryNavigation ⟨growth, source, cleanupSearchBase⟩ 3 .left
      (searchRef growth source (cleanupSearchBase + 1)) (.erase (some .left))
  , .boundaryNavigation ⟨growth, source, cleanupSearchBase + 1⟩ 2 .left
      (searchRef growth source (cleanupSearchBase + 2)) (.erase (some .left))
  , .boundaryNavigation ⟨growth, source, cleanupSearchBase + 2⟩ 1 .left
      (searchRef growth source (cleanupSearchBase + 3)) (.erase (some .left))
  , .boundaryNavigation ⟨growth, source, cleanupSearchBase + 3⟩ 0 .left
      (searchRef growth source (cleanupSearchBase + 4)) (.erase (some .left))
  , .tagNavigation ⟨growth, source, cleanupSearchBase + 4⟩ .left
      .sharedReturn
  ]

def incrementCommands (growth : Turing.Dir) (source next : Nat)
    (register : Register) : List RawCommand :=
  incrementShiftCommands growth source register ++
    routeCommandsAux growth source secondarySearchBase
      (bodyDirectBase + 2) (.logical growth next)
      (AnchoredCounterGeometry.routeFromIncrement register) ++
    cleanupCommands growth source

def incrementRules (growth : Turing.Dir) (source next : Nat)
    (register : Register) : List RawDirectRule :=
  let route := AnchoredCounterGeometry.routeFromIncrement register
  let afterShift := match route with
    | [] => ControlRef.logical growth next
    | _ :: _ => directRef growth source (bodyDirectBase + 1)
  [ ⟨growth, directRef growth source bodyDirectBase, .blank,
      afterShift, .right⟩
  ] ++
    routeEntryRules growth source
      (directRef growth source (bodyDirectBase + 1))
      (MarkerSchedule.decrementStartBoundary register)
      secondarySearchBase route ++
    routeContinuationRules growth source secondarySearchBase
      (bodyDirectBase + 2) route ++
    [ ⟨growth, directRef growth source testDirectSlot, .nonblank,
        searchRef growth source cleanupSearchBase, .left⟩
    ]

/-! ## Conditional-decrement body -/

def decrementShiftCommandsAux (growth : Turing.Dir) (source : Nat)
    (searchSlot : Nat) : List (Fin 5) → List RawCommand
  | [] => []
  | expected :: labels =>
      let success := match labels with
        | [] => directRef growth source finishDirectSlot
        | _ :: _ => searchRef growth source (searchSlot + 1)
      .markerShift ⟨growth, source, searchSlot⟩ expected .right .left
          success (some .right) none ::
        decrementShiftCommandsAux growth source (searchSlot + 1) labels

def decrementShiftCommands (growth : Turing.Dir) (source : Nat)
    (register : Register) : List RawCommand :=
  decrementShiftCommandsAux growth source secondarySearchBase
    (MarkerShift.decrementOrder register)

def decrementCommands (growth : Turing.Dir) (source : Nat)
    (register : Register) (ifZero : Nat) : List RawCommand :=
  routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
      (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register) ++
    decrementShiftCommands growth source register ++
    routeCommandsAux growth source zeroSearchBase zeroDirectBase
      (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register)

def decrementRules (growth : Turing.Dir) (source : Nat)
    (register : Register) (_ifZero ifPositive : Nat) : List RawDirectRule :=
  let toTest := AnchoredCounterGeometry.routeToDecrementStart register
  let zeroRoute := AnchoredCounterGeometry.routeFromZero register
  routeEntryRules growth source (directRef growth source bodyDirectBase) 4
      bodySearchBase toTest ++
    routeContinuationRules growth source bodySearchBase
      (bodyDirectBase + 1) toTest ++
    [ ⟨growth, directRef growth source testDirectSlot,
        .boundary (MarkerSchedule.decrementStartBoundary register),
        directRef growth source branchDirectSlot, .left⟩
    , ⟨growth, directRef growth source branchDirectSlot, .blank,
        searchRef growth source secondarySearchBase, .right⟩
    , ⟨growth, directRef growth source branchDirectSlot,
        .boundary (AnchoredCounterGeometry.registerGap register).castSucc,
        searchRef growth source zeroSearchBase, .right⟩
    , ⟨growth, directRef growth source finishDirectSlot, .blank,
        .logical growth ifPositive, .left⟩
    ] ++
    routeContinuationRules growth source zeroSearchBase zeroDirectBase
      zeroRoute

/-! ## Enumerating the fixed global counter program -/

def commandsForRule (growth : Turing.Dir)
    (rule : CounterMachine.Rule) : List RawCommand :=
  validationCommands growth rule.1 rule.2 ++
    match rule.2 with
    | .increment register next =>
        incrementCommands growth rule.1 next register
    | .decrement register ifZero _ =>
        decrementCommands growth rule.1 register ifZero

def directRulesForRule (growth : Turing.Dir)
    (rule : CounterMachine.Rule) : List RawDirectRule :=
  validationRules growth rule.1 ++
    match rule.2 with
    | .increment register next =>
        incrementRules growth rule.1 next register
    | .decrement register ifZero ifPositive =>
        decrementRules growth rule.1 register ifZero ifPositive

def rawCommandsFor (growth : Turing.Dir) : List RawCommand :=
  GlobalSourceProgram.program.flatMap (commandsForRule growth)

def rawDirectRulesFor (growth : Turing.Dir) : List RawDirectRule :=
  GlobalSourceProgram.program.flatMap (directRulesForRule growth)

/-- Both physical copies share one tagged bounded-search controller. -/
def rawCommands : List RawCommand :=
  rawCommandsFor .right ++ rawCommandsFor .left

def rawDirectRules : List RawDirectRule :=
  rawDirectRulesFor .right ++ rawDirectRulesFor .left

/-- There is exactly one return symbol for every enumerated bounded search. -/
abbrev numTags : Nat := rawCommands.length

theorem rawCommands_length : rawCommands.length = numTags := rfl

/-! ## Finite logical-state bound -/

def instructionTargets : CounterMachine.Instruction → List Nat
  | .increment _ next => [next]
  | .decrement _ ifZero ifPositive => [ifZero, ifPositive]

def ruleStates (rule : CounterMachine.Rule) : List Nat :=
  rule.1 :: instructionTargets rule.2

def programStates : List Nat :=
  GlobalSourceProgram.program.flatMap ruleStates

def maximum : List Nat → Nat
  | [] => 0
  | state :: states => max state (maximum states)

theorem le_maximum_of_mem {state : Nat} {states : List Nat}
    (hstate : state ∈ states) : state ≤ maximum states := by
  induction states with
  | nil => simp at hstate
  | cons head tail ih =>
      simp only [List.mem_cons] at hstate
      simp only [maximum]
      rcases hstate with rfl | hstate
      · exact Nat.le_max_left _ _
      · exact (ih hstate).trans (Nat.le_max_right _ _)

/-- One more than every source or target state named by the fixed counter
program. -/
def logicalSpan : Nat := maximum programStates + 1

theorem state_lt_logicalSpan {state : Nat} (hstate : state ∈ programStates) :
    state < logicalSpan := by
  exact Nat.lt_succ_of_le (le_maximum_of_mem hstate)

theorem source_mem_programStates (rule : CounterMachine.Rule)
    (hrule : rule ∈ GlobalSourceProgram.program) : rule.1 ∈ programStates := by
  simp only [programStates, List.mem_flatMap]
  exact ⟨rule, hrule, by simp [ruleStates]⟩

/-! ## Concrete state allocation -/

/-- Index of a symbolic search; known generated addresses occur exactly once,
and later well-formedness proofs can replace this executable lookup by their
enumeration index. -/
def searchIndex (address : SearchAddress) : Nat :=
  (rawCommands.map RawCommand.address).findIdx (fun candidate =>
    candidate == address)

theorem searchIndex_lt_numTags {address : SearchAddress}
    (haddress : address ∈ rawCommands.map RawCommand.address) :
    searchIndex address < numTags := by
  unfold searchIndex numTags
  have hfound := List.findIdx_lt_length_of_exists
    (xs := rawCommands.map RawCommand.address)
    (p := fun candidate => candidate == address)
    ⟨address, haddress, by simp⟩
  simpa using hfound

theorem command_searchIndex_lt_numTags {command : RawCommand}
    (hcommand : command ∈ rawCommands) :
    searchIndex command.address < numTags := by
  apply searchIndex_lt_numTags
  exact List.mem_map.mpr ⟨command, hcommand, rfl⟩

def controllerReturn (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  BoundedMarkerProgram.commandOffset base (CanonicalInitializer.radius c)
    numTags

def controllerCoreEntry (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  controllerReturn base c + 1

def initializerEnd (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  CanonicalInitializerProgram.exitState (controllerCoreEntry base c) c numTags

def directSpan : Nat := logicalSpan * directStride

def rightLogicalBase (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  initializerEnd base c

def rightDirectBase (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  rightLogicalBase base c + logicalSpan

def leftLogicalBase (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  rightDirectBase base c + directSpan

def leftDirectBase (base : Nat) (c : Nat.Partrec.Code) : Nat :=
  leftLogicalBase base c + logicalSpan

def logicalBase (base : Nat) (c : Nat.Partrec.Code) : Turing.Dir → Nat
  | .right => rightLogicalBase base c
  | .left => leftLogicalBase base c

def directBase (base : Nat) (c : Nat.Partrec.Code) : Turing.Dir → Nat
  | .right => rightDirectBase base c
  | .left => leftDirectBase base c

def logicalState (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState : Nat) : Nat :=
  logicalBase base c growth + counterState

def directState (base : Nat) (c : Nat.Partrec.Code)
    (address : DirectAddress) : Nat :=
  directBase base c address.growth +
    address.counterState * directStride + address.slot

def searchState (base : Nat) (c : Nat.Partrec.Code)
    (address : SearchAddress) : Nat :=
  BoundedMarkerProgram.commandOffset base (CanonicalInitializer.radius c)
    (searchIndex address)

def resolve (base : Nat) (c : Nat.Partrec.Code) : ControlRef → Nat
  | .logical growth counterState => logicalState base c growth counterState
  | .direct address => directState base c address
  | .search address => searchState base c address
  | .sharedReturn => controllerReturn base c

theorem logicalState_bounds (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) {counterState : Nat}
    (hstate : counterState < logicalSpan) :
    logicalBase base c growth ≤ logicalState base c growth counterState ∧
      logicalState base c growth counterState <
        logicalBase base c growth + logicalSpan := by
  simp only [logicalState]
  omega

theorem directState_bounds (base : Nat) (c : Nat.Partrec.Code)
    {address : DirectAddress} (hstate : address.counterState < logicalSpan)
    (hslot : address.slot < directStride) :
    directBase base c address.growth ≤ directState base c address ∧
      directState base c address <
        directBase base c address.growth + directSpan := by
  simp only [directState, directSpan]
  constructor
  · omega
  · have hslotBlock :
        address.counterState * directStride + address.slot <
          (address.counterState + 1) * directStride := by
      have hadd := Nat.add_lt_add_left hslot
        (address.counterState * directStride)
      simpa [Nat.add_mul, Nat.add_assoc] using hadd
    have hblockSpan :
        (address.counterState + 1) * directStride ≤
          logicalSpan * directStride :=
      Nat.mul_le_mul_right directStride (Nat.succ_le_iff.mpr hstate)
    simpa only [Nat.add_assoc] using
      Nat.add_lt_add_left (hslotBlock.trans_le hblockSpan)
        (directBase base c address.growth)

theorem rightLogical_before_rightDirect (base : Nat)
    (c : Nat.Partrec.Code) :
    rightLogicalBase base c + logicalSpan = rightDirectBase base c := rfl

theorem rightDirect_before_leftLogical (base : Nat)
    (c : Nat.Partrec.Code) :
    rightDirectBase base c + directSpan = leftLogicalBase base c := rfl

theorem leftLogical_before_leftDirect (base : Nat)
    (c : Nat.Partrec.Code) :
    leftLogicalBase base c + logicalSpan = leftDirectBase base c := rfl

/-- The four allocated counter intervals are pairwise ordered and hence
pairwise disjoint. -/
theorem allocated_ranges_ordered (base : Nat) (c : Nat.Partrec.Code) :
    rightLogicalBase base c ≤ rightDirectBase base c ∧
    rightDirectBase base c ≤ leftLogicalBase base c ∧
    leftLogicalBase base c ≤ leftDirectBase base c := by
  simp [rightDirectBase, leftLogicalBase, leftDirectBase]

/-- The four concrete intervals, listed in increasing address order. -/
def allocatedRanges (base : Nat) (c : Nat.Partrec.Code) :
    List (Nat × Nat) :=
  [ (rightLogicalBase base c, logicalSpan)
  , (rightDirectBase base c, directSpan)
  , (leftLogicalBase base c, logicalSpan)
  , (leftDirectBase base c, directSpan)
  ]

/-- Consecutive (and therefore every earlier/later) ranges are separated by
their half-open endpoints. -/
theorem allocatedRanges_pairwise_separated (base : Nat)
    (c : Nat.Partrec.Code) :
    (allocatedRanges base c).Pairwise fun first second =>
      first.1 + first.2 ≤ second.1 := by
  simp [allocatedRanges, rightDirectBase, leftLogicalBase, leftDirectBase]
  omega

theorem right_direct_ne_left_logical (base : Nat) (c : Nat.Partrec.Code)
    {rightState leftState : Nat}
    (hright : rightDirectBase base c ≤ rightState ∧
      rightState < rightDirectBase base c + directSpan)
    (hleft : leftLogicalBase base c ≤ leftState ∧
      leftState < leftLogicalBase base c + logicalSpan) :
    rightState ≠ leftState := by
  intro heq
  subst leftState
  rw [← rightDirect_before_leftLogical] at hleft
  omega

/-! ## Executable tagged command list -/

def compileNavigationAction (growth : Turing.Dir) :
    RawNavigationAction → BoundedMarkerProgram.NavigationAction
  | .preserve => .preserve
  | .erase departure => .erase (departure.map (orient growth))

def compileCommand (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length) :
    BoundedMarkerProgram.Command rawCommands.length :=
  match rawCommands.get tag with
  | .boundaryNavigation address expected direction success action =>
      .boundaryNavigation expected (orient address.growth direction)
        (resolve base c success) tag
        (compileNavigationAction address.growth action)
  | .tagNavigation address direction success =>
      .tagNavigation (orient address.growth direction)
        (resolve base c success) tag
  | .markerShift address expected search shift success departure collision =>
      .markerShift ⟨expected, orient address.growth search,
          orient address.growth shift⟩
        (resolve base c success) tag (departure.map (orient address.growth))
        (collision.map (resolve base c))

def commands (base : Nat) (c : Nat.Partrec.Code) :
    List (BoundedMarkerProgram.Command numTags) :=
  List.ofFn (compileCommand base c)

@[simp] theorem commands_length (base : Nat) (c : Nat.Partrec.Code) :
    (commands base c).length = numTags := by
  simp only [commands, List.length_ofFn, numTags]

@[simp] theorem compileCommand_returnTag (base : Nat)
    (c : Nat.Partrec.Code) (tag : Fin rawCommands.length) :
    (compileCommand base c tag).returnTag = tag := by
  unfold compileCommand
  generalize rawCommands.get tag = command
  cases command <;> rfl

theorem commands_returnTag_get (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length) :
    ((commands base c).get
      ⟨tag.val, by simpa only [commands_length, rawCommands_length] using
        tag.isLt⟩).returnTag =
      ⟨tag.val, by simpa only [rawCommands_length] using tag.isLt⟩ := by
  simp only [commands, List.get_ofFn, compileCommand_returnTag]
  apply Fin.ext
  rfl

theorem commands_returnTags_nodup (base : Nat) (c : Nat.Partrec.Code) :
    ((commands base c).map Command.returnTag).Nodup := by
  rw [commands, ← List.ofFn_comp']
  simpa only [compileCommand_returnTag] using
    (List.nodup_ofFn_ofInjective
      (f := fun tag : Fin rawCommands.length => tag) fun _ _ h => h)

theorem commands_returnTags_eq_finRange (base : Nat)
    (c : Nat.Partrec.Code) :
    (commands base c).map Command.returnTag = List.finRange numTags := by
  rw [commands, ← List.ofFn_comp']
  simpa only [compileCommand_returnTag, Function.id_def] using
    (List.ofFn_id rawCommands.length)

theorem controllerReturn_eq (base : Nat) (c : Nat.Partrec.Code) :
    BoundedMarkerProgram.returnState base (CanonicalInitializer.radius c)
      (commands base c) = controllerReturn base c := by
  simp [BoundedMarkerProgram.returnState, controllerReturn]

theorem controllerCoreEntry_eq (base : Nat) (c : Nat.Partrec.Code) :
    BoundedMarkerProgram.coreEntry base (CanonicalInitializer.radius c)
      (commands base c) = controllerCoreEntry base c := by
  simp [BoundedMarkerProgram.coreEntry, controllerCoreEntry,
    controllerReturn_eq]

/-! ## Tag-selected initializer and direct finite table -/

def initializerGrowth (tag : Fin numTags) : Turing.Dir :=
  (rawCommands.get tag).physicalSearchDirection

/-- Canonical entry of the oriented copy selected by a failed search. -/
def canonicalEntry (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) : Nat :=
  logicalState base c growth
    (GlobalSourceSemantics.canonicalCounterCfg c).state

def initializerExitFor (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin numTags) : Nat :=
  canonicalEntry base c (initializerGrowth tag)

def initializerTable (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  CanonicalInitializerProgram.table (controllerCoreEntry base c) c numTags
    initializerGrowth (initializerExitFor base c)

@[simp] theorem compileCommand_searchDirection (base : Nat)
    (c : Nat.Partrec.Code) (tag : Fin rawCommands.length) :
    (compileCommand base c tag).searchDirection =
      (rawCommands.get tag).physicalSearchDirection := by
  unfold compileCommand
  generalize rawCommands.get tag = command
  cases command <;> rfl

theorem initializerGrowth_eq_command (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin numTags) :
    initializerGrowth tag = ((commands base c).get
      ⟨tag.val, by simpa only [commands_length] using tag.isLt⟩).searchDirection := by
  let rawTag : Fin rawCommands.length :=
    ⟨tag.val, by simpa only [numTags] using tag.isLt⟩
  change (rawCommands.get rawTag).physicalSearchDirection = _
  simp only [commands, List.get_ofFn, compileCommand_searchDirection]
  congr 2

theorem initializerExitFor_eq (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin numTags) :
    initializerExitFor base c tag =
      canonicalEntry base c (initializerGrowth tag) := rfl

def symbolsForRead (read : RawRead) : List (Symbol numTags) :=
  match read with
  | .blank => [blankSymbol]
  | .boundary label => [boundarySymbol label]
  | .nonblank => nonblankSymbols numTags

def directRuleTable (base : Nat) (c : Nat.Partrec.Code)
    (rule : RawDirectRule) : FiniteTM0.Table (AlphabetSize numTags) :=
  (symbolsForRead rule.read).map fun symbol =>
    FiniteTM0.Rule.mk (resolve base c rule.source) symbol
      (resolve base c rule.target)
      (liftAction (MarkerMachine.moveAction
        (orient rule.growth rule.direction)))

/-- All one-cell glue rules between bounded searches. -/
def directTable (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  rawDirectRules.flatMap (directRuleTable base c)

/-- The initializer and all direct glue rules form the shared core appended
after the tagged bounded-search controller. -/
def coreTable (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  initializerTable base c ++ directTable base c

/-- Complete executable finite table of the current compilation plan. -/
def table (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  BoundedMarkerProgram.table base (CanonicalInitializer.radius c)
    (commands base c) (coreTable base c)

end

end CounterControlPlan
end Hooper
end Kari
end LeanWang
