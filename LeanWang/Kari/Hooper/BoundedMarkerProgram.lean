/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.NestingMachine
import LeanWang.Kari.Hooper.FiniteTM0Path

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

/-- Finite targets understood by the bounded controller.  Boundary targets
recognize one marker label; `anyTag` recognizes any physical return tag. -/
inductive Target (numTags : Nat) where
  | boundary (label : Fin 5)
  | anyTag
  deriving DecidableEq

/-- What to do after the expected marker has been found. -/
inductive FoundAction where
  /-- Search-only navigation: leave the target and head in place. -/
  | preserve
  /-- Erase a found boundary, optionally departing by one head step. -/
  | erase (departure : Option Turing.Dir)
  /-- Move the marker one cell in `shiftDirection`.  If `departure` is
  present, take that head step after rewriting the marker and only then enter
  the external success state. -/
  | shift (written : Fin 5) (shiftDirection : Turing.Dir)
      (departure : Option Turing.Dir)
      (collisionState : Option FiniteTM0.State)
  deriving DecidableEq

/-- Actions exposed by boundary-navigation commands. -/
inductive NavigationAction where
  | preserve
  | erase (departure : Option Turing.Dir)
  deriving DecidableEq

/-- One bounded-search command.  `returnTag` is written before entering the
shared nested core and is consumed by the shared return dispatcher.  The
constructors rule out the meaningless operation of shifting an `anyTag`
target. -/
inductive Command (numTags : Nat) where
  | boundaryNavigation (expected : Fin 5)
      (searchDirection : Turing.Dir)
      (successState : FiniteTM0.State) (returnTag : Fin numTags)
      (action : NavigationAction)
  | tagNavigation (searchDirection : Turing.Dir)
      (successState : FiniteTM0.State) (returnTag : Fin numTags)
  | markerShift (move : MarkerProgram.Move)
      (successState : FiniteTM0.State) (returnTag : Fin numTags)
      (departure : Option Turing.Dir)
      (collisionState : Option FiniteTM0.State)
  deriving DecidableEq

def Command.target {numTags : Nat} : Command numTags → Target numTags
  | .boundaryNavigation expected _ _ _ _ => .boundary expected
  | .tagNavigation _ _ _ => .anyTag
  | .markerShift move _ _ _ _ => .boundary move.expected

def Command.searchDirection {numTags : Nat} : Command numTags → Turing.Dir
  | .boundaryNavigation _ direction _ _ _ => direction
  | .tagNavigation direction _ _ => direction
  | .markerShift move _ _ _ _ => move.searchDirection

def Command.successState {numTags : Nat} :
    Command numTags → FiniteTM0.State
  | .boundaryNavigation _ _ successState _ _ => successState
  | .tagNavigation _ successState _ => successState
  | .markerShift _ successState _ _ _ => successState

def Command.returnTag {numTags : Nat} : Command numTags → Fin numTags
  | .boundaryNavigation _ _ _ returnTag _ => returnTag
  | .tagNavigation _ _ returnTag => returnTag
  | .markerShift _ _ returnTag _ _ => returnTag

def Command.foundAction {numTags : Nat} : Command numTags → FoundAction
  | .boundaryNavigation _ _ _ _ .preserve => .preserve
  | .boundaryNavigation _ _ _ _ (.erase departure) => .erase departure
  | .tagNavigation _ _ _ => .preserve
  | .markerShift move _ _ departure collisionState =>
      .shift move.expected move.shiftDirection departure collisionState

/-- Navigation toward an arbitrary finite target. -/
def Command.navigateTarget {numTags : Nat} (target : Target numTags)
    (searchDirection : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) : Command numTags :=
  match target with
  | .boundary expected =>
      .boundaryNavigation expected searchDirection successState returnTag
        .preserve
  | .anyTag => .tagNavigation searchDirection successState returnTag

/-- Backward-compatible navigation toward one boundary label. -/
def Command.navigate {numTags : Nat} (expected : Fin 5)
    (searchDirection : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) : Command numTags :=
  .boundaryNavigation expected searchDirection successState returnTag
    .preserve

/-- Boundary navigation that erases the found marker and optionally departs
one cell before entering its success state. -/
def Command.erase {numTags : Nat} (expected : Fin 5)
    (searchDirection : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir := none) :
    Command numTags :=
  .boundaryNavigation expected searchDirection successState returnTag
    (.erase departure)

/-- Cleanup navigation: find any physical tag and preserve it while entering
the shared return dispatcher. -/
def Command.cleanup {numTags : Nat} (searchDirection : Turing.Dir)
    (sharedReturn : FiniteTM0.State) (returnTag : Fin numTags) :
    Command numTags :=
  .tagNavigation searchDirection sharedReturn returnTag

/-- Marker-shift descriptor with optional departure and collision exits. -/
def Command.move {numTags : Nat} (move : MarkerProgram.Move)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir := none)
    (collisionState : Option FiniteTM0.State := none) : Command numTags :=
  .markerShift move successState returnTag departure collisionState

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

/-- Semantic recognition predicate for a finite target. -/
def Target.Matches {numTags : Nat} :
    Target numTags → Symbol numTags → Prop
  | .boundary label, symbol => symbol = boundarySymbol label
  | .anyTag, symbol => ∃ tag : Fin numTags, symbol = tagSymbol tag

instance {numTags : Nat} (target : Target numTags)
    (symbol : Symbol numTags) : Decidable (target.Matches symbol) := by
  cases target <;> simp only [Target.Matches] <;> infer_instance

/-- A labelled boundary has a unique first-blank distance from a fixed tape
and direction. -/
theorem boundaryGap_distance_unique
    {numTags : Nat}
    {T : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {first second : Nat} {target : Fin 5}
    (firstGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction first)
    (secondGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches T direction second) :
    first = second := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hblank := secondGap.blank hlt
    have hmarked := firstGap.marked
    rw [show T (FullTM0.Tape.offset direction first) =
        boundarySymbol target by
      simpa [Target.Matches] using hmarked] at hblank
    exact blankSymbol_ne_boundarySymbol target hblank.symm
  · have hblank := firstGap.blank hlt
    have hmarked := secondGap.marked
    rw [show T (FullTM0.Tape.offset direction second) =
        boundarySymbol target by
      simpa [Target.Matches] using hmarked] at hblank
    exact blankSymbol_ne_boundarySymbol target hblank.symm

/-- Target-recognition rules at one scan state.  Every recognized symbol is
rewritten to itself, so arbitrary native tagged tapes are preserved. -/
def targetRules {numTags : Nat} (state success : FiniteTM0.State) :
    Target numTags → FiniteTM0.Table (AlphabetSize numTags)
  | .boundary label =>
      [FiniteTM0.Rule.mk state (boundarySymbol label) success
        (.write (boundarySymbol label))]
  | .anyTag =>
      (List.finRange numTags).map fun tag =>
        FiniteTM0.Rule.mk state (tagSymbol tag) success
          (.write (tagSymbol tag))

theorem targetRules_deterministic {numTags : Nat}
    (state success : FiniteTM0.State) (target : Target numTags) :
    FiniteTM0.Deterministic (targetRules state success target) := by
  cases target with
  | boundary label =>
      simp [targetRules, FiniteTM0.Deterministic, FiniteTM0.Rule.mk]
  | anyTag =>
      let key := fun tag : Fin numTags => (state, tagSymbol tag)
      have hkey : Function.Injective key := by
        intro first second heq
        apply tagSymbol_injective
        exact congrArg Prod.snd heq
      have h := (List.nodup_finRange numTags).map hkey
      simpa [targetRules, FiniteTM0.Deterministic, FiniteTM0.Rule.mk,
        key, List.map_map, Function.comp_def] using h

theorem lookupAction_targetRules {numTags : Nat}
    (state success : FiniteTM0.State) (target : Target numTags)
    (symbol : Symbol numTags) (hmatch : target.Matches symbol) :
    FiniteTM0.lookupAction (targetRules state success target) state symbol =
      some (success, .write symbol) := by
  rw [FiniteTM0.lookupAction_eq_some_iff_of_deterministic
    (targetRules_deterministic state success target)]
  cases target with
  | boundary label =>
      simp only [Target.Matches] at hmatch
      subst symbol
      simp [targetRules, FiniteTM0.Rule.mk]
  | anyTag =>
      rcases hmatch with ⟨tag, rfl⟩
      simp [targetRules, FiniteTM0.Rule.mk, List.mem_finRange]

theorem target_not_blank {numTags : Nat} (target : Target numTags) :
    ¬ target.Matches (blankSymbol : Symbol numTags) := by
  cases target with
  | boundary label => exact blankSymbol_ne_boundarySymbol label
  | anyTag =>
      rintro ⟨tag, htag⟩
      exact blankSymbol_ne_tagSymbol tag htag

theorem lookupAction_targetRules_blank {numTags : Nat}
    (state success : FiniteTM0.State) (target : Target numTags) :
    FiniteTM0.lookupAction (targetRules state success target)
      state (blankSymbol : Symbol numTags) = none := by
  apply FiniteTM0.lookupAction_eq_none_of_key_not_mem
  cases target with
  | boundary label =>
      simp [targetRules, FiniteTM0.Rule.mk,
        blankSymbol_ne_boundarySymbol label]
  | anyTag =>
      simp only [targetRules, List.map_map, List.mem_map,
        FiniteTM0.Rule.mk, Function.comp_apply]
      rintro ⟨tag, -, heq⟩
      exact blankSymbol_ne_tagSymbol tag (congrArg Prod.snd heq).symm

theorem lookupAction_targetRules_state_ne {numTags : Nat}
    {state query success : FiniteTM0.State} (target : Target numTags)
    (hne : query ≠ state) (symbol : Symbol numTags) :
    FiniteTM0.lookupAction (targetRules state success target)
      query symbol = none := by
  apply FiniteTM0.lookupAction_eq_none_of_key_not_mem
  cases target with
  | boundary label =>
      simp [targetRules, FiniteTM0.Rule.mk, hne]
  | anyTag =>
      simp only [targetRules, List.map_map, List.mem_map,
        FiniteTM0.Rule.mk, Function.comp_apply]
      rintro ⟨tag, -, heq⟩
      exact hne (congrArg Prod.fst heq).symm

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

/-! ## Native tagged bounded scans -/

/-- A bounded scan over the enlarged alphabet.  The target-rule family is
finite even for `anyTag`, while blank rules retain the original bounded-search
geometry. -/
def nativeScanTableAux {numTags : Nat} (target : Target numTags)
    (direction : Turing.Dir) (success launch : FiniteTM0.State) :
    Nat → FiniteTM0.State → FiniteTM0.Table (AlphabetSize numTags)
  | 0, state =>
      targetRules state success target ++
        [FiniteTM0.Rule.mk state blankSymbol launch (.write blankSymbol)]
  | remaining + 1, state =>
      targetRules state success target ++
        FiniteTM0.Rule.mk state blankSymbol (state + 1)
            (liftAction (MarkerMachine.moveAction direction)) ::
          nativeScanTableAux target direction success launch
            remaining (state + 1)

/-- Native scan prefix in the local controller states. -/
def nativeScanTable {numTags : Nat} (radius : Nat)
    (target : Target numTags) (direction : Turing.Dir) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  nativeScanTableAux target direction
    (NestingMachine.localSuccessState radius)
    (NestingMachine.localLaunchState radius)
    (NestingMachine.bound radius) 0

@[simp]
theorem lookup_nativeScanTableAux_target_current {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining : Nat) (symbol : Symbol numTags)
    (hmatch : target.Matches symbol) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch remaining state)
        state symbol =
      some (success, .write symbol) := by
  cases remaining <;>
    simp only [nativeScanTableAux, FiniteTM0Program.lookupAction_append,
      lookupAction_targetRules state success target symbol hmatch]

@[simp]
theorem lookup_nativeScanTableAux_blank_current {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state : Nat) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch 0 state)
        state blankSymbol =
      some (launch, .write blankSymbol) := by
  simp [nativeScanTableAux, FiniteTM0Program.lookupAction_append,
    lookupAction_targetRules_blank, FiniteTM0.lookupAction,
    FiniteTM0.Rule.mk]

@[simp]
theorem lookup_nativeScanTableAux_blank_step {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining : Nat) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch
          (remaining + 1) state)
        state blankSymbol =
      some (state + 1,
        liftAction (MarkerMachine.moveAction direction)) := by
  simp [nativeScanTableAux, FiniteTM0Program.lookupAction_append,
    lookupAction_targetRules_blank, FiniteTM0.lookupAction,
    FiniteTM0.Rule.mk]

theorem lookup_nativeScanTableAux_target_at {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining i : Nat) (symbol : Symbol numTags)
    (hmatch : target.Matches symbol) (hi : i ≤ remaining) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch remaining state)
        (state + i) symbol =
      some (success, .write symbol) := by
  induction i generalizing remaining state with
  | zero =>
      simpa using lookup_nativeScanTableAux_target_current target direction
        success launch state remaining symbol hmatch
  | succ i ih =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          have hstate : state + (i + 1) ≠ state := by omega
          simp only [nativeScanTableAux,
            FiniteTM0Program.lookupAction_append,
            lookupAction_targetRules_state_ne target hstate symbol,
            FiniteTM0.lookupAction]
          have hkey :
              (state + (i + 1), symbol) ≠
                (state, (blankSymbol : Symbol numTags)) := by
            exact fun h => hstate (congrArg Prod.fst h)
          simp only [FiniteTM0.Rule.mk, if_neg hkey]
          have htail := ih (state := state + 1) (remaining := remaining)
            (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem lookup_nativeScanTableAux_blank_at {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining i : Nat) (hi : i < remaining) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch remaining state)
        (state + i) blankSymbol =
      some (state + i + 1,
        liftAction (MarkerMachine.moveAction direction)) := by
  induction i generalizing remaining state with
  | zero =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          simpa using lookup_nativeScanTableAux_blank_step
            target direction success launch state remaining
  | succ i ih =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          have hstate : state + (i + 1) ≠ state := by omega
          simp only [nativeScanTableAux,
            FiniteTM0Program.lookupAction_append,
            lookupAction_targetRules_state_ne target hstate
              (blankSymbol : Symbol numTags), FiniteTM0.lookupAction]
          have hkey :
              (state + (i + 1), (blankSymbol : Symbol numTags)) ≠
                (state, blankSymbol) := by
            exact fun h => hstate (congrArg Prod.fst h)
          simp only [FiniteTM0.Rule.mk, if_neg hkey]
          have htail := ih (state := state + 1) (remaining := remaining)
            (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem lookup_nativeScanTableAux_launch_at {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining : Nat) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch remaining state)
        (state + remaining) blankSymbol =
      some (launch, .write blankSymbol) := by
  induction remaining generalizing state with
  | zero =>
      simpa using lookup_nativeScanTableAux_blank_current
        target direction success launch state
  | succ remaining ih =>
      have hstate : state + (remaining + 1) ≠ state := by omega
      simp only [nativeScanTableAux,
        FiniteTM0Program.lookupAction_append,
        lookupAction_targetRules_state_ne target hstate
          (blankSymbol : Symbol numTags), FiniteTM0.lookupAction]
      have hkey :
          (state + (remaining + 1), (blankSymbol : Symbol numTags)) ≠
            (state, blankSymbol) := by
        exact fun h => hstate (congrArg Prod.fst h)
      simp only [FiniteTM0.Rule.mk, if_neg hkey]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (state + 1)

/-- One complete native local controller.  Only the scan depends on the
target; the finite unwind still uses the embedded blank alphabet. -/
def nativeLocalTable {numTags : Nat} (radius : Nat)
    (target : Target numTags) (direction : Turing.Dir) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  nativeScanTable radius target direction ++
    liftTable (NestingMachine.unwindTable radius direction)

/-! ## State layout and executable command tables -/

/-- Four private continuation states suffice for clearing, verifying,
optional departure, and near-tag resumption. -/
def continuationWidth : Nat := 4

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

/-- State entered after a near-tag return has been cleared. -/
def resumeState (radius offset : Nat) : FiniteTM0.State :=
  clearState radius offset + 3

/-- Directional return dispatchers after all private command blocks.  Hooper's
return mechanism remembers the direction from which the nested core returned,
so the two directions receive distinct states. -/
def returnState (base radius : Nat) {numTags : Nat}
    (commands : List (Command numTags)) (direction : Turing.Dir) :
    FiniteTM0.State :=
  commandOffset base radius commands.length +
    match direction with
    | .left => 0
    | .right => 1

theorem returnState_injective (base radius : Nat) {numTags : Nat}
    (commands : List (Command numTags)) :
    Function.Injective (returnState base radius commands) := by
  intro first second h
  cases first <;> cases second <;> simp [returnState] at h ⊢

/-- One shared entry for the eventual canonical nested computation. -/
def coreEntry (base radius : Nat) {numTags : Nat}
    (commands : List (Command numTags)) : FiniteTM0.State :=
  commandOffset base radius commands.length + 2

theorem returnState_lt_coreEntry (base radius : Nat) {numTags : Nat}
    (commands : List (Command numTags)) (direction : Turing.Dir) :
    returnState base radius commands direction <
      coreEntry base radius commands := by
  cases direction <;> simp [returnState, coreEntry]

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

private theorem launch_ne_found (radius offset : Nat) :
    launchState radius offset ≠ foundState radius offset := by
  intro h
  change offset + (radius + 1 + 2) =
    offset + (radius + 1 + 1) at h
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

private theorem resume_ne_launch (radius offset : Nat) :
    resumeState radius offset ≠ launchState radius offset := by
  intro h
  change offset + (2 * (radius + 1) + 3) + 3 =
    offset + (radius + 1 + 2) at h
  omega

private theorem resume_ne_found (radius offset : Nat) :
    resumeState radius offset ≠ foundState radius offset := by
  intro h
  change offset + (2 * (radius + 1) + 3) + 3 =
    offset + (radius + 1 + 1) at h
  omega

private theorem resume_ne_clear (radius offset : Nat) :
    resumeState radius offset ≠ clearState radius offset := by
  simp [resumeState]

private theorem resume_ne_verify (radius offset : Nat) :
    resumeState radius offset ≠ verifyState radius offset := by
  simp [resumeState, verifyState]

private theorem resume_ne_depart (radius offset : Nat) :
    resumeState radius offset ≠ departState radius offset := by
  simp [resumeState, departState]

/-- All nonblank symbols of the tagged marker alphabet. -/
def nonblankSymbols (numTags : Nat) : List (Symbol numTags) :=
  (List.finRange 5).map boundarySymbol ++
    (List.finRange numTags).map tagSymbol

/-- Collision exits preserve the observed nonblank symbol. -/
def collisionRules {numTags : Nat} (state collision : FiniteTM0.State) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  (nonblankSymbols numTags).map fun symbol =>
    FiniteTM0.Rule.mk state symbol collision (.write symbol)

/-- Explicit continuation and failed-launch rules for one command.  These
rules precede the lifted bounded controller in `commandTable`; their source
states are reserved holes in or immediately after that controller. -/
def continuationTable {numTags : Nat} (radius offset sharedCore : Nat)
    (command : Command numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  let launchRule := FiniteTM0.Rule.mk (launchState radius offset)
    blankSymbol sharedCore (.write (tagSymbol command.returnTag))
  let resumeRule := FiniteTM0.Rule.mk (resumeState radius offset)
    blankSymbol (entryState radius offset)
      (liftAction (MarkerMachine.moveAction command.searchDirection))
  match command with
  | .boundaryNavigation expected _ successState _ .preserve =>
      launchRule ::
        targetRules (foundState radius offset) successState
          (.boundary expected) ++ [resumeRule]
  | .boundaryNavigation expected _ successState _ (.erase none) =>
      [ launchRule
      , FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol expected) successState (.write blankSymbol)
      , resumeRule
      ]
  | .boundaryNavigation expected _ successState _
      (.erase (some departure)) =>
      [ launchRule
      , FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol expected) (departState radius offset)
          (.write blankSymbol)
      , FiniteTM0.Rule.mk (departState radius offset) blankSymbol
          successState (liftAction (MarkerMachine.moveAction departure))
      , resumeRule
      ]
  | .tagNavigation _ successState _ =>
      launchRule ::
        targetRules (foundState radius offset) successState .anyTag ++
          [resumeRule]
  | .markerShift move successState _ departure collisionState =>
      let verifyTarget := match departure with
        | none => successState
        | some _ => departState radius offset
      let collisions := match collisionState with
        | none => []
        | some collision =>
            collisionRules (verifyState radius offset) collision
      let departureRules := match departure with
        | none => []
        | some direction =>
            [FiniteTM0.Rule.mk (departState radius offset)
              (boundarySymbol move.expected) successState
              (liftAction (MarkerMachine.moveAction direction))]
      [ launchRule
      , FiniteTM0.Rule.mk (foundState radius offset)
          (boundarySymbol move.expected) (clearState radius offset)
          (.write blankSymbol)
      , FiniteTM0.Rule.mk (clearState radius offset) blankSymbol
          (verifyState radius offset)
          (liftAction (MarkerMachine.moveAction move.shiftDirection))
      , FiniteTM0.Rule.mk (verifyState radius offset) blankSymbol
          verifyTarget (.write (boundarySymbol move.expected))
      ] ++ collisions ++ departureRules ++ [resumeRule]

/-- Lift and relocate the finite bounded controller used by one descriptor. -/
def privateControllerTable {numTags : Nat} (radius offset : Nat)
    (command : Command numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  FiniteTM0Program.relocate offset
    (nativeLocalTable radius command.target command.searchDirection)

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

/-- Directional return rules.  A tag is accepted only at the return state
matching the direction in which its command searches.  Distinct command tags
still give distinct rule keys independently of their directions. -/
def returnTable {numTags : Nat} (radius : Nat)
    (sharedReturn : Turing.Dir → FiniteTM0.State) :
    Nat → List (Command numTags) →
      FiniteTM0.Table (AlphabetSize numTags)
  | _, [] => []
  | offset, command :: commands =>
      FiniteTM0.Rule.mk (sharedReturn command.searchDirection)
          (tagSymbol command.returnTag)
          (resumeState radius offset) (.write blankSymbol) ::
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

/-! ## Native tagged-tape scan semantics -/

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
private theorem tape_write_read {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) : T.write T.read = T := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.read, FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

theorem step_nativeScan_blank_at {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (i : Nat) (hi : i < NestingMachine.bound radius)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = blankSymbol) :
    FullTM0.step
        (FiniteTM0.machine (nativeScanTable radius target direction))
        ⟨i, T⟩ =
      some ⟨i + 1, T.move direction⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, nativeScanTable]
  rw [hread]
  have hlookup := lookup_nativeScanTableAux_blank_at target direction
    (NestingMachine.localSuccessState radius)
    (NestingMachine.localLaunchState radius) 0
    (NestingMachine.bound radius) i hi
  simp only [Nat.zero_add] at hlookup
  rw [hlookup]
  simp [liftAction_moveAction_toStmt]

theorem step_nativeScan_target_at {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (i : Nat) (hi : i ≤ NestingMachine.bound radius)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : target.Matches T.read) :
    FullTM0.step
        (FiniteTM0.machine (nativeScanTable radius target direction))
        ⟨i, T⟩ =
      some ⟨NestingMachine.localSuccessState radius, T⟩ := by
  let symbol := T.read
  simp only [FullTM0.step, FiniteTM0.machine, nativeScanTable]
  have hlookup := lookup_nativeScanTableAux_target_at target direction
    (NestingMachine.localSuccessState radius)
    (NestingMachine.localLaunchState radius) 0
    (NestingMachine.bound radius) i symbol hmatch hi
  simp only [Nat.zero_add] at hlookup
  rw [hlookup]
  simp only [Option.map_some, FiniteTM0.Action.toStmt_write]
  congr
  simpa [symbol, FullTM0.Tape.read] using tape_write_read T

theorem step_nativeScan_launch {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = blankSymbol) :
    FullTM0.step
        (FiniteTM0.machine (nativeScanTable radius target direction))
        ⟨NestingMachine.bound radius, T⟩ =
      some ⟨NestingMachine.localLaunchState radius, T⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, nativeScanTable]
  rw [hread]
  have hlookup := lookup_nativeScanTableAux_launch_at target direction
    (NestingMachine.localSuccessState radius)
    (NestingMachine.localLaunchState radius) 0
    (NestingMachine.bound radius)
  simp only [Nat.zero_add] at hlookup
  rw [hlookup]
  simp only [Option.map_some, FiniteTM0.Action.toStmt_write]
  congr
  rw [← hread]
  exact tape_write_read T

/-- Cross a guarded native blank prefix without changing any tape symbol. -/
theorem nativeScan_moves_reaches {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (progress distance : Nat)
    (hbound : progress + distance ≤ NestingMachine.bound radius)
    (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ i < distance,
      T (FullTM0.Tape.offset direction i) = blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine (nativeScanTable radius target direction))
      ⟨progress, T⟩
      ⟨progress + distance, T.moveN direction distance⟩ := by
  induction distance generalizing progress T with
  | zero =>
      simp only [Nat.add_zero, FullTM0.Tape.moveN_zero]
      exact Relation.ReflTransGen.refl
  | succ distance ih =>
      have hprogress : progress < NestingMachine.bound radius := by omega
      have hread : T.read = blankSymbol := by
        simpa [FullTM0.Tape.read] using hblank 0
          (Nat.zero_lt_succ distance)
      have hfirst := reaches_of_step
        (step_nativeScan_blank_at radius target direction progress
          hprogress T hread)
      have htailBlank : ∀ i < distance,
          (T.move direction) (FullTM0.Tape.offset direction i) =
            blankSymbol := by
        intro i hi
        simpa using hblank (i + 1) (Nat.succ_lt_succ hi)
      have hrest := ih (progress + 1) (by omega)
        (T.move direction) htailBlank
      have hall := hfirst.trans hrest
      simpa [FullTM0.Reaches, StateTransition.Reaches,
        FullTM0.Tape.move_moveN, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

/-- A selected target in the native tagged tape reaches the local found
state while preserving the entire tape outside head motion. -/
theorem nativeScan_reaches_found {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) target.Matches
      T direction distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches
      (FiniteTM0.machine (nativeScanTable radius target direction))
      ⟨0, T⟩
      ⟨NestingMachine.localSuccessState radius,
        T.moveN direction distance⟩ := by
  have hmoves := nativeScan_moves_reaches radius target direction 0 distance
    (by simpa using hnear) T (fun i hi => hgap.blank hi)
  have hmatch : target.Matches (T.moveN direction distance).read := by
    simpa [FullTM0.Tape.read] using hgap.marked
  have hfinish := reaches_of_step
    (step_nativeScan_target_at radius target direction distance hnear
      (T.moveN direction distance) hmatch)
  have hmoves' : FullTM0.Reaches
      (FiniteTM0.machine (nativeScanTable radius target direction))
      ⟨0, T⟩ ⟨distance, T.moveN direction distance⟩ := by
    simpa using hmoves
  exact hmoves'.trans hfinish

theorem nativeScan_reaches_launch {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) target.Matches
      T direction distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (nativeScanTable radius target direction))
      ⟨0, T⟩
      ⟨NestingMachine.localLaunchState radius,
        T.moveN direction (NestingMachine.bound radius)⟩ := by
  have hmoves := nativeScan_moves_reaches radius target direction 0
    (NestingMachine.bound radius) (by simp) T
    (fun i hi => hgap.blank (Nat.lt_trans hi hfar))
  have hread :
      (T.moveN direction (NestingMachine.bound radius)).read =
        blankSymbol := by
    simpa [FullTM0.Tape.read] using hgap.blank hfar
  have hfinish := reaches_of_step
    (step_nativeScan_launch radius target direction
      (T.moveN direction (NestingMachine.bound radius)) hread)
  have hmoves' : FullTM0.Reaches
      (FiniteTM0.machine (nativeScanTable radius target direction))
      ⟨0, T⟩
      ⟨NestingMachine.bound radius,
        T.moveN direction (NestingMachine.bound radius)⟩ := by
    simpa using hmoves
  exact hmoves'.trans hfinish

theorem private_reaches_found_native {numTags : Nat}
    (radius offset : Nat) (command : Command numTags)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) command.target.Matches
      T command.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches
      (FiniteTM0.machine (privateControllerTable radius offset command))
      ⟨entryState radius offset, T⟩
      ⟨foundState radius offset,
        T.moveN command.searchDirection distance⟩ := by
  have hscan := nativeScan_reaches_found radius command.target
    command.searchDirection T distance hgap hnear
  have hlocal := FiniteTM0Program.reaches_append_left
    (nativeScanTable radius command.target command.searchDirection)
    (liftTable (numTags := numTags)
      (NestingMachine.unwindTable radius command.searchDirection)) hscan
  have hrelocate := FiniteTM0Program.reaches_relocate offset
    (nativeLocalTable radius command.target command.searchDirection) hlocal
  simpa [privateControllerTable, nativeLocalTable,
    FiniteTM0Program.liftCfg, entryState, foundState] using hrelocate

theorem private_reaches_launch_native {numTags : Nat}
    (radius offset : Nat) (command : Command numTags)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) command.target.Matches
      T command.searchDirection distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (privateControllerTable radius offset command))
      ⟨entryState radius offset, T⟩
      ⟨launchState radius offset,
        T.moveN command.searchDirection (NestingMachine.bound radius)⟩ := by
  have hscan := nativeScan_reaches_launch radius command.target
    command.searchDirection T distance hgap hfar
  have hlocal := FiniteTM0Program.reaches_append_left
    (nativeScanTable radius command.target command.searchDirection)
    (liftTable (numTags := numTags)
      (NestingMachine.unwindTable radius command.searchDirection)) hscan
  have hrelocate := FiniteTM0Program.reaches_relocate offset
    (nativeLocalTable radius command.target command.searchDirection) hlocal
  simpa [privateControllerTable, nativeLocalTable,
    FiniteTM0Program.liftCfg, entryState, launchState] using hrelocate

/-! ## Source-state separation -/

theorem sourceStates_liftTable {numTags : Nat}
    (rules : FiniteTM0.Table MarkerMachine.AlphabetSize) :
    FiniteTM0.sourceStates (liftTable (numTags := numTags) rules) =
      FiniteTM0.sourceStates rules := by
  simp [FiniteTM0.sourceStates, liftTable, liftRule, FiniteTM0.Rule.mk,
    List.map_map, Function.comp_def]

theorem sourceStates_relocate {numSymbols : Nat} (offset : Nat)
    (rules : FiniteTM0.Table numSymbols) :
    FiniteTM0.sourceStates (FiniteTM0Program.relocate offset rules) =
      (FiniteTM0.sourceStates rules).map (offset + ·) := by
  simp [FiniteTM0.sourceStates, FiniteTM0Program.relocate,
    FiniteTM0Program.relocateRule, FiniteTM0.Rule.mk, List.map_map,
    Function.comp_def]

theorem source_mem_targetRules {numTags : Nat}
    {state success source : Nat} {target : Target numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (targetRules state success target)) :
    source = state := by
  cases target with
  | boundary label =>
      simpa [targetRules, FiniteTM0.sourceStates, FiniteTM0.Rule.mk]
        using hsource
  | anyTag =>
      simp only [targetRules, FiniteTM0.sourceStates, List.map_map,
        List.mem_map, FiniteTM0.Rule.mk, Function.comp_apply] at hsource
      rcases hsource with ⟨tag, -, h⟩
      exact h.symm

theorem source_mem_nativeScanTableAux {numTags : Nat}
    {target : Target numTags} {direction : Turing.Dir}
    {success launch state remaining source : Nat}
    (hsource : source ∈ FiniteTM0.sourceStates
      (nativeScanTableAux target direction success launch remaining state)) :
    state ≤ source ∧ source ≤ state + remaining := by
  induction remaining generalizing state with
  | zero =>
      simp only [nativeScanTableAux, FiniteTM0.sourceStates,
        List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil] at hsource
      rcases hsource with htarget | hblank
      · have h := source_mem_targetRules htarget
        subst source
        simp
      · rcases hblank with hblank | hfalse
        · subst source
          simp
        · contradiction
  | succ remaining ih =>
      simp only [nativeScanTableAux, FiniteTM0.sourceStates,
        List.map_append, List.mem_append, List.map_cons,
        List.mem_cons] at hsource
      rcases hsource with htarget | hblank | htail
      · have h := source_mem_targetRules htarget
        subst source
        simp
      · subst source
        simp
      · have h := ih htail
        omega

theorem source_mem_nativeLocalTable {numTags : Nat}
    {radius source : Nat} {target : Target numTags}
    {direction : Turing.Dir}
    (hsource : source ∈ FiniteTM0.sourceStates
      (nativeLocalTable radius target direction)) :
    source < NestingMachine.localWidth radius ∧
      (source ≤ NestingMachine.bound radius ∨
        NestingMachine.localUnwindState radius ≤ source) := by
  simp only [nativeLocalTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hsource
  rcases hsource with hscan | hunwind
  · have hb := source_mem_nativeScanTableAux
      (target := target) (direction := direction)
      (success := NestingMachine.localSuccessState radius)
      (launch := NestingMachine.localLaunchState radius)
      (state := 0) (remaining := NestingMachine.bound radius)
      hscan
    constructor
    · exact lt_of_le_of_lt hb.2 (by
        simp [NestingMachine.localWidth, NestingMachine.bound]
        omega)
    · left
      simpa using hb.2
  · have hunwind' : source ∈ FiniteTM0.sourceStates
        (NestingMachine.unwindTable radius direction) := by
      rw [← sourceStates_liftTable (numTags := numTags)]
      exact hunwind
    have hb := NestingMachine.source_mem_unwindTableAux
      (by simpa [NestingMachine.unwindTable] using hunwind')
    constructor
    · simp [NestingMachine.localWidth, NestingMachine.localUnwindState,
        NestingMachine.bound] at hb ⊢
      omega
    · exact Or.inr (by simpa [NestingMachine.unwindTable] using hb.1)

theorem source_mem_privateControllerTable {numTags : Nat}
    {radius offset source : Nat} {command : Command numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (privateControllerTable radius offset command)) :
    offset ≤ source ∧ source < clearState radius offset ∧
      source ≠ foundState radius offset ∧
      source ≠ launchState radius offset := by
  simp only [privateControllerTable, sourceStates_relocate,
    List.mem_map] at hsource
  rcases hsource with ⟨localState, hlocal, rfl⟩
  have hb := source_mem_nativeLocalTable hlocal
  refine ⟨Nat.le_add_right offset localState, ?_, ?_, ?_⟩
  · simpa [clearState] using Nat.add_lt_add_left hb.1 offset
  · intro heq
    have heq' : localState = NestingMachine.bound radius + 1 := by
      apply Nat.add_left_cancel (n := offset)
      simpa [foundState, NestingMachine.localSuccessState] using heq
    rcases hb.2 with hscan | hunwind
    · rw [heq'] at hscan
      omega
    · rw [heq'] at hunwind
      simp [NestingMachine.localUnwindState] at hunwind
  · intro heq
    have heq' : localState = NestingMachine.bound radius + 2 := by
      apply Nat.add_left_cancel (n := offset)
      simpa [launchState, NestingMachine.localLaunchState] using heq
    rcases hb.2 with hscan | hunwind
    · rw [heq'] at hscan
      omega
    · rw [heq'] at hunwind
      simp [NestingMachine.localUnwindState] at hunwind

theorem source_mem_continuationTable {numTags : Nat}
    {radius offset sharedCore source : Nat} {command : Command numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command)) :
    source = launchState radius offset ∨
      source = foundState radius offset ∨
      clearState radius offset ≤ source := by
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve =>
          simp only [continuationTable, FiniteTM0.sourceStates,
            List.map_cons, List.map_append, List.mem_cons,
            List.mem_append, List.map_nil, List.not_mem_nil,
            FiniteTM0.Rule.mk] at hsource
          rcases hsource with (rfl | htarget) | hresume
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (source_mem_targetRules htarget))
          · rcases hresume with hresume | hfalse
            · subst source
              exact Or.inr (Or.inr (by simp [resumeState]))
            · contradiction
      | erase departure =>
          cases departure <;>
            simp [continuationTable, FiniteTM0.sourceStates,
              FiniteTM0.Rule.mk, resumeState, departState] at hsource ⊢ <;>
            aesop
  | tagNavigation direction success returnTag =>
      simp only [continuationTable, FiniteTM0.sourceStates,
        List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, List.map_nil, List.not_mem_nil,
        FiniteTM0.Rule.mk] at hsource
      rcases hsource with (rfl | htarget) | hresume
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (source_mem_targetRules htarget))
      · rcases hresume with hresume | hfalse
        · subst source
          exact Or.inr (Or.inr (by simp [resumeState]))
        · contradiction
  | markerShift move success returnTag departure collisionState =>
      cases departure <;> cases collisionState <;>
        simp [continuationTable, collisionRules, nonblankSymbols,
          FiniteTM0.sourceStates, FiniteTM0.Rule.mk, clearState,
          verifyState, departState, resumeState] at hsource ⊢ <;>
        aesop

theorem source_mem_continuationTable_exact {numTags : Nat}
    {radius offset sharedCore source : Nat} {command : Command numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command)) :
    source = launchState radius offset ∨
      source = foundState radius offset ∨
      source = clearState radius offset ∨
      source = verifyState radius offset ∨
      source = departState radius offset ∨
      source = resumeState radius offset := by
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve =>
          simp only [continuationTable, FiniteTM0.sourceStates,
            List.map_cons, List.map_append, List.mem_cons,
            List.mem_append, List.map_nil, List.not_mem_nil,
            FiniteTM0.Rule.mk] at hsource
          rcases hsource with (hlaunch | htarget) | hresume
          · exact Or.inl hlaunch
          · exact Or.inr (Or.inl (source_mem_targetRules htarget))
          · rcases hresume with hresume | hfalse
            · exact Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr hresume))))
            · contradiction
      | erase departure =>
          cases departure <;>
            simp [continuationTable, FiniteTM0.sourceStates,
              FiniteTM0.Rule.mk] at hsource <;>
            aesop
  | tagNavigation direction success returnTag =>
      simp only [continuationTable, FiniteTM0.sourceStates,
        List.map_cons, List.map_append, List.mem_cons,
        List.mem_append, List.map_nil, List.not_mem_nil,
        FiniteTM0.Rule.mk] at hsource
      rcases hsource with (hlaunch | htarget) | hresume
      · exact Or.inl hlaunch
      · exact Or.inr (Or.inl (source_mem_targetRules htarget))
      · rcases hresume with hresume | hfalse
        · exact Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr hresume))))
        · contradiction
  | markerShift move success returnTag departure collisionState =>
      cases departure <;> cases collisionState <;>
        simp [continuationTable, collisionRules, nonblankSymbols,
          FiniteTM0.sourceStates, FiniteTM0.Rule.mk] at hsource <;>
        aesop

theorem private_continuation_source_disjoint {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    ∀ source,
      source ∈ FiniteTM0.sourceStates
        (privateControllerTable radius offset command) →
      source ∉ FiniteTM0.sourceStates
        (continuationTable radius offset sharedCore command) := by
  intro source hprivate hcontinuation
  have hp := source_mem_privateControllerTable hprivate
  rcases source_mem_continuationTable_exact hcontinuation with
    hlaunch | hfound | hclear | hverify | hdepart | hresume
  · exact hp.2.2.2 hlaunch
  · exact hp.2.2.1 hfound
  · exact (Nat.ne_of_lt hp.2.1) hclear
  · apply Nat.not_le_of_gt hp.2.1
    rw [hverify]
    simp [verifyState]
  · apply Nat.not_le_of_gt hp.2.1
    rw [hdepart]
    simp [departState]
  · apply Nat.not_le_of_gt hp.2.1
    rw [hresume]
    simp [resumeState]

/-- Native tagged-tape reachability through a complete selected command up to
its found-state handoff. -/
theorem command_reaches_found_native {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) command.target.Matches
      T command.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTable radius offset sharedCore command))
      ⟨entryState radius offset, T⟩
      ⟨foundState radius offset,
        T.moveN command.searchDirection distance⟩ := by
  exact FiniteTM0Path.reaches_append_right_of_source_separate
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command)
    (private_continuation_source_disjoint radius offset sharedCore command)
    (private_reaches_found_native radius offset command T distance hgap hnear)

/-! ## Linking command families -/

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

theorem CommandAt.command_mem {numTags radius base commandOffset}
    {command : Command numTags} {commands : List (Command numTags)}
    (h : CommandAt radius base commandOffset command commands) :
    command ∈ commands := by
  induction h with
  | head => simp
  | tail _ _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem source_mem_continuationTable_bounds {numTags : Nat}
    {radius offset sharedCore source : Nat} {command : Command numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command)) :
    offset ≤ source ∧ source < offset + blockWidth radius := by
  rcases source_mem_continuationTable_exact hsource with
    hlaunch | hfound | hclear | hverify | hdepart | hresume <;>
    subst source <;> constructor <;>
    simp [launchState, foundState, clearState, verifyState, departState,
      resumeState, blockWidth, continuationWidth,
      NestingMachine.localLaunchState,
      NestingMachine.localSuccessState,
      NestingMachine.localWidth, NestingMachine.bound] <;>
    omega

theorem source_mem_commandTable {numTags : Nat}
    {radius offset sharedCore source : Nat} {command : Command numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (commandTable radius offset sharedCore command)) :
    offset ≤ source ∧ source < offset + blockWidth radius := by
  simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hsource
  rcases hsource with hcontinuation | hprivate
  · exact source_mem_continuationTable_bounds hcontinuation
  · have hp := source_mem_privateControllerTable hprivate
    refine ⟨hp.1, Nat.lt_trans hp.2.1 ?_⟩
    simp [clearState, blockWidth, continuationWidth]

theorem source_mem_commandTables {numTags : Nat}
    {radius sharedCore offset source : Nat}
    {commands : List (Command numTags)}
    (hsource : source ∈ FiniteTM0.sourceStates
      (commandTables radius sharedCore offset commands)) :
    offset ≤ source ∧
      source < offset + commands.length * blockWidth radius := by
  induction commands generalizing offset with
  | nil => simp [commandTables, FiniteTM0.sourceStates] at hsource
  | cons first commands ih =>
      simp only [commandTables, FiniteTM0.sourceStates, List.map_append,
        List.mem_append] at hsource
      rcases hsource with hfirst | hrest
      · have hb := source_mem_commandTable hfirst
        constructor
        · exact hb.1
        · calc
            source < offset + blockWidth radius := hb.2
            _ ≤ offset + (commands.length + 1) * blockWidth radius := by
              simp [Nat.add_mul]
      · have hb := ih hrest
        constructor
        · exact Nat.le_trans (Nat.le_add_right _ _) hb.1
        · simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hb.2

theorem commandTables_reaches_of_at {numTags : Nat}
    {radius sharedCore base commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
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
      apply FiniteTM0Path.reaches_append_right_of_source_separate
        (commandTable radius offset sharedCore first)
        (commandTables radius sharedCore
          (offset + blockWidth radius) commands)
        ?_ (ih hreach)
      intro source hrest hfirst
      have hrestBounds := source_mem_commandTables hrest
      have hfirstBounds := source_mem_commandTable hfirst
      exact (Nat.not_le_of_gt hfirstBounds.2) hrestBounds.1

theorem table_reaches_of_commandAt {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
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

/-- Whole-machine native reachability to the selected command's found state.
Arbitrary tags and symbols outside the guarded blank prefix are untouched. -/
theorem machine_reaches_found_native {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) command.target.Matches
      T command.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨foundState radius commandOffset,
        T.moveN command.searchDirection distance⟩ := by
  exact table_reaches_of_commandAt core hat
    (command_reaches_found_native radius commandOffset
      (coreEntry base radius commands) command T distance hgap hnear)

/-! ## Found continuations, launch, and near-tag return -/

/-- Native tape at core entry after the failed-search tag is written. -/
def taggedFrameTapeNative {numTags : Nat} (radius : Nat)
    (command : Command numTags) (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  (T.moveN command.searchDirection
    (NestingMachine.bound radius)).write (tagSymbol command.returnTag)

/-- A navigation target is preserved while control enters its success state.
This is the critical `anyTag` cleanup behavior. -/
theorem continuation_reaches_navigation_native {numTags : Nat}
    (radius offset sharedCore : Nat) (target : Target numTags)
    (direction : Turing.Dir) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (T : FullTM0.Tape (Symbol numTags))
    (hmatch : target.Matches T.read) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore
          (Command.navigateTarget target direction successState returnTag)))
      ⟨foundState radius offset, T⟩ ⟨successState, T⟩ := by
  apply reaches_of_step
  have hlaunch : launchState radius offset ≠ foundState radius offset := by
    simp [launchState, foundState, NestingMachine.localLaunchState,
      NestingMachine.localSuccessState]
  have hresume : resumeState radius offset ≠ foundState radius offset := by
    intro h
    change offset + (2 * (radius + 1) + 3) + 3 =
      offset + (radius + 1 + 1) at h
    omega
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore
        (Command.navigateTarget target direction successState returnTag))
      (foundState radius offset) T.read =
        some (successState, .write T.read) := by
    cases target with
    | boundary expected =>
        have hkey :
            (foundState radius offset, T.read) ≠
              (launchState radius offset, blankSymbol) := by
          intro h
          exact hlaunch (congrArg Prod.fst h).symm
        change FiniteTM0.lookupAction
            (FiniteTM0.Rule.mk (launchState radius offset) blankSymbol
                sharedCore (.write (tagSymbol returnTag)) ::
              (targetRules (foundState radius offset) successState
                  (.boundary expected) ++
                [FiniteTM0.Rule.mk (resumeState radius offset) blankSymbol
                  (entryState radius offset)
                  (liftAction (MarkerMachine.moveAction direction))]))
            (foundState radius offset) T.read = _
        rw [FiniteTM0.lookupAction_cons_ne hkey]
        rw [FiniteTM0Program.lookupAction_append]
        rw [lookupAction_targetRules _ _ _ _ hmatch]
    | anyTag =>
        have hkey :
            (foundState radius offset, T.read) ≠
              (launchState radius offset, blankSymbol) := by
          intro h
          exact hlaunch (congrArg Prod.fst h).symm
        change FiniteTM0.lookupAction
            (FiniteTM0.Rule.mk (launchState radius offset) blankSymbol
                sharedCore (.write (tagSymbol returnTag)) ::
              (targetRules (foundState radius offset) successState .anyTag ++
                [FiniteTM0.Rule.mk (resumeState radius offset) blankSymbol
                  (entryState radius offset)
                  (liftAction (MarkerMachine.moveAction direction))]))
            (foundState radius offset) T.read = _
        rw [FiniteTM0.lookupAction_cons_ne hkey]
        rw [FiniteTM0Program.lookupAction_append]
        rw [lookupAction_targetRules _ _ _ _ hmatch]
  simp only [FullTM0.step, FiniteTM0.machine_apply, hlookup,
    Option.map_some, FiniteTM0.Action.toStmt_write]
  rw [tape_write_read]

/-- Failed native search writes its physical return tag at the current frame
boundary and enters the shared core. -/
theorem continuation_reaches_core_native {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape (Symbol numTags)) (hblank : T.read = blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨launchState radius offset, T⟩
      ⟨sharedCore, T.write (tagSymbol command.returnTag)⟩ := by
  apply reaches_of_step
  have hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore command)
      (launchState radius offset) blankSymbol =
        some (sharedCore, .write (tagSymbol command.returnTag)) := by
    cases command with
    | boundaryNavigation expected direction success returnTag action =>
        cases action with
        | preserve =>
            simp [continuationTable, FiniteTM0.lookupAction,
              FiniteTM0.Rule.mk]
        | erase departure =>
            cases departure <;>
              simp [continuationTable, FiniteTM0.lookupAction,
                FiniteTM0.Rule.mk]
    | tagNavigation direction success returnTag =>
        simp [continuationTable, FiniteTM0.lookupAction,
          FiniteTM0.Rule.mk]
    | markerShift move success returnTag departure collisionState =>
        cases departure <;> cases collisionState <;>
          simp [continuationTable, FiniteTM0.lookupAction,
            FiniteTM0.Rule.mk]
  simp only [FullTM0.step]
  rw [hblank]
  simp [FiniteTM0.machine_apply, hlookup]

theorem command_reaches_core_native {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) command.target.Matches
      T command.searchDirection distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (commandTable radius offset sharedCore command))
      ⟨entryState radius offset, T⟩
      ⟨sharedCore, taggedFrameTapeNative radius command T⟩ := by
  have hprivate := private_reaches_launch_native radius offset command T
    distance hgap hfar
  have hprivate' := FiniteTM0Path.reaches_append_right_of_source_separate
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command)
    (private_continuation_source_disjoint radius offset sharedCore command)
    hprivate
  have hblank :
      (T.moveN command.searchDirection
        (NestingMachine.bound radius)).read = blankSymbol := by
    simpa [FullTM0.Tape.read] using hgap.blank hfar
  have hcontinuation := continuation_reaches_core_native radius offset
    sharedCore command
    (T.moveN command.searchDirection (NestingMachine.bound radius)) hblank
  have hcontinuation' := FiniteTM0Program.reaches_append_left
    (continuationTable radius offset sharedCore command)
    (privateControllerTable radius offset command) hcontinuation
  exact hprivate'.trans hcontinuation'

theorem machine_reaches_core_native {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol) command.target.Matches
      T command.searchDirection distance)
    (hfar : NestingMachine.bound radius < distance) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨coreEntry base radius commands,
        taggedFrameTapeNative radius command T⟩ := by
  exact table_reaches_of_commandAt core hat
    (command_reaches_core_native radius commandOffset
      (coreEntry base radius commands) command T distance hgap hfar)

/-- A cleanup command reaches the shared return dispatcher while preserving
the actual physical tag it found. -/
theorem command_cleanup_reaches_return {numTags : Nat}
    (radius offset sharedCore sharedReturn : Nat)
    (direction : Turing.Dir) (returnTag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol)
      (Target.anyTag : Target numTags).Matches T direction distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (commandTable radius offset sharedCore
          (Command.cleanup direction sharedReturn returnTag)))
      ⟨entryState radius offset, T⟩
      ⟨sharedReturn, T.moveN direction distance⟩ := by
  have hfound := command_reaches_found_native radius offset sharedCore
    (Command.cleanup direction sharedReturn returnTag)
    T distance hgap hnear
  have hmatch : (Target.anyTag : Target numTags).Matches
      (T.moveN direction distance).read := by
    simpa [FullTM0.Tape.read] using hgap.marked
  have hcontinuation := continuation_reaches_navigation_native
    radius offset sharedCore (Target.anyTag : Target numTags) direction
    sharedReturn returnTag (T.moveN direction distance) hmatch
  have hcontinuation' := FiniteTM0Program.reaches_append_left
    (continuationTable radius offset sharedCore
      (Command.cleanup direction sharedReturn returnTag))
    (privateControllerTable radius offset
      (Command.cleanup direction sharedReturn returnTag))
    (by simpa only [Command.cleanup, Command.navigateTarget]
      using hcontinuation)
  exact hfound.trans hcontinuation'

theorem machine_cleanup_reaches_return {numTags : Nat}
    {base radius commandOffset : Nat} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (direction : Turing.Dir) (returnTag : Fin numTags)
    (hat : CommandAt radius base commandOffset
      (Command.cleanup direction
        (returnState base radius commands direction) returnTag)
      commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol)
      (Target.anyTag : Target numTags).Matches T direction distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨returnState base radius commands direction,
        T.moveN direction distance⟩ := by
  exact table_reaches_of_commandAt core hat
    (command_cleanup_reaches_return radius commandOffset
      (coreEntry base radius commands)
      (returnState base radius commands direction)
      direction returnTag T distance hgap hnear)

/-! ## Determinism and computable lookup -/

private theorem key_mem_sourceStates {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols}
    {key : FiniteTM0.Key numSymbols}
    (hkey : key ∈ rules.map Prod.fst) :
    key.1 ∈ FiniteTM0.sourceStates rules := by
  rcases List.mem_map.mp hkey with ⟨rule, hrule, heq⟩
  exact List.mem_map.mpr
    ⟨rule, hrule, congrArg Prod.fst heq⟩

private theorem key_mem_targetRules {numTags : Nat}
    {state success : FiniteTM0.State} {target : Target numTags}
    {key : FiniteTM0.Key (AlphabetSize numTags)}
    (hkey : key ∈ (targetRules state success target).map Prod.fst) :
    key.1 = state ∧ target.Matches key.2 := by
  cases target with
  | boundary label =>
      simp only [targetRules, List.map_cons, List.map_nil,
        List.mem_singleton, FiniteTM0.Rule.mk] at hkey
      subst key
      exact ⟨rfl, rfl⟩
  | anyTag =>
      simp only [targetRules, List.map_map, List.mem_map,
        FiniteTM0.Rule.mk, Function.comp_apply] at hkey
      rcases hkey with ⟨tag, -, rfl⟩
      exact ⟨rfl, ⟨tag, rfl⟩⟩

theorem nativeScanTableAux_deterministic {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining : Nat) :
    FiniteTM0.Deterministic
      (nativeScanTableAux target direction success launch remaining state) := by
  induction remaining generalizing state with
  | zero =>
      simp only [nativeScanTableAux, FiniteTM0.Deterministic,
        List.map_append, List.map_cons, List.map_nil]
      apply List.Nodup.append
        (targetRules_deterministic state success target) (by simp)
      rw [List.disjoint_iff_ne]
      intro targetKey htarget blankKey hblank heq
      simp only [List.mem_singleton] at hblank
      have hshape := key_mem_targetRules htarget
      have hsymbol : targetKey.2 = (blankSymbol : Symbol numTags) :=
        (congrArg Prod.snd heq).trans (congrArg Prod.snd hblank)
      exact target_not_blank target (hsymbol ▸ hshape.2)
  | succ remaining ih =>
      simp only [nativeScanTableAux, FiniteTM0.Deterministic,
        List.map_append, List.map_cons]
      have hblankNot :
          (state, (blankSymbol : Symbol numTags)) ∉
            (nativeScanTableAux target direction success launch remaining
              (state + 1)).map Prod.fst := by
        intro htail
        have hsource := key_mem_sourceStates htail
        have hbounds := source_mem_nativeScanTableAux hsource
        omega
      have hrest : List.Nodup
          ((state, (blankSymbol : Symbol numTags)) ::
            (nativeScanTableAux target direction success launch remaining
              (state + 1)).map Prod.fst) :=
        List.Nodup.cons hblankNot (ih (state + 1))
      apply List.Nodup.append
        (targetRules_deterministic state success target) hrest
      rw [List.disjoint_iff_ne]
      intro targetKey htarget restKey hrestKey heq
      have hshape := key_mem_targetRules htarget
      simp only [List.mem_cons] at hrestKey
      rcases hrestKey with hblank | htail
      · have hsymbol : targetKey.2 = (blankSymbol : Symbol numTags) :=
          (congrArg Prod.snd heq).trans (congrArg Prod.snd hblank)
        exact target_not_blank target (hsymbol ▸ hshape.2)
      · have hsource := key_mem_sourceStates htail
        have hbounds := source_mem_nativeScanTableAux hsource
        have hrestState : restKey.1 = state :=
          (congrArg Prod.fst heq).symm.trans hshape.1
        rw [hrestState] at hbounds
        omega

theorem nativeScanTable_deterministic {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir) :
    FiniteTM0.Deterministic (nativeScanTable radius target direction) := by
  exact nativeScanTableAux_deterministic target direction
    (NestingMachine.localSuccessState radius)
    (NestingMachine.localLaunchState radius) 0
    (NestingMachine.bound radius)

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

theorem nativeLocalTable_deterministic {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir) :
    FiniteTM0.Deterministic (nativeLocalTable radius target direction) := by
  simp only [nativeLocalTable, FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append
    (nativeScanTable_deterministic radius target direction)
    (liftTable_deterministic
      (unwindTableAux_deterministic direction 0
        (NestingMachine.localUnwindState radius) radius))
  rw [List.disjoint_iff_ne]
  intro scanKey hscan unwindKey hunwind heq
  subst unwindKey
  have hscanSource := key_mem_sourceStates hscan
  have hunwindSource := key_mem_sourceStates hunwind
  have hscanBound := source_mem_nativeScanTableAux
    (by simpa [nativeScanTable] using hscanSource)
  rw [sourceStates_liftTable] at hunwindSource
  have hunwindBound := NestingMachine.source_mem_unwindTableAux
    (by simpa [NestingMachine.unwindTable] using hunwindSource)
  simp only [NestingMachine.localUnwindState,
    NestingMachine.bound] at hunwindBound hscanBound
  omega

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

theorem privateControllerTable_deterministic {numTags : Nat}
    (radius offset : Nat) (command : Command numTags) :
    FiniteTM0.Deterministic
      (privateControllerTable radius offset command) := by
  exact relocate_deterministic
    (nativeLocalTable_deterministic radius command.target
      command.searchDirection) offset

theorem nonblankSymbols_nodup (numTags : Nat) :
    (nonblankSymbols numTags).Nodup := by
  simp only [nonblankSymbols]
  apply List.Nodup.append
  · apply (List.nodup_finRange 5).map
    intro first second heq
    exact (boundarySymbol_injective first second).mp heq
  · exact (List.nodup_finRange numTags).map tagSymbol_injective
  · rw [List.disjoint_iff_ne]
    intro boundary hboundary tag htag heq
    rcases List.mem_map.mp hboundary with ⟨label, -, rfl⟩
    rcases List.mem_map.mp htag with ⟨returnTag, -, rfl⟩
    exact boundarySymbol_ne_tagSymbol label returnTag heq

theorem blankSymbol_not_mem_nonblankSymbols {numTags : Nat} :
    (blankSymbol : Symbol numTags) ∉ nonblankSymbols numTags := by
  simp only [nonblankSymbols, List.mem_append, List.mem_map, not_or]
  constructor
  · rintro ⟨label, -, heq⟩
    exact blankSymbol_ne_boundarySymbol label heq.symm
  · rintro ⟨returnTag, -, heq⟩
    exact blankSymbol_ne_tagSymbol returnTag heq.symm

private theorem key_mem_collisionRules {numTags : Nat}
    {state collision : FiniteTM0.State}
    {key : FiniteTM0.Key (AlphabetSize numTags)}
    (hkey : key ∈ (collisionRules state collision).map Prod.fst) :
    key.1 = state ∧ key.2 ∈ nonblankSymbols numTags := by
  simp only [collisionRules, List.map_map, List.mem_map,
    FiniteTM0.Rule.mk, Function.comp_apply] at hkey
  rcases hkey with ⟨symbol, hsymbol, rfl⟩
  exact ⟨rfl, hsymbol⟩

private theorem source_mem_collisionRules {numTags : Nat}
    {state collision source : FiniteTM0.State}
    (hsource : source ∈ FiniteTM0.sourceStates
      (collisionRules (numTags := numTags) state collision)) :
    source = state := by
  simp only [collisionRules, FiniteTM0.sourceStates, List.map_map,
    List.mem_map, FiniteTM0.Rule.mk, Function.comp_apply] at hsource
  rcases hsource with ⟨symbol, -, heq⟩
  exact heq.symm

theorem collisionRules_deterministic {numTags : Nat}
    (state collision : FiniteTM0.State) :
    FiniteTM0.Deterministic
      (collisionRules (numTags := numTags) state collision) := by
  let collisionKey := fun symbol : Symbol numTags => (state, symbol)
  have hinjective : Function.Injective collisionKey := by
    intro first second heq
    exact congrArg Prod.snd heq
  have hmapped := (nonblankSymbols_nodup numTags).map hinjective
  simpa [FiniteTM0.Deterministic, collisionRules, FiniteTM0.Rule.mk,
    collisionKey, List.map_map, Function.comp_def] using hmapped

private theorem deterministic_append_of_source_disjoint {numSymbols : Nat}
    {first second : FiniteTM0.Table numSymbols}
    (hfirst : FiniteTM0.Deterministic first)
    (hsecond : FiniteTM0.Deterministic second)
    (hdisjoint : List.Disjoint (FiniteTM0.sourceStates first)
      (FiniteTM0.sourceStates second)) :
    FiniteTM0.Deterministic (first ++ second) := by
  simp only [FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append hfirst hsecond
  rw [List.disjoint_iff_ne]
  intro firstKey hfirstKey secondKey hsecondKey heq
  have hfirstSource := key_mem_sourceStates hfirstKey
  have hsecondSource := key_mem_sourceStates hsecondKey
  exact (List.disjoint_iff_ne.mp hdisjoint) firstKey.1 hfirstSource
    secondKey.1 hsecondSource (congrArg Prod.fst heq)

private theorem launch_target_resume_deterministic {numTags : Nat}
    (radius offset sharedCore success : Nat) (target : Target numTags)
    (returnTag : Fin numTags) (direction : Turing.Dir) :
    FiniteTM0.Deterministic
      (FiniteTM0.Rule.mk (launchState radius offset) blankSymbol sharedCore
          (.write (tagSymbol returnTag)) ::
        targetRules (foundState radius offset) success target ++
          [FiniteTM0.Rule.mk (resumeState radius offset) blankSymbol
            (entryState radius offset)
            (liftAction (MarkerMachine.moveAction direction))]) := by
  rw [FiniteTM0.Deterministic]
  simp only [List.map_cons, List.map_append, FiniteTM0.Rule.mk]
  apply List.Nodup.cons
  · intro hmem
    rcases List.mem_append.mp hmem with htarget | hresume
    · have hshape := key_mem_targetRules htarget
      simp [launchState, foundState, NestingMachine.localLaunchState,
        NestingMachine.localSuccessState] at hshape
    · have hresume' := List.mem_singleton.mp hresume
      have hstate := congrArg Prod.fst hresume'
      exact resume_ne_launch radius offset hstate.symm
  · apply List.Nodup.append
      (targetRules_deterministic (foundState radius offset) success target)
      (by simp)
    rw [List.disjoint_iff_ne]
    intro targetKey htarget resumeKey hresume heq
    have hresume' := List.mem_singleton.mp hresume
    have hshape := key_mem_targetRules htarget
    have hstate := congrArg Prod.fst heq
    rw [hresume'] at hstate
    exact resume_ne_found radius offset
      (hshape.1.symm.trans hstate).symm

private theorem verify_collision_deterministic {numTags : Nat}
    (radius offset verifyTarget collision : Nat)
    (expected : Fin 5) :
    FiniteTM0.Deterministic
      (FiniteTM0.Rule.mk (verifyState radius offset)
          (blankSymbol : Symbol numTags) verifyTarget
          (.write (boundarySymbol expected)) ::
        collisionRules (numTags := numTags)
          (verifyState radius offset) collision) := by
  simp only [FiniteTM0.Deterministic, List.map_cons]
  apply List.Nodup.cons
  · intro hcollision
    have hshape := key_mem_collisionRules hcollision
    exact blankSymbol_not_mem_nonblankSymbols hshape.2
  · exact collisionRules_deterministic _ _

private theorem markerShift_collision_deterministic {numTags : Nat}
    (radius offset sharedCore : Nat) (move : MarkerProgram.Move)
    (success : Nat) (returnTag : Fin numTags)
    (departure : Option Turing.Dir) (collision : Nat) :
    FiniteTM0.Deterministic
      (continuationTable radius offset sharedCore
        (.markerShift move success returnTag departure (some collision))) := by
  -- Partition the table by control-state family.  Determinism within each
  -- family is local; the rest of the proof establishes source disjointness.
  let prefixRules : FiniteTM0.Table (AlphabetSize numTags) :=
    [ FiniteTM0.Rule.mk (launchState radius offset) blankSymbol sharedCore
        (.write (tagSymbol returnTag))
    , FiniteTM0.Rule.mk (foundState radius offset)
        (boundarySymbol move.expected) (clearState radius offset)
        (.write blankSymbol)
    , FiniteTM0.Rule.mk (clearState radius offset) blankSymbol
        (verifyState radius offset)
        (liftAction (MarkerMachine.moveAction move.shiftDirection))
    ]
  let verifyTarget := match departure with
    | none => success
    | some _ => departState radius offset
  let verifyGroup : FiniteTM0.Table (AlphabetSize numTags) :=
    FiniteTM0.Rule.mk (verifyState radius offset) blankSymbol verifyTarget
        (.write (boundarySymbol move.expected)) ::
      collisionRules (verifyState radius offset) collision
  let resumeGroup : FiniteTM0.Table (AlphabetSize numTags) :=
    [FiniteTM0.Rule.mk (resumeState radius offset) blankSymbol
      (entryState radius offset)
      (liftAction (MarkerMachine.moveAction move.searchDirection))]
  have hprefix : FiniteTM0.Deterministic prefixRules := by
    simp [prefixRules, FiniteTM0.Deterministic, FiniteTM0.Rule.mk,
      launch_ne_found radius offset,
      (clear_ne_launch radius offset).symm,
      (clear_ne_found radius offset).symm]
  have hverify : FiniteTM0.Deterministic verifyGroup := by
    simpa [verifyGroup] using
      (verify_collision_deterministic (numTags := numTags) radius offset
        verifyTarget collision move.expected)
  -- Classify the possible sources of the fixed prefix and verification
  -- groups so state-separation lemmas can prove the append disjointness.
  have hprefixSource : ∀ source,
      source ∈ FiniteTM0.sourceStates prefixRules →
      source = launchState radius offset ∨
        source = foundState radius offset ∨
        source = clearState radius offset := by
    intro source hsource
    simp only [prefixRules, FiniteTM0.sourceStates, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil,
      FiniteTM0.Rule.mk] at hsource
    rcases hsource with hsource | hsource | hsource
    · exact Or.inl hsource
    · exact Or.inr (Or.inl hsource)
    · rcases hsource with hsource | hfalse
      · exact Or.inr (Or.inr hsource)
      · contradiction
  have hverifySource : ∀ source,
      source ∈ FiniteTM0.sourceStates verifyGroup →
      source = verifyState radius offset := by
    intro source hsource
    simp only [verifyGroup, FiniteTM0.sourceStates, List.map_cons,
      List.mem_cons] at hsource
    rcases hsource with hsource | hsource
    · simpa [FiniteTM0.Rule.mk] using hsource
    · exact source_mem_collisionRules hsource
  have hprefixVerifyDisjoint : List.Disjoint
      (FiniteTM0.sourceStates prefixRules)
      (FiniteTM0.sourceStates verifyGroup) := by
    rw [List.disjoint_iff_ne]
    intro first hfirst second hsecond heq
    have hfirstShape := hprefixSource first hfirst
    have hsecondEq := hverifySource second hsecond
    rw [hsecondEq] at heq
    rcases hfirstShape with hfirstEq | hfirstEq | hfirstEq
    · rw [hfirstEq] at heq
      exact verify_ne_launch radius offset heq.symm
    · rw [hfirstEq] at heq
      exact verify_ne_found radius offset heq.symm
    · rw [hfirstEq] at heq
      exact verify_ne_clear radius offset heq.symm
  have hprefixVerify : FiniteTM0.Deterministic
      (prefixRules ++ verifyGroup) :=
    deterministic_append_of_source_disjoint hprefix hverify
      hprefixVerifyDisjoint
  have hprefixVerifySource : ∀ source,
      source ∈ FiniteTM0.sourceStates (prefixRules ++ verifyGroup) →
      source = launchState radius offset ∨
        source = foundState radius offset ∨
        source = clearState radius offset ∨
        source = verifyState radius offset := by
    intro source hsource
    simp only [FiniteTM0.sourceStates, List.map_append,
      List.mem_append] at hsource
    rcases hsource with hsource | hsource
    · rcases hprefixSource source hsource with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (hverifySource source hsource)))
  have hresume : FiniteTM0.Deterministic resumeGroup := by
    simp [resumeGroup, FiniteTM0.Deterministic, FiniteTM0.Rule.mk]
  -- With no departure move, only the resume group remains to be appended.
  -- A departure adds one more singleton group before that same resume rule.
  cases departure with
  | none =>
      have hdisjoint : List.Disjoint
          (FiniteTM0.sourceStates (prefixRules ++ verifyGroup))
          (FiniteTM0.sourceStates resumeGroup) := by
        rw [List.disjoint_iff_ne]
        intro first hfirst second hsecond heq
        have hfirstShape := hprefixVerifySource first hfirst
        have hsecondEq : second = resumeState radius offset := by
          simpa [resumeGroup, FiniteTM0.sourceStates, FiniteTM0.Rule.mk]
            using hsecond
        rw [hsecondEq] at heq
        rcases hfirstShape with h | h | h | h
        · rw [h] at heq
          exact resume_ne_launch radius offset heq.symm
        · rw [h] at heq
          exact resume_ne_found radius offset heq.symm
        · rw [h] at heq
          exact resume_ne_clear radius offset heq.symm
        · rw [h] at heq
          exact resume_ne_verify radius offset heq.symm
      have hall := deterministic_append_of_source_disjoint
        hprefixVerify hresume hdisjoint
      simpa [continuationTable, prefixRules, verifyTarget, verifyGroup,
        resumeGroup, Command.returnTag, Command.searchDirection,
        List.append_assoc] using hall
  | some direction =>
      let departureGroup : FiniteTM0.Table (AlphabetSize numTags) :=
        [FiniteTM0.Rule.mk (departState radius offset)
          (boundarySymbol move.expected) success
          (liftAction (MarkerMachine.moveAction direction))]
      have hdeparture : FiniteTM0.Deterministic departureGroup := by
        simp [departureGroup, FiniteTM0.Deterministic, FiniteTM0.Rule.mk]
      have hdepartDisjoint : List.Disjoint
          (FiniteTM0.sourceStates (prefixRules ++ verifyGroup))
          (FiniteTM0.sourceStates departureGroup) := by
        rw [List.disjoint_iff_ne]
        intro first hfirst second hsecond heq
        have hfirstShape := hprefixVerifySource first hfirst
        have hsecondEq : second = departState radius offset := by
          simpa [departureGroup, FiniteTM0.sourceStates, FiniteTM0.Rule.mk]
            using hsecond
        rw [hsecondEq] at heq
        rcases hfirstShape with h | h | h | h
        · rw [h] at heq
          exact depart_ne_launch radius offset heq.symm
        · rw [h] at heq
          exact depart_ne_found radius offset heq.symm
        · rw [h] at heq
          exact depart_ne_clear radius offset heq.symm
        · rw [h] at heq
          exact depart_ne_verify radius offset heq.symm
      have hpvd : FiniteTM0.Deterministic
          ((prefixRules ++ verifyGroup) ++ departureGroup) :=
        deterministic_append_of_source_disjoint hprefixVerify hdeparture
          hdepartDisjoint
      have hresumeDisjoint : List.Disjoint
          (FiniteTM0.sourceStates
            ((prefixRules ++ verifyGroup) ++ departureGroup))
          (FiniteTM0.sourceStates resumeGroup) := by
        rw [List.disjoint_iff_ne]
        intro first hfirst second hsecond heq
        have hsecondEq : second = resumeState radius offset := by
          simpa [resumeGroup, FiniteTM0.sourceStates, FiniteTM0.Rule.mk]
            using hsecond
        rw [hsecondEq] at heq
        simp only [FiniteTM0.sourceStates, List.map_append,
          List.mem_append] at hfirst
        rcases hfirst with hfirst | hfirst
        · have hfirst' : first ∈ FiniteTM0.sourceStates
              (prefixRules ++ verifyGroup) := by
            simpa [FiniteTM0.sourceStates, List.map_append] using hfirst
          rcases hprefixVerifySource first hfirst' with h | h | h | h
          · rw [h] at heq
            exact resume_ne_launch radius offset heq.symm
          · rw [h] at heq
            exact resume_ne_found radius offset heq.symm
          · rw [h] at heq
            exact resume_ne_clear radius offset heq.symm
          · rw [h] at heq
            exact resume_ne_verify radius offset heq.symm
        · have hfirstEq : first = departState radius offset := by
            simpa [departureGroup, FiniteTM0.sourceStates,
              FiniteTM0.Rule.mk] using hfirst
          rw [hfirstEq] at heq
          exact resume_ne_depart radius offset heq.symm
      have hall := deterministic_append_of_source_disjoint
        hpvd hresume hresumeDisjoint
      simpa [continuationTable, prefixRules, verifyTarget, verifyGroup,
        departureGroup, resumeGroup, Command.returnTag,
        Command.searchDirection, List.append_assoc] using hall

theorem continuationTable_deterministic {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    FiniteTM0.Deterministic
      (continuationTable radius offset sharedCore command) := by
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve =>
          simpa [continuationTable, Command.returnTag,
            Command.searchDirection] using
            (launch_target_resume_deterministic radius offset sharedCore
              success (.boundary expected) returnTag direction)
      | erase departure =>
          cases departure with
          | none =>
              simp [continuationTable, FiniteTM0.Deterministic,
                FiniteTM0.Rule.mk, launch_ne_found radius offset,
                (resume_ne_launch radius offset).symm,
                (resume_ne_found radius offset).symm]
          | some departure =>
              simp [continuationTable, FiniteTM0.Deterministic,
                FiniteTM0.Rule.mk, launch_ne_found radius offset,
                (depart_ne_launch radius offset).symm,
                (depart_ne_found radius offset).symm,
                (resume_ne_launch radius offset).symm,
                (resume_ne_found radius offset).symm,
                (resume_ne_depart radius offset).symm]
  | tagNavigation direction success returnTag =>
      simpa [continuationTable, Command.returnTag,
        Command.searchDirection] using
        (launch_target_resume_deterministic radius offset sharedCore
          success (.anyTag : Target numTags) returnTag direction)
  | markerShift move success returnTag departure collisionState =>
      cases collisionState with
      | some collision =>
          exact markerShift_collision_deterministic radius offset sharedCore
            move success returnTag departure collision
      | none =>
          cases departure with
          | none =>
              simp [continuationTable, FiniteTM0.Deterministic,
                FiniteTM0.Rule.mk, launch_ne_found radius offset,
                (clear_ne_launch radius offset).symm,
                (verify_ne_launch radius offset).symm,
                (resume_ne_launch radius offset).symm,
                (clear_ne_found radius offset).symm,
                (verify_ne_found radius offset).symm,
                (resume_ne_found radius offset).symm,
                (verify_ne_clear radius offset).symm,
                (resume_ne_clear radius offset).symm,
                (resume_ne_verify radius offset).symm]
          | some departure =>
              simp [continuationTable, FiniteTM0.Deterministic,
                FiniteTM0.Rule.mk, launch_ne_found radius offset,
                (clear_ne_launch radius offset).symm,
                (verify_ne_launch radius offset).symm,
                (depart_ne_launch radius offset).symm,
                (resume_ne_launch radius offset).symm,
                (clear_ne_found radius offset).symm,
                (verify_ne_found radius offset).symm,
                (depart_ne_found radius offset).symm,
                (resume_ne_found radius offset).symm,
                (verify_ne_clear radius offset).symm,
                (depart_ne_clear radius offset).symm,
                (resume_ne_clear radius offset).symm,
                (depart_ne_verify radius offset).symm,
                (resume_ne_verify radius offset).symm,
                (resume_ne_depart radius offset).symm]

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
  have hcontinuationSource := key_mem_sourceStates hcontinuation
  have hprivateSource := key_mem_sourceStates hprivate
  apply private_continuation_source_disjoint radius offset sharedCore command
    privateKey.1 hprivateSource
  rw [← congrArg Prod.fst heq]
  exact hcontinuationSource

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
      apply Nat.ne_of_lt (lt_of_lt_of_le hfirstBounds.2 hrestBounds.1)
      exact congrArg Prod.fst heq

theorem returnTable_keys {numTags : Nat}
    (radius : Nat) (sharedReturn : Turing.Dir → FiniteTM0.State)
    (offset : Nat) (commands : List (Command numTags)) :
    (returnTable radius sharedReturn offset commands).map Prod.fst =
      commands.map fun command =>
        (sharedReturn command.searchDirection,
          tagSymbol command.returnTag) := by
  induction commands generalizing offset with
  | nil => rfl
  | cons command commands ih =>
      simp [returnTable, FiniteTM0.Rule.mk, ih]

theorem returnTable_deterministic {numTags : Nat}
    (radius : Nat) (sharedReturn : Turing.Dir → FiniteTM0.State)
    (offset : Nat) (commands : List (Command numTags))
    (htags : (commands.map (fun command => command.returnTag)).Nodup) :
    FiniteTM0.Deterministic
      (returnTable radius sharedReturn offset commands) := by
  let returnKey := fun command : Command numTags =>
    (sharedReturn command.searchDirection, tagSymbol command.returnTag)
  have hcommands : commands.Nodup := htags.of_map _
  have htagInjective :=
    (List.nodup_map_iff_inj_on hcommands).mp htags
  have hmapped : (commands.map returnKey).Nodup := hcommands.map_on (by
    intro first hfirst second hsecond heq
    have htag : first.returnTag = second.returnTag := by
      apply tagSymbol_injective
      exact congrArg Prod.snd heq
    exact htagInjective first hfirst second hsecond htag)
  rw [FiniteTM0.Deterministic,
    returnTable_keys radius sharedReturn offset commands]
  exact hmapped

theorem source_mem_returnTable {numTags : Nat}
    {radius offset source : Nat}
    {sharedReturn : Turing.Dir → FiniteTM0.State}
    {commands : List (Command numTags)}
    (hsource : source ∈ FiniteTM0.sourceStates
      (returnTable radius sharedReturn offset commands)) :
    ∃ direction, source = sharedReturn direction := by
  induction commands generalizing offset with
  | nil => simp [returnTable, FiniteTM0.sourceStates] at hsource
  | cons command commands ih =>
      simp only [returnTable, FiniteTM0.sourceStates, List.map_cons,
        List.mem_cons] at hsource
      rcases hsource with hfirst | hrest
      · exact ⟨command.searchDirection, hfirst⟩
      · exact ih hrest

theorem source_mem_controllerTable {numTags : Nat}
    {base radius source : Nat} {commands : List (Command numTags)}
    (hsource : source ∈ FiniteTM0.sourceStates
      (controllerTable base radius commands)) :
    source < coreEntry base radius commands := by
  simp only [controllerTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hsource
  rcases hsource with hcommands | hreturn
  · have hbounds := source_mem_commandTables hcommands
    change source < base + commands.length * blockWidth radius + 2
    exact lt_trans hbounds.2 (by omega)
  · rcases source_mem_returnTable hreturn with ⟨direction, rfl⟩
    exact returnState_lt_coreEntry base radius commands direction

theorem controllerTable_deterministic {numTags : Nat}
    (base radius : Nat) (commands : List (Command numTags))
    (htags : (commands.map (fun command => command.returnTag)).Nodup) :
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
  rcases source_mem_returnTable hreturnSource with ⟨direction, hreturnEq⟩
  have hcommandUpper : commandKey.1 <
      commandOffset base radius commands.length := by
    exact hcommandBounds.2
  have hreturnLower : commandOffset base radius commands.length ≤
      returnState base radius commands direction := by
    cases direction <;> simp [returnState]
  apply Nat.ne_of_lt (lt_of_lt_of_le hcommandUpper hreturnLower)
  rw [congrArg Prod.fst heq, hreturnEq]

theorem table_deterministic {numTags : Nat}
    (base radius : Nat) (commands : List (Command numTags))
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (htags : (commands.map (fun command => command.returnTag)).Nodup)
    (hcore : FiniteTM0.Deterministic core)
    (hfresh : ∀ source ∈ FiniteTM0.sourceStates core,
      coreEntry base radius commands ≤ source) :
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

private theorem resumeRule_mem_continuationTable {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    FiniteTM0.Rule.mk (resumeState radius offset) blankSymbol
        (entryState radius offset)
        (liftAction (MarkerMachine.moveAction command.searchDirection)) ∈
      continuationTable radius offset sharedCore command := by
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve =>
          simp [continuationTable, Command.searchDirection]
      | erase departure =>
          cases departure <;>
            simp [continuationTable, Command.searchDirection]
  | tagNavigation direction success returnTag =>
      simp [continuationTable, Command.searchDirection]
  | markerShift move success returnTag departure collisionState =>
      cases departure <;> cases collisionState <;>
        simp [continuationTable, Command.searchDirection]

/-- Clearing a nearby return tag enters `resumeState`; this rule makes the
outer bounded search advance exactly one cell before restarting. -/
theorem continuation_resume_reaches {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (T : FullTM0.Tape (Symbol numTags)) (hblank : T.read = blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (continuationTable radius offset sharedCore command))
      ⟨resumeState radius offset, T⟩
      ⟨entryState radius offset, T.move command.searchDirection⟩ := by
  have hlookup :
      FiniteTM0.lookupAction
          (continuationTable radius offset sharedCore command)
          (resumeState radius offset) blankSymbol =
        some (entryState radius offset,
          liftAction (MarkerMachine.moveAction command.searchDirection)) :=
    (FiniteTM0.lookupAction_eq_some_iff_of_deterministic
      (continuationTable_deterministic radius offset sharedCore command)).2
      (resumeRule_mem_continuationTable radius offset sharedCore command)
  apply reaches_of_step
  simp only [FullTM0.step]
  rw [hblank]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    liftAction_moveAction_toStmt]

/-- The exact resume transition remains available in the complete machine,
including every other command block, the shared dispatcher, and the core. -/
theorem machine_resume_reaches {numTags : Nat}
    {base radius commandOffset : Nat}
    {command : Command numTags} {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (hat : CommandAt radius base commandOffset command commands)
    (T : FullTM0.Tape (Symbol numTags)) (hblank : T.read = blankSymbol) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨resumeState radius commandOffset, T⟩
      ⟨entryState radius commandOffset,
        T.move command.searchDirection⟩ := by
  apply table_reaches_of_commandAt core hat
  exact FiniteTM0Program.reaches_append_left
    (continuationTable radius commandOffset
      (coreEntry base radius commands) command)
    (privateControllerTable radius commandOffset command)
    (continuation_resume_reaches radius commandOffset
      (coreEntry base radius commands) command T hblank)

/-- A distinct physical return tag selects exactly the corresponding
command-local resume state and is cleared back to blank. -/
theorem lookupAction_returnTable_of_at {numTags : Nat}
    {radius base commandOffset : Nat}
    {sharedReturn : Turing.Dir → FiniteTM0.State}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (htags : (commands.map (fun command => command.returnTag)).Nodup) :
    FiniteTM0.lookupAction (returnTable radius sharedReturn base commands)
        (sharedReturn command.searchDirection)
        (tagSymbol command.returnTag) =
      some (resumeState radius commandOffset, .write blankSymbol) := by
  induction hat with
  | head offset command commands =>
      simp [returnTable, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]
  | tail offset commandOffset first command commands hat ih =>
      simp only [List.map_cons, List.nodup_cons] at htags
      have htagMem : command.returnTag ∈
          commands.map (fun command => command.returnTag) :=
        List.mem_map.mpr ⟨command, hat.command_mem, rfl⟩
      have htagNe : command.returnTag ≠ first.returnTag := by
        intro heq
        apply htags.1
        rw [← heq]
        exact htagMem
      have hkeyNe :
          (sharedReturn command.searchDirection,
              tagSymbol command.returnTag) ≠
            (sharedReturn first.searchDirection,
              tagSymbol first.returnTag) := by
        intro heq
        apply htagNe
        apply tagSymbol_injective
        exact congrArg Prod.snd heq
      change FiniteTM0.lookupAction
          (FiniteTM0.Rule.mk (sharedReturn first.searchDirection)
              (tagSymbol first.returnTag)
              (resumeState radius offset) (.write blankSymbol) ::
            returnTable radius sharedReturn
              (offset + blockWidth radius) commands)
          (sharedReturn command.searchDirection)
          (tagSymbol command.returnTag) = _
      rw [FiniteTM0.lookupAction_cons_ne hkeyNe]
      exact ih htags.2

theorem lookupAction_returnTable_of_tag_not_mem {numTags : Nat}
    {radius offset state : Nat}
    {sharedReturn : Turing.Dir → FiniteTM0.State}
    {commands : List (Command numTags)} {returnTag : Fin numTags}
    (htag : returnTag ∉ commands.map (fun command => command.returnTag)) :
    FiniteTM0.lookupAction (returnTable radius sharedReturn offset commands)
        state (tagSymbol returnTag) = none := by
  induction commands generalizing offset with
  | nil => simp [returnTable, FiniteTM0.lookupAction]
  | cons command commands ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at htag
      have hkeyNe :
          (state, tagSymbol returnTag) ≠
            (sharedReturn command.searchDirection,
              tagSymbol command.returnTag) := by
        intro heq
        apply htag.1
        apply tagSymbol_injective
        exact congrArg Prod.snd heq
      change FiniteTM0.lookupAction
          (FiniteTM0.Rule.mk (sharedReturn command.searchDirection)
              (tagSymbol command.returnTag)
              (resumeState radius offset) (.write blankSymbol) ::
            returnTable radius sharedReturn
              (offset + blockWidth radius) commands)
          state (tagSymbol returnTag) = none
      rw [FiniteTM0.lookupAction_cons_ne hkeyNe]
      exact ih htag.2

/-- The same tag at the return state for the opposite direction has no
dispatcher rule.  Thus a nested core that returns from the wrong side halts
instead of silently resuming the command. -/
theorem lookupAction_returnTable_wrong_direction_of_at {numTags : Nat}
    {radius base commandOffset : Nat}
    {sharedReturn : Turing.Dir → FiniteTM0.State}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (htags : (commands.map (fun command => command.returnTag)).Nodup)
    (hreturn : Function.Injective sharedReturn) :
    FiniteTM0.lookupAction (returnTable radius sharedReturn base commands)
        (sharedReturn (NestingMachine.opposite command.searchDirection))
        (tagSymbol command.returnTag) = none := by
  induction hat with
  | head offset command commands =>
      simp only [List.map_cons, List.nodup_cons] at htags
      have hopposite : NestingMachine.opposite command.searchDirection ≠
          command.searchDirection := by
        cases command.searchDirection <;> simp [NestingMachine.opposite]
      have hkeyNe :
          (sharedReturn (NestingMachine.opposite command.searchDirection),
              tagSymbol command.returnTag) ≠
            (sharedReturn command.searchDirection,
              tagSymbol command.returnTag) := by
        intro heq
        apply hopposite
        apply hreturn
        exact congrArg Prod.fst heq
      change FiniteTM0.lookupAction
          (FiniteTM0.Rule.mk (sharedReturn command.searchDirection)
              (tagSymbol command.returnTag)
              (resumeState radius offset) (.write blankSymbol) ::
            returnTable radius sharedReturn
              (offset + blockWidth radius) commands)
          (sharedReturn (NestingMachine.opposite command.searchDirection))
          (tagSymbol command.returnTag) = none
      rw [FiniteTM0.lookupAction_cons_ne hkeyNe]
      exact lookupAction_returnTable_of_tag_not_mem htags.1
  | tail offset commandOffset first command commands hat ih =>
      simp only [List.map_cons, List.nodup_cons] at htags
      have htagMem : command.returnTag ∈
          commands.map (fun command => command.returnTag) :=
        List.mem_map.mpr ⟨command, hat.command_mem, rfl⟩
      have htagNe : command.returnTag ≠ first.returnTag := by
        intro heq
        apply htags.1
        rw [← heq]
        exact htagMem
      have hkeyNe :
          (sharedReturn (NestingMachine.opposite command.searchDirection),
              tagSymbol command.returnTag) ≠
            (sharedReturn first.searchDirection,
              tagSymbol first.returnTag) := by
        intro heq
        apply htagNe
        apply tagSymbol_injective
        exact congrArg Prod.snd heq
      change FiniteTM0.lookupAction
          (FiniteTM0.Rule.mk (sharedReturn first.searchDirection)
              (tagSymbol first.returnTag)
              (resumeState radius offset) (.write blankSymbol) ::
            returnTable radius sharedReturn
              (offset + blockWidth radius) commands)
          (sharedReturn (NestingMachine.opposite command.searchDirection))
          (tagSymbol command.returnTag) = none
      rw [FiniteTM0.lookupAction_cons_ne hkeyNe]
      exact ih htags.2

theorem returnTable_reaches_resume {numTags : Nat}
    {radius base commandOffset : Nat}
    {sharedReturn : Turing.Dir → FiniteTM0.State}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (htags : (commands.map (fun command => command.returnTag)).Nodup)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = tagSymbol command.returnTag) :
    FullTM0.Reaches
      (FiniteTM0.machine (returnTable radius sharedReturn base commands))
      ⟨sharedReturn command.searchDirection, T⟩
      ⟨resumeState radius commandOffset, T.write blankSymbol⟩ := by
  have hlookup := lookupAction_returnTable_of_at
    (sharedReturn := sharedReturn) hat htags
  apply reaches_of_step
  simp only [FullTM0.step]
  rw [hread]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    FiniteTM0.Action.toStmt_write]

/-- Lookup in every fully generated tagged table is computable.  Together
with the explicit finite-list construction, this is the executable finiteness
interface needed by later compiler layers. -/
theorem table_lookup_computable {numTags : Nat}
    (base radius : Nat) (commands : List (Command numTags))
    (core : FiniteTM0.Table (AlphabetSize numTags)) :
    Computable fun input : FiniteTM0.Key (AlphabetSize numTags) =>
      FiniteTM0.lookupAction (table base radius commands core)
        input.1 input.2 :=
  (FiniteTM0.lookupAction_computable
    (numSymbols := AlphabetSize numTags)).comp
    ((Computable.const (table base radius commands core)).pair Computable.id)

end BoundedMarkerProgram
end Hooper
end Kari
end LeanWang
