/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTiles
import LeanWang.UniversalTM0TableauSemantics

/-!
# A fixed one-sided machine for the universal TM0 evaluator

The two-sided TM0 tape is folded at the origin: one one-sided cell stores
source positions `-(i + 1)` and `i`.  The active half and the TM0 label live in
finite control.  A source move takes one target step.  A source write takes two
target steps: write while moving left, then return to the original cell.  The
origin bit stored in the first target cell handles the one-sided boundary.

This lets the reduction reuse `MachineInputTiles` instead of maintaining a
second, bespoke Wang-tableau correctness proof.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Machine

open UniversalTM0Semantic

abbrev Symbol := UniversalTM0Tableau.Symbol
abbrev Label := UniversalTM0Tableau.Label
abbrev Side := UniversalTM0Tableau.Side

local instance : DecidableEq Symbol := Classical.decEq Symbol
local instance : DecidableEq Label := Classical.decEq Label

/-- A reachable label of the one fixed Mathlib TM0 machine. -/
abbrev SupportedLabel := {q : Label // q ∈ tm0Support}

local instance : Inhabited SupportedLabel :=
  ⟨⟨default, tm0_supports.1⟩⟩

/-- One cell of the folded source tape. -/
structure TapeSymbol where
  atOrigin : Bool
  left : Symbol
  right : Symbol
deriving DecidableEq

namespace TapeSymbol

def blank : TapeSymbol := ⟨false, default, default⟩

def active : TapeSymbol → Side → Symbol
  | cell, .left => cell.left
  | cell, .right => cell.right

def write (cell : TapeSymbol) (side : Side) (symbol : Symbol) : TapeSymbol :=
  match side with
  | .left => { cell with left := symbol }
  | .right => { cell with right := symbol }

end TapeSymbol

def tapeSymbols : List TapeSymbol := do
  let atOrigin ← [false, true]
  let left ← UniversalTM0Tableau.symbols
  let right ← UniversalTM0Tableau.symbols
  pure ⟨atOrigin, left, right⟩

theorem mem_tapeSymbols (symbol : TapeSymbol) : symbol ∈ tapeSymbols := by
  rcases symbol with ⟨atOrigin, left, right⟩
  simp [tapeSymbols, UniversalTM0Tableau.mem_symbols]

local instance : Encodable TapeSymbol :=
  Encodable.encodableOfList tapeSymbols mem_tapeSymbols

/-- Finite control for the folded simulation. -/
inductive State where
  | run (side : Side) (label : SupportedLabel)
  | returnBoundary (side : Side) (label : SupportedLabel)
  | returnRight (side : Side) (label : SupportedLabel)
  | halt
deriving DecidableEq

local instance : Inhabited State :=
  ⟨.run .right ⟨default, tm0_supports.1⟩⟩

def supportedLabels : List SupportedLabel := tm0Support.attach.toList

theorem mem_supportedLabels (q : SupportedLabel) : q ∈ supportedLabels := by
  simp [supportedLabels]

def stateValues : List State :=
  [.halt] ++ UniversalTM0Tableau.sides.flatMap fun side =>
    supportedLabels.flatMap fun q =>
      [.run side q, .returnBoundary side q, .returnRight side q]

theorem mem_stateValues (state : State) : state ∈ stateValues := by
  cases state with
  | halt => simp [stateValues]
  | run side q | returnBoundary side q | returnRight side q =>
      simp [stateValues, UniversalTM0Tableau.mem_sides, mem_supportedLabels]

local instance : Encodable State :=
  Encodable.encodableOfList stateValues mem_stateValues

def symbolCode (symbol : TapeSymbol) : Nat := Encodable.encode symbol

def stateCode (state : State) : Nat := Encodable.encode state

def decodeSymbol (code : Nat) : TapeSymbol :=
  (Encodable.decode code : Option TapeSymbol).getD TapeSymbol.blank

def decodeState (code : Nat) : State :=
  (Encodable.decode code : Option State).getD default

@[simp] theorem decodeSymbol_symbolCode (symbol : TapeSymbol) :
    decodeSymbol (symbolCode symbol) = symbol := by
  simp [decodeSymbol, symbolCode]

@[simp] theorem decodeState_stateCode (state : State) :
    decodeState (stateCode state) = state := by
  simp [decodeState, stateCode]

def supportedLabel (q : Label) : SupportedLabel :=
  if hq : q ∈ tm0Support then ⟨q, hq⟩ else default

theorem supportedLabel_val_of_mem {q : Label} (hq : q ∈ tm0Support) :
    (supportedLabel q).1 = q := by
  simp [supportedLabel, hq]

def physicalMove (side : Side) (atOrigin : Bool) (dir : Turing.Dir) : Move :=
  if atOrigin && side.isInward dir then .left
  else if side.isOutward dir then .right else .left

/-- One step of the finite-control folded simulator. -/
def typedStep : State → TapeSymbol → TapeSymbol × State × Move
  | .halt, cell => (cell, .halt, .left)
  | .returnBoundary side q, cell => (cell, .run side q, .left)
  | .returnRight side q, cell => (cell, .run side q, .right)
  | .run side q, cell =>
      match tm0 q.1 (cell.active side) with
      | none => (cell, .halt, .left)
      | some (q', .write symbol) =>
          let next := supportedLabel q'
          if cell.atOrigin then
            (cell.write side symbol, .returnBoundary side next, .left)
          else
            (cell.write side symbol, .returnRight side next, .left)
      | some (q', .move dir) =>
          let next := supportedLabel q'
          (cell, .run (UniversalTM0Tableau.nextSide side cell.atOrigin dir) next,
            physicalMove side cell.atOrigin dir)

def symbols : List Nat := tapeSymbols.map symbolCode

def states : List Nat := stateValues.map stateCode

def step (state symbol : Nat) : Nat × Nat × Move :=
  let next := typedStep (decodeState state) (decodeSymbol symbol)
  (symbolCode next.1, stateCode next.2.1, next.2.2)

/-- The fixed one-sided machine used by the generic Wang history construction. -/
def machine : Machine where
  symbols := symbols
  states := states
  blank := symbolCode TapeSymbol.blank
  start := stateCode (.run .right ⟨default, tm0_supports.1⟩)
  halt := stateCode .halt
  step := step
  blank_mem := List.mem_map.2 ⟨TapeSymbol.blank,
    mem_tapeSymbols TapeSymbol.blank, rfl⟩
  start_mem := List.mem_map.2 ⟨.run .right ⟨default, tm0_supports.1⟩,
    mem_stateValues _, rfl⟩
  halt_mem := List.mem_map.2 ⟨.halt, mem_stateValues .halt, rfl⟩
  step_symbol_mem := by
    intro q a hq ha
    exact List.mem_map.2 ⟨(typedStep (decodeState q) (decodeSymbol a)).1,
      mem_tapeSymbols _, rfl⟩
  step_state_mem := by
    intro q a hq ha
    exact List.mem_map.2 ⟨(typedStep (decodeState q) (decodeSymbol a)).2.1,
      mem_stateValues _, rfl⟩

@[simp] theorem machine_blank : machine.blank = symbolCode TapeSymbol.blank := rfl

@[simp] theorem machine_start :
    machine.start = stateCode (.run .right ⟨default, tm0_supports.1⟩) := rfl

@[simp] theorem machine_halt : machine.halt = stateCode .halt := rfl

@[simp] theorem machine_step_code (state : State) (symbol : TapeSymbol) :
    machine.step (stateCode state) (symbolCode symbol) =
      let next := typedStep state symbol
      (symbolCode next.1, stateCode next.2.1, next.2.2) := by
  simp [machine, step]

/-- Fold a finite Mathlib TM0 input onto the one-sided target tape. -/
def input (source : List Symbol) : List Nat :=
  symbolCode ⟨true, default, source.headI⟩ ::
    source.tail.map fun symbol => symbolCode ⟨false, default, symbol⟩

theorem input_supported (source : List Symbol) :
    MachineInput.Supported machine (input source) := by
  intro symbol hsymbol
  simp only [input, List.mem_cons, List.mem_map] at hsymbol
  rcases hsymbol with rfl | ⟨sourceSymbol, _hsource, rfl⟩
  · exact List.mem_map.2 ⟨_, mem_tapeSymbols _, rfl⟩
  · exact List.mem_map.2 ⟨_, mem_tapeSymbols _, rfl⟩

def sourceAt (source : List Symbol) (position : Nat) : Symbol :=
  source.getI position

theorem symbolsAt_initial (source : List Symbol) (position : Nat) :
    UniversalTM0Tableau.symbolsAt
        (UniversalTM0Tableau.Config.initial source).source.Tape .right 0 position =
      (default, sourceAt source position) := by
  cases position with
  | zero =>
      have hleft : UniversalTM0Tableau.sourceOffset .right 0
          (UniversalTM0Tableau.leftAbs 0) = Int.negSucc 0 := by
        simp [UniversalTM0Tableau.sourceOffset, UniversalTM0Tableau.activeAbs,
          UniversalTM0Tableau.leftAbs, UniversalTM0Tableau.rightAbs]
      have hright : UniversalTM0Tableau.sourceOffset .right 0
          (UniversalTM0Tableau.rightAbs 0) = 0 := by
        simp [UniversalTM0Tableau.sourceOffset, UniversalTM0Tableau.activeAbs,
          UniversalTM0Tableau.rightAbs]
      rw [UniversalTM0Tableau.symbolsAt, hleft, hright]
      have hget : source.headI = source.getI 0 :=
        (List.getI_zero_eq_headI (l := source)).symm
      simp [UniversalTM0Tableau.Config.initial, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        sourceAt, hget]
  | succ position =>
      have hleft : UniversalTM0Tableau.sourceOffset .right 0
          (UniversalTM0Tableau.leftAbs (position + 1)) =
            Int.negSucc (position + 1) := by
        simp [UniversalTM0Tableau.sourceOffset, UniversalTM0Tableau.activeAbs,
          UniversalTM0Tableau.leftAbs, UniversalTM0Tableau.rightAbs]
        omega
      have hright : UniversalTM0Tableau.sourceOffset .right 0
          (UniversalTM0Tableau.rightAbs (position + 1)) =
            Int.ofNat (position + 1) := by
        simp [UniversalTM0Tableau.sourceOffset, UniversalTM0Tableau.activeAbs,
          UniversalTM0Tableau.rightAbs]
      rw [UniversalTM0Tableau.symbolsAt, hleft, hright]
      have hget : source.tail.getI position = source.getI (position + 1) := by
        cases source <;> rfl
      simp [UniversalTM0Tableau.Config.initial, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        sourceAt, hget]

/-- The folded target symbol represented by a semantic TM0 configuration. -/
def foldedSymbol (config : UniversalTM0Tableau.Config) (position : Nat) : TapeSymbol :=
  let cell := config.cellAt position
  ⟨decide (position = 0), cell.left, cell.right⟩

abbrev ConfigSupported (config : UniversalTM0Tableau.Config) : Prop :=
  config.source.q ∈ tm0Support

theorem foldedSymbol_initial (source : List Symbol) (position : Nat) :
    foldedSymbol (UniversalTM0Tableau.Config.initial source) position =
      ⟨decide (position = 0), default, sourceAt source position⟩ := by
  change TapeSymbol.mk (decide (position = 0))
    (UniversalTM0Tableau.symbolsAt
      (UniversalTM0Tableau.Config.initial source).source.Tape .right 0 position).1
    (UniversalTM0Tableau.symbolsAt
      (UniversalTM0Tableau.Config.initial source).source.Tape .right 0 position).2 = _
  rw [symbolsAt_initial]

/-- Encode a supported semantic TM0 configuration as a target machine ID. -/
def toID (config : UniversalTM0Tableau.Config) (supported : ConfigSupported config) : ID where
  tape := fun position => symbolCode (foldedSymbol config position)
  head := config.head
  state := stateCode (.run config.side ⟨config.source.q, supported⟩)

theorem initialID_eq_toID (source : List Symbol) :
    MachineInput.initialID machine (input source) =
      toID (UniversalTM0Tableau.Config.initial source) tm0_supports.1 := by
  apply ID.ext
  · funext position
    change MachineInput.tape machine.blank (input source) position =
      symbolCode (foldedSymbol
        (UniversalTM0Tableau.Config.initial source) position)
    rw [foldedSymbol_initial]
    cases position with
    | zero =>
        simp [MachineInput.tape, input, sourceAt]
        rw [List.getI_zero_eq_headI]
    | succ position =>
        simp [MachineInput.tape, input, sourceAt, TapeSymbol.blank,
          ← List.getI_eq_getElem?_getD]
  · rfl
  · rfl

@[simp] theorem toID_head (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) :
    (toID config supported).head = config.head := rfl

@[simp] theorem toID_state (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) :
    (toID config supported).state =
      stateCode (.run config.side ⟨config.source.q, supported⟩) := rfl

theorem foldedSymbol_active_head (config : UniversalTM0Tableau.Config) :
    (foldedSymbol config config.head).active config.side =
      config.source.Tape.head := by
  have hactive :
      (foldedSymbol config config.head).active config.side =
        (config.cellAt config.head).activeSymbol config.side := by
    cases hside : config.side <;>
      simp [foldedSymbol, TapeSymbol.active,
        UniversalTM0Tableau.Cell.activeSymbol]
  exact hactive.trans (UniversalTM0Tableau.cellAt_activeSymbol config)

theorem foldedSymbol_afterMove (config : UniversalTM0Tableau.Config)
    (q' : Label) (dir : Turing.Dir) (position : Nat) :
    foldedSymbol (config.afterMove q' dir) position =
      foldedSymbol config position := by
  rw [foldedSymbol, foldedSymbol,
    UniversalTM0Tableau.Config.cellAt_afterMove]
  cases hcell : config.cellAt position
  simp [UniversalTM0Tableau.Cell.withHead]

theorem foldedSymbol_afterWrite (config : UniversalTM0Tableau.Config)
    (q' : Label) (symbol : Symbol) (position : Nat) :
    foldedSymbol (config.afterWrite q' symbol) position =
      if position = config.head then
        (foldedSymbol config position).write config.side symbol
      else foldedSymbol config position := by
  rw [foldedSymbol, foldedSymbol,
    UniversalTM0Tableau.Config.cellAt_afterWrite]
  by_cases hposition : position = config.head
  · rw [if_pos hposition, if_pos hposition]
    cases hcell : config.cellAt position
    cases config.side <;>
      simp [TapeSymbol.write, UniversalTM0Tableau.Cell.writeActive,
        UniversalTM0Tableau.Cell.withHead]
  · rw [if_neg hposition, if_neg hposition]

theorem physicalMove_apply (side : Side) (head : Nat) (dir : Turing.Dir) :
    (physicalMove side (decide (head = 0)) dir).apply head =
      UniversalTM0Tableau.moveHead side (decide (head = 0)) head dir := by
  cases side <;> cases dir <;> by_cases hhead : head = 0 <;>
    subst_vars <;>
    simp_all [physicalMove, UniversalTM0Tableau.moveHead,
      UniversalTM0Tableau.Side.isInward,
      UniversalTM0Tableau.Side.isOutward, Move.apply]

theorem stateCode_run_ne_halt (side : Side) (q : SupportedLabel) :
    stateCode (.run side q) ≠ stateCode .halt := by
  intro h
  have := Encodable.encode_injective h
  cases this

theorem toID_state_ne_halt (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) :
    (toID config supported).state ≠ machine.halt := by
  exact stateCode_run_ne_halt _ _

theorem stateCode_returnBoundary_ne_halt (side : Side) (q : SupportedLabel) :
    stateCode (.returnBoundary side q) ≠ stateCode .halt := by
  intro h
  have := Encodable.encode_injective h
  cases this

theorem stateCode_returnRight_ne_halt (side : Side) (q : SupportedLabel) :
    stateCode (.returnRight side q) ≠ stateCode .halt := by
  intro h
  have := Encodable.encode_injective h
  cases this

theorem typedStep_run_move (side : Side) (q : SupportedLabel)
    (cell : TapeSymbol) (q' : Label) (dir : Turing.Dir)
    (hstep : tm0 q.1 (cell.active side) = some (q', .move dir)) :
    typedStep (.run side q) cell =
      (cell,
        .run (UniversalTM0Tableau.nextSide side cell.atOrigin dir)
          (supportedLabel q'),
        physicalMove side cell.atOrigin dir) := by
  simp [typedStep, hstep]

theorem typedStep_folded_move (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) (q' : Label) (dir : Turing.Dir)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .move dir))
    (nextSupported : ConfigSupported (config.afterMove q' dir)) :
    typedStep (.run config.side ⟨config.source.q, supported⟩)
        (foldedSymbol config config.head) =
      (foldedSymbol config config.head,
        .run (UniversalTM0Tableau.nextSide config.side
          (decide (config.head = 0)) dir) ⟨q', nextSupported⟩,
        physicalMove config.side (decide (config.head = 0)) dir) := by
  have hstep' : tm0 config.source.q
      ((foldedSymbol config config.head).active config.side) =
        some (q', .move dir) := by
    rw [foldedSymbol_active_head]
    exact hstep
  rw [typedStep_run_move _ _ _ _ _ hstep']
  have hsupported : supportedLabel q' = ⟨q', nextSupported⟩ := by
    apply Subtype.ext
    exact supportedLabel_val_of_mem
      (tm0_supports.2 (by rw [hstep]; rfl) supported)
  simp [foldedSymbol, hsupported]

theorem nextID_toID_move (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) (q' : Label) (dir : Turing.Dir)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .move dir))
    (nextSupported : ConfigSupported (config.afterMove q' dir)) :
    machine.nextID (toID config supported) =
      toID (config.afterMove q' dir) nextSupported := by
  rw [Machine.nextID_of_ne_halt (toID_state_ne_halt config supported)]
  have htyped := typedStep_folded_move config supported q' dir hstep nextSupported
  apply ID.ext
  · funext position
    simp only [toID, machine_step_code, htyped]
    by_cases hposition : position = config.head
    · subst position
      simp [foldedSymbol_afterMove]
    · simp [foldedSymbol_afterMove, hposition]
  · simp [toID, machine_step_code, htyped, physicalMove_apply,
      UniversalTM0Tableau.Config.afterMove]
  · simp [toID, machine_step_code, htyped,
      UniversalTM0Tableau.Config.afterMove]

theorem typedStep_run_write (side : Side) (q : SupportedLabel)
    (cell : TapeSymbol) (q' : Label) (symbol : Symbol)
    (hstep : tm0 q.1 (cell.active side) = some (q', .write symbol)) :
    typedStep (.run side q) cell =
      if cell.atOrigin then
        (cell.write side symbol,
          .returnBoundary side (supportedLabel q'), .left)
      else
        (cell.write side symbol,
          .returnRight side (supportedLabel q'), .left) := by
  simp [typedStep, hstep]

/-- The intermediate target configuration used to simulate a TM0 write. -/
def writeReturnID (config : UniversalTM0Tableau.Config)
    (q' : Label) (symbol : Symbol) : ID where
  tape := fun position =>
    symbolCode (foldedSymbol (config.afterWrite q' symbol) position)
  head := config.head.pred
  state := stateCode (if config.head = 0 then
    .returnBoundary config.side (supportedLabel q')
  else .returnRight config.side (supportedLabel q'))

theorem nextID_toID_write_first (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) (q' : Label) (symbol : Symbol)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .write symbol)) :
    machine.nextID (toID config supported) = writeReturnID config q' symbol := by
  rw [Machine.nextID_of_ne_halt (toID_state_ne_halt config supported)]
  have hstep' : tm0 config.source.q
      ((foldedSymbol config config.head).active config.side) =
        some (q', .write symbol) := by
    rw [foldedSymbol_active_head]
    exact hstep
  have htyped := typedStep_run_write config.side
    ⟨config.source.q, supported⟩ (foldedSymbol config config.head)
    q' symbol hstep'
  apply ID.ext
  · funext position
    simp only [toID, machine_step_code, htyped]
    rw [show (writeReturnID config q' symbol).tape position =
      symbolCode (foldedSymbol (config.afterWrite q' symbol) position) by rfl]
    rw [foldedSymbol_afterWrite]
    by_cases hhead : config.head = 0
    · by_cases hposition : position = config.head
      · simp [foldedSymbol, hhead, hposition]
      · have hposition0 : position ≠ 0 := by
          simpa [hhead] using hposition
        simp [foldedSymbol, hhead, hposition0]
    · by_cases hposition : position = config.head <;>
        simp [foldedSymbol, hhead, hposition]
  · simp only [toID, machine_step_code, htyped]
    by_cases hhead : config.head = 0 <;>
      simp [writeReturnID, foldedSymbol, hhead, Move.apply]
  · simp only [toID, machine_step_code, htyped]
    by_cases hhead : config.head = 0 <;>
      simp [writeReturnID, foldedSymbol, hhead]

theorem writeReturnID_state_ne_halt (config : UniversalTM0Tableau.Config)
    (q' : Label) (symbol : Symbol) :
    (writeReturnID config q' symbol).state ≠ machine.halt := by
  by_cases hhead : config.head = 0
  · simpa [writeReturnID, hhead] using
      stateCode_returnBoundary_ne_halt config.side (supportedLabel q')
  · simpa [writeReturnID, hhead] using
      stateCode_returnRight_ne_halt config.side (supportedLabel q')

theorem nextID_writeReturnID (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) (q' : Label) (symbol : Symbol)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .write symbol))
    (nextSupported : ConfigSupported (config.afterWrite q' symbol)) :
    machine.nextID (writeReturnID config q' symbol) =
      toID (config.afterWrite q' symbol) nextSupported := by
  rw [Machine.nextID_of_ne_halt
    (writeReturnID_state_ne_halt config q' symbol)]
  have hsupported : supportedLabel q' = ⟨q', nextSupported⟩ := by
    apply Subtype.ext
    exact supportedLabel_val_of_mem
      (tm0_supports.2 (by rw [hstep]; rfl) supported)
  apply ID.ext
  · funext position
    by_cases hhead : config.head = 0
    all_goals
      simp [writeReturnID, toID, machine_step_code, typedStep, hhead]
      intro hposition
      subst position
      rfl
  · by_cases hhead : config.head = 0
    · simp [writeReturnID, toID, machine_step_code, typedStep, hhead,
        Move.apply, UniversalTM0Tableau.Config.afterWrite]
    · simp [writeReturnID, toID, machine_step_code, typedStep, hhead,
        Move.apply, UniversalTM0Tableau.Config.afterWrite]
      omega
  · by_cases hhead : config.head = 0 <;>
      simp [writeReturnID, toID, machine_step_code, typedStep, hhead, hsupported,
        UniversalTM0Tableau.Config.afterWrite]

theorem nextID_nextID_toID_write (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config) (q' : Label) (symbol : Symbol)
    (hstep : tm0 config.source.q config.source.Tape.head =
      some (q', .write symbol))
    (nextSupported : ConfigSupported (config.afterWrite q' symbol)) :
    machine.nextID (machine.nextID (toID config supported)) =
      toID (config.afterWrite q' symbol) nextSupported := by
  rw [nextID_toID_write_first config supported q' symbol hstep]
  exact nextID_writeReturnID config supported q' symbol hstep nextSupported

theorem typedStep_run_none (side : Side) (q : SupportedLabel)
    (cell : TapeSymbol) (hstep : tm0 q.1 (cell.active side) = none) :
    typedStep (.run side q) cell = (cell, .halt, .left) := by
  simp [typedStep, hstep]

theorem nextID_toID_state_halt (config : UniversalTM0Tableau.Config)
    (supported : ConfigSupported config)
    (hstep : tm0 config.source.q config.source.Tape.head = none) :
    (machine.nextID (toID config supported)).state = machine.halt := by
  rw [Machine.nextID_state_of_ne_halt (toID_state_ne_halt config supported)]
  have hstep' : tm0 config.source.q
      ((foldedSymbol config config.head).active config.side) = none := by
    rw [foldedSymbol_active_head]
    exact hstep
  have htyped := typedStep_run_none config.side
    ⟨config.source.q, supported⟩ (foldedSymbol config config.head) hstep'
  change (machine.step
    (stateCode (.run config.side ⟨config.source.q, supported⟩))
    (symbolCode (foldedSymbol config config.head))).2.1 = machine.halt
  rw [machine_step_code]
  rw [htyped]
  rfl

/-- A source configuration corresponds to its folded target configuration. -/
def Corresponds (config : UniversalTM0Tableau.Config) (id : ID) : Prop :=
  ∃ supported : ConfigSupported config, toID config supported = id

theorem configStep_respects_transition :
    StateTransition.Respects UniversalTM0Tableau.Config.step
      (MachineInput.transition machine) Corresponds := by
  intro config id hcorresponds
  rcases hcorresponds with ⟨supported, rfl⟩
  cases hstep : tm0 config.source.q config.source.Tape.head with
  | none =>
      simp only [UniversalTM0Tableau.Config.step, hstep]
      apply (MachineInput.transition_eq_none_iff machine _).2
      exact nextID_toID_state_halt config supported hstep
  | some result =>
      rcases result with ⟨q', stmt⟩
      have nextSupported : q' ∈ tm0Support :=
        tm0_supports.2 (by rw [hstep]; rfl) supported
      cases stmt with
      | move dir =>
          simp only [UniversalTM0Tableau.Config.step, hstep]
          refine ⟨toID (config.afterMove q' dir) nextSupported,
            ⟨nextSupported, rfl⟩, ?_⟩
          apply Relation.TransGen.single
          have hnext := nextID_toID_move config supported q' dir hstep nextSupported
          have hne := toID_state_ne_halt
            (config.afterMove q' dir) nextSupported
          unfold MachineInput.transition
          rw [hnext, if_neg hne]
          rfl
      | write symbol =>
          simp only [UniversalTM0Tableau.Config.step, hstep]
          refine ⟨toID (config.afterWrite q' symbol) nextSupported,
            ⟨nextSupported, rfl⟩, ?_⟩
          apply Relation.TransGen.tail
            (b := writeReturnID config q' symbol)
          · apply Relation.TransGen.single
            have hnext := nextID_toID_write_first
              config supported q' symbol hstep
            have hne := writeReturnID_state_ne_halt config q' symbol
            unfold MachineInput.transition
            rw [hnext, if_neg hne]
            rfl
          · have hnext := nextID_writeReturnID
              config supported q' symbol hstep nextSupported
            have hne := toID_state_ne_halt
              (config.afterWrite q' symbol) nextSupported
            unfold MachineInput.transition
            rw [hnext, if_neg hne]
            rfl

/-- Forget the folding coordinates and retain the underlying TM0 configuration. -/
def Projects (config : UniversalTM0Tableau.Config)
    (source : Turing.TM0.Cfg Symbol Label) : Prop :=
  config.source = source

theorem configStep_respects_tm0Step :
    StateTransition.Respects UniversalTM0Tableau.Config.step
      (Turing.TM0.step tm0) Projects := by
  intro config source hprojects
  subst source
  cases hstep : tm0 config.source.q config.source.Tape.head with
  | none =>
      simp only [UniversalTM0Tableau.Config.step, hstep]
      simp [Turing.TM0.step, hstep]
  | some result =>
      rcases result with ⟨q', stmt⟩
      cases stmt with
      | move dir =>
          let next := config.afterMove q' dir
          have hconfig : config.step = some next := by
            simp [UniversalTM0Tableau.Config.step, hstep, next]
          simp only [hconfig]
          refine ⟨next.source, rfl, Relation.TransGen.single ?_⟩
          exact UniversalTM0Tableau.Config.step_source hconfig
      | write symbol =>
          let next := config.afterWrite q' symbol
          have hconfig : config.step = some next := by
            simp [UniversalTM0Tableau.Config.step, hstep, next]
          simp only [hconfig]
          refine ⟨next.source, rfl, Relation.TransGen.single ?_⟩
          exact UniversalTM0Tableau.Config.step_source hconfig

theorem tm0Step_eval_dom_iff_configStep_eval_dom (source : List Symbol) :
    (StateTransition.eval (Turing.TM0.step tm0)
      (Turing.TM0.init source)).Dom ↔
    (StateTransition.eval UniversalTM0Tableau.Config.step
      (UniversalTM0Tableau.Config.initial source)).Dom := by
  apply StateTransition.tr_eval_dom configStep_respects_tm0Step
  rfl

theorem transition_eval_dom_iff_configStep_eval_dom (source : List Symbol) :
    (StateTransition.eval (MachineInput.transition machine)
      (MachineInput.initialID machine (input source))).Dom ↔
    (StateTransition.eval UniversalTM0Tableau.Config.step
      (UniversalTM0Tableau.Config.initial source)).Dom := by
  apply StateTransition.tr_eval_dom configStep_respects_transition
  exact ⟨tm0_supports.1, (initialID_eq_toID source).symm⟩

theorem tm0_eval_dom_iff_step_eval_dom (source : List Symbol) :
    (Turing.TM0.eval tm0 source).Dom ↔
      (StateTransition.eval (Turing.TM0.step tm0)
        (Turing.TM0.init source)).Dom := by
  unfold Turing.TM0.eval
  rfl

/-- The fixed one-sided machine halts exactly when the universal TM0 evaluator does. -/
theorem halts_iff_tm0_eval_dom (source : List Symbol) :
    MachineInput.Halts machine (input source) ↔
      (Turing.TM0.eval tm0 source).Dom := by
  calc
    MachineInput.Halts machine (input source) ↔
        (StateTransition.eval (MachineInput.transition machine)
          (MachineInput.initialID machine (input source))).Dom :=
      (MachineInput.transition_eval_dom_iff_halts machine (input source)).symm
    _ ↔ (StateTransition.eval UniversalTM0Tableau.Config.step
          (UniversalTM0Tableau.Config.initial source)).Dom :=
      transition_eval_dom_iff_configStep_eval_dom source
    _ ↔ (StateTransition.eval (Turing.TM0.step tm0)
          (Turing.TM0.init source)).Dom :=
      (tm0Step_eval_dom_iff_configStep_eval_dom source).symm
    _ ↔ (Turing.TM0.eval tm0 source).Dom :=
      (tm0_eval_dom_iff_step_eval_dom source).symm

end UniversalTM0Machine
end LeanWang
