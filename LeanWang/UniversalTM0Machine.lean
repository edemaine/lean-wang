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

private def supportedNext (q : SupportedLabel) (symbol : Symbol)
    (q' : Label) (stmt : Turing.TM0.Stmt Symbol)
    (hstep : tm0 q.1 symbol = some (q', stmt)) : SupportedLabel :=
  ⟨q', tm0_supports.2 (by rw [hstep]; rfl) q.2⟩

def physicalMove (side : Side) (atOrigin : Bool) (dir : Turing.Dir) : Move :=
  if atOrigin && side.isInward dir then .left
  else if side.isOutward dir then .right else .left

/-- One step of the finite-control folded simulator. -/
def typedStep : State → TapeSymbol → TapeSymbol × State × Move
  | .halt, cell => (cell, .halt, .left)
  | .returnBoundary side q, cell => (cell, .run side q, .left)
  | .returnRight side q, cell => (cell, .run side q, .right)
  | .run side q, cell =>
      match hstep : tm0 q.1 (cell.active side) with
      | none => (cell, .halt, .left)
      | some (q', .write symbol) =>
          let next := supportedNext q (cell.active side) q' (.write symbol) hstep
          if cell.atOrigin then
            (cell.write side symbol, .returnBoundary side next, .left)
          else
            (cell.write side symbol, .returnRight side next, .left)
      | some (q', .move dir) =>
          let next := supportedNext q (cell.active side) q' (.move dir) hstep
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

end UniversalTM0Machine
end LeanWang
