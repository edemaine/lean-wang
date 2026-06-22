/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Machine
import LeanWang.PartrecToTM2Support

/-!
Finite `TableProgram` header data for Mathlib's `PartrecToTM2` evaluator.

This file does not yet build the transition table. It packages the finite
alphabet and finite control-state list from `PartrecToTM2Support` in the exact
shape expected by `TableProgram`, so the remaining reduction work can focus on
generating and proving the transition rows.
-/

noncomputable section

namespace LeanWang

namespace PartrecToTM2Table

open Turing

/-- The table-machine blank symbol for encoded `PartrecToTM2` stacks. -/
def blankSymbol : Nat :=
  PartrecToTM2Support.tapeSymbolCode none

@[simp]
theorem blankSymbol_eq_zero : blankSymbol = 0 :=
  rfl

/-- Raw finite table-machine symbol list for encoded `PartrecToTM2` stacks. -/
def symbols : List Nat :=
  PartrecToTM2Support.tapeSymbols

theorem symbols_nodup : symbols.Nodup :=
  PartrecToTM2Support.tapeSymbols_nodup

theorem blankSymbol_mem_symbols : blankSymbol ∈ symbols := by
  exact PartrecToTM2Support.tapeSymbolCode_mem_tapeSymbols none

theorem stackCellSymbol_mem_symbols (s : Option Turing.PartrecToTM2.Γ') :
    PartrecToTM2Support.tapeSymbolCode s ∈ symbols :=
  PartrecToTM2Support.tapeSymbolCode_mem_tapeSymbols s

/-- Raw finite table-machine state list for the evaluator control substates. -/
def states (tc : Turing.ToPartrec.Code) : List Nat :=
  PartrecToTM2Support.controlStates tc

theorem states_nodup (tc : Turing.ToPartrec.Code) :
    (states tc).Nodup := by
  unfold states PartrecToTM2Support.controlStates
  exact List.nodup_range

theorem startState_mem_states (tc : Turing.ToPartrec.Code) :
    PartrecToTM2Support.startState tc ∈ states tc :=
  PartrecToTM2Support.startState_mem_controlStates tc

theorem haltState_mem_states (tc : Turing.ToPartrec.Code) :
    PartrecToTM2Support.haltState tc ∈ states tc :=
  PartrecToTM2Support.haltState_mem_controlStates tc

theorem labelState_mem_states {tc : Turing.ToPartrec.Code}
    {q : Turing.PartrecToTM2.Λ'}
    (hq : q ∈ PartrecToTM2Support.labels tc) :
    PartrecToTM2Support.statementIndex tc (some (Turing.PartrecToTM2.tr q)) ∈ states tc :=
  PartrecToTM2Support.labelState_mem_controlStates hq

theorem statementState_mem_states {tc : Turing.ToPartrec.Code}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    PartrecToTM2Support.statementIndex tc stmt ∈ states tc :=
  PartrecToTM2Support.statementIndex_mem_controlStates hstmt

/--
`TableProgram` header for a future `PartrecToTM2` table-machine reduction.

The transition table is an explicit parameter; later construction work should
fill this table with rows simulating the supported TM2 statement substates.
-/
def programWithTable (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) : TableProgram where
  symbols := symbols
  states := states tc
  blank := blankSymbol
  start := PartrecToTM2Support.startState tc
  halt := PartrecToTM2Support.haltState tc
  table := table

@[simp]
theorem programWithTable_symbols (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).symbols = symbols :=
  rfl

@[simp]
theorem programWithTable_states (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).states = states tc :=
  rfl

@[simp]
theorem programWithTable_blank (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).blank = blankSymbol :=
  rfl

@[simp]
theorem programWithTable_start (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).start = PartrecToTM2Support.startState tc :=
  rfl

@[simp]
theorem programWithTable_halt (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).halt = PartrecToTM2Support.haltState tc :=
  rfl

@[simp]
theorem programWithTable_table (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).table = table :=
  rfl

theorem programWithTable_blank_mem_symbols (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).blank ∈ (programWithTable tc table).symbols := by
  exact blankSymbol_mem_symbols

theorem programWithTable_start_mem_states (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).start ∈ (programWithTable tc table).states := by
  exact startState_mem_states tc

theorem programWithTable_halt_mem_states (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).halt ∈ (programWithTable tc table).states := by
  exact haltState_mem_states tc

end PartrecToTM2Table

end LeanWang

end
