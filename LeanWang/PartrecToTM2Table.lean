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

/-- Decode the low two bits of an interleaved tape position as a stack name. -/
def stackNameOfCode : Nat → Option Turing.PartrecToTM2.K'
  | 0 => some Turing.PartrecToTM2.K'.main
  | 1 => some Turing.PartrecToTM2.K'.rev
  | 2 => some Turing.PartrecToTM2.K'.aux
  | 3 => some Turing.PartrecToTM2.K'.stack
  | _ => none

theorem stackNameOfCode_stackNameCode (k : Turing.PartrecToTM2.K') :
    stackNameOfCode (PartrecToTM2Support.stackNameCode k) = some k := by
  cases k <;> rfl

/-- Position of stack cell `i` for stack `k` in the interleaved one-tape layout. -/
def stackCellPos (k : Turing.PartrecToTM2.K') (i : Nat) : Nat :=
  4 * i + PartrecToTM2Support.stackNameCode k

theorem stackCellPos_mod_four (k : Turing.PartrecToTM2.K') (i : Nat) :
    stackCellPos k i % 4 = PartrecToTM2Support.stackNameCode k := by
  cases k <;> simp [stackCellPos, PartrecToTM2Support.stackNameCode]

theorem stackCellPos_div_four (k : Turing.PartrecToTM2.K') (i : Nat) :
    stackCellPos k i / 4 = i := by
  cases k <;>
    simp [stackCellPos, PartrecToTM2Support.stackNameCode, Nat.add_comm,
      Nat.add_mul_div_left _ _ (by decide : 0 < 4)]

/-- One-sided tape encoding of the four `PartrecToTM2` stacks. -/
def encodedTape (cfg : Turing.PartrecToTM2.Cfg') : Nat → Nat :=
  fun p =>
    match stackNameOfCode (p % 4) with
    | none => blankSymbol
    | some k => PartrecToTM2Support.tapeSymbolCode ((cfg.stk k)[p / 4]?)

theorem encodedTape_stackCell (cfg : Turing.PartrecToTM2.Cfg')
    (k : Turing.PartrecToTM2.K') (i : Nat) :
    encodedTape cfg (stackCellPos k i) =
      PartrecToTM2Support.tapeSymbolCode ((cfg.stk k)[i]?) := by
  simp [encodedTape, stackCellPos_mod_four, stackCellPos_div_four,
    stackNameOfCode_stackNameCode]

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

/-- The statement substate corresponding to a TM2 configuration label. -/
def cfgStatement : Option Turing.PartrecToTM2.Λ' → Option Turing.PartrecToTM2.Stmt'
  | none => none
  | some q => some (Turing.PartrecToTM2.tr q)

/-- Encoded table-machine state of a `PartrecToTM2` configuration. -/
noncomputable def encodedState (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') : Nat :=
  PartrecToTM2Support.statementIndex tc (cfgStatement cfg.l)

theorem encodedState_mem_states {tc : Turing.ToPartrec.Code}
    {cfg : Turing.PartrecToTM2.Cfg'}
    (hlabel : cfg.l ∈ Finset.insertNone (PartrecToTM2Support.labels tc)) :
    encodedState tc cfg ∈ states tc := by
  cases hcfg : cfg.l with
  | none =>
      simpa [encodedState, cfgStatement, hcfg, PartrecToTM2Support.haltState] using
        haltState_mem_states tc
  | some q =>
      have hq : q ∈ PartrecToTM2Support.labels tc := by
        exact Finset.some_mem_insertNone.1 (by simpa [hcfg] using hlabel)
      simpa [encodedState, cfgStatement, hcfg] using labelState_mem_states hq

/-- One-tape instantaneous description representing a `PartrecToTM2` configuration. -/
noncomputable def encodedID (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') : ID where
  tape := encodedTape cfg
  head := 0
  state := encodedState tc cfg

@[simp]
theorem encodedID_tape (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') :
    (encodedID tc cfg).tape = encodedTape cfg :=
  rfl

@[simp]
theorem encodedID_head (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') :
    (encodedID tc cfg).head = 0 :=
  rfl

@[simp]
theorem encodedID_state (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') :
    (encodedID tc cfg).state = encodedState tc cfg :=
  rfl

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
