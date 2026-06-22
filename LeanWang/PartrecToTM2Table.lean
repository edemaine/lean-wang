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

/-- Reserved table-machine state used to initialize the fixed input `[0]`. -/
def initState : Nat :=
  0

/-- Shift a TM2 statement-substate index into the table-machine state namespace. -/
def evaluatorStateCode (n : Nat) : Nat :=
  n + 1

/-- Finite table-machine states for the TM2 evaluator substates. -/
def evaluatorStates (tc : Turing.ToPartrec.Code) : List Nat :=
  (PartrecToTM2Support.controlStates tc).map evaluatorStateCode

/-- Raw finite table-machine state list, including the initialization state. -/
def states (tc : Turing.ToPartrec.Code) : List Nat :=
  initState :: evaluatorStates tc

theorem states_nodup (tc : Turing.ToPartrec.Code) :
    (states tc).Nodup := by
  unfold states evaluatorStates evaluatorStateCode PartrecToTM2Support.controlStates initState
  simp [List.nodup_range.map (by intro a b h; exact Nat.succ.inj h)]

/-- Table-machine state that starts the TM2 evaluator after initialization. -/
noncomputable def evalStartState (tc : Turing.ToPartrec.Code) : Nat :=
  evaluatorStateCode (PartrecToTM2Support.startState tc)

/-- Table-machine halting state corresponding to the halted TM2 configuration. -/
noncomputable def haltState (tc : Turing.ToPartrec.Code) : Nat :=
  evaluatorStateCode (PartrecToTM2Support.haltState tc)

theorem initState_mem_states (tc : Turing.ToPartrec.Code) :
    initState ∈ states tc := by
  simp [states]

theorem evalStartState_mem_states (tc : Turing.ToPartrec.Code) :
    evalStartState tc ∈ states tc := by
  unfold evalStartState states evaluatorStates evaluatorStateCode
  simp [PartrecToTM2Support.startState_mem_controlStates tc]

theorem haltState_mem_states (tc : Turing.ToPartrec.Code) :
    haltState tc ∈ states tc := by
  unfold haltState states evaluatorStates evaluatorStateCode
  simp [PartrecToTM2Support.haltState_mem_controlStates tc]

theorem labelState_mem_states {tc : Turing.ToPartrec.Code}
    {q : Turing.PartrecToTM2.Λ'}
    (hq : q ∈ PartrecToTM2Support.labels tc) :
    evaluatorStateCode
      (PartrecToTM2Support.statementIndex tc (some (Turing.PartrecToTM2.tr q))) ∈ states tc := by
  unfold states evaluatorStates evaluatorStateCode
  simp [PartrecToTM2Support.labelState_mem_controlStates hq]

theorem statementState_mem_states {tc : Turing.ToPartrec.Code}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    evaluatorStateCode (PartrecToTM2Support.statementIndex tc stmt) ∈ states tc := by
  unfold states evaluatorStates evaluatorStateCode
  simp [PartrecToTM2Support.statementIndex_mem_controlStates hstmt]

/-- The statement substate corresponding to a TM2 configuration label. -/
def cfgStatement : Option Turing.PartrecToTM2.Λ' → Option Turing.PartrecToTM2.Stmt'
  | none => none
  | some q => some (Turing.PartrecToTM2.tr q)

/-- Encoded table-machine state of a `PartrecToTM2` configuration. -/
noncomputable def encodedState (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') : Nat :=
  evaluatorStateCode (PartrecToTM2Support.statementIndex tc (cfgStatement cfg.l))

theorem encodedState_mem_states {tc : Turing.ToPartrec.Code}
    {cfg : Turing.PartrecToTM2.Cfg'}
    (hlabel : cfg.l ∈ Finset.insertNone (PartrecToTM2Support.labels tc)) :
    encodedState tc cfg ∈ states tc := by
  cases hcfg : cfg.l with
  | none =>
      simpa [encodedState, cfgStatement, hcfg, haltState, PartrecToTM2Support.haltState] using
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

/--
Representation invariant connecting a one-tape table-machine ID with a
`PartrecToTM2` configuration.

The invariant records the head convention, the encoded control state, and the
semantically meaningful interleaved stack cells. It intentionally avoids full
tape extensional equality, because later transition rows only need to preserve
the stack-cell view of the encoding.
-/
noncomputable def RepresentsCfg (tc : Turing.ToPartrec.Code) (id : ID)
    (cfg : Turing.PartrecToTM2.Cfg') : Prop :=
  id.head = 0 ∧
    id.state = encodedState tc cfg ∧
      ∀ k i, id.tape (stackCellPos k i) = encodedTape cfg (stackCellPos k i)

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

theorem encodedID_representsCfg (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') :
    RepresentsCfg tc (encodedID tc cfg) cfg := by
  constructor
  · rfl
  constructor
  · rfl
  · intro k i
    rfl

theorem RepresentsCfg.state_mem_states {tc : Turing.ToPartrec.Code}
    {id : ID} {cfg : Turing.PartrecToTM2.Cfg'}
    (h : RepresentsCfg tc id cfg)
    (hlabel : cfg.l ∈ Finset.insertNone (PartrecToTM2Support.labels tc)) :
    id.state ∈ states tc := by
  rw [h.2.1]
  exact encodedState_mem_states hlabel

theorem encodedTape_init_main_zero (tc : Turing.ToPartrec.Code) :
    encodedTape (Turing.PartrecToTM2.init tc [0])
      (stackCellPos Turing.PartrecToTM2.K'.main 0) =
        PartrecToTM2Support.tapeSymbolCode (some Turing.PartrecToTM2.Γ'.cons) := by
  simp [encodedTape_stackCell, Turing.PartrecToTM2.init, Turing.PartrecToTM2.K'.elim]

theorem encodedTape_init_main_succ (tc : Turing.ToPartrec.Code) (i : Nat) :
    encodedTape (Turing.PartrecToTM2.init tc [0])
      (stackCellPos Turing.PartrecToTM2.K'.main (i + 1)) = blankSymbol := by
  simp [encodedTape_stackCell, Turing.PartrecToTM2.init, Turing.PartrecToTM2.K'.elim,
    blankSymbol]

theorem encodedTape_init_rev (tc : Turing.ToPartrec.Code) (i : Nat) :
    encodedTape (Turing.PartrecToTM2.init tc [0])
      (stackCellPos Turing.PartrecToTM2.K'.rev i) = blankSymbol := by
  simp [encodedTape_stackCell, Turing.PartrecToTM2.init, Turing.PartrecToTM2.K'.elim,
    blankSymbol]

theorem encodedTape_init_aux (tc : Turing.ToPartrec.Code) (i : Nat) :
    encodedTape (Turing.PartrecToTM2.init tc [0])
      (stackCellPos Turing.PartrecToTM2.K'.aux i) = blankSymbol := by
  simp [encodedTape_stackCell, Turing.PartrecToTM2.init, Turing.PartrecToTM2.K'.elim,
    blankSymbol]

theorem encodedTape_init_stack (tc : Turing.ToPartrec.Code) (i : Nat) :
    encodedTape (Turing.PartrecToTM2.init tc [0])
      (stackCellPos Turing.PartrecToTM2.K'.stack i) = blankSymbol := by
  simp [encodedTape_stackCell, Turing.PartrecToTM2.init, Turing.PartrecToTM2.K'.elim,
    blankSymbol]

theorem encodedState_init (tc : Turing.ToPartrec.Code) :
    encodedState tc (Turing.PartrecToTM2.init tc [0]) = evalStartState tc := by
  simp [encodedState, evalStartState, cfgStatement, PartrecToTM2Support.startState,
    PartrecToTM2Support.startLabel, Turing.PartrecToTM2.init]

/-- Symbol written by the fixed-input initialization row. -/
def inputZeroSymbol : Nat :=
  PartrecToTM2Support.tapeSymbolCode (some Turing.PartrecToTM2.Γ'.cons)

theorem inputZeroSymbol_mem_symbols : inputZeroSymbol ∈ symbols :=
  stackCellSymbol_mem_symbols (some Turing.PartrecToTM2.Γ'.cons)

/--
First transition row for the future TM2-to-table reduction/compiler.

On the blank empty-input tape, it writes the encoding of `[0]` to the main
stack's first cell and enters the TM2 evaluator start state. The left move keeps
the one-sided head at `0`.
-/
noncomputable def initTransition (tc : Turing.ToPartrec.Code) : TableTransition where
  state := initState
  read := blankSymbol
  write := inputZeroSymbol
  next := evalStartState tc
  move := Move.left

@[simp]
theorem initTransition_state (tc : Turing.ToPartrec.Code) :
    (initTransition tc).state = initState :=
  rfl

@[simp]
theorem initTransition_read (tc : Turing.ToPartrec.Code) :
    (initTransition tc).read = blankSymbol :=
  rfl

@[simp]
theorem initTransition_write (tc : Turing.ToPartrec.Code) :
    (initTransition tc).write = inputZeroSymbol :=
  rfl

@[simp]
theorem initTransition_next (tc : Turing.ToPartrec.Code) :
    (initTransition tc).next = evalStartState tc :=
  rfl

@[simp]
theorem initTransition_move (tc : Turing.ToPartrec.Code) :
    (initTransition tc).move = Move.left :=
  rfl

theorem initTransition_write_mem_symbols (tc : Turing.ToPartrec.Code) :
    (initTransition tc).write ∈ symbols :=
  inputZeroSymbol_mem_symbols

theorem initTransition_next_mem_states (tc : Turing.ToPartrec.Code) :
    (initTransition tc).next ∈ states tc :=
  evalStartState_mem_states tc

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
  start := initState
  halt := haltState tc
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
    (programWithTable tc table).start = initState :=
  rfl

@[simp]
theorem programWithTable_halt (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).halt = haltState tc :=
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
  exact initState_mem_states tc

theorem programWithTable_halt_mem_states (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithTable tc table).halt ∈ (programWithTable tc table).states := by
  exact haltState_mem_states tc

/-- Header plus the fixed first initialization row. -/
noncomputable def programWithInitTable (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) : TableProgram :=
  programWithTable tc (initTransition tc :: table)

theorem programWithInitTable_first_transition (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithInitTable tc table).toTableMachine.transition?
      (programWithInitTable tc table).start
      (programWithInitTable tc table).blank = some (initTransition tc) := by
  apply TableProgram.transition?_eq_some_of_table_head_matches
  · rfl
  · simp [programWithInitTable, TableTransition.matchesInput, initState, blankSymbol]

theorem programWithInitTable_runEmpty_one (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) :
    (programWithInitTable tc table).toMachine.runEmpty 1 =
      { tape := fun i => if i = 0 then inputZeroSymbol else blankSymbol
        head := 0
        state := evalStartState tc } := by
  have hfind := programWithInitTable_first_transition tc table
  have hwrite :
      (initTransition tc).write ∈ (programWithInitTable tc table).supportedSymbols := by
    change inputZeroSymbol ∈ blankSymbol :: symbols
    exact List.mem_cons_of_mem blankSymbol inputZeroSymbol_mem_symbols
  have hnext :
      (initTransition tc).next ∈ (programWithInitTable tc table).supportedStates := by
    change evalStartState tc ∈ initState :: haltState tc :: states tc
    exact List.mem_cons_of_mem initState
      (List.mem_cons_of_mem (haltState tc) (evalStartState_mem_states tc))
  have hstart : (programWithInitTable tc table).start ≠ (programWithInitTable tc table).halt := by
    simp [programWithInitTable, initState, haltState, evaluatorStateCode]
  have hrun := TableProgram.toMachine_runEmpty_one_of_initial_transition
    (P := programWithInitTable tc table) (e := initTransition tc)
    hstart hfind hwrite hnext
  simpa [programWithInitTable, Move.apply, inputZeroSymbol] using hrun

theorem programWithInitTable_runEmpty_one_stackCell (tc : Turing.ToPartrec.Code)
    (table : List TableTransition)
    (k : Turing.PartrecToTM2.K') (i : Nat) :
    ((programWithInitTable tc table).toMachine.runEmpty 1).tape (stackCellPos k i) =
      encodedTape (Turing.PartrecToTM2.init tc [0]) (stackCellPos k i) := by
  rw [programWithInitTable_runEmpty_one]
  rw [encodedTape_stackCell]
  cases k <;> cases i <;>
    simp [stackCellPos, PartrecToTM2Support.stackNameCode,
      Turing.PartrecToTM2.init, Turing.PartrecToTM2.K'.elim, inputZeroSymbol,
      blankSymbol]

theorem programWithInitTable_runEmpty_one_represents_init
    (tc : Turing.ToPartrec.Code) (table : List TableTransition) :
    RepresentsCfg tc ((programWithInitTable tc table).toMachine.runEmpty 1)
      (Turing.PartrecToTM2.init tc [0]) := by
  constructor
  · rw [programWithInitTable_runEmpty_one]
  constructor
  · rw [programWithInitTable_runEmpty_one, encodedState_init]
  · intro k i
    exact programWithInitTable_runEmpty_one_stackCell tc table k i

end PartrecToTM2Table

end LeanWang

end
