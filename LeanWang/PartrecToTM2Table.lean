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

/-- Finite list of decoded table-machine stack-cell symbols. -/
def cellSymbols : List (Option Turing.PartrecToTM2.Γ') :=
  [none,
    some Turing.PartrecToTM2.Γ'.consₗ,
    some Turing.PartrecToTM2.Γ'.cons,
    some Turing.PartrecToTM2.Γ'.bit0,
    some Turing.PartrecToTM2.Γ'.bit1]

theorem cellSymbols_nodup : cellSymbols.Nodup := by
  decide

theorem tapeSymbolCode_mem_symbols (s : Option Turing.PartrecToTM2.Γ') :
    PartrecToTM2Support.tapeSymbolCode s ∈ symbols :=
  stackCellSymbol_mem_symbols s

theorem tapeSymbolCode_cellSymbols_eq_symbols :
    cellSymbols.map PartrecToTM2Support.tapeSymbolCode = symbols := by
  rfl

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
def encodedStacks (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ') :
    Nat → Nat :=
  fun p =>
    match stackNameOfCode (p % 4) with
    | none => blankSymbol
    | some k => PartrecToTM2Support.tapeSymbolCode ((stk k)[p / 4]?)

theorem encodedStacks_stackCell
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (i : Nat) :
    encodedStacks stk (stackCellPos k i) =
      PartrecToTM2Support.tapeSymbolCode ((stk k)[i]?) := by
  simp [encodedStacks, stackCellPos_mod_four, stackCellPos_div_four,
    stackNameOfCode_stackNameCode]

/-- Push one symbol onto stack `k`. -/
def pushStack
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (a : Turing.PartrecToTM2.Γ') :
    ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ' :=
  Function.update stk k (a :: stk k)

/-- Pop one symbol from stack `k`, if present. -/
def popStack
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') :
    ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ' :=
  Function.update stk k (stk k).tail

@[simp]
theorem pushStack_self
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (a : Turing.PartrecToTM2.Γ') :
    pushStack stk k a k = a :: stk k := by
  simp [pushStack]

theorem pushStack_of_ne
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    {k k' : Turing.PartrecToTM2.K'} (a : Turing.PartrecToTM2.Γ')
    (h : k' ≠ k) :
    pushStack stk k a k' = stk k' := by
  simp [pushStack, Function.update_of_ne h]

@[simp]
theorem popStack_self
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') :
    popStack stk k k = (stk k).tail := by
  simp [popStack]

theorem popStack_of_ne
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    {k k' : Turing.PartrecToTM2.K'} (h : k' ≠ k) :
    popStack stk k k' = stk k' := by
  simp [popStack, Function.update_of_ne h]

theorem encodedStacks_pushStack_target_zero
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (a : Turing.PartrecToTM2.Γ') :
    encodedStacks (pushStack stk k a) (stackCellPos k 0) =
      PartrecToTM2Support.tapeSymbolCode (some a) := by
  simp [encodedStacks_stackCell]

theorem encodedStacks_pushStack_target_succ
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (a : Turing.PartrecToTM2.Γ') (i : Nat) :
    encodedStacks (pushStack stk k a) (stackCellPos k (i + 1)) =
      encodedStacks stk (stackCellPos k i) := by
  simp [encodedStacks_stackCell]

theorem encodedStacks_pushStack_other
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    {k k' : Turing.PartrecToTM2.K'} (a : Turing.PartrecToTM2.Γ') (i : Nat)
    (h : k' ≠ k) :
    encodedStacks (pushStack stk k a) (stackCellPos k' i) =
      encodedStacks stk (stackCellPos k' i) := by
  simp [encodedStacks_stackCell, pushStack_of_ne stk a h]

theorem encodedStacks_popStack_target
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (i : Nat) :
    encodedStacks (popStack stk k) (stackCellPos k i) =
      encodedStacks stk (stackCellPos k (i + 1)) := by
  cases stk k <;> cases i <;> simp [encodedStacks_stackCell]

theorem encodedStacks_popStack_other
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    {k k' : Turing.PartrecToTM2.K'} (i : Nat) (h : k' ≠ k) :
    encodedStacks (popStack stk k) (stackCellPos k' i) =
      encodedStacks stk (stackCellPos k' i) := by
  simp [encodedStacks_stackCell, popStack_of_ne stk h]

theorem pushStack_eq_tm2_update
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') (a : Turing.PartrecToTM2.Γ') :
    pushStack stk k a = Function.update stk k (a :: stk k) :=
  rfl

theorem popStack_eq_tm2_update
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ')
    (k : Turing.PartrecToTM2.K') :
    popStack stk k = Function.update stk k (stk k).tail :=
  rfl

theorem tm2_stepAux_push
    (k : Turing.PartrecToTM2.K')
    (f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt')
    (var : Option Turing.PartrecToTM2.Γ')
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ') :
    Turing.TM2.stepAux (Turing.TM2.Stmt.push k f q) var stk =
      Turing.TM2.stepAux q var (pushStack stk k (f var)) := by
  rfl

theorem tm2_stepAux_peek_var
    (k : Turing.PartrecToTM2.K')
    (f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt')
    (var : Option Turing.PartrecToTM2.Γ')
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ') :
    Turing.TM2.stepAux (Turing.TM2.Stmt.peek k f q) var stk =
      Turing.TM2.stepAux q (f var (stk k).head?) stk := by
  rfl

theorem tm2_stepAux_pop
    (k : Turing.PartrecToTM2.K')
    (f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt')
    (var : Option Turing.PartrecToTM2.Γ')
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ') :
    Turing.TM2.stepAux (Turing.TM2.Stmt.pop k f q) var stk =
      Turing.TM2.stepAux q (f var (stk k).head?) (popStack stk k) := by
  rfl

/-- One-sided tape encoding of a full `PartrecToTM2` configuration. -/
def encodedTape (cfg : Turing.PartrecToTM2.Cfg') : Nat → Nat :=
  encodedStacks cfg.stk

theorem encodedTape_stackCell (cfg : Turing.PartrecToTM2.Cfg')
    (k : Turing.PartrecToTM2.K') (i : Nat) :
    encodedTape cfg (stackCellPos k i) =
      PartrecToTM2Support.tapeSymbolCode ((cfg.stk k)[i]?) := by
  exact encodedStacks_stackCell cfg.stk k i

/-- Reserved table-machine state used to initialize the fixed input `[0]`. -/
def initState : Nat :=
  0

/-- Shift a TM2 statement-substate index into the table-machine state namespace. -/
def evaluatorStateCode (n : Nat) : Nat :=
  n + 1

/-- Numeric index for a TM2 evaluator substate, including the finite local variable. -/
noncomputable def evaluatorSubstateIndex (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Option Turing.PartrecToTM2.Stmt') : Nat :=
  PartrecToTM2Support.tapeSymbolCode var * (PartrecToTM2Support.statementList tc).length +
    PartrecToTM2Support.statementIndex tc stmt

/-- Table-machine state for a TM2 evaluator substate. -/
noncomputable def statementState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Option Turing.PartrecToTM2.Stmt') : Nat :=
  evaluatorStateCode (evaluatorSubstateIndex tc var stmt)

theorem evaluatorSubstateIndex_lt {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    evaluatorSubstateIndex tc var stmt < 5 * (PartrecToTM2Support.statementList tc).length := by
  have hvar := PartrecToTM2Support.tapeSymbolCode_lt_five var
  have hstmtlt := PartrecToTM2Support.statementIndex_lt_length hstmt
  unfold evaluatorSubstateIndex
  exact lt_of_lt_of_le
    (Nat.add_lt_add_left hstmtlt _)
    (by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hvar))

/-- Number of finite evaluator substates before auxiliary stack-action states. -/
def evaluatorStateCount (tc : Turing.ToPartrec.Code) : Nat :=
  5 * (PartrecToTM2Support.statementList tc).length

/-- Finite auxiliary states currently reserved for `peek` stack actions. -/
def peekAuxStateCount (tc : Turing.ToPartrec.Code) : Nat :=
  evaluatorStateCount tc * 4

/-- Number of possible carried cells during stack shifting. -/
def stackShiftCarryCount : Nat := 5

/-- Reserved finite phase count for future `push`/`pop` stack-shifting microprograms. -/
def stackShiftPhaseCount : Nat := 8

/-- Finite auxiliary states reserved for future `push`/`pop` stack-shifting actions. -/
def stackShiftAuxStateCount (tc : Turing.ToPartrec.Code) : Nat :=
  evaluatorStateCount tc * stackShiftCarryCount * stackShiftPhaseCount * 4

/-- Total number of non-initial table-machine state codes currently reserved. -/
def stateCount (tc : Turing.ToPartrec.Code) : Nat :=
  evaluatorStateCount tc + peekAuxStateCount tc + stackShiftAuxStateCount tc

theorem evaluatorSubstateIndex_lt_stateCount {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    evaluatorSubstateIndex tc var stmt < stateCount tc := by
  have hindex := evaluatorSubstateIndex_lt (tc := tc) (var := var) hstmt
  unfold stateCount evaluatorStateCount
  omega

/-- Finite table-machine states for the TM2 evaluator substates. -/
def evaluatorStates (tc : Turing.ToPartrec.Code) : List Nat :=
  (List.range (evaluatorStateCount tc)).map evaluatorStateCode

/-- Raw finite table-machine state list, including initialization and auxiliary states. -/
def states (tc : Turing.ToPartrec.Code) : List Nat :=
  initState :: (List.range (stateCount tc)).map evaluatorStateCode

theorem states_nodup (tc : Turing.ToPartrec.Code) :
    (states tc).Nodup := by
  unfold states evaluatorStateCode initState
  simp [List.nodup_range.map (by intro a b h; exact Nat.succ.inj h)]

theorem evaluatorStateCode_mem_states {tc : Turing.ToPartrec.Code} {n : Nat}
    (hn : n < stateCount tc) :
    evaluatorStateCode n ∈ states tc := by
  unfold states evaluatorStateCode
  simp [hn]

theorem statementState_mem_states {tc : Turing.ToPartrec.Code}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    {var : Option Turing.PartrecToTM2.Γ'}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    statementState tc var stmt ∈ states tc := by
  unfold statementState
  exact evaluatorStateCode_mem_states (evaluatorSubstateIndex_lt_stateCount hstmt)

/-- Table-machine state that starts the TM2 evaluator after initialization. -/
noncomputable def evalStartState (tc : Turing.ToPartrec.Code) : Nat :=
  statementState tc none (some (Turing.PartrecToTM2.tr (PartrecToTM2Support.startLabel tc)))

/-- Table-machine halting state corresponding to the halted TM2 configuration. -/
noncomputable def haltState (tc : Turing.ToPartrec.Code) : Nat :=
  statementState tc none none

theorem initState_mem_states (tc : Turing.ToPartrec.Code) :
    initState ∈ states tc := by
  simp [states]

theorem evalStartState_mem_states (tc : Turing.ToPartrec.Code) :
    evalStartState tc ∈ states tc := by
  exact statementState_mem_states
    (PartrecToTM2Support.label_statement_mem_list
      (PartrecToTM2Support.startLabel_mem_labelList tc))

theorem haltState_mem_states (tc : Turing.ToPartrec.Code) :
    haltState tc ∈ states tc := by
  exact statementState_mem_states (PartrecToTM2Support.none_mem_statementList tc)

theorem labelState_mem_states {tc : Turing.ToPartrec.Code}
    {q : Turing.PartrecToTM2.Λ'}
    {var : Option Turing.PartrecToTM2.Γ'}
    (hq : q ∈ PartrecToTM2Support.labels tc) :
    statementState tc var (some (Turing.PartrecToTM2.tr q)) ∈ states tc := by
  exact statementState_mem_states (PartrecToTM2Support.label_statement_mem_list_of_label_mem hq)

/-- Shift an auxiliary substate index into the table-machine state namespace. -/
noncomputable def auxStateCode (tc : Turing.ToPartrec.Code) (n : Nat) : Nat :=
  evaluatorStateCode (evaluatorStateCount tc + n)

/-- Auxiliary state index for moving to or from a stack's top cell during `peek`. -/
noncomputable def peekAuxIndex (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt') (offset : Nat) : Nat :=
  evaluatorSubstateIndex tc var (some stmt) * 4 + offset

/-- Auxiliary table-machine state reserved for a `peek` microprogram. -/
noncomputable def peekAuxState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt') (offset : Nat) : Nat :=
  auxStateCode tc (peekAuxIndex tc var stmt offset)

theorem peekAuxIndex_lt_count {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {offset : Nat}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc)
    (hoffset : offset < 4) :
    peekAuxIndex tc var stmt offset < peekAuxStateCount tc := by
  have hidx : evaluatorSubstateIndex tc var (some stmt) < evaluatorStateCount tc := by
    simpa [evaluatorStateCount] using evaluatorSubstateIndex_lt hstmt
  unfold peekAuxIndex peekAuxStateCount
  omega

theorem peekAuxState_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {offset : Nat}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc)
    (hoffset : offset < 4) :
    peekAuxState tc var stmt offset ∈ states tc := by
  unfold peekAuxState auxStateCode
  apply evaluatorStateCode_mem_states
  have hpeek := peekAuxIndex_lt_count (tc := tc) (var := var) (stmt := stmt)
    (offset := offset) hstmt hoffset
  unfold stateCount
  omega

theorem peekAuxState0_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {stmt : Turing.PartrecToTM2.Stmt'}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc) :
    peekAuxState tc var stmt 0 ∈ states tc :=
  peekAuxState_mem_states hstmt (by decide : 0 < 4)

theorem peekAuxState1_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {stmt : Turing.PartrecToTM2.Stmt'}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc) :
    peekAuxState tc var stmt 1 ∈ states tc :=
  peekAuxState_mem_states hstmt (by decide : 1 < 4)

theorem peekAuxState2_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {stmt : Turing.PartrecToTM2.Stmt'}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc) :
    peekAuxState tc var stmt 2 ∈ states tc :=
  peekAuxState_mem_states hstmt (by decide : 2 < 4)

theorem peekAuxState3_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {stmt : Turing.PartrecToTM2.Stmt'}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc) :
    peekAuxState tc var stmt 3 ∈ states tc :=
  peekAuxState_mem_states hstmt (by decide : 3 < 4)

/-- Auxiliary state index for future `push`/`pop` stack-shifting microprograms. -/
noncomputable def stackShiftAuxIndex (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt')
    (carry : Option Turing.PartrecToTM2.Γ') (phase offset : Nat) : Nat :=
  (((evaluatorSubstateIndex tc var (some stmt) * stackShiftCarryCount +
      PartrecToTM2Support.tapeSymbolCode carry) * stackShiftPhaseCount + phase) * 4) +
    offset

/-- Auxiliary table-machine state reserved for a future stack-shifting microprogram. -/
noncomputable def stackShiftAuxState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt')
    (carry : Option Turing.PartrecToTM2.Γ') (phase offset : Nat) : Nat :=
  auxStateCode tc (peekAuxStateCount tc +
    stackShiftAuxIndex tc var stmt carry phase offset)

theorem stackShiftAuxIndex_lt_count {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {carry : Option Turing.PartrecToTM2.Γ'}
    {phase offset : Nat}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc)
    (hphase : phase < stackShiftPhaseCount) (hoffset : offset < 4) :
    stackShiftAuxIndex tc var stmt carry phase offset < stackShiftAuxStateCount tc := by
  have hidx : evaluatorSubstateIndex tc var (some stmt) < evaluatorStateCount tc := by
    simpa [evaluatorStateCount] using evaluatorSubstateIndex_lt hstmt
  have hcarry : PartrecToTM2Support.tapeSymbolCode carry < stackShiftCarryCount := by
    simpa [stackShiftCarryCount] using PartrecToTM2Support.tapeSymbolCode_lt_five carry
  unfold stackShiftAuxIndex stackShiftAuxStateCount stackShiftCarryCount stackShiftPhaseCount at *
  omega

theorem stackShiftAuxState_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {carry : Option Turing.PartrecToTM2.Γ'}
    {phase offset : Nat}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc)
    (hphase : phase < stackShiftPhaseCount) (hoffset : offset < 4) :
    stackShiftAuxState tc var stmt carry phase offset ∈ states tc := by
  unfold stackShiftAuxState auxStateCode
  apply evaluatorStateCode_mem_states
  have hshift := stackShiftAuxIndex_lt_count (tc := tc) (var := var) (stmt := stmt)
    (carry := carry) (phase := phase) (offset := offset) hstmt hphase hoffset
  unfold stateCount
  omega

/-- Encoded control state for a TM2 statement microstate. -/
noncomputable def encodedStmtState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Option Turing.PartrecToTM2.Stmt') : Nat :=
  match stmt with
  | none => haltState tc
  | some stmt => statementState tc var (some stmt)

theorem encodedStmtState_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    encodedStmtState tc var stmt ∈ states tc := by
  cases stmt with
  | none =>
      exact haltState_mem_states tc
  | some stmt =>
      exact statementState_mem_states hstmt

/-- The statement substate corresponding to a full TM2 configuration label. -/
def cfgStmt : Option Turing.PartrecToTM2.Λ' → Option Turing.PartrecToTM2.Stmt'
  | none => none
  | some q => some (Turing.PartrecToTM2.tr q)

/-- Encoded table-machine state of a `PartrecToTM2` configuration. -/
noncomputable def encodedState (tc : Turing.ToPartrec.Code)
    (cfg : Turing.PartrecToTM2.Cfg') : Nat :=
  encodedStmtState tc cfg.var (cfgStmt cfg.l)

theorem encodedState_mem_states {tc : Turing.ToPartrec.Code}
    {cfg : Turing.PartrecToTM2.Cfg'}
    (hlabel : cfg.l ∈ Finset.insertNone (PartrecToTM2Support.labels tc)) :
    encodedState tc cfg ∈ states tc := by
  cases hcfg : cfg.l with
  | none =>
      simpa [encodedState, encodedStmtState, cfgStmt, hcfg] using
        haltState_mem_states tc
  | some q =>
      have hq : q ∈ PartrecToTM2Support.labels tc := by
        exact Finset.some_mem_insertNone.1 (by simpa [hcfg] using hlabel)
      simpa [encodedState, encodedStmtState, cfgStmt, hcfg] using
        labelState_mem_states (var := cfg.var) hq

/--
Representation invariant connecting a one-tape table-machine ID with a
`PartrecToTM2` statement microstate.

The state component records both Mathlib's finite local variable and the
current statement substate. The tape component records the semantically
meaningful interleaved stack cells.
-/
noncomputable def RepresentsSubstate (tc : Turing.ToPartrec.Code) (id : ID)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Option Turing.PartrecToTM2.Stmt')
    (stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ') : Prop :=
  id.head = 0 ∧
    id.state = encodedStmtState tc var stmt ∧
      ∀ k i, id.tape (stackCellPos k i) = encodedStacks stk (stackCellPos k i)

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
  RepresentsSubstate tc id cfg.var (cfgStmt cfg.l) cfg.stk

theorem representsCfg_iff_representsSubstate (tc : Turing.ToPartrec.Code)
    (id : ID) (cfg : Turing.PartrecToTM2.Cfg') :
    RepresentsCfg tc id cfg ↔
      RepresentsSubstate tc id cfg.var (cfgStmt cfg.l) cfg.stk := by
  rfl

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
  · simp [encodedState]
  · intro k i
    rfl

theorem RepresentsCfg.state_mem_states {tc : Turing.ToPartrec.Code}
    {id : ID} {cfg : Turing.PartrecToTM2.Cfg'}
    (h : RepresentsCfg tc id cfg)
    (hlabel : cfg.l ∈ Finset.insertNone (PartrecToTM2Support.labels tc)) :
    id.state ∈ states tc := by
  rw [h.2.1]
  exact encodedState_mem_states hlabel

theorem RepresentsSubstate.tape_head_mem_symbols {tc : Turing.ToPartrec.Code}
    {id : ID} {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    (h : RepresentsSubstate tc id var stmt stk) :
    id.tape id.head ∈ symbols := by
  have htape := h.2.2 Turing.PartrecToTM2.K'.main 0
  rw [h.1]
  rw [show (0 : Nat) = stackCellPos Turing.PartrecToTM2.K'.main 0 by rfl]
  rw [htape]
  exact stackCellSymbol_mem_symbols ((stk Turing.PartrecToTM2.K'.main)[0]?)

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
  simp [encodedState, encodedStmtState, cfgStmt, evalStartState, statementState,
    evaluatorSubstateIndex, PartrecToTM2Support.startLabel, Turing.PartrecToTM2.init]

/-- Symbol written by the fixed-input initialization row. -/
def inputZeroSymbol : Nat :=
  PartrecToTM2Support.tapeSymbolCode (some Turing.PartrecToTM2.Γ'.cons)

theorem inputZeroSymbol_mem_symbols : inputZeroSymbol ∈ symbols :=
  stackCellSymbol_mem_symbols (some Turing.PartrecToTM2.Γ'.cons)

/--
One table row for a statement microstep that does not change the encoded stacks.

The row is parameterized by the symbol it reads so that a finite list of these
rows can cover all tape symbols while preserving the tape cell by writing the
same symbol back.
-/
def stationaryTransition (state read next : Nat) : TableTransition where
  state := state
  read := read
  write := read
  next := next
  move := Move.left

@[simp]
theorem stationaryTransition_state (state read next : Nat) :
    (stationaryTransition state read next).state = state :=
  rfl

@[simp]
theorem stationaryTransition_read (state read next : Nat) :
    (stationaryTransition state read next).read = read :=
  rfl

@[simp]
theorem stationaryTransition_write (state read next : Nat) :
    (stationaryTransition state read next).write = read :=
  rfl

@[simp]
theorem stationaryTransition_next (state read next : Nat) :
    (stationaryTransition state read next).next = next :=
  rfl

@[simp]
theorem stationaryTransition_move (state read next : Nat) :
    (stationaryTransition state read next).move = Move.left :=
  rfl

@[simp]
theorem stationaryTransition_matchesInput (state read next : Nat) :
    (stationaryTransition state read next).matchesInput state read = true := by
  simp [TableTransition.matchesInput]

theorem stationaryTransition_action (state read next : Nat) :
    (stationaryTransition state read next).action = (read, next, Move.left) :=
  rfl

theorem stationaryTransition_write_mem_symbols {state read next : Nat}
    (hread : read ∈ symbols) :
    (stationaryTransition state read next).write ∈ symbols :=
  hread

/-- Finite row family covering all possible read symbols for a stationary microstep. -/
def stationaryRows (state next : Nat) : List TableTransition :=
  symbols.map fun read => stationaryTransition state read next

theorem stationaryTransition_mem_stationaryRows {state read next : Nat}
    (hread : read ∈ symbols) :
    stationaryTransition state read next ∈ stationaryRows state next :=
  List.mem_map.2 ⟨read, hread, rfl⟩

theorem stationaryRows_write_mem_symbols {state next : Nat}
    {e : TableTransition}
    (he : e ∈ stationaryRows state next) :
    e.write ∈ symbols := by
  rcases List.mem_map.1 he with ⟨read, hread, rfl⟩
  exact hread

theorem stationaryRows_find?_eq_some {state read next : Nat}
    (hread : read ∈ symbols) :
    (stationaryRows state next).find?
        (fun e => e.matchesInput state read) =
      some (stationaryTransition state read next) := by
  have hlt : read < 5 := by
    simpa [symbols, PartrecToTM2Support.tapeSymbols] using hread
  cases read with
  | zero =>
      simp [stationaryRows, symbols, PartrecToTM2Support.tapeSymbols,
        TableTransition.matchesInput]
  | succ read =>
      cases read with
      | zero =>
          simp [stationaryRows, symbols, PartrecToTM2Support.tapeSymbols,
            TableTransition.matchesInput]
      | succ read =>
          cases read with
          | zero =>
              simp [stationaryRows, symbols, PartrecToTM2Support.tapeSymbols,
                TableTransition.matchesInput]
              omega
          | succ read =>
              cases read with
              | zero =>
                  simp [stationaryRows, symbols, PartrecToTM2Support.tapeSymbols,
                    TableTransition.matchesInput]
                  omega
              | succ read =>
                  cases read with
                  | zero =>
                      simp [stationaryRows, symbols, PartrecToTM2Support.tapeSymbols,
                        TableTransition.matchesInput]
                      omega
                  | succ read =>
                      omega

theorem toMachine_nextID_of_stationaryTransition {P : TableProgram} {id : ID}
    {next : Nat}
    (hhead : id.head = 0)
    (hstate : id.state ≠ P.halt)
    (hfind :
      P.toTableMachine.transition? id.state (id.tape id.head) =
        some (stationaryTransition id.state (id.tape id.head) next))
    (hread : id.tape id.head ∈ P.supportedSymbols)
    (hnext : next ∈ P.supportedStates) :
    P.toMachine.nextID id =
      { tape := id.tape
        head := 0
        state := next } := by
  have hwrite :
      (stationaryTransition id.state (id.tape id.head) next).write ∈
        P.supportedSymbols := by
    simpa using hread
  have hnext' :
      (stationaryTransition id.state (id.tape id.head) next).next ∈
        P.supportedStates := by
    simpa using hnext
  rw [TableProgram.toMachine_nextID_of_transition?_eq_some hstate hfind hwrite hnext']
  cases id with
  | mk tape head state =>
      change head = 0 at hhead
      subst head
      simp only [stationaryTransition_write, stationaryTransition_move, stationaryTransition_next,
        ID.mk.injEq, and_true]
      constructor
      · funext i
        by_cases hi : i = 0 <;> simp [hi]
      · simp [Move.apply]

theorem toMachine_nextID_stationary_representsSubstate
    {P : TableProgram} {tc : Turing.ToPartrec.Code} {id : ID}
    {var nextVar : Option Turing.PartrecToTM2.Γ'}
    {stmt nextStmt : Option Turing.PartrecToTM2.Stmt'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    (hrep : RepresentsSubstate tc id var stmt stk)
    (hstate : id.state ≠ P.halt)
    (hfind :
      P.toTableMachine.transition? id.state (id.tape id.head) =
        some (stationaryTransition id.state (id.tape id.head)
          (encodedStmtState tc nextVar nextStmt)))
    (hread : id.tape id.head ∈ P.supportedSymbols)
    (hnext : encodedStmtState tc nextVar nextStmt ∈ P.supportedStates) :
    RepresentsSubstate tc (P.toMachine.nextID id) nextVar nextStmt stk := by
  rw [toMachine_nextID_of_stationaryTransition hrep.1 hstate hfind hread hnext]
  constructor
  · rfl
  constructor
  · rfl
  · exact hrep.2.2

/--
One table row that writes back the read symbol and moves in the given direction.

This is used by bounded `peek` travel and return fragments, where the tape
contents should not change while the head moves between stack columns.
-/
def sameWriteMoveTransition (state read next : Nat) (move : Move) : TableTransition where
  state := state
  read := read
  write := read
  next := next
  move := move

@[simp]
theorem sameWriteMoveTransition_state (state read next : Nat) (move : Move) :
    (sameWriteMoveTransition state read next move).state = state :=
  rfl

@[simp]
theorem sameWriteMoveTransition_read (state read next : Nat) (move : Move) :
    (sameWriteMoveTransition state read next move).read = read :=
  rfl

@[simp]
theorem sameWriteMoveTransition_write (state read next : Nat) (move : Move) :
    (sameWriteMoveTransition state read next move).write = read :=
  rfl

@[simp]
theorem sameWriteMoveTransition_next (state read next : Nat) (move : Move) :
    (sameWriteMoveTransition state read next move).next = next :=
  rfl

@[simp]
theorem sameWriteMoveTransition_move (state read next : Nat) (move : Move) :
    (sameWriteMoveTransition state read next move).move = move :=
  rfl

@[simp]
theorem sameWriteMoveTransition_matchesInput (state read next : Nat) (move : Move) :
    (sameWriteMoveTransition state read next move).matchesInput state read = true := by
  simp [TableTransition.matchesInput]

theorem sameWriteMoveTransition_write_mem_symbols {state read next : Nat} {move : Move}
    (hread : read ∈ symbols) :
    (sameWriteMoveTransition state read next move).write ∈ symbols :=
  hread

/-- Finite row family covering all possible read symbols for a same-write move. -/
def sameWriteMoveRows (state next : Nat) (move : Move) : List TableTransition :=
  symbols.map fun read => sameWriteMoveTransition state read next move

theorem sameWriteMoveTransition_mem_rows {state read next : Nat} {move : Move}
    (hread : read ∈ symbols) :
    sameWriteMoveTransition state read next move ∈ sameWriteMoveRows state next move :=
  List.mem_map.2 ⟨read, hread, rfl⟩

theorem sameWriteMoveRows_write_mem_symbols {state next : Nat} {move : Move}
    {e : TableTransition}
    (he : e ∈ sameWriteMoveRows state next move) :
    e.write ∈ symbols := by
  rcases List.mem_map.1 he with ⟨read, hread, rfl⟩
  exact hread

theorem sameWriteMoveRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {state next : Nat} {move : Move}
    {e : TableTransition} (he : e ∈ sameWriteMoveRows state next move)
    (hnext : next ∈ states tc) :
    e.next ∈ states tc := by
  rcases List.mem_map.1 he with ⟨_read, _hread, rfl⟩
  exact hnext

/-- Phase used while moving from head `0` to the selected stack column. -/
def stackShiftTravelPhase : Nat := 0

theorem stackShiftTravelPhase_lt_count :
    stackShiftTravelPhase < stackShiftPhaseCount := by
  decide

/-- Auxiliary state used while traveling to a stack column with a carried cell. -/
noncomputable def stackShiftTravelState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt')
    (carry : Option Turing.PartrecToTM2.Γ') (offset : Nat) : Nat :=
  stackShiftAuxState tc var stmt carry stackShiftTravelPhase offset

theorem stackShiftTravelState_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {carry : Option Turing.PartrecToTM2.Γ'}
    {offset : Nat}
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc)
    (hoffset : offset < 4) :
    stackShiftTravelState tc var stmt carry offset ∈ states tc :=
  stackShiftAuxState_mem_states hstmt stackShiftTravelPhase_lt_count hoffset

/-- State reached once the bounded travel prefix is positioned at stack column `k`. -/
noncomputable def stackShiftTargetState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt')
    (carry : Option Turing.PartrecToTM2.Γ') (k : Turing.PartrecToTM2.K') :
    Nat :=
  match PartrecToTM2Support.stackNameCode k with
  | 0 => encodedStmtState tc var (some stmt)
  | offset => stackShiftTravelState tc var stmt carry offset

set_option linter.flexible false in
theorem stackShiftTargetState_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {carry : Option Turing.PartrecToTM2.Γ'}
    (k : Turing.PartrecToTM2.K')
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc) :
    stackShiftTargetState tc var stmt carry k ∈ states tc := by
  cases k <;>
    simp [stackShiftTargetState, PartrecToTM2Support.stackNameCode]
  · exact encodedStmtState_mem_states hstmt
  · exact stackShiftTravelState_mem_states hstmt (by decide : 1 < 4)
  · exact stackShiftTravelState_mem_states hstmt (by decide : 2 < 4)
  · exact stackShiftTravelState_mem_states hstmt (by decide : 3 < 4)

/--
Bounded prefix rows that move from head `0` to the selected stack column while
preserving all traversed cells and remembering the carried stack cell in the
control state.
-/
noncomputable def stackShiftTravelRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (stmt : Turing.PartrecToTM2.Stmt')
    (carry : Option Turing.PartrecToTM2.Γ') (k : Turing.PartrecToTM2.K') :
    List TableTransition :=
  let start := encodedStmtState tc var (some stmt)
  match PartrecToTM2Support.stackNameCode k with
  | 0 => []
  | 1 =>
      sameWriteMoveRows start (stackShiftTravelState tc var stmt carry 1) Move.right
  | 2 =>
      sameWriteMoveRows start (stackShiftTravelState tc var stmt carry 1) Move.right ++
      sameWriteMoveRows (stackShiftTravelState tc var stmt carry 1)
        (stackShiftTravelState tc var stmt carry 2) Move.right
  | _ =>
      sameWriteMoveRows start (stackShiftTravelState tc var stmt carry 1) Move.right ++
      sameWriteMoveRows (stackShiftTravelState tc var stmt carry 1)
        (stackShiftTravelState tc var stmt carry 2) Move.right ++
      sameWriteMoveRows (stackShiftTravelState tc var stmt carry 2)
        (stackShiftTravelState tc var stmt carry 3) Move.right

set_option linter.flexible false in
theorem stackShiftTravelRows_write_mem_symbols {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {carry : Option Turing.PartrecToTM2.Γ'}
    {k : Turing.PartrecToTM2.K'} {e : TableTransition}
    (he : e ∈ stackShiftTravelRows tc var stmt carry k) :
    e.write ∈ symbols := by
  cases k <;>
    simp [stackShiftTravelRows, PartrecToTM2Support.stackNameCode] at he
  · exact sameWriteMoveRows_write_mem_symbols he
  · rcases he with he | he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact sameWriteMoveRows_write_mem_symbols he
  · rcases he with he | he | he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact sameWriteMoveRows_write_mem_symbols he

set_option linter.flexible false in
theorem stackShiftTravelRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Turing.PartrecToTM2.Stmt'} {carry : Option Turing.PartrecToTM2.Γ'}
    {k : Turing.PartrecToTM2.K'} {e : TableTransition}
    (he : e ∈ stackShiftTravelRows tc var stmt carry k)
    (hstmt : some stmt ∈ PartrecToTM2Support.statementList tc) :
    e.next ∈ states tc := by
  cases k <;>
    simp [stackShiftTravelRows, PartrecToTM2Support.stackNameCode] at he
  · apply sameWriteMoveRows_next_mem_states he
    exact stackShiftTravelState_mem_states hstmt (by decide : 1 < 4)
  · rcases he with he | he
    · apply sameWriteMoveRows_next_mem_states he
      exact stackShiftTravelState_mem_states hstmt (by decide : 1 < 4)
    · apply sameWriteMoveRows_next_mem_states he
      exact stackShiftTravelState_mem_states hstmt (by decide : 2 < 4)
  · rcases he with he | he | he
    · apply sameWriteMoveRows_next_mem_states he
      exact stackShiftTravelState_mem_states hstmt (by decide : 1 < 4)
    · apply sameWriteMoveRows_next_mem_states he
      exact stackShiftTravelState_mem_states hstmt (by decide : 2 < 4)
    · apply sameWriteMoveRows_next_mem_states he
      exact stackShiftTravelState_mem_states hstmt (by decide : 3 < 4)

/-- Return state after a `peek` read has moved one step left. -/
noncomputable def peekReturnState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') (q : Turing.PartrecToTM2.Stmt')
    (offset : Nat) : Nat :=
  match offset with
  | 0 => encodedStmtState tc var (some q)
  | offset + 1 => peekAuxState tc var q offset

theorem peekReturnState_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {q : Turing.PartrecToTM2.Stmt'}
    {offset : Nat}
    (hq : some q ∈ PartrecToTM2Support.statementList tc)
    (hoffset : offset < 4) :
    peekReturnState tc var q offset ∈ states tc := by
  cases offset with
  | zero =>
      exact encodedStmtState_mem_states hq
  | succ offset =>
      apply peekAuxState_mem_states hq
      omega

/--
Rows that read a decoded top-of-stack symbol during `peek`.

The row writes the same symbol back, moves left, and enters the state determined
by applying the TM2 local-variable update to the decoded symbol.
-/
noncomputable def peekReadRows (tc : Turing.ToPartrec.Code)
    (readState : Nat)
    (var : Option Turing.PartrecToTM2.Γ')
    (f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt') (returnOffset : Nat) :
    List TableTransition :=
  cellSymbols.map fun s =>
    { state := readState
      read := PartrecToTM2Support.tapeSymbolCode s
      write := PartrecToTM2Support.tapeSymbolCode s
      next := peekReturnState tc (f var s) q returnOffset
      move := Move.left }

theorem peekReadTransition_mem_rows {tc : Turing.ToPartrec.Code}
    {readState : Nat} {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {returnOffset : Nat}
    {s : Option Turing.PartrecToTM2.Γ'} (hs : s ∈ cellSymbols) :
    ({ state := readState
       read := PartrecToTM2Support.tapeSymbolCode s
       write := PartrecToTM2Support.tapeSymbolCode s
       next := peekReturnState tc (f var s) q returnOffset
       move := Move.left } : TableTransition) ∈
      peekReadRows tc readState var f q returnOffset :=
  List.mem_map.2 ⟨s, hs, rfl⟩

theorem peekReadRows_write_mem_symbols {tc : Turing.ToPartrec.Code}
    {readState : Nat} {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {returnOffset : Nat}
    {e : TableTransition}
    (he : e ∈ peekReadRows tc readState var f q returnOffset) :
    e.write ∈ symbols := by
  rcases List.mem_map.1 he with ⟨s, hs, rfl⟩
  exact tapeSymbolCode_mem_symbols s

theorem peekReadRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {readState : Nat} {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {returnOffset : Nat}
    {e : TableTransition}
    (he : e ∈ peekReadRows tc readState var f q returnOffset)
    (hq : some q ∈ PartrecToTM2Support.statementList tc)
    (hoffset : returnOffset < 4) :
    e.next ∈ states tc := by
  rcases List.mem_map.1 he with ⟨s, _hs, rfl⟩
  exact peekReturnState_mem_states hq hoffset

/-- Return rows for one possible decoded `peek` result. -/
noncomputable def peekReturnMoveRowsForVar (tc : Turing.ToPartrec.Code)
    (postVar : Option Turing.PartrecToTM2.Γ') (q : Turing.PartrecToTM2.Stmt')
    (offset : Nat) : List TableTransition :=
  sameWriteMoveRows
    (peekAuxState tc postVar q offset)
    (peekReturnState tc postVar q offset)
    Move.left

/-- Return rows for all possible decoded `peek` results. -/
noncomputable def peekReturnMoveRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt') (offset : Nat) :
    List TableTransition :=
  (cellSymbols.map fun s => peekReturnMoveRowsForVar tc (f var s) q offset).flatten

theorem peekReturnMoveRowsForVar_write_mem_symbols {tc : Turing.ToPartrec.Code}
    {postVar : Option Turing.PartrecToTM2.Γ'} {q : Turing.PartrecToTM2.Stmt'}
    {offset : Nat} {e : TableTransition}
    (he : e ∈ peekReturnMoveRowsForVar tc postVar q offset) :
    e.write ∈ symbols :=
  sameWriteMoveRows_write_mem_symbols he

theorem peekReturnMoveRowsForVar_next_mem_states {tc : Turing.ToPartrec.Code}
    {postVar : Option Turing.PartrecToTM2.Γ'} {q : Turing.PartrecToTM2.Stmt'}
    {offset : Nat} {e : TableTransition}
    (he : e ∈ peekReturnMoveRowsForVar tc postVar q offset)
    (hq : some q ∈ PartrecToTM2Support.statementList tc) (hoffset : offset < 4) :
    e.next ∈ states tc :=
  sameWriteMoveRows_next_mem_states he (peekReturnState_mem_states hq hoffset)

theorem peekReturnMoveRows_write_mem_symbols {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {offset : Nat} {e : TableTransition}
    (he : e ∈ peekReturnMoveRows tc var f q offset) :
    e.write ∈ symbols := by
  unfold peekReturnMoveRows at he
  rcases List.mem_flatten.1 he with ⟨rows, hrows, he⟩
  rcases List.mem_map.1 hrows with ⟨s, _hs, rfl⟩
  exact peekReturnMoveRowsForVar_write_mem_symbols he

theorem peekReturnMoveRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {offset : Nat} {e : TableTransition}
    (he : e ∈ peekReturnMoveRows tc var f q offset)
    (hq : some q ∈ PartrecToTM2Support.statementList tc) (hoffset : offset < 4) :
    e.next ∈ states tc := by
  unfold peekReturnMoveRows at he
  rcases List.mem_flatten.1 he with ⟨rows, hrows, he⟩
  rcases List.mem_map.1 hrows with ⟨s, _hs, rfl⟩
  exact peekReturnMoveRowsForVar_next_mem_states he hq hoffset

/-- Originating TM2 `peek` statement. -/
def peekStmt (k : Turing.PartrecToTM2.K')
    (f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt') : Turing.PartrecToTM2.Stmt' :=
  Turing.TM2.Stmt.peek k f q

/-- First auxiliary state reached when moving right toward a stack column. -/
noncomputable def peekMoveState (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') (stmt : Turing.PartrecToTM2.Stmt')
    (offset : Nat) : Nat :=
  peekAuxState tc var stmt offset

/-- Complete bounded row family for a `peek` stack action. -/
noncomputable def peekRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') (k : Turing.PartrecToTM2.K')
    (f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt') : List TableTransition :=
  let origin := peekStmt k f q
  let start := encodedStmtState tc var (some origin)
  match PartrecToTM2Support.stackNameCode k with
  | 0 =>
      peekReadRows tc start var f q 0
  | 1 =>
      sameWriteMoveRows start (peekMoveState tc var origin 1) Move.right ++
      peekReadRows tc (peekMoveState tc var origin 1) var f q 1 ++
      peekReturnMoveRows tc var f q 0
  | 2 =>
      sameWriteMoveRows start (peekMoveState tc var origin 1) Move.right ++
      sameWriteMoveRows (peekMoveState tc var origin 1)
        (peekMoveState tc var origin 2) Move.right ++
      peekReadRows tc (peekMoveState tc var origin 2) var f q 2 ++
      peekReturnMoveRows tc var f q 1 ++
      peekReturnMoveRows tc var f q 0
  | _ =>
      sameWriteMoveRows start (peekMoveState tc var origin 1) Move.right ++
      sameWriteMoveRows (peekMoveState tc var origin 1)
        (peekMoveState tc var origin 2) Move.right ++
      sameWriteMoveRows (peekMoveState tc var origin 2)
        (peekMoveState tc var origin 3) Move.right ++
      peekReadRows tc (peekMoveState tc var origin 3) var f q 3 ++
      peekReturnMoveRows tc var f q 2 ++
      peekReturnMoveRows tc var f q 1 ++
      peekReturnMoveRows tc var f q 0

set_option linter.flexible false in
theorem peekRows_write_mem_symbols {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {k : Turing.PartrecToTM2.K'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {e : TableTransition}
    (he : e ∈ peekRows tc var k f q) :
    e.write ∈ symbols := by
  cases k <;>
    simp [peekRows, PartrecToTM2Support.stackNameCode] at he
  · exact peekReadRows_write_mem_symbols he
  · rcases he with he | he | he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact peekReadRows_write_mem_symbols he
    · exact peekReturnMoveRows_write_mem_symbols he
  · rcases he with he | he | he | he | he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact peekReadRows_write_mem_symbols he
    · exact peekReturnMoveRows_write_mem_symbols he
    · exact peekReturnMoveRows_write_mem_symbols he
  · rcases he with he | he | he | he | he | he | he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact sameWriteMoveRows_write_mem_symbols he
    · exact peekReadRows_write_mem_symbols he
    · exact peekReturnMoveRows_write_mem_symbols he
    · exact peekReturnMoveRows_write_mem_symbols he
    · exact peekReturnMoveRows_write_mem_symbols he

set_option linter.flexible false in
theorem peekRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {k : Turing.PartrecToTM2.K'}
    {f : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ' →
      Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {e : TableTransition}
    (he : e ∈ peekRows tc var k f q)
    (horigin : some (peekStmt k f q) ∈ PartrecToTM2Support.statementList tc)
    (hq : some q ∈ PartrecToTM2Support.statementList tc) :
    e.next ∈ states tc := by
  cases k <;>
    simp [peekRows, PartrecToTM2Support.stackNameCode] at he
  · exact peekReadRows_next_mem_states he hq (by decide : 0 < 4)
  · rcases he with he | he | he
    · apply sameWriteMoveRows_next_mem_states he
      simpa [peekMoveState] using peekAuxState1_mem_states horigin
    · exact peekReadRows_next_mem_states he hq (by decide : 1 < 4)
    · exact peekReturnMoveRows_next_mem_states he hq (by decide : 0 < 4)
  · rcases he with he | he | he | he | he
    · apply sameWriteMoveRows_next_mem_states he
      simpa [peekMoveState] using peekAuxState1_mem_states horigin
    · apply sameWriteMoveRows_next_mem_states he
      simpa [peekMoveState] using peekAuxState2_mem_states horigin
    · exact peekReadRows_next_mem_states he hq (by decide : 2 < 4)
    · exact peekReturnMoveRows_next_mem_states he hq (by decide : 1 < 4)
    · exact peekReturnMoveRows_next_mem_states he hq (by decide : 0 < 4)
  · rcases he with he | he | he | he | he | he | he
    · apply sameWriteMoveRows_next_mem_states he
      simpa [peekMoveState] using peekAuxState1_mem_states horigin
    · apply sameWriteMoveRows_next_mem_states he
      simpa [peekMoveState] using peekAuxState2_mem_states horigin
    · apply sameWriteMoveRows_next_mem_states he
      simpa [peekMoveState] using peekAuxState3_mem_states horigin
    · exact peekReadRows_next_mem_states he hq (by decide : 3 < 4)
    · exact peekReturnMoveRows_next_mem_states he hq (by decide : 2 < 4)
    · exact peekReturnMoveRows_next_mem_states he hq (by decide : 1 < 4)
    · exact peekReturnMoveRows_next_mem_states he hq (by decide : 0 < 4)

/-- Stationary rows for a TM2 `load` microstep. -/
noncomputable def loadRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (a : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ')
    (q : Turing.PartrecToTM2.Stmt') : List TableTransition :=
  stationaryRows
    (encodedStmtState tc var (some (Turing.TM2.Stmt.load a q)))
    (encodedStmtState tc (a var) (some q))

theorem loadTransition_mem_loadRows {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {a : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'} {read : Nat}
    (hread : read ∈ symbols) :
    stationaryTransition
        (encodedStmtState tc var (some (Turing.TM2.Stmt.load a q))) read
        (encodedStmtState tc (a var) (some q)) ∈
      loadRows tc var a q :=
  stationaryTransition_mem_stationaryRows hread

theorem loadRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {a : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'}
    (hq : some q ∈ PartrecToTM2Support.statementList tc) :
    encodedStmtState tc (a var) (some q) ∈ states tc :=
  encodedStmtState_mem_states hq

/-- Stationary rows for a TM2 `branch` microstep. -/
noncomputable def branchRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (p : Option Turing.PartrecToTM2.Γ' → Bool)
    (q₁ q₂ : Turing.PartrecToTM2.Stmt') : List TableTransition :=
  stationaryRows
    (encodedStmtState tc var (some (Turing.TM2.Stmt.branch p q₁ q₂)))
    (encodedStmtState tc var (some (cond (p var) q₁ q₂)))

theorem branchTransition_mem_branchRows {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {p : Option Turing.PartrecToTM2.Γ' → Bool}
    {q₁ q₂ : Turing.PartrecToTM2.Stmt'} {read : Nat}
    (hread : read ∈ symbols) :
    stationaryTransition
        (encodedStmtState tc var (some (Turing.TM2.Stmt.branch p q₁ q₂))) read
        (encodedStmtState tc var (some (cond (p var) q₁ q₂))) ∈
      branchRows tc var p q₁ q₂ :=
  stationaryTransition_mem_stationaryRows hread

theorem branchRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {p : Option Turing.PartrecToTM2.Γ' → Bool}
    {q₁ q₂ : Turing.PartrecToTM2.Stmt'}
    (hq₁ : some q₁ ∈ PartrecToTM2Support.statementList tc)
    (hq₂ : some q₂ ∈ PartrecToTM2Support.statementList tc) :
    encodedStmtState tc var (some (cond (p var) q₁ q₂)) ∈ states tc := by
  by_cases hp : p var = true
  · simpa [hp] using encodedStmtState_mem_states (tc := tc) (var := var) hq₁
  · have hpfalse : p var = false := by
      cases h : p var <;> simp [h] at hp ⊢
    simpa [hpfalse] using encodedStmtState_mem_states (tc := tc) (var := var) hq₂

/-- Stationary rows for a TM2 `goto` microstep. -/
noncomputable def gotoRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ')
    (f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ') :
    List TableTransition :=
  stationaryRows
    (encodedStmtState tc var (some (Turing.TM2.Stmt.goto f)))
    (encodedStmtState tc var (cfgStmt (some (f var))))

theorem gotoTransition_mem_gotoRows {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ'} {read : Nat}
    (hread : read ∈ symbols) :
    stationaryTransition
        (encodedStmtState tc var (some (Turing.TM2.Stmt.goto f))) read
        (encodedStmtState tc var (cfgStmt (some (f var)))) ∈
      gotoRows tc var f :=
  stationaryTransition_mem_stationaryRows hread

theorem gotoRows_next_mem_states {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ'}
    (hf : f var ∈ PartrecToTM2Support.labels tc) :
    encodedStmtState tc var (cfgStmt (some (f var))) ∈ states tc := by
  simpa [cfgStmt, encodedStmtState] using labelState_mem_states (var := var) hf

/-- Stationary rows for a TM2 `halt` microstep. -/
noncomputable def haltRows (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') : List TableTransition :=
  stationaryRows
    (encodedStmtState tc var (some (Turing.TM2.Stmt.halt)))
    (encodedStmtState tc var none)

theorem haltTransition_mem_haltRows {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {read : Nat}
    (hread : read ∈ symbols) :
    stationaryTransition
        (encodedStmtState tc var (some (Turing.TM2.Stmt.halt))) read
        (encodedStmtState tc var none) ∈
      haltRows tc var :=
  stationaryTransition_mem_stationaryRows hread

theorem haltRows_next_mem_states (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') :
    encodedStmtState tc var none ∈ states tc := by
  exact haltState_mem_states tc

/-- A child statement of a supported statement is also in the finite statement list. -/
theorem childStmt_mem_statementList {tc : Turing.ToPartrec.Code}
    {parent child : Turing.PartrecToTM2.Stmt'}
    (hchild : child ∈ Turing.TM2.stmts₁ parent)
    (hparent : some parent ∈ PartrecToTM2Support.statementList tc) :
    some child ∈ PartrecToTM2Support.statementList tc := by
  exact PartrecToTM2Support.mem_statementList.2
    (Turing.TM2.stmts_trans hchild
      (PartrecToTM2Support.mem_statementList.1 hparent))

/--
Rows currently implemented for one supported statement substate.

The stack-shifting `push` and `pop` microprograms are intentionally left empty
here; their rows need the unbounded stack-tail shift machinery. The implemented
fragment covers the stationary statement forms and the bounded read-only
`peek` action.
-/
noncomputable def implementedStatementRowsForStmt (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') :
    Option Turing.PartrecToTM2.Stmt' → List TableTransition
  | none => []
  | some (Turing.TM2.Stmt.push _ _ _) => []
  | some (Turing.TM2.Stmt.peek k f q) => peekRows tc var k f q
  | some (Turing.TM2.Stmt.pop _ _ _) => []
  | some (Turing.TM2.Stmt.load a q) => loadRows tc var a q
  | some (Turing.TM2.Stmt.branch p q₁ q₂) => branchRows tc var p q₁ q₂
  | some (Turing.TM2.Stmt.goto f) => gotoRows tc var f
  | some Turing.TM2.Stmt.halt => haltRows tc var

theorem implementedStatementRowsForStmt_write_mem_symbols
    {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'} {e : TableTransition}
    (he : e ∈ implementedStatementRowsForStmt tc var stmt) :
    e.write ∈ symbols := by
  cases stmt with
  | none =>
      simp [implementedStatementRowsForStmt] at he
  | some stmt =>
      cases stmt with
      | push k f q =>
          simp [implementedStatementRowsForStmt] at he
      | peek k f q =>
          exact peekRows_write_mem_symbols he
      | pop k f q =>
          simp [implementedStatementRowsForStmt] at he
      | load a q =>
          exact stationaryRows_write_mem_symbols he
      | branch p q₁ q₂ =>
          exact stationaryRows_write_mem_symbols he
      | goto f =>
          exact stationaryRows_write_mem_symbols he
      | halt =>
          exact stationaryRows_write_mem_symbols he

theorem implementedStatementRowsForStmt_next_mem_states
    {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'} {e : TableTransition}
    (he : e ∈ implementedStatementRowsForStmt tc var stmt)
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    e.next ∈ states tc := by
  cases stmt with
  | none =>
      simp [implementedStatementRowsForStmt] at he
  | some stmt =>
      cases stmt with
      | push k f q =>
          simp [implementedStatementRowsForStmt] at he
      | peek k f q =>
          have hq : some q ∈ PartrecToTM2Support.statementList tc :=
            childStmt_mem_statementList
              (parent := Turing.TM2.Stmt.peek k f q) (child := q)
              (by
                classical
                unfold Turing.TM2.stmts₁
                exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self)
              hstmt
          exact peekRows_next_mem_states he hstmt hq
      | pop k f q =>
          simp [implementedStatementRowsForStmt] at he
      | load a q =>
          have hq : some q ∈ PartrecToTM2Support.statementList tc :=
            childStmt_mem_statementList
              (parent := Turing.TM2.Stmt.load a q) (child := q)
              (by
                classical
                unfold Turing.TM2.stmts₁
                exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self)
              hstmt
          rcases List.mem_map.1 he with ⟨read, hread, rfl⟩
          exact loadRows_next_mem_states hq
      | branch p q₁ q₂ =>
          have hq₁ : some q₁ ∈ PartrecToTM2Support.statementList tc :=
            childStmt_mem_statementList
              (parent := Turing.TM2.Stmt.branch p q₁ q₂) (child := q₁)
              (by
                classical
                unfold Turing.TM2.stmts₁
                exact Finset.mem_insert_of_mem
                  (Finset.mem_union_left _ Turing.TM2.stmts₁_self))
              hstmt
          have hq₂ : some q₂ ∈ PartrecToTM2Support.statementList tc :=
            childStmt_mem_statementList
              (parent := Turing.TM2.Stmt.branch p q₁ q₂) (child := q₂)
              (by
                classical
                unfold Turing.TM2.stmts₁
                exact Finset.mem_insert_of_mem
                  (Finset.mem_union_right _ Turing.TM2.stmts₁_self))
              hstmt
          rcases List.mem_map.1 he with ⟨read, hread, rfl⟩
          exact branchRows_next_mem_states hq₁ hq₂
      | goto f =>
          have hsupport :=
            PartrecToTM2Support.statement_supports
              (PartrecToTM2Support.mem_statementList.1 hstmt)
          rcases List.mem_map.1 he with ⟨read, hread, rfl⟩
          exact gotoRows_next_mem_states (hsupport var)
      | halt =>
          rcases List.mem_map.1 he with ⟨read, hread, rfl⟩
          exact haltRows_next_mem_states tc var

/-- Implemented rows for all supported statement substates at one local-variable value. -/
noncomputable def implementedStatementRowsForVar (tc : Turing.ToPartrec.Code)
    (var : Option Turing.PartrecToTM2.Γ') : List TableTransition :=
  ((PartrecToTM2Support.statementList tc).map
    fun stmt => implementedStatementRowsForStmt tc var stmt).flatten

theorem implementedStatementRowsForVar_write_mem_symbols
    {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {e : TableTransition}
    (he : e ∈ implementedStatementRowsForVar tc var) :
    e.write ∈ symbols := by
  unfold implementedStatementRowsForVar at he
  rcases List.mem_flatten.1 he with ⟨rows, hrows, he⟩
  rcases List.mem_map.1 hrows with ⟨stmt, _hstmt, rfl⟩
  exact implementedStatementRowsForStmt_write_mem_symbols he

theorem implementedStatementRowsForVar_next_mem_states
    {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'} {e : TableTransition}
    (he : e ∈ implementedStatementRowsForVar tc var) :
    e.next ∈ states tc := by
  unfold implementedStatementRowsForVar at he
  rcases List.mem_flatten.1 he with ⟨rows, hrows, he⟩
  rcases List.mem_map.1 hrows with ⟨stmt, hstmt, rfl⟩
  exact implementedStatementRowsForStmt_next_mem_states he hstmt

/-- Concrete table fragment for all currently implemented `PartrecToTM2` statement rows. -/
noncomputable def implementedStatementRows (tc : Turing.ToPartrec.Code) :
    List TableTransition :=
  (cellSymbols.map fun var => implementedStatementRowsForVar tc var).flatten

theorem implementedStatementRows_write_mem_symbols
    {tc : Turing.ToPartrec.Code} {e : TableTransition}
    (he : e ∈ implementedStatementRows tc) :
    e.write ∈ symbols := by
  unfold implementedStatementRows at he
  rcases List.mem_flatten.1 he with ⟨rows, hrows, he⟩
  rcases List.mem_map.1 hrows with ⟨var, _hvar, rfl⟩
  exact implementedStatementRowsForVar_write_mem_symbols he

theorem implementedStatementRows_next_mem_states
    {tc : Turing.ToPartrec.Code} {e : TableTransition}
    (he : e ∈ implementedStatementRows tc) :
    e.next ∈ states tc := by
  unfold implementedStatementRows at he
  rcases List.mem_flatten.1 he with ⟨rows, hrows, he⟩
  rcases List.mem_map.1 hrows with ⟨var, _hvar, rfl⟩
  exact implementedStatementRowsForVar_next_mem_states he

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

theorem RepresentsSubstate.tape_head_mem_supportedSymbols {tc : Turing.ToPartrec.Code}
    {id : ID} {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    {table : List TableTransition}
    (h : RepresentsSubstate tc id var stmt stk) :
    id.tape id.head ∈ (programWithTable tc table).supportedSymbols := by
  change id.tape id.head ∈ blankSymbol :: symbols
  exact List.mem_cons_of_mem blankSymbol h.tape_head_mem_symbols

theorem programWithTable_stationaryRows_transition?
    (tc : Turing.ToPartrec.Code) (state read next : Nat)
    (hread : read ∈ symbols) :
    (programWithTable tc (stationaryRows state next)).toTableMachine.transition?
        state read =
      some (stationaryTransition state read next) := by
  unfold TableMachine.transition?
  simpa [programWithTable, TableProgram.toTableMachine, TableProgram.supportedSymbols,
    TableProgram.supportedStates] using
    stationaryRows_find?_eq_some (state := state) (next := next) hread

theorem encodedStmtState_mem_supportedStates {tc : Turing.ToPartrec.Code}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stmt : Option Turing.PartrecToTM2.Stmt'}
    {table : List TableTransition}
    (hstmt : stmt ∈ PartrecToTM2Support.statementList tc) :
    encodedStmtState tc var stmt ∈ (programWithTable tc table).supportedStates := by
  change encodedStmtState tc var stmt ∈ initState :: haltState tc :: states tc
  exact List.mem_cons_of_mem initState
    (List.mem_cons_of_mem (haltState tc) (encodedStmtState_mem_states hstmt))

theorem loadRows_nextID_representsSubstate
    {tc : Turing.ToPartrec.Code} {id : ID}
    {var : Option Turing.PartrecToTM2.Γ'}
    {a : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ'}
    {q : Turing.PartrecToTM2.Stmt'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    (hrep : RepresentsSubstate tc id var (some (Turing.TM2.Stmt.load a q)) stk)
    (hstate : id.state ≠ haltState tc)
    (hq : some q ∈ PartrecToTM2Support.statementList tc) :
    RepresentsSubstate tc
      ((programWithTable tc (loadRows tc var a q)).toMachine.nextID id)
      (a var) (some q) stk := by
  refine toMachine_nextID_stationary_representsSubstate
    (P := programWithTable tc (loadRows tc var a q)) hrep ?_ ?_ ?_ ?_
  · simpa using hstate
  · rw [hrep.2.1]
    exact programWithTable_stationaryRows_transition? tc
      (encodedStmtState tc var (some (Turing.TM2.Stmt.load a q)))
      (id.tape id.head)
      (encodedStmtState tc (a var) (some q))
      hrep.tape_head_mem_symbols
  · exact hrep.tape_head_mem_supportedSymbols
  · exact encodedStmtState_mem_supportedStates hq

theorem branchRows_nextID_representsSubstate
    {tc : Turing.ToPartrec.Code} {id : ID}
    {var : Option Turing.PartrecToTM2.Γ'}
    {p : Option Turing.PartrecToTM2.Γ' → Bool}
    {q₁ q₂ : Turing.PartrecToTM2.Stmt'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    (hrep : RepresentsSubstate tc id var (some (Turing.TM2.Stmt.branch p q₁ q₂)) stk)
    (hstate : id.state ≠ haltState tc)
    (hq₁ : some q₁ ∈ PartrecToTM2Support.statementList tc)
    (hq₂ : some q₂ ∈ PartrecToTM2Support.statementList tc) :
    RepresentsSubstate tc
      ((programWithTable tc (branchRows tc var p q₁ q₂)).toMachine.nextID id)
      var (some (cond (p var) q₁ q₂)) stk := by
  refine toMachine_nextID_stationary_representsSubstate
    (P := programWithTable tc (branchRows tc var p q₁ q₂)) hrep ?_ ?_ ?_ ?_
  · simpa using hstate
  · rw [hrep.2.1]
    exact programWithTable_stationaryRows_transition? tc
      (encodedStmtState tc var (some (Turing.TM2.Stmt.branch p q₁ q₂)))
      (id.tape id.head)
      (encodedStmtState tc var (some (cond (p var) q₁ q₂)))
      hrep.tape_head_mem_symbols
  · exact hrep.tape_head_mem_supportedSymbols
  · change encodedStmtState tc var (some (cond (p var) q₁ q₂)) ∈
      initState :: haltState tc :: states tc
    exact List.mem_cons_of_mem initState
      (List.mem_cons_of_mem (haltState tc)
        (branchRows_next_mem_states hq₁ hq₂))

theorem gotoRows_nextID_representsSubstate
    {tc : Turing.ToPartrec.Code} {id : ID}
    {var : Option Turing.PartrecToTM2.Γ'}
    {f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    (hrep : RepresentsSubstate tc id var (some (Turing.TM2.Stmt.goto f)) stk)
    (hstate : id.state ≠ haltState tc)
    (hf : f var ∈ PartrecToTM2Support.labels tc) :
    RepresentsSubstate tc
      ((programWithTable tc (gotoRows tc var f)).toMachine.nextID id)
      var (cfgStmt (some (f var))) stk := by
  refine toMachine_nextID_stationary_representsSubstate
    (P := programWithTable tc (gotoRows tc var f)) hrep ?_ ?_ ?_ ?_
  · simpa using hstate
  · rw [hrep.2.1]
    exact programWithTable_stationaryRows_transition? tc
      (encodedStmtState tc var (some (Turing.TM2.Stmt.goto f)))
      (id.tape id.head)
      (encodedStmtState tc var (cfgStmt (some (f var))))
      hrep.tape_head_mem_symbols
  · exact hrep.tape_head_mem_supportedSymbols
  · change encodedStmtState tc var (cfgStmt (some (f var))) ∈
      initState :: haltState tc :: states tc
    exact List.mem_cons_of_mem initState
      (List.mem_cons_of_mem (haltState tc)
        (gotoRows_next_mem_states hf))

theorem haltRows_nextID_representsSubstate
    {tc : Turing.ToPartrec.Code} {id : ID}
    {var : Option Turing.PartrecToTM2.Γ'}
    {stk : ∀ _k : Turing.PartrecToTM2.K', List Turing.PartrecToTM2.Γ'}
    (hrep : RepresentsSubstate tc id var (some Turing.TM2.Stmt.halt) stk)
    (hstate : id.state ≠ haltState tc) :
    RepresentsSubstate tc
      ((programWithTable tc (haltRows tc var)).toMachine.nextID id)
      var none stk := by
  refine toMachine_nextID_stationary_representsSubstate
    (P := programWithTable tc (haltRows tc var)) hrep ?_ ?_ ?_ ?_
  · simpa using hstate
  · rw [hrep.2.1]
    exact programWithTable_stationaryRows_transition? tc
      (encodedStmtState tc var (some Turing.TM2.Stmt.halt))
      (id.tape id.head)
      (encodedStmtState tc var none)
      hrep.tape_head_mem_symbols
  · exact hrep.tape_head_mem_supportedSymbols
  · change encodedStmtState tc var none ∈ initState :: haltState tc :: states tc
    exact List.mem_cons_of_mem initState
      (List.mem_cons_of_mem (haltState tc) (haltRows_next_mem_states tc var))

/-- Header plus the fixed first initialization row. -/
noncomputable def programWithInitTable (tc : Turing.ToPartrec.Code)
    (table : List TableTransition) : TableProgram :=
  programWithTable tc (initTransition tc :: table)

/-- Program using the currently implemented `PartrecToTM2` statement-row fragment. -/
noncomputable def programWithImplementedRows (tc : Turing.ToPartrec.Code) :
    TableProgram :=
  programWithInitTable tc (implementedStatementRows tc)

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
    simp [programWithInitTable, initState, haltState, statementState, evaluatorStateCode]
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
  · rw [programWithInitTable_runEmpty_one]
    change evalStartState tc = encodedState tc (Turing.PartrecToTM2.init tc [0])
    exact (encodedState_init tc).symm
  · intro k i
    exact programWithInitTable_runEmpty_one_stackCell tc table k i

end PartrecToTM2Table

end LeanWang

end
