/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Finite-control support facts for Mathlib's `PartrecToTM2` evaluator.

The current machine-side reduction starts with Mathlib's `PartrecToTM2`
evaluator, then uses Mathlib's TM2-to-TM1-to-TM0 translations before compiling
the resulting finite TM0 data. Mathlib already provides the finite
reachable-label set `Turing.PartrecToTM2.codeSupp`; this file packages the
exact support facts needed for the evaluator configuration used by that route.
-/

noncomputable section

namespace LeanWang

namespace PartrecToTM2Support

open Turing
open Turing.PartrecToTM2

/-- The evaluator label used by `PartrecToTM2.init tc [0]`. -/
def startLabel (tc : ToPartrec.Code) : Λ' :=
  trNormal tc Cont'.halt

/-- Finite set of TM2 labels reachable from the evaluator start label. -/
def labels (tc : ToPartrec.Code) : Finset Λ' :=
  codeSupp tc Cont'.halt

/-- The four stack names used by Mathlib's `PartrecToTM2` evaluator. -/
def stackNames : List K' :=
  [K'.main, K'.rev, K'.aux, K'.stack]

theorem stackNames_nodup : stackNames.Nodup := by
  simp [stackNames]

theorem mem_stackNames (k : K') : k ∈ stackNames := by
  cases k <;> simp [stackNames]

/-- Numeric code for a `PartrecToTM2` stack name. -/
def stackNameCode : K' → Nat
  | K'.main => 0
  | K'.rev => 1
  | K'.aux => 2
  | K'.stack => 3

theorem stackNameCode_lt_four (k : K') : stackNameCode k < 4 := by
  cases k <;> decide

theorem stackNameCode_injective : Function.Injective stackNameCode := by
  intro a b h
  cases a <;> cases b <;> simp [stackNameCode] at h ⊢

/-- The finite stack alphabet used by Mathlib's `PartrecToTM2` evaluator. -/
def stackAlphabet : Finset Γ' :=
  Finset.univ

/-- List form of the finite stack alphabet. -/
def stackAlphabetList : List Γ' :=
  stackAlphabet.toList

theorem mem_stackAlphabet (a : Γ') : a ∈ stackAlphabet := by
  simp [stackAlphabet]

theorem mem_stackAlphabetList (a : Γ') : a ∈ stackAlphabetList := by
  simp [stackAlphabetList, mem_stackAlphabet]

theorem stackAlphabetList_nodup : stackAlphabetList.Nodup := by
  exact Finset.nodup_toList stackAlphabet

/-- Numeric code for a `PartrecToTM2` stack symbol. -/
def stackSymbolCode : Γ' → Nat
  | Γ'.consₗ => 0
  | Γ'.cons => 1
  | Γ'.bit0 => 2
  | Γ'.bit1 => 3

theorem stackSymbolCode_lt_four (a : Γ') : stackSymbolCode a < 4 := by
  cases a <;> decide

theorem stackSymbolCode_injective : Function.Injective stackSymbolCode := by
  intro a b h
  cases a <;> cases b <;> simp [stackSymbolCode] at h ⊢

/--
Numeric tape symbol code for a `PartrecToTM2` stack cell.

`none` is the blank cell and `some a` stores one of the four stack symbols.
-/
def tapeSymbolCode : Option Γ' → Nat
  | none => 0
  | some a => stackSymbolCode a + 1

theorem tapeSymbolCode_lt_five (s : Option Γ') : tapeSymbolCode s < 5 := by
  cases s with
  | none => decide
  | some a => cases a <;> decide

theorem tapeSymbolCode_injective : Function.Injective tapeSymbolCode := by
  intro a b h
  cases a with
  | none =>
      cases b <;> simp [tapeSymbolCode, stackSymbolCode] at h ⊢
  | some a =>
      cases b with
      | none =>
          cases a <;> simp [tapeSymbolCode, stackSymbolCode] at h
      | some b =>
          have hcode : stackSymbolCode a = stackSymbolCode b := by
            have h' : stackSymbolCode a + 1 = stackSymbolCode b + 1 := by
              simpa [tapeSymbolCode] using h
            omega
          exact congrArg some (stackSymbolCode_injective hcode)

/-- Finite tape alphabet needed to store blank cells and stack symbols. -/
def tapeSymbols : List Nat :=
  List.range 5

theorem tapeSymbolCode_mem_tapeSymbols (s : Option Γ') :
    tapeSymbolCode s ∈ tapeSymbols :=
  List.mem_range.2 (tapeSymbolCode_lt_five s)

theorem tapeSymbols_nodup : tapeSymbols.Nodup := by
  exact List.nodup_range

theorem startLabel_mem_labels (tc : ToPartrec.Code) :
    startLabel tc ∈ labels tc :=
  codeSupp_self tc Cont'.halt (trStmts₁_self _)

/-- List form of the finite evaluator label set. -/
def labelList (tc : ToPartrec.Code) : List Λ' :=
  (labels tc).toList

theorem mem_labelList {tc : ToPartrec.Code} {q : Λ'} :
    q ∈ labelList tc ↔ q ∈ labels tc := by
  simp [labelList]

theorem labelList_nodup (tc : ToPartrec.Code) :
    (labelList tc).Nodup := by
  exact Finset.nodup_toList (labels tc)

theorem startLabel_mem_labelList (tc : ToPartrec.Code) :
    startLabel tc ∈ labelList tc :=
  mem_labelList.2 (startLabel_mem_labels tc)

/-- Index of a reachable evaluator label in `labelList tc`. -/
def labelIndex (tc : ToPartrec.Code) (q : Λ') : Nat :=
  (labelList tc).findIdx fun r => decide (r = q)

theorem labelIndex_lt_length {tc : ToPartrec.Code} {q : Λ'}
    (hq : q ∈ labelList tc) :
    labelIndex tc q < (labelList tc).length := by
  unfold labelIndex
  exact List.findIdx_lt_length_of_exists ⟨q, hq, by simp⟩

theorem init_label_mem_labels (tc : ToPartrec.Code) :
    (init tc [0]).l ∈ Finset.insertNone (labels tc) := by
  exact Finset.some_mem_insertNone.2 (startLabel_mem_labels tc)

/--
Mathlib's support theorem specialized to the evaluator label set.

The `Inhabited` instance is deliberately local: `TM2.Supports` stores the start
label as `default`, and for the reduction this default is `startLabel tc`.
-/
theorem tr_supports_labels (tc : ToPartrec.Code) :
    @TM2.Supports _ _ _ _ ⟨startLabel tc⟩ tr (labels tc) := by
  change @TM2.Supports _ _ _ _ ⟨trNormal tc Cont'.halt⟩ tr (codeSupp tc Cont'.halt)
  exact tr_supports tc Cont'.halt

/--
Finite set of TM2 statement substates needed to execute all evaluator labels in
`labels tc`.
-/
def statements (tc : ToPartrec.Code) : Finset (Option Stmt') :=
  by
    classical
    exact TM2.stmts tr (labels tc)

/-- List form of the finite statement-substate set. -/
def statementList (tc : ToPartrec.Code) : List (Option Stmt') :=
  by
    classical
    exact (statements tc).toList

theorem mem_statementList {tc : ToPartrec.Code} {stmt : Option Stmt'} :
    stmt ∈ statementList tc ↔ stmt ∈ statements tc := by
  classical
  simp [statementList]

theorem statementList_nodup (tc : ToPartrec.Code) :
    (statementList tc).Nodup := by
  classical
  exact Finset.nodup_toList (statements tc)

theorem none_mem_statements (tc : ToPartrec.Code) :
    none ∈ statements tc := by
  classical
  change none ∈ Finset.insertNone ((labels tc).biUnion fun q => TM2.stmts₁ (tr q))
  exact Finset.none_mem_insertNone

theorem none_mem_statementList (tc : ToPartrec.Code) :
    none ∈ statementList tc :=
  mem_statementList.2 (none_mem_statements tc)

theorem label_statement_mem {tc : ToPartrec.Code} {q : Λ'}
    (hq : q ∈ labels tc) :
    some (tr q) ∈ statements tc := by
  classical
  exact Finset.some_mem_insertNone.2
    (Finset.mem_biUnion.2 ⟨q, hq, TM2.stmts₁_self⟩)

theorem label_statement_mem_list {tc : ToPartrec.Code} {q : Λ'}
    (hq : q ∈ labelList tc) :
    some (tr q) ∈ statementList tc :=
  mem_statementList.2 (label_statement_mem (mem_labelList.1 hq))

theorem label_statement_mem_list_of_label_mem {tc : ToPartrec.Code} {q : Λ'}
    (hq : q ∈ labels tc) :
    some (tr q) ∈ statementList tc :=
  label_statement_mem_list (mem_labelList.2 hq)

/-- Index of a TM2 statement substate in `statementList tc`. -/
noncomputable def statementIndex (tc : ToPartrec.Code) (stmt : Option Stmt') : Nat := by
  classical
  exact (statementList tc).findIdx fun s => decide (s = stmt)

theorem statementIndex_lt_length {tc : ToPartrec.Code} {stmt : Option Stmt'}
    (hstmt : stmt ∈ statementList tc) :
    statementIndex tc stmt < (statementList tc).length := by
  unfold statementIndex
  classical
  exact List.findIdx_lt_length_of_exists ⟨stmt, hstmt, by simp⟩

/-- Numeric state codes for the finite statement substates. -/
def controlStates (tc : ToPartrec.Code) : List Nat :=
  List.range (statementList tc).length

theorem statementIndex_mem_controlStates {tc : ToPartrec.Code} {stmt : Option Stmt'}
    (hstmt : stmt ∈ statementList tc) :
    statementIndex tc stmt ∈ controlStates tc := by
  exact List.mem_range.2 (statementIndex_lt_length hstmt)

/-- Control state for the initial evaluator statement. -/
noncomputable def startState (tc : ToPartrec.Code) : Nat :=
  statementIndex tc (some (tr (startLabel tc)))

/-- Control state for the halted TM2 configuration. -/
noncomputable def haltState (tc : ToPartrec.Code) : Nat :=
  statementIndex tc none

theorem startState_mem_controlStates (tc : ToPartrec.Code) :
    startState tc ∈ controlStates tc := by
  exact statementIndex_mem_controlStates (label_statement_mem_list (startLabel_mem_labelList tc))

theorem haltState_mem_controlStates (tc : ToPartrec.Code) :
    haltState tc ∈ controlStates tc := by
  exact statementIndex_mem_controlStates (none_mem_statementList tc)

theorem labelState_mem_controlStates {tc : ToPartrec.Code} {q : Λ'}
    (hq : q ∈ labels tc) :
    statementIndex tc (some (tr q)) ∈ controlStates tc := by
  exact statementIndex_mem_controlStates (label_statement_mem_list_of_label_mem hq)

theorem statement_supports {tc : ToPartrec.Code} {stmt : Stmt'}
    (hstmt : some stmt ∈ statements tc) :
    TM2.SupportsStmt (labels tc) stmt := by
  classical
  letI : Inhabited Λ' := ⟨startLabel tc⟩
  exact TM2.stmts_supportsStmt (tr_supports_labels tc) hstmt

theorem labels_step_closed {tc : ToPartrec.Code}
    {cfg cfg' : Cfg'}
    (hstep : cfg' ∈ TM2.step tr cfg)
    (hcfg : cfg.l ∈ Finset.insertNone (labels tc)) :
    cfg'.l ∈ Finset.insertNone (labels tc) := by
  letI : Inhabited Λ' := ⟨startLabel tc⟩
  exact TM2.step_supports tr (tr_supports_labels tc) hstep hcfg

theorem labels_reaches_closed {tc : ToPartrec.Code}
    {cfg cfg' : Cfg'}
    (hreach : TM2.Reaches tr cfg cfg')
    (hcfg : cfg.l ∈ Finset.insertNone (labels tc)) :
    cfg'.l ∈ Finset.insertNone (labels tc) := by
  induction hreach with
  | refl =>
      exact hcfg
  | tail _ hstep ih =>
      exact labels_step_closed hstep ih

theorem init_reaches_label_mem {tc : ToPartrec.Code}
    {cfg : Cfg'}
    (hreach : TM2.Reaches tr (init tc [0]) cfg) :
    cfg.l ∈ Finset.insertNone (labels tc) :=
  labels_reaches_closed hreach (init_label_mem_labels tc)

end PartrecToTM2Support

end LeanWang

end
