/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourceCore.Basic

/-!
Bounded-search source-code descriptor rows and accumulator decoder.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

noncomputable def sourceSearchCodeOneRowsVar
    (c : Code) (k : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  match TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none => []
  | some stmt =>
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v

theorem sourceSearchCodeOneRowsVar_stmt_none
    {c : Code} {k : Nat} {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSearchCodeOneRowsVar c k v = [] := by
  simp [sourceSearchCodeOneRowsVar, hstmt]

theorem sourceSearchCodeOneRowsVar_eq_nil_of_statementCount_le
    {c : Code} {k : Nat} (v : TM0Route.PartrecVar)
    (hk : sourceStatementCount c ≤ k) :
    sourceSearchCodeOneRowsVar c k v = [] := by
  exact sourceSearchCodeOneRowsVar_stmt_none
    (TM0Route.partrecStartedTM0StatementAt?_eq_none_of_count_le
      (NatPartrecToToPartrec.translate c) (by simpa [sourceStatementCount] using hk))

theorem sourceSearchCodeOneRowsVar_statementCount_add
    (c : Code) (offset : Nat) (v : TM0Route.PartrecVar) :
    sourceSearchCodeOneRowsVar c (sourceStatementCount c + offset) v = [] :=
  sourceSearchCodeOneRowsVar_eq_nil_of_statementCount_le v (Nat.le_add_right _ _)

theorem sourceSearchCodeOneRowsVar_statementCount_add_primrec :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 (sourceStatementCount p.1 + p.2.1) p.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSearchCodeOneRowsVar_statementCount_add p.1 p.2.1 p.2.2).symm

noncomputable def sourceSearchCodeInteriorRowsVar
    (c : Code) (j : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  sourceSearchCodeOneRowsVar c (j + 1) v

theorem sourceSearchCodeInteriorRowsVar_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hj : Primrec (fun p : Code × Nat × TM0Route.PartrecVar => p.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  exact hrows.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair hj (Primrec.snd.comp Primrec.snd)))

noncomputable def sourceSearchCodeBoundedInteriorRowsVar
    (c : Code) (j : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  if j + 1 < sourceStatementCount c then
    sourceSearchCodeInteriorRowsVar c j v
  else
    []

theorem sourceSearchCodeBoundedInteriorRowsVar_eq_interior
    {c : Code} {j : Nat} {v : TM0Route.PartrecVar}
    (hj : j + 1 < sourceStatementCount c) :
    sourceSearchCodeBoundedInteriorRowsVar c j v =
      sourceSearchCodeInteriorRowsVar c j v := by
  simp [sourceSearchCodeBoundedInteriorRowsVar, hj]

theorem sourceSearchCodeBoundedInteriorRowsVar_eq_nil
    {c : Code} {j : Nat} {v : TM0Route.PartrecVar}
    (hj : ¬ j + 1 < sourceStatementCount c) :
    sourceSearchCodeBoundedInteriorRowsVar c j v = [] := by
  simp [sourceSearchCodeBoundedInteriorRowsVar, hj]

theorem sourceSearchCodeBoundedInteriorRowsVar_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hbound : PrimrecPred (fun p : Code × Nat × TM0Route.PartrecVar =>
      p.2.1 + 1 < sourceStatementCount p.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (sourceStatementCount_primrec.comp Primrec.fst)
  have hnil : Primrec (fun _p : Code × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  exact (Primrec.ite hbound hinterior hnil).of_eq fun p => by
    rfl

theorem sourceSearchCodeOneRowsVar_stmt_some
    {c : Code} {k : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some stmt) :
    sourceSearchCodeOneRowsVar c k v =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v := by
  simp [sourceSearchCodeOneRowsVar, hstmt]

theorem sourceSearchCodeOneRowsVar_stmt_some_none
    {c : Code} {k : Nat} {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some
          (none : Option (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
            (Turing.TM2to1.Λ'
              TM0Route.PartrecStack TM0Route.PartrecStackSymbol
              (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
              TM0Route.PartrecVar)
            TM0Route.PartrecVar))) :
    sourceSearchCodeOneRowsVar c k v = [] := by
  rw [sourceSearchCodeOneRowsVar_stmt_some hstmt]
  exact TM0FoldedCompiler.simStepDataForStmtLabelWithCode_none
    (NatPartrecToToPartrec.translate c)
    (TM0FiniteCompiler.stateCodeBySupportSearch
      (NatPartrecToToPartrec.translate c)
      (TM0Route.partrecStartedTM0StatementCount
        (NatPartrecToToPartrec.translate c))
      (((none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar)), v) :
        Turing.TM1to0.Λ'
          (TM0Route.partrecStartedTM1Machine
            (NatPartrecToToPartrec.translate c))))
    v

theorem sourceSearchCodeOneRowsVar_zero
    (c : Code) (v : TM0Route.PartrecVar) :
    sourceSearchCodeOneRowsVar c 0 v = [] := by
  exact sourceSearchCodeOneRowsVar_stmt_some_none (sourceStatementAt_zero c)

theorem sourceSearchCodeOneRowsVar_zero_primrec :
    Primrec (fun p : Code × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 0 p.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSearchCodeOneRowsVar_zero p.1 p.2).symm

theorem sourceSearchCodeOneRowsVar_eq_boundedInterior
    (c : Code) (k : Nat) (v : TM0Route.PartrecVar) :
    sourceSearchCodeOneRowsVar c k v =
      if k = 0 then
        []
      else
        sourceSearchCodeBoundedInteriorRowsVar c (k - 1) v := by
  by_cases hzero : k = 0
  · simp [hzero, sourceSearchCodeOneRowsVar_zero]
  · by_cases hlt : k < sourceStatementCount c
    · have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourceSearchCodeBoundedInteriorRowsVar,
        sourceSearchCodeInteriorRowsVar, hkpred, hlt]
    · have hle : sourceStatementCount c ≤ k := Nat.le_of_not_gt hlt
      have hrows : sourceSearchCodeOneRowsVar c k v = [] :=
        sourceSearchCodeOneRowsVar_eq_nil_of_statementCount_le v hle
      have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourceSearchCodeBoundedInteriorRowsVar, hkpred, hlt, hrows]

theorem sourceSearchCodeOneRowsVar_primrec_of_boundedInterior
    (hinterior : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2) := by
  have hzero : PrimrecPred (fun p : Code × Nat × TM0Route.PartrecVar =>
      p.2.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hnil : Primrec (fun _p : Code × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hkPred : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      p.2.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have helse : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 (p.2.1 - 1) p.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair hkPred (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.ite hzero hnil helse).of_eq fun p => by
    exact (sourceSearchCodeOneRowsVar_eq_boundedInterior p.1 p.2.1 p.2.2).symm

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c 1 k i =
      match TM0Route.partrecVarList[i]? with
      | none => []
      | some v => sourceSearchCodeOneRowsVar c k v := by
  cases hv : TM0Route.partrecVarList[i]? with
  | none =>
      rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_var_none
        (c := c) (fuel := 0) (k := k) (i := i) hv]
      simp [sourceSimStepDataForLabelIndexFromWithSearchCode_zero]
  | some v =>
      cases hstmt : TM0Route.partrecStartedTM0StatementAt?
          (NatPartrecToToPartrec.translate c) k with
      | none =>
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none
            (c := c) (fuel := 0) (k := k) (i := i) (v := v) hv hstmt]
          simp [sourceSearchCodeOneRowsVar_stmt_none hstmt]
      | some stmt =>
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
            (c := c) (fuel := 0) (k := k) (i := i) (v := v)
            (stmt := stmt) hv hstmt]
          simp [sourceSearchCodeOneRowsVar_stmt_some hstmt]

set_option linter.style.longLine false in
/--
For each fixed source code, support-search one-row descriptors are primitive
recursive in the statement offset and source variable.

The proof goes through the already available fixed-code label-index decoder and
uses the finite index of the variable in `partrecVarList`.
-/
theorem sourceSearchCodeOneRowsVar_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar c p.1 p.2) := by
  let tc := NatPartrecToToPartrec.translate c
  let idx : Nat × TM0Route.PartrecVar → Nat :=
    fun p => @List.idxOf TM0Route.PartrecVar instBEqOfDecidableEq
      p.2 TM0Route.partrecVarList
  have hidx : Primrec idx :=
    (Primrec.list_idxOf₁ TM0Route.partrecVarList).comp Primrec.snd
  have hdecoder : Primrec (fun p : Nat × TM0Route.PartrecVar =>
      sourceSimStepDataForLabelIndexFromWithSearchCode c 1 p.1
        (idx p)) := by
    exact (TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_primrec_fixed
      tc).comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair Primrec.fst hidx))
  exact hdecoder.of_eq fun p => by
    rw [sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows]
    have hget :
        TM0Route.partrecVarList[idx p]? = some p.2 := by
      rcases p with ⟨_k, v⟩
      cases v with
      | none =>
          simp [idx, TM0Route.partrecVarList]
      | some a =>
          cases a <;>
            simp [idx, TM0Route.partrecVarList, PartrecToTM2Support.stackAlphabetList]
    simp [hget]

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_zero
    (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c 1 0 i = [] := by
  rw [sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows]
  cases h : TM0Route.partrecVarList[i]? with
  | none => rfl
  | some v => exact sourceSearchCodeOneRowsVar_zero c v

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_zero_primrec :
    Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 0 p.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourceSimStepDataForLabelIndexFromWithSearchCode_one_zero p.1 p.2).symm

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_one_primrec_of_varRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun _p : Code × Nat × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 v) := by
    apply Primrec₂.mk
    exact hvarRows.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    rw [sourceSimStepDataForLabelIndexFromWithSearchCode_one_eq_varRows]
    cases TM0Route.partrecVarList[p.2.2]? <;> rfl

/-- State for the source-level bounded-search descriptor decoder.

The first two fields are the current statement offset and variable-list offset.
The optional row list records that the decoder has already resolved; `none`
means the scan should continue with the next statement block.
-/
abbrev SourceSearchCodeDecoderState :=
  Nat × Nat × Option (List TM0FoldedCompiler.SimStepData)

def sourceSearchCodeDecoderRows (s : SourceSearchCodeDecoderState) :
    List TM0FoldedCompiler.SimStepData :=
  s.2.2.getD []

def sourceSearchCodeDecoderInit (k i : Nat) : SourceSearchCodeDecoderState :=
  (k, i, none)

noncomputable def sourceSearchCodeDecoderStepVar
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none => (k, i, some [])
  | some stmt =>
      (k, i, some
        (TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c)
          (TM0FiniteCompiler.stateCodeBySupportSearch
            (NatPartrecToToPartrec.translate c)
            (TM0Route.partrecStartedTM0StatementCount
              (NatPartrecToToPartrec.translate c))
            ((stmt, v) :
              Turing.TM1to0.Λ'
                (TM0Route.partrecStartedTM1Machine
                  (NatPartrecToToPartrec.translate c))))
          stmt v))

noncomputable def sourceSearchCodeDecoderStepNone (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some v => sourceSearchCodeDecoderStepVar c k i v

noncomputable def sourceSearchCodeDecoderStepNoneRows (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some _ => (k, i, some (sourceSimStepDataForLabelIndexFromWithSearchCode c 1 k i))

/-- One accumulator step for the source-level bounded-search descriptor decoder. -/
noncomputable def sourceSearchCodeDecoderStep (c : Code)
    (s : SourceSearchCodeDecoderState) : SourceSearchCodeDecoderState :=
  match s.2.2 with
  | some rows => (s.1, s.2.1, some rows)
  | none => sourceSearchCodeDecoderStepNone c s.1 s.2.1

theorem sourceSearchCodeDecoderStep_resolved
    (c : Code) (k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourceSearchCodeDecoderStep c (k, i, some rows) = (k, i, some rows) := by
  rfl

theorem sourceSearchCodeDecoderStep_var_none
    {c : Code} {k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourceSearchCodeDecoderStep c (k, i, none) =
      (k + 1, i - TM0Route.partrecVarList.length, none) := by
  simp [sourceSearchCodeDecoderStep, sourceSearchCodeDecoderStepNone, hv]

theorem sourceSearchCodeDecoderStep_stmt_none
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSearchCodeDecoderStep c (k, i, none) =
      (k, i, some []) := by
  simp [sourceSearchCodeDecoderStep, sourceSearchCodeDecoderStepNone,
    sourceSearchCodeDecoderStepVar, hv, hstmt]

theorem sourceSearchCodeDecoderStep_stmt_some
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some stmt) :
    sourceSearchCodeDecoderStep c (k, i, none) =
      (k, i, some
        (TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c)
          (TM0FiniteCompiler.stateCodeBySupportSearch
            (NatPartrecToToPartrec.translate c)
            (TM0Route.partrecStartedTM0StatementCount
              (NatPartrecToToPartrec.translate c))
            ((stmt, v) :
              Turing.TM1to0.Λ'
                (TM0Route.partrecStartedTM1Machine
                  (NatPartrecToToPartrec.translate c))))
          stmt v)) := by
  simp [sourceSearchCodeDecoderStep, sourceSearchCodeDecoderStepNone,
    sourceSearchCodeDecoderStepVar, hv, hstmt]

theorem sourceSearchCodeDecoderStepVar_eq_oneRows
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    sourceSearchCodeDecoderStepVar c k i v =
      (k, i, some (sourceSearchCodeOneRowsVar c k v)) := by
  unfold sourceSearchCodeDecoderStepVar sourceSearchCodeOneRowsVar
  cases TM0Route.partrecStartedTM0StatementAt? (NatPartrecToToPartrec.translate c) k <;> rfl

theorem sourceSearchCodeDecoderStepVar_primrec_of_oneRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2.2) :=
    hvarRows.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.pair
    (Primrec.fst.comp Primrec.snd)
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.option_some.comp hrows))).of_eq fun p => by
        exact (sourceSearchCodeDecoderStepVar_eq_oneRows
          p.1 p.2.1 p.2.2.1 p.2.2.2).symm

theorem sourceSearchCodeDecoderStepNone_primrec_of_stepVar
    (hvar : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun p : Code × Nat × Nat =>
      (p.2.1 + 1, p.2.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2 v) := by
    apply Primrec₂.mk
    exact hvar.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? <;>
      simp [sourceSearchCodeDecoderStepNone, h]

theorem sourceSearchCodeDecoderStep_primrec_of_stepNone
    (hnone : Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) := by
  have hopt : Primrec (fun p : Code × SourceSearchCodeDecoderState => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnoneCase : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2.1) := by
    exact hnone.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hsome : Primrec₂
      (fun p : Code × SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData =>
          (p.2.1, p.2.2.1, some rows)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.option_some.comp Primrec.snd))
  exact (Primrec.option_casesOn hopt hnoneCase hsome).of_eq fun p => by
    cases h : p.2.2.2 <;> simp [sourceSearchCodeDecoderStep, h]

theorem sourceSearchCodeDecoderStep_primrec_of_stepVar
    (hvar : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) :=
  sourceSearchCodeDecoderStep_primrec_of_stepNone
    (sourceSearchCodeDecoderStepNone_primrec_of_stepVar hvar)

theorem sourceSearchCodeDecoderStep_primrec_of_oneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) :=
  sourceSearchCodeDecoderStep_primrec_of_stepVar
    (sourceSearchCodeDecoderStepVar_primrec_of_oneRows hvarRows)

theorem sourceSearchCodeDecoderStepNone_eq_rows (c : Code) (k i : Nat) :
    sourceSearchCodeDecoderStepNone c k i =
      sourceSearchCodeDecoderStepNoneRows c k i := by
  unfold sourceSearchCodeDecoderStepNone sourceSearchCodeDecoderStepNoneRows
  cases hv : TM0Route.partrecVarList[i]? with
  | none =>
      rfl
  | some v =>
      unfold sourceSearchCodeDecoderStepVar
      cases hstmt : TM0Route.partrecStartedTM0StatementAt?
          (NatPartrecToToPartrec.translate c) k with
      | none =>
          simp [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none
            (c := c) (fuel := 0) (k := k) (i := i) (v := v) hv hstmt]
      | some stmt =>
          simp [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
            (c := c) (fuel := 0) (k := k) (i := i) (v := v)
            (stmt := stmt) hv hstmt]

theorem sourceSearchCodeDecoderStepNone_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun p : Code × Nat × Nat =>
      (p.2.1 + 1, p.2.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun _v : TM0Route.PartrecVar =>
      (p.2.1, p.2.2,
        some (sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2))) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp
          (hrows.comp
            (Primrec.pair (Primrec.fst.comp Primrec.fst)
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
                (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))))
  have hrowsStep : Primrec (fun p : Code × Nat × Nat =>
      sourceSearchCodeDecoderStepNoneRows p.1 p.2.1 p.2.2) :=
    (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
      cases h : TM0Route.partrecVarList[p.2.2]? <;>
        simp [sourceSearchCodeDecoderStepNoneRows, h]
  exact hrowsStep.of_eq fun p =>
    (sourceSearchCodeDecoderStepNone_eq_rows p.1 p.2.1 p.2.2).symm

theorem sourceSearchCodeDecoderStep_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2) :=
  sourceSearchCodeDecoderStep_primrec_of_stepNone
    (sourceSearchCodeDecoderStepNone_primrec_of_oneRows hrows)

noncomputable def sourceSearchCodeDecoderStateFrom
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    SourceSearchCodeDecoderState :=
  fuel.rec s (fun _ s => sourceSearchCodeDecoderStep c s)

theorem sourceSearchCodeDecoderStateFrom_succ_eq_step
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    sourceSearchCodeDecoderStateFrom c (fuel + 1) s =
      sourceSearchCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderStep c s) := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourceSearchCodeDecoderStep c
          (sourceSearchCodeDecoderStateFrom c (fuel + 1) s) =
        sourceSearchCodeDecoderStep c
          (sourceSearchCodeDecoderStateFrom c fuel
          (sourceSearchCodeDecoderStep c s))
      rw [ih]

theorem sourceSearchCodeDecoderStateFrom_resolved
    (c : Code) (fuel k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourceSearchCodeDecoderStateFrom c fuel (k, i, some rows) =
      (k, i, some rows) := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourceSearchCodeDecoderStep c
          (sourceSearchCodeDecoderStateFrom c fuel (k, i, some rows)) =
        (k, i, some rows)
      rw [ih]
      exact sourceSearchCodeDecoderStep_resolved c k i rows

theorem sourceSearchCodeDecoderRows_stateFrom_none_eq
    (c : Code) (fuel k i : Nat) :
    sourceSearchCodeDecoderRows
        (sourceSearchCodeDecoderStateFrom c fuel (k, i, none)) =
      sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      simp [sourceSearchCodeDecoderStateFrom, sourceSearchCodeDecoderRows,
        sourceSimStepDataForLabelIndexFromWithSearchCode_zero]
  | succ fuel ih =>
      rw [sourceSearchCodeDecoderStateFrom_succ_eq_step]
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [sourceSearchCodeDecoderStep_var_none hv]
          rw [ih]
          rw [sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_var_none hv]
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt?
              (NatPartrecToToPartrec.translate c) k with
          | none =>
              rw [sourceSearchCodeDecoderStep_stmt_none hv hstmt]
              rw [sourceSearchCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_none hv hstmt]
          | some stmt =>
              rw [sourceSearchCodeDecoderStep_stmt_some hv hstmt]
              rw [sourceSearchCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithSearchCode_succ_of_stmt_some
                  hv hstmt]

noncomputable def sourceSearchCodeDecoderState (c : Code) (fuel k i : Nat) :
    SourceSearchCodeDecoderState :=
  sourceSearchCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderInit k i)

noncomputable def sourceSearchCodeDecoder (c : Code) (fuel k i : Nat) :
    List TM0FoldedCompiler.SimStepData :=
  sourceSearchCodeDecoderRows (sourceSearchCodeDecoderState c fuel k i)

theorem sourceSearchCodeDecoderRows_primrec :
    Primrec sourceSearchCodeDecoderRows := by
  unfold sourceSearchCodeDecoderRows
  have hopt : Primrec (fun s : SourceSearchCodeDecoderState => s.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnone : Primrec (fun _s : SourceSearchCodeDecoderState =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂
      (fun _s : SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData => rows) :=
    Primrec₂.right
  exact (Primrec.option_casesOn hopt hnone hsome).of_eq fun s => by
    cases s.2.2 <;> rfl

set_option maxHeartbeats 800000 in
-- The final equality unfolds the `nat_rec'` accumulator over nested product projections.
theorem sourceSearchCodeDecoder_primrec_of_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoder p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let fuel : Code × Nat × Nat × Nat → Nat := fun p => p.2.1
  let kFn : Code × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let iFn : Code × Nat × Nat × Nat → Nat := fun p => p.2.2.2
  have hfuel : Primrec fuel := Primrec.fst.comp Primrec.snd
  have hk : Primrec kFn := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec iFn := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoderInit (kFn p) (iFn p)) := by
    unfold sourceSearchCodeDecoderInit
    exact Primrec.pair hk (Primrec.pair hi (Primrec.const none))
  have hiterStep : Primrec₂
      (fun p : Code × Nat × Nat × Nat =>
        fun s : Nat × SourceSearchCodeDecoderState =>
          sourceSearchCodeDecoderStep p.1 s.2) := by
    apply Primrec₂.mk
    exact hstep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  have hstate : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoderState p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    exact (Primrec.nat_rec' hfuel hbase hiterStep).of_eq fun p => by
      unfold sourceSearchCodeDecoderState sourceSearchCodeDecoderInit fuel kFn iFn
      rfl
  exact (sourceSearchCodeDecoderRows_primrec.comp hstate).of_eq fun p => by
    unfold sourceSearchCodeDecoder
    rfl

theorem sourceSearchCodeDecoder_primrec_of_oneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSearchCodeDecoder p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSearchCodeDecoder_primrec_of_step
    (sourceSearchCodeDecoderStep_primrec_of_oneVarRows hvarRows)

theorem sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode
    (c : Code) (fuel k i : Nat) :
    sourceSearchCodeDecoder c fuel k i =
      sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i := by
  unfold sourceSearchCodeDecoder sourceSearchCodeDecoderState sourceSearchCodeDecoderInit
  exact sourceSearchCodeDecoderRows_stateFrom_none_eq c fuel k i

theorem sourceSearchCodeDecoder_eq_nil_of_bound_le
    {c : Code} {fuel k i : Nat}
    (hi : fuel * TM0Route.partrecVarList.length ≤ i) :
    sourceSearchCodeDecoder c fuel k i = [] := by
  rw [sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode]
  exact sourceSimStepDataForLabelIndexFromWithSearchCode_eq_nil_of_bound_le hi

theorem sourceSearchCodeDecoder_eq_nil_of_statementCount_le
    (c : Code) (fuel k i : Nat) (hk : sourceStatementCount c ≤ k) :
    sourceSearchCodeDecoder c fuel k i = [] := by
  rw [sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode]
  exact sourceSimStepDataForLabelIndexFromWithSearchCode_eq_nil_of_statementCount_le
    c fuel k i hk

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  (sourceSearchCodeDecoder_primrec_of_step hstep).of_eq fun p =>
    sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneVarRows
    (hvarRows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step
    (sourceSearchCodeDecoderStep_primrec_of_oneVarRows hvarRows)

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step
    (sourceSearchCodeDecoderStep_primrec_of_oneRows hrows)



end TM0FoldedReduction

end LeanWang
