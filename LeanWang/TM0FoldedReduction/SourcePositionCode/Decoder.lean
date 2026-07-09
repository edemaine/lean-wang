/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourcePositionCode.OneRows

/-!
Source-specialized generated position-code accumulator and decoder.

The one-row and interior generated position-code rows live in
`SourcePositionCode.OneRows`; this module contains the accumulator step and
iterated decoder that turn those rows into the source label-index decoder.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

noncomputable def sourcePositionCodeDecoderStepNone (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some v => (k, i, some (sourcePositionCodeOneRowsIndexVar c k i v))

noncomputable def sourcePositionCodeDecoderStep (c : Code)
    (s : SourceSearchCodeDecoderState) : SourceSearchCodeDecoderState :=
  match s.2.2 with
  | some rows => (s.1, s.2.1, some rows)
  | none => sourcePositionCodeDecoderStepNone c s.1 s.2.1

theorem sourcePositionCodeDecoderStep_resolved
    (c : Code) (k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourcePositionCodeDecoderStep c (k, i, some rows) = (k, i, some rows) := by
  rfl

theorem sourcePositionCodeDecoderStep_var_none
    {c : Code} {k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourcePositionCodeDecoderStep c (k, i, none) =
      (k + 1, i - TM0Route.partrecVarList.length, none) := by
  simp [sourcePositionCodeDecoderStep, sourcePositionCodeDecoderStepNone, hv]

theorem sourcePositionCodeDecoderStep_stmt_none
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourcePositionCodeDecoderStep c (k, i, none) =
      (k, i, some []) := by
  simp [sourcePositionCodeDecoderStep, sourcePositionCodeDecoderStepNone, hv,
    sourcePositionCodeOneRowsIndexVar_stmt_none hstmt]

theorem sourcePositionCodeDecoderStep_stmt_some
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
    sourcePositionCodeDecoderStep c (k, i, none) =
      (k, i, some
        (TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c)
          (TM0FoldedCompiler.labelPositionCode k i stmt v) stmt v)) := by
  simp [sourcePositionCodeDecoderStep, sourcePositionCodeDecoderStepNone, hv,
    sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]

theorem sourcePositionCodeDecoderStepNone_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
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
      (p.2.1, p.2.2, some (sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2 v))) := by
    apply Primrec₂.mk
    have hrow : Primrec (fun p : (Code × Nat × Nat) × TM0Route.PartrecVar =>
        sourcePositionCodeOneRowsIndexVar p.1.1 p.1.2.1 p.1.2.2 p.2) :=
      hvarRows.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
              Primrec.snd)))
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp hrow))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? <;>
      simp [sourcePositionCodeDecoderStepNone, h]

theorem sourcePositionCodeDecoderStep_primrec_of_stepNone
    (hnone : Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) := by
  have hopt : Primrec (fun p : Code × SourceSearchCodeDecoderState => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnoneCase : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2.1) := by
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
    cases h : p.2.2.2 <;> simp [sourcePositionCodeDecoderStep, h]

theorem sourcePositionCodeDecoderStep_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) :=
  sourcePositionCodeDecoderStep_primrec_of_stepNone
    (sourcePositionCodeDecoderStepNone_primrec_of_indexVarRows hvarRows)

theorem sourcePositionCodeDecoderStepNone_primrec_of_oneRowsAtIndex
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeOneRowsAtIndex p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeDecoderStepNone p.1 p.2.1 p.2.2) := by
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
      (p.2.1, p.2.2, some (sourcePositionCodeOneRowsAtIndex p.1 p.2.1 p.2.2))) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp (hrows.comp Primrec.fst)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? with
    | none =>
        simp [sourcePositionCodeDecoderStepNone, h]
    | some v =>
        simp [sourcePositionCodeDecoderStepNone, sourcePositionCodeOneRowsAtIndex, h]

theorem sourcePositionCodeDecoderStep_primrec_of_oneRowsAtIndex
    (hrows : Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeOneRowsAtIndex p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) :=
  sourcePositionCodeDecoderStep_primrec_of_stepNone
    (sourcePositionCodeDecoderStepNone_primrec_of_oneRowsAtIndex hrows)

set_option linter.style.longLine false in
/-- Fixed-code primitive-recursiveness of the generated position-code unresolved accumulator step. -/
theorem sourcePositionCodeDecoderStepNone_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat =>
      sourcePositionCodeDecoderStepNone c p.1 p.2) := by
  have hlookup : Primrec (fun p : Nat × Nat =>
      TM0Route.partrecVarList[p.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp Primrec.snd
  have hnone : Primrec (fun p : Nat × Nat =>
      (p.1 + 1, p.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp Primrec.fst)
      (Primrec.pair
        (Primrec.nat_sub.comp Primrec.snd
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hrows := sourcePositionCodeOneRowsIndexVar_primrec_fixed c
  have hsome : Primrec₂ (fun p : Nat × Nat => fun v : TM0Route.PartrecVar =>
      (p.1, p.2, some (sourcePositionCodeOneRowsIndexVar c p.1 p.2 v))) := by
    apply Primrec₂.mk
    have hrow : Primrec (fun p : (Nat × Nat) × TM0Route.PartrecVar =>
        sourcePositionCodeOneRowsIndexVar c p.1.1 p.1.2 p.2) :=
      hrows.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
    exact Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst)
        (Primrec.option_some.comp hrow))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2]? <;>
      simp [sourcePositionCodeDecoderStepNone, h]

set_option linter.style.longLine false in
/-- Fixed-code primitive-recursiveness of the generated position-code accumulator step. -/
theorem sourcePositionCodeDecoderStep_primrec_fixed (c : Code) :
    Primrec (fun s : SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep c s) := by
  have hopt : Primrec (fun s : SourceSearchCodeDecoderState => s.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnone := sourcePositionCodeDecoderStepNone_primrec_fixed c
  have hnoneCase : Primrec (fun s : SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStepNone c s.1 s.2.1) :=
    hnone.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hsome : Primrec₂
      (fun s : SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData =>
          (s.1, s.2.1, some rows)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp Primrec.snd))
  exact (Primrec.option_casesOn hopt hnoneCase hsome).of_eq fun s => by
    cases h : s.2.2 <;> simp [sourcePositionCodeDecoderStep, h]

set_option linter.style.longLine false in
/--
Primitive recursiveness of the source-specialized position-code label-index
decoder is enough for the generated position-code accumulator step.

This avoids asking for primitive recursiveness of
`sourcePositionCodeOneRowsIndexVar` at arbitrary numeric variable slots.  The
accumulator step only uses slots that successfully decode through the fixed
`partrecVarList`, and in that branch the one-row payload is exactly the
`fuel = 1` position-code label-index decoder.
-/
theorem sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) := by
  apply sourcePositionCodeDecoderStep_primrec_of_stepNone
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
  have hrows : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 1 p.2.1 p.2.2) :=
    hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.const 1) Primrec.snd))
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun _v : TM0Route.PartrecVar =>
      (p.2.1, p.2.2,
        some (sourceSimStepDataForLabelIndexFromWithPositionCode p.1 1 p.2.1 p.2.2))) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp (hrows.comp Primrec.fst)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? with
    | none =>
        simp [sourcePositionCodeDecoderStepNone, h]
    | some v =>
        simp [sourcePositionCodeDecoderStepNone, h,
          sourceSimStepDataForLabelIndexFromWithPositionCode_one_eq_indexVarRows]

noncomputable def sourcePositionCodeDecoderStateFrom
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    SourceSearchCodeDecoderState :=
  fuel.rec s (fun _ s => sourcePositionCodeDecoderStep c s)

theorem sourcePositionCodeDecoderStateFrom_succ_eq_step
    (c : Code) (fuel : Nat) (s : SourceSearchCodeDecoderState) :
    sourcePositionCodeDecoderStateFrom c (fuel + 1) s =
      sourcePositionCodeDecoderStateFrom c fuel (sourcePositionCodeDecoderStep c s) := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourcePositionCodeDecoderStep c
          (sourcePositionCodeDecoderStateFrom c (fuel + 1) s) =
        sourcePositionCodeDecoderStep c
          (sourcePositionCodeDecoderStateFrom c fuel
          (sourcePositionCodeDecoderStep c s))
      rw [ih]

theorem sourcePositionCodeDecoderStateFrom_resolved
    (c : Code) (fuel k i : Nat) (rows : List TM0FoldedCompiler.SimStepData) :
    sourcePositionCodeDecoderStateFrom c fuel (k, i, some rows) =
      (k, i, some rows) := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      change sourcePositionCodeDecoderStep c
          (sourcePositionCodeDecoderStateFrom c fuel (k, i, some rows)) =
        (k, i, some rows)
      rw [ih]
      exact sourcePositionCodeDecoderStep_resolved c k i rows

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_zero
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c 0 k i = [] := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  simp [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_zero]

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_var_none
    {c : Code} {fuel k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) k i =
      sourceSimStepDataForLabelIndexFromWithPositionCode c fuel
        (k + 1) (i - TM0Route.partrecVarList.length) := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_var_none
    (tc := NatPartrecToToPartrec.translate c) hv]

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_none
    {c : Code} {fuel k i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) k i = [] := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_stmt_none
    (tc := NatPartrecToToPartrec.translate c) hv hstmt]
  rfl

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_some
    {c : Code} {fuel k i : Nat} {v : TM0Route.PartrecVar}
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
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) k i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode k i stmt v) stmt v := by
  simpa using
    sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
      (c := c) (fuel := fuel + 1) (k := k) (block := 0)
      (i := i) (v := v) (stmt := stmt) (by omega) hv (by simpa using hstmt)

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_eq_nil_of_statementCount_le
    (c : Code) (fuel k i : Nat) (hk : sourceStatementCount c ≤ k) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i = [] := by
  induction fuel generalizing k i with
  | zero =>
      exact sourceSimStepDataForLabelIndexFromWithPositionCode_zero c k i
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_var_none
            (c := c) (fuel := fuel) (k := k) (i := i) hv]
          exact ih (k + 1) (i - TM0Route.partrecVarList.length) (by omega)
      | some v =>
          exact sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_none
            (c := c) (fuel := fuel) (k := k) (i := i) (v := v) hv
            (TM0Route.partrecStartedTM0StatementAt?_eq_none_of_count_le
              (NatPartrecToToPartrec.translate c)
              (by simpa [sourceStatementCount] using hk))

theorem sourcePositionCodeDecoderRows_stateFrom_none_eq
    (c : Code) (fuel k i : Nat) :
    sourceSearchCodeDecoderRows
        (sourcePositionCodeDecoderStateFrom c fuel (k, i, none)) =
      sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      simp [sourcePositionCodeDecoderStateFrom, sourceSearchCodeDecoderRows,
        sourceSimStepDataForLabelIndexFromWithPositionCode_zero]
  | succ fuel ih =>
      rw [sourcePositionCodeDecoderStateFrom_succ_eq_step]
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [sourcePositionCodeDecoderStep_var_none hv]
          rw [ih]
          rw [sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_var_none hv]
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt?
              (NatPartrecToToPartrec.translate c) k with
          | none =>
              rw [sourcePositionCodeDecoderStep_stmt_none hv hstmt]
              rw [sourcePositionCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_none
                  hv hstmt]
          | some stmt =>
              rw [sourcePositionCodeDecoderStep_stmt_some hv hstmt]
              rw [sourcePositionCodeDecoderStateFrom_resolved]
              simp [sourceSearchCodeDecoderRows,
                sourceSimStepDataForLabelIndexFromWithPositionCode_succ_of_stmt_some
                  hv hstmt]

noncomputable def sourcePositionCodeDecoderState (c : Code) (fuel k i : Nat) :
    SourceSearchCodeDecoderState :=
  sourcePositionCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderInit k i)

noncomputable def sourcePositionCodeDecoder (c : Code) (fuel k i : Nat) :
    List TM0FoldedCompiler.SimStepData :=
  sourceSearchCodeDecoderRows (sourcePositionCodeDecoderState c fuel k i)

set_option maxHeartbeats 800000 in
-- The accumulator proof expands a nested `nat_rec'` over product-coded decoder state.
theorem sourcePositionCodeDecoder_primrec_of_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourcePositionCodeDecoder p.1 p.2.1 p.2.2.1 p.2.2.2) := by
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
          sourcePositionCodeDecoderStep p.1 s.2) := by
    apply Primrec₂.mk
    exact hstep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  have hstate : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourcePositionCodeDecoderState p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    exact (Primrec.nat_rec' hfuel hbase hiterStep).of_eq fun p => by
      unfold sourcePositionCodeDecoderState sourceSearchCodeDecoderInit fuel kFn iFn
      rfl
  exact (sourceSearchCodeDecoderRows_primrec.comp hstate).of_eq fun p => by
    unfold sourcePositionCodeDecoder
    rfl

theorem sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode
    (c : Code) (fuel k i : Nat) :
    sourcePositionCodeDecoder c fuel k i =
      sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i := by
  unfold sourcePositionCodeDecoder sourcePositionCodeDecoderState sourceSearchCodeDecoderInit
  exact sourcePositionCodeDecoderRows_stateFrom_none_eq c fuel k i

theorem sourcePositionCodeDecoder_eq_nil_of_bound_le
    {c : Code} {fuel k i : Nat}
    (hi : fuel * TM0Route.partrecVarList.length ≤ i) :
    sourcePositionCodeDecoder c fuel k i = [] := by
  rw [sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode]
  exact sourceSimStepDataForLabelIndexFromWithPositionCode_eq_nil_of_bound_le hi

theorem sourcePositionCodeDecoder_eq_nil_of_statementCount_le
    (c : Code) (fuel k i : Nat) (hk : sourceStatementCount c ≤ k) :
    sourcePositionCodeDecoder c fuel k i = [] := by
  rw [sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode]
  exact sourceSimStepDataForLabelIndexFromWithPositionCode_eq_nil_of_statementCount_le
    c fuel k i hk

set_option linter.style.longLine false in
/--
For each fixed source code, the full generated position-code label-index
decoder is primitive recursive in the fuel, statement offset, and flat label
index.

The remaining final-reduction target is the uniform source-code version, where
the source code itself is an input.
-/
theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_fixed
    (c : Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode c p.1 p.2.1 p.2.2) := by
  let tc := NatPartrecToToPartrec.translate c
  exact (TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode_primrec_fixed
    tc).of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexFromWithPositionCode
      rfl

set_option linter.style.longLine false in
/-- Fixed-code primitive-recursiveness of the iterated generated position-code decoder. -/
theorem sourcePositionCodeDecoder_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      sourcePositionCodeDecoder c p.1 p.2.1 p.2.2) :=
  (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_fixed c).of_eq
    fun p =>
      (sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode
        c p.1 p.2.1 p.2.2).symm

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  (sourcePositionCodeDecoder_primrec_of_step hstep).of_eq fun p =>
    sourcePositionCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithPositionCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step
    (sourcePositionCodeDecoderStep_primrec_of_indexVarRows hvarRows)

set_option linter.style.longLine false in
/--
Under duplicate-free started-TM0 statement support, the source-specialized
position-code descriptor decoder agrees with the support-search-code decoder.

This exposes the main bridge between the cleaner generated position-code route
and the older support-search-code presentation.
-/
theorem sourceSimStepDataForLabelIndexFromWithPositionCode_eq_searchCode_of_statementList_nodup
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup)
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i =
      sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    sourceSimStepDataForLabelIndexFromWithSearchCode
  rw [TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal]
  · rw [TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_eq_withCode]
  · intro q hq
    exact TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_minimal_of_statementList_nodup
      (NatPartrecToToPartrec.translate c) (hnodup c) hq

set_option linter.style.longLine false in
/--
Support-search-code primitive recursiveness plus duplicate-free statement
support gives source-specialized position-code primitive recursiveness.
-/
theorem sourcePositionCodeLabelIndexFrom_primrec_of_searchCodeLabelIndexFrom
    (hsearch : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hsearch.of_eq fun p =>
    (sourceSimStepDataForLabelIndexFromWithPositionCode_eq_searchCode_of_statementList_nodup
      hnodup p.1 p.2.1 p.2.2.1 p.2.2.2).symm


end TM0FoldedReduction

end LeanWang
