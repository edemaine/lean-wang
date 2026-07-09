/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Source

/-!
Core offset-start descriptor definitions and pointwise position-code start lemmas.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

noncomputable def sourceSimStepDataForLabelIndexStart
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStart
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical numeric-state offset-start decoder. -/
noncomputable def sourceSimStepDataForLabelIndexStartWithCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical bounded-search offset-start decoder. -/
noncomputable def sourceSimStepDataForLabelIndexStartWithSearchCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
    (NatPartrecToToPartrec.translate c) i

set_option linter.style.longLine false in
/-- Primitive-recursion target for the global numeric-state start decoder. -/
abbrev GlobalCodeLabelIndexStartPrimrec : Prop :=
  Primrec (fun p : Turing.ToPartrec.Code × Nat =>
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)

set_option linter.style.longLine false in
/-- Primitive-recursion target for the source-specialized numeric-state start decoder. -/
abbrev SourceCodeLabelIndexStartPrimrec : Prop :=
  Primrec (fun p : Code × Nat =>
    sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)

set_option linter.style.longLine false in
/-- Primitive-recursion target for the source-specialized bounded-search start decoder. -/
abbrev SourceSearchCodeLabelIndexStartPrimrec : Prop :=
  Primrec (fun p : Code × Nat =>
    sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexStartSplit? c i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
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
  unfold sourceSimStepDataForLabelIndexStartWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
  change sourceSimStepDataForLabelIndexFromWithSearchCode c
      (sourceStatementCount c) 0 i =
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
  unfold sourceLabelIndexStartSplit? at hsplit
  exact sourceSimStepDataForLabelIndexFromWithSearchCode_of_split hsplit hstmt

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_block_var_get?
    {c : Code} {block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < sourceStatementCount c)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c
        (TM0Route.partrecVarList.length * block + i) =
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
  exact sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    (sourceLabelIndexStartSplit?_of_block_var_get? (c := c) hblock hv) hstmt

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((none, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar))
        v := by
  exact sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    (sourceLabelIndexStartSplit?_of_var_get? (c := c) hv) (sourceStatementAt_zero c)

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c
        (TM0Route.partrecVarList.length + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCodeBySupportSearch
          (NatPartrecToToPartrec.translate c)
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate c))
          ((sourceStatementOne c, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (sourceStatementOne c) v := by
  exact sourceSimStepDataForLabelIndexStartWithSearchCode_of_split
    (sourceLabelIndexStartSplit?_of_one_add_var_get? (c := c) hv) (sourceStatementAt_one c)

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_eq_nil_of_labelCount_le
    {c : Code} {i : Nat} (hi : sourceLabelCount c ≤ i) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i = [] := by
  unfold sourceSimStepDataForLabelIndexStartWithSearchCode
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
  change sourceSimStepDataForLabelIndexFromWithSearchCode c
      (sourceStatementCount c) 0 i = []
  rw [sourceLabelCount_eq_statementCount_mul] at hi
  exact sourceSimStepDataForLabelIndexFromWithSearchCode_eq_nil_of_bound_le hi

/-- Source-code version of the canonical position-coded offset-start decoder. -/
noncomputable def sourceSimStepDataForLabelIndexStartWithPositionCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
    (NatPartrecToToPartrec.translate c) i

set_option linter.style.longLine false in
/--
Primitive-recursion target for the source-level position-coded start decoder.
This is weaker than the full offset decoder target: the fuel is fixed to the
translated source statement count and the statement offset is fixed to zero,
which is exactly the decoder used to build `positionProgramData`.
-/
abbrev SourcePositionCodeLabelIndexStartPrimrec : Prop :=
  Primrec (fun p : Code × Nat =>
    sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2)

set_option linter.style.longLine false in
/--
For a fixed source code, the canonical start decoder is primitive recursive in
the flat label index.

The final source target is stronger: it must be uniform in the source code
itself.  This fixed-code lemma records that the remaining difficulty is that
uniformity, not the start-offset arithmetic.
-/
theorem sourceSimStepDataForLabelIndexStart_primrec_fixed (c : Code) :
    Primrec (sourceSimStepDataForLabelIndexStart c) := by
  let tc := NatPartrecToToPartrec.translate c
  exact (TM0FoldedCompiler.simStepDataForLabelIndexStart_primrec_fixed
    tc).of_eq fun i => by
      unfold sourceSimStepDataForLabelIndexStart
      rfl

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of the numeric-state start decoder. -/
theorem sourceSimStepDataForLabelIndexStartWithCode_primrec_fixed (c : Code) :
    Primrec (sourceSimStepDataForLabelIndexStartWithCode c) := by
  let tc := NatPartrecToToPartrec.translate c
  exact (TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode_primrec_fixed
    tc).of_eq fun i => by
      unfold sourceSimStepDataForLabelIndexStartWithCode
      rfl

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of the support-search start decoder. -/
theorem sourceSimStepDataForLabelIndexStartWithSearchCode_primrec_fixed
    (c : Code) :
    Primrec (sourceSimStepDataForLabelIndexStartWithSearchCode c) := by
  let tc := NatPartrecToToPartrec.translate c
  exact (TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode_primrec_fixed
    tc).of_eq fun i => by
      unfold sourceSimStepDataForLabelIndexStartWithSearchCode
      rfl

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of the position-coded start decoder. -/
theorem sourceSimStepDataForLabelIndexStartWithPositionCode_primrec_fixed
    (c : Code) :
    Primrec (sourceSimStepDataForLabelIndexStartWithPositionCode c) := by
  let tc := NatPartrecToToPartrec.translate c
  exact (TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode_primrec_fixed
    tc).of_eq fun i => by
      unfold sourceSimStepDataForLabelIndexStartWithPositionCode
      rfl

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_split
    {c : Code} {i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexStartSplit? c i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode stmtIndex
          (i % TM0Route.partrecVarList.length) stmt v) stmt v := by
  unfold sourceSimStepDataForLabelIndexStartWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
  change sourceSimStepDataForLabelIndexFromWithPositionCode c
      (sourceStatementCount c) 0 i =
    TM0FoldedCompiler.simStepDataForStmtLabelWithCode
      (NatPartrecToToPartrec.translate c)
      (TM0FoldedCompiler.labelPositionCode stmtIndex
        (i % TM0Route.partrecVarList.length) stmt v) stmt v
  unfold sourceLabelIndexStartSplit? at hsplit
  exact sourceSimStepDataForLabelIndexFromWithPositionCode_of_split hsplit hstmt

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
    {c : Code} {block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < sourceStatementCount c)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode block i stmt v) stmt v := by
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  rw [sourceSimStepDataForLabelIndexStartWithPositionCode_of_split
    (sourceLabelIndexStartSplit?_of_block_var_get? (c := c) hblock hv) hstmt]
  simp [hmod]

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode 0 i
          (none : Option (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
            (Turing.TM2to1.Λ'
              TM0Route.PartrecStack TM0Route.PartrecStackSymbol
              (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
              TM0Route.PartrecVar)
            TM0Route.PartrecVar)) v)
        (none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar))
        v := by
  simpa using
    sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
      (c := c) (block := 0) (i := i) (v := v)
      (sourceStatementCount_pos c) hv (sourceStatementAt_zero c)

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_var_get?_eq_nil
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i = [] := by
  rw [sourceSimStepDataForLabelIndexStartWithPositionCode_of_var_get? hv]
  exact TM0FoldedCompiler.simStepDataForStmtLabelWithCode_none
    (NatPartrecToToPartrec.translate c)
    (TM0FoldedCompiler.labelPositionCode 0 i
      (none : Option (Turing.TM1.Stmt
        (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
        (Turing.TM2to1.Λ'
          TM0Route.PartrecStack TM0Route.PartrecStackSymbol
          (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
          TM0Route.PartrecVar)
        TM0Route.PartrecVar))
      v)
    v

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_eq_nil_of_lt
    {c : Code} {i : Nat}
    (hi : i < TM0Route.partrecVarList.length) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i = [] := by
  have hv :
      TM0Route.partrecVarList[i]? = some (TM0Route.partrecVarList[i]) :=
    List.getElem?_eq_getElem hi
  exact sourceSimStepDataForLabelIndexStartWithPositionCode_of_var_get?_eq_nil hv

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_range_eq_nil
    (c : Code) (n : Nat) (hn : n ≤ TM0Route.partrecVarList.length) :
    (List.range n).flatMap
        (sourceSimStepDataForLabelIndexStartWithPositionCode c) =
      [] := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      have hprefix : n ≤ TM0Route.partrecVarList.length := Nat.le_of_succ_le hn
      have hlast : n < TM0Route.partrecVarList.length := hn
      simp [ih hprefix,
        sourceSimStepDataForLabelIndexStartWithPositionCode_eq_nil_of_lt
          (c := c) hlast]

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_firstBlock_eq_nil
    (c : Code) :
    (List.range TM0Route.partrecVarList.length).flatMap
        (sourceSimStepDataForLabelIndexStartWithPositionCode c) =
      [] :=
  sourceSimStepDataForLabelIndexStartWithPositionCode_range_eq_nil
    c TM0Route.partrecVarList.length (le_refl _)

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_eq_nil_of_labelCount_le
    {c : Code} {i : Nat} (hi : sourceLabelCount c ≤ i) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i = [] := by
  unfold sourceSimStepDataForLabelIndexStartWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  change (TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
      (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i).elim []
      (fun q => TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c) q.2 q.1.1 q.1.2) = []
  rw [sourceLabelAtByStatementStartWithPositionCode?_eq_none_of_labelCount_le
    (c := c) (i := i) hi]
  rfl

theorem sourcePartrecVarList_length_le_sourceLabelCount (c : Code) :
    TM0Route.partrecVarList.length ≤ sourceLabelCount c := by
  rw [sourceLabelCount_eq_statementCount_mul]
  nth_rewrite 1 [← Nat.one_mul TM0Route.partrecVarList.length]
  exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (sourceStatementCount_pos c))

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode 1 i (sourceStatementOne c) v)
        (sourceStatementOne c) v := by
  simpa [Nat.mul_one] using
    sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
      (c := c) (block := 1) (i := i) (v := v)
      (sourceStatementCount_one_lt c) hv (sourceStatementAt_one c)

theorem sourcePositionCodeOneRowsAtIndex_one_eq_startWithPositionCode_of_lt
    {c : Code} {i : Nat} (hi : i < TM0Route.partrecVarList.length) :
    sourcePositionCodeOneRowsAtIndex c 1 i =
      sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length + i) := by
  have hv :
      TM0Route.partrecVarList[i]? = some (TM0Route.partrecVarList[i]) :=
    List.getElem?_eq_getElem hi
  rw [sourcePositionCodeOneRowsAtIndex_of_var_get? hv]
  rw [sourcePositionCodeOneRowsIndexVar_one]
  exact (sourceSimStepDataForLabelIndexStartWithPositionCode_of_one_add_var_get?
    (c := c) (i := i) (v := TM0Route.partrecVarList[i]) hv).symm

theorem sourcePositionCodeOneRowsAtIndex_one_eq_nil_of_length_le
    {c : Code} {i : Nat} (hi : TM0Route.partrecVarList.length ≤ i) :
    sourcePositionCodeOneRowsAtIndex c 1 i = [] := by
  have hv : TM0Route.partrecVarList[i]? = none :=
    List.getElem?_eq_none_iff.2 hi
  exact sourcePositionCodeOneRowsAtIndex_eq_nil_of_var_none hv

theorem sourcePositionCodeFirstInteriorRowsAtIndexPrimrec_of_labelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeFirstInteriorRowsAtIndexPrimrec := by
  have hinRange : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1
        (TM0Route.partrecVarList.length + p.2)) :=
    hstart.comp
      (Primrec.pair Primrec.fst
        (Primrec.nat_add.comp
          (Primrec.const TM0Route.partrecVarList.length) Primrec.snd))
  have houtRange : Primrec (fun _p : Code × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hlt : PrimrecPred (fun p : Code × Nat =>
      p.2 < TM0Route.partrecVarList.length) :=
    Primrec.nat_lt.comp Primrec.snd
      (Primrec.const TM0Route.partrecVarList.length)
  exact (Primrec.ite hlt hinRange houtRange).of_eq fun p => by
    by_cases hi : p.2 < TM0Route.partrecVarList.length
    · simp [hi,
        sourcePositionCodeOneRowsAtIndex_one_eq_startWithPositionCode_of_lt
          (c := p.1) (i := p.2) hi]
    · have hle : TM0Route.partrecVarList.length ≤ p.2 := Nat.le_of_not_gt hi
      simp [hi, sourcePositionCodeOneRowsAtIndex_one_eq_nil_of_length_le
        (c := p.1) (i := p.2) hle]

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_interior_var_get?
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hj : j + 1 < sourceStatementCount c)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length * (j + 1) + i) =
      sourcePositionCodeInteriorRowsIndexVar c j i v := by
  rcases sourceStatementAt?_exists_of_lt (c := c) (i := j + 1) hj with
    ⟨stmt, hstmt⟩
  rw [sourceSimStepDataForLabelIndexStartWithPositionCode_of_block_var_get?
    (c := c) (block := j + 1) (i := i) (v := v) hj hv hstmt]
  rw [sourcePositionCodeInteriorRowsIndexVar,
    sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_of_interior_index_lt
    {c : Code} {j i : Nat}
    (hj : j + 1 < sourceStatementCount c)
    (hi : i < TM0Route.partrecVarList.length) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c
        (TM0Route.partrecVarList.length * (j + 1) + i) =
      sourcePositionCodeInteriorRowsIndexVar c j i (TM0Route.partrecVarList[i]) := by
  exact sourceSimStepDataForLabelIndexStartWithPositionCode_of_interior_var_get?
    (c := c) (j := j) (i := i) (v := TM0Route.partrecVarList[i]) hj
    (List.getElem?_eq_getElem hi)

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_interior_block_range_eq
    (c : Code) (j n : Nat)
    (hj : j + 1 < sourceStatementCount c)
    (hn : n ≤ TM0Route.partrecVarList.length) :
    (List.range n).flatMap
        (fun i => sourceSimStepDataForLabelIndexStartWithPositionCode c
          (TM0Route.partrecVarList.length * (j + 1) + i)) =
      (List.range n).flatMap
        (sourcePositionCodeInteriorRowsAtIndex c j) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      have hprefix : n ≤ TM0Route.partrecVarList.length := Nat.le_of_succ_le hn
      have hlast : n < TM0Route.partrecVarList.length := hn
      have hslot :
          sourceSimStepDataForLabelIndexStartWithPositionCode c
              (TM0Route.partrecVarList.length * (j + 1) + n) =
            sourcePositionCodeInteriorRowsAtIndex c j n := by
        rw [sourceSimStepDataForLabelIndexStartWithPositionCode_of_interior_index_lt
          (c := c) (j := j) (i := n) hj hlast]
        rw [sourcePositionCodeInteriorRowsAtIndex_of_var_get?
          (c := c) (j := j) (i := n) (v := TM0Route.partrecVarList[n])
          (List.getElem?_eq_getElem hlast)]
  -- `simp` uses the induction hypothesis for the prefix and `hslot` for the
  -- newly appended slot.
      simp [ih hprefix, hslot]

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_interior_block_eq
    (c : Code) (j : Nat)
    (hj : j + 1 < sourceStatementCount c) :
    (List.range TM0Route.partrecVarList.length).flatMap
        (fun i => sourceSimStepDataForLabelIndexStartWithPositionCode c
          (TM0Route.partrecVarList.length * (j + 1) + i)) =
      (List.range TM0Route.partrecVarList.length).flatMap
        (sourcePositionCodeInteriorRowsAtIndex c j) :=
  sourceSimStepDataForLabelIndexStartWithPositionCode_interior_block_range_eq
    c j TM0Route.partrecVarList.length hj (le_refl _)

set_option linter.style.longLine false in
/--
The source-level position-code start decoder recovers the pointwise
interior-row target.  The proof branches on whether the requested numeric slot
is a genuine `partrecVarList` entry; for genuine slots it reads the flat
started decoder at row `j + 1`, and for out-of-range slots it returns the known
empty row directly.
-/
theorem sourcePositionCodeInteriorRowsAtIndexPrimrec_of_labelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeInteriorRowsAtIndexPrimrec := by
  let width : Nat := TM0Route.partrecVarList.length
  let flatIndex : Code × Nat × Nat → Nat :=
    fun p => width * (p.2.1 + 1) + p.2.2
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnil : Primrec (fun _p : Code × Nat × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hflatIndex : Primrec flatIndex := by
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const width)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have hstartAt : Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 (flatIndex p)) :=
    hstart.comp (Primrec.pair Primrec.fst hflatIndex)
  have hbound : PrimrecPred (fun p : Code × Nat × Nat =>
      p.2.1 + 1 < sourceStatementCount p.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (sourceStatementCount_primrec.comp Primrec.fst)
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun _v : TM0Route.PartrecVar =>
      if p.2.1 + 1 < sourceStatementCount p.1 then
        sourceSimStepDataForLabelIndexStartWithPositionCode p.1 (flatIndex p)
      else
        []) := by
    apply Primrec₂.mk
    exact Primrec.ite (hbound.comp Primrec.fst)
      (hstartAt.comp Primrec.fst)
      (Primrec.const ([] : List TM0FoldedCompiler.SimStepData))
  exact (Primrec.option_casesOn hlookup hnil hsome).of_eq fun p => by
    cases hv : TM0Route.partrecVarList[p.2.2]? with
    | none =>
        simp [sourcePositionCodeInteriorRowsAtIndex, hv]
    | some v =>
        by_cases hb : p.2.1 + 1 < sourceStatementCount p.1
        · have hslot :
            sourceSimStepDataForLabelIndexStartWithPositionCode p.1
                (TM0Route.partrecVarList.length * (p.2.1 + 1) + p.2.2) =
              sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2 v :=
            sourceSimStepDataForLabelIndexStartWithPositionCode_of_interior_var_get?
              (c := p.1) (j := p.2.1) (i := p.2.2) (v := v) hb hv
          simp [sourcePositionCodeInteriorRowsAtIndex, hv, hb, flatIndex, width, hslot]
        · have hbLe : sourceStatementCount p.1 ≤ p.2.1 + 1 :=
            Nat.le_of_not_gt hb
          have hlabelLe :
              sourceLabelCount p.1 ≤
                TM0Route.partrecVarList.length * (p.2.1 + 1) + p.2.2 := by
            rw [sourceLabelCount_eq_statementCount_mul]
            calc
              sourceStatementCount p.1 * TM0Route.partrecVarList.length ≤
                  (p.2.1 + 1) * TM0Route.partrecVarList.length :=
                Nat.mul_le_mul_right TM0Route.partrecVarList.length hbLe
              _ = TM0Route.partrecVarList.length * (p.2.1 + 1) := by
                rw [Nat.mul_comm]
              _ ≤ TM0Route.partrecVarList.length * (p.2.1 + 1) + p.2.2 :=
                Nat.le_add_right _ _
          have hstartNil :
              sourceSimStepDataForLabelIndexStartWithPositionCode p.1
                  (TM0Route.partrecVarList.length * (p.2.1 + 1) + p.2.2) = [] :=
            sourceSimStepDataForLabelIndexStartWithPositionCode_eq_nil_of_labelCount_le
              (c := p.1)
              (i := TM0Route.partrecVarList.length * (p.2.1 + 1) + p.2.2)
              hlabelLe
          have hinteriorNil :
              sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2 v = [] := by
            unfold sourcePositionCodeInteriorRowsIndexVar
            exact sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le v hbLe
          simp [sourcePositionCodeInteriorRowsAtIndex, hv, hb, hinteriorNil]

set_option linter.style.longLine false in
/--
The source-level position-code start decoder also recovers the bounded
interior at-index target used by the accumulator route.
-/
theorem sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_labelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
    (sourcePositionCodeInteriorRowsAtIndexPrimrec_of_labelIndexStart hstart)

set_option linter.style.longLine false in
/--
The position-code start decoder is already strong enough to recover the full
source-specialized offset decoder target: first recover pointwise interior rows,
then use the existing bounded-interior accumulator route.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_labelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeLabelIndexFromPrimrec_of_interiorAtIndex
    (sourcePositionCodeInteriorRowsAtIndexPrimrec_of_labelIndexStart hstart)

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_tail_index_eq
    {c : Code} {n : Nat}
    (hlo : TM0Route.partrecVarList.length ≤ n)
    (hhi : n < sourceLabelCount c) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c n =
      sourcePositionCodeInteriorRowsAtIndex c
        (n / TM0Route.partrecVarList.length - 1)
        (n % TM0Route.partrecVarList.length) := by
  have hmod :
      n % TM0Route.partrecVarList.length < TM0Route.partrecVarList.length :=
    Nat.mod_lt n sourcePartrecVarList_length_pos
  let v : TM0Route.PartrecVar :=
    TM0Route.partrecVarList[n % TM0Route.partrecVarList.length]'hmod
  have hv :
      TM0Route.partrecVarList[n % TM0Route.partrecVarList.length]? = some v := by
    simp [v, List.getElem?_eq_getElem (l := TM0Route.partrecVarList) hmod]
  have hblock_pos : 0 < n / TM0Route.partrecVarList.length :=
    Nat.div_pos hlo sourcePartrecVarList_length_pos
  have hblock_lt :
      n / TM0Route.partrecVarList.length < sourceStatementCount c :=
    sourceLabelIndexStartSplit?_block_lt_of_lt_labelCount hhi
  have hj :
      n / TM0Route.partrecVarList.length - 1 + 1 < sourceStatementCount c := by
    rwa [Nat.sub_one_add_one (Nat.ne_of_gt hblock_pos)]
  have hidx :
      TM0Route.partrecVarList.length *
          (n / TM0Route.partrecVarList.length - 1 + 1) +
        n % TM0Route.partrecVarList.length = n := by
    rw [Nat.sub_one_add_one (Nat.ne_of_gt hblock_pos)]
    simpa [Nat.mul_comm] using Nat.div_add_mod n TM0Route.partrecVarList.length
  calc
    sourceSimStepDataForLabelIndexStartWithPositionCode c n =
        sourceSimStepDataForLabelIndexStartWithPositionCode c
          (TM0Route.partrecVarList.length *
              (n / TM0Route.partrecVarList.length - 1 + 1) +
            n % TM0Route.partrecVarList.length) := by
          exact (congrArg (sourceSimStepDataForLabelIndexStartWithPositionCode c)
            hidx).symm
    _ = sourcePositionCodeInteriorRowsIndexVar c
          (n / TM0Route.partrecVarList.length - 1)
          (n % TM0Route.partrecVarList.length) v := by
          rw [sourceSimStepDataForLabelIndexStartWithPositionCode_of_interior_var_get?
            (c := c) (j := n / TM0Route.partrecVarList.length - 1)
            (i := n % TM0Route.partrecVarList.length) (v := v) hj hv]
    _ = sourcePositionCodeInteriorRowsAtIndex c
          (n / TM0Route.partrecVarList.length - 1)
          (n % TM0Route.partrecVarList.length) := by
          exact (sourcePositionCodeInteriorRowsAtIndex_of_var_get?
            (c := c) (j := n / TM0Route.partrecVarList.length - 1)
            (i := n % TM0Route.partrecVarList.length) (v := v) hv).symm

end TM0FoldedReduction

end LeanWang
