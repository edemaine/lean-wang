/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Source

/-!
This module is split out from `LeanWang.TM0FoldedReduction` so Lake can
cache the machine-side reduction layers separately while preserving the old
public import path.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/-- Source-code version of the canonical offset-start descriptor decoder. -/
def sourceSimStepDataForLabelIndexStart
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStart
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical numeric-state offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical bounded-search offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithSearchCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
    (NatPartrecToToPartrec.translate c) i

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

/-- Source-code version of the canonical position-coded offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithPositionCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
    (NatPartrecToToPartrec.translate c) i

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

/-- Source-code version of the semantic label-index descriptor decoder. -/
def sourceSimStepDataForLabelIndex
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndex
    (NatPartrecToToPartrec.translate c) i

/-- Source-code indexed descriptor list for the folded finite-TM0 reduction. -/
def sourceSimStepDataByLabelIndex (c : Code) : List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndex c)

/-- Source-code indexed descriptor list through the numeric-state decoder path. -/
def sourceSimStepDataByLabelIndexWithCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithCode c)

/-- Source-code indexed descriptor list through the bounded-search decoder path. -/
def sourceSimStepDataByLabelIndexWithSearchCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithSearchCode c)

/-- Source-code indexed descriptor list through the position-coded decoder path. -/
def sourceSimStepDataByLabelIndexWithPositionCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithPositionCode c)

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_tail_after_firstBlock
    (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      (List.Ico TM0Route.partrecVarList.length (sourceLabelCount c)).flatMap
        (sourceSimStepDataForLabelIndexStartWithPositionCode c) := by
  unfold sourceSimStepDataByLabelIndexWithPositionCode
  rw [flatMap_range_dropPrefix
    (sourceSimStepDataForLabelIndexStartWithPositionCode c)
    (sourcePartrecVarList_length_le_sourceLabelCount c)]
  simp [sourceSimStepDataForLabelIndexStartWithPositionCode_firstBlock_eq_nil c]

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_interiorRowsByTailIndex
    (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      sourcePositionCodeInteriorRowsByTailIndex c := by
  rw [sourceSimStepDataByLabelIndexWithPositionCode_eq_tail_after_firstBlock]
  unfold sourcePositionCodeInteriorRowsByTailIndex
  apply flatMap_congr_of_mem
  intro n hn
  have hbounds :
      TM0Route.partrecVarList.length ≤ n ∧ n < sourceLabelCount c := by
    simpa using (List.Ico.mem (n := TM0Route.partrecVarList.length)
      (m := sourceLabelCount c) (l := n)).1 hn
  exact sourceSimStepDataForLabelIndexStartWithPositionCode_tail_index_eq
    (c := c) (n := n) hbounds.1 hbounds.2

theorem sourceSimStepDataForLabelIndexStart_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStart c i =
      sourceSimStepDataForLabelIndex c i := by
  unfold sourceSimStepDataForLabelIndexStart sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataForLabelIndexStart_eq
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithCode_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithCode c i =
      sourceSimStepDataForLabelIndex c i := by
  unfold sourceSimStepDataForLabelIndexStartWithCode sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode_eq
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
      sourceSimStepDataForLabelIndexStartWithCode c i := by
  unfold sourceSimStepDataForLabelIndexStartWithSearchCode
    sourceSimStepDataForLabelIndexStartWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
        (NatPartrecToToPartrec.translate c) i :=
  rfl

theorem sourceSimStepDataForLabelIndexFrom_eq_withCode
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFrom c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFrom sourceSimStepDataForLabelIndexFromWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexFrom_eq_withCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    sourceSimStepDataForLabelIndexFromWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataByLabelIndex_eq (c : Code) :
    sourceSimStepDataByLabelIndex c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndex sourceSimStepData sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataByLabelIndex_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithCode c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndexWithCode sourceSimStepData
  exact TM0FoldedCompiler.simStepDataByLabelIndexWithCode_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithSearchCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithSearchCode c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndexWithSearchCode sourceSimStepData
  exact TM0FoldedCompiler.simStepDataByLabelIndexWithSearchCode_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode
        (NatPartrecToToPartrec.translate c) := by
  rfl

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
    (c : Code)
    (hmin : ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      sourceSimStepDataByLabelIndexWithCode c := by
  change TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode
      (NatPartrecToToPartrec.translate c) =
    TM0FoldedCompiler.simStepDataByLabelIndexWithCode
      (NatPartrecToToPartrec.translate c)
  exact
    TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
      (NatPartrecToToPartrec.translate c) hmin

theorem sourceSimRowsOfStepDataByLabelIndexWithPositionCode_eq_of_minimal
    (c : Code)
    (hmin : ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    TM0FoldedCompiler.simRowsOfStepData
        (sourceSimStepDataByLabelIndexWithPositionCode c) =
      TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c) := by
  rw [sourceSimStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal c hmin]
  rw [sourceSimStepDataByLabelIndexWithCode_eq c]
  rw [sourceSimStepData_eq c]
  exact (TM0FoldedCompiler.simRows_eq_stepData
    (NatPartrecToToPartrec.translate c)).symm

/--
Primitive recursiveness of the translated source-level offset decoder is enough
for the source-level indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndex_primrec_of_source_labelIndexFrom
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndex := by
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStart p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFrom p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (sourceStatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStart sourceSimStepDataForLabelIndexFrom
        TM0FoldedCompiler.simStepDataForLabelIndexStart
      rfl
  have hlabel : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndex p.1 p.2) :=
    hstart.of_eq fun p => sourceSimStepDataForLabelIndexStart_eq p.1 p.2
  unfold sourceSimStepDataByLabelIndex
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hlabel

/--
Primitive recursiveness of the source-level canonical numeric-state decoder is
enough for the source-level numeric-state indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithCode := by
  unfold sourceSimStepDataByLabelIndexWithCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level bounded-search start decoder is
enough for the source-level bounded-search indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithSearchCode := by
  unfold sourceSimStepDataByLabelIndexWithSearchCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level position-coded start decoder is
enough for the source-level position-coded indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode := by
  unfold sourceSimStepDataByLabelIndexWithPositionCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_interiorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode :=
  (sourcePositionCodeInteriorRowsByTailIndex_primrec_of_interior hinterior).of_eq
    fun c => (sourceSimStepDataByLabelIndexWithPositionCode_eq_interiorRowsByTailIndex c).symm

/--
Primitive recursiveness of the source-level numeric-state offset decoder is
enough for primitive recursiveness of the source-level numeric-state indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexFromWithCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithCode := by
  apply sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithCode
        sourceSimStepDataForLabelIndexFromWithCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
      rfl
  exact hstart

/--
Primitive recursiveness of the source-level bounded-search offset decoder is
enough for primitive recursiveness of the source-level bounded-search indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_from
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithSearchCode := by
  apply sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithSearchCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithSearchCode
        sourceSimStepDataForLabelIndexFromWithSearchCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
      rfl
  exact hstart

/--
Primitive recursiveness of the source-level position-coded offset decoder is
enough for primitive recursiveness of the source-level position-coded indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode := by
  apply sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithPositionCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithPositionCode
        sourceSimStepDataForLabelIndexFromWithPositionCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
      rfl
  exact hstart

/--
The older global offset-decoder target implies the source-specific decoder
target by precomposing with the `Nat.Partrec.Code` translation.
-/
theorem sourceSimStepDataForLabelIndexFrom_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFrom
        rfl

/--
The source-level numeric-state offset decoder implies the source-level semantic
offset decoder by the data-level `WithCode` factoring theorem.
-/
theorem sourceSimStepDataForLabelIndexFrom_primrec_of_source_withCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hindex.of_eq fun p =>
    (sourceSimStepDataForLabelIndexFrom_eq_withCode p.1 p.2.1 p.2.2.1 p.2.2.2).symm

/--
The older global numeric-state offset-decoder target implies the source-specific
numeric-state decoder target by precomposing with the source translation.
-/
theorem sourceSimStepDataForLabelIndexFromWithCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithCode
        rfl

/--
The older global bounded-search offset-decoder target implies the
source-specific bounded-search decoder target by precomposing with the source
translation.
-/
theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithSearchCode
        rfl

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithPositionCode
        rfl

set_option linter.style.longLine false in
/--
The global position-code label-index decoder target implies the source-specific
target by precomposing with `NatPartrecToToPartrec.translate`.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex

set_option linter.style.longLine false in
/--
The global position-code label-index decoder target implies the generated
source-code accumulator-step target used by the preferred final route.
-/
theorem sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) :=
  sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex)

set_option linter.style.longLine false in
/-- Named version of `sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode`. -/
theorem sourcePositionCodeDecoderStepPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode hindex

set_option linter.style.longLine false in
/--
The source-specific position-code label-index decoder target implies the
generated source-code accumulator-step target used by the final route.
-/
theorem sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFromPrimrec
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode hindex

theorem sourceLabelAtByStatementFromWithPositionCode_code_mem_states
    {c : Code} {fuel k i : Nat}
    {q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat}
    (h : TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i = some q) :
    q.2 ∈ TM0Route.partrecStartedTM0States (NatPartrecToToPartrec.translate c) :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_code_mem_states
    (NatPartrecToToPartrec.translate c) h

theorem sourceLabelAtByStatementFromWithPositionCode_support_get?
    {c : Code} {fuel k i : Nat}
    {q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat}
    (h : TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i = some q) :
    (TM0Route.partrecStartedTM0LabelSupportList
        (NatPartrecToToPartrec.translate c))[q.2]? = some q.1 :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_support_get?
    (NatPartrecToToPartrec.translate c) h

theorem sourceLabelAtByStatementFromWithPositionCode_minimal_of_statementList_nodup
    {c : Code} {fuel k i : Nat}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    {q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat}
    (h : TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i = some q) :
    ∀ m, m < q.2 →
      (TM0Route.partrecStartedTM0LabelSupportList
        (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1 :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_minimal_of_statementList_nodup
    (NatPartrecToToPartrec.translate c) hnodup h

theorem sourceLabelSupportList_get_position_of_statementAt?
    {c : Code} {block i : Nat}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    (TM0Route.partrecStartedTM0LabelSupportList
      (NatPartrecToToPartrec.translate c))[
        1 + block * TM0Route.partrecVarList.length + i]? =
      some ((stmt, v) :
        Turing.TM1to0.Λ'
          (TM0Route.partrecStartedTM1Machine
            (NatPartrecToToPartrec.translate c))) :=
  TM0Route.partrecStartedTM0LabelSupportList_get_position_of_statementAt?
    (NatPartrecToToPartrec.translate c) hstmt hv

theorem sourcePosition_mem_states_of_statementAt?
    {c : Code} {block i : Nat}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    1 + block * TM0Route.partrecVarList.length + i ∈
      TM0Route.partrecStartedTM0States (NatPartrecToToPartrec.translate c) :=
  TM0Route.partrecStartedTM0_position_mem_states_of_statementAt?
    (NatPartrecToToPartrec.translate c) hstmt hv

theorem sourceStateCodeBySupportSearch_eq_stateCode_of_statementAt?
    {c : Code} {block i : Nat}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) block = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    TM0FiniteCompiler.stateCodeBySupportSearch
        (NatPartrecToToPartrec.translate c)
        (sourceStatementCount c)
        ((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))) =
      TM0FiniteCompiler.stateCode
        (NatPartrecToToPartrec.translate c)
        ((stmt, v) :
          Turing.TM1to0.Λ'
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c))) := by
  apply TM0FiniteCompiler.stateCodeBySupportSearch_eq_stateCode
  exact List.mem_iff_getElem?.2
    ⟨1 + block * TM0Route.partrecVarList.length + i,
      sourceLabelSupportList_get_position_of_statementAt? hstmt hv⟩

theorem sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSearchCodeOneRowsVar c k v =
      sourcePositionCodeOneRowsIndexVar c k i v := by
  cases hstmt : TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none =>
      rw [sourceSearchCodeOneRowsVar_stmt_none hstmt,
        sourcePositionCodeOneRowsIndexVar_stmt_none hstmt]
  | some stmt =>
      rw [sourceSearchCodeOneRowsVar_stmt_some hstmt,
        sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]
      have hsearch := sourceStateCodeBySupportSearch_eq_stateCode_of_statementAt?
        (c := c) (block := k) (i := i) (v := v) hstmt hv
      have hmin :
          ∀ m, m < TM0FoldedCompiler.labelPositionCode k i stmt v →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠
                some ((stmt, v) :
                  Turing.TM1to0.Λ'
                    (TM0Route.partrecStartedTM1Machine
                      (NatPartrecToToPartrec.translate c))) :=
        TM0FoldedCompiler.labelPositionCode_minimal_of_statementList_nodup
          (NatPartrecToToPartrec.translate c) hnodup hstmt hv
      have hposition :
          TM0FoldedCompiler.labelPositionCode k i stmt v =
            TM0FiniteCompiler.stateCode
              (NatPartrecToToPartrec.translate c)
              ((stmt, v) :
                Turing.TM1to0.Λ'
                  (TM0Route.partrecStartedTM1Machine
                    (NatPartrecToToPartrec.translate c))) :=
        TM0FoldedCompiler.labelPositionCode_eq_stateCode_of_minimal
          (NatPartrecToToPartrec.translate c) hstmt hv hmin
      have hcode :
          TM0FiniteCompiler.stateCodeBySupportSearch
              (NatPartrecToToPartrec.translate c)
              (sourceStatementCount c)
              ((stmt, v) :
                Turing.TM1to0.Λ'
                  (TM0Route.partrecStartedTM1Machine
                    (NatPartrecToToPartrec.translate c))) =
            TM0FoldedCompiler.labelPositionCode k i stmt v :=
        hsearch.trans hposition.symm
      exact congrArg
        (fun qCode => TM0FoldedCompiler.simStepDataForStmtLabelWithCode
          (NatPartrecToToPartrec.translate c) qCode stmt v) hcode

theorem sourceSearchCodeBoundedInteriorRowsVar_eq_positionCodeBoundedInteriorRowsIndexVar
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSearchCodeBoundedInteriorRowsVar c j v =
      sourcePositionCodeBoundedInteriorRowsIndexVar c j i v := by
  by_cases hlt : j + 1 < sourceStatementCount c
  · rw [sourceSearchCodeBoundedInteriorRowsVar_eq_interior hlt,
      sourcePositionCodeBoundedInteriorRowsIndexVar_eq_interior hlt]
    exact sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
      (c := c) (k := j + 1) (i := i) (v := v) hnodup hv
  · rw [sourceSearchCodeBoundedInteriorRowsVar_eq_nil hlt,
      sourcePositionCodeBoundedInteriorRowsIndexVar_eq_nil hlt]

theorem sourceSearchCodeInteriorRowsVar_eq_positionCodeInteriorRowsIndexVar
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSearchCodeInteriorRowsVar c j v =
      sourcePositionCodeInteriorRowsIndexVar c j i v :=
  sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
    (c := c) (k := j + 1) (i := i) (v := v) hnodup hv

def sourcePartrecVarIndex (v : TM0Route.PartrecVar) : Nat :=
  TM0Route.partrecVarList.findIdx fun w => decide (w = v)

theorem sourcePartrecVarIndex_primrec : Primrec sourcePartrecVarIndex := by
  unfold sourcePartrecVarIndex
  exact Primrec.list_findIdx₁ (l := TM0Route.partrecVarList)
    (Primrec.beq.comp₂ Primrec₂.right Primrec₂.left)

theorem sourcePartrecVarIndex_getElem? (v : TM0Route.PartrecVar) :
    TM0Route.partrecVarList[sourcePartrecVarIndex v]? = some v := by
  unfold sourcePartrecVarIndex
  have hmem : v ∈ TM0Route.partrecVarList := TM0Route.mem_partrecVarList v
  have hidx : TM0Route.partrecVarList.findIdx (fun w => decide (w = v)) <
      TM0Route.partrecVarList.length := by
    exact List.findIdx_lt_length_of_exists ⟨v, hmem, by simp⟩
  have hfind := (List.findIdx_eq (xs := TM0Route.partrecVarList)
    (p := fun w => decide (w = v)) hidx).1 rfl
  exact List.getElem?_eq_some_iff.2 ⟨hidx, of_decide_eq_true hfind.1⟩

theorem sourceSearchCodeOneRowsVar_primrec_of_positionCodeOneRows
    (hrows : SourcePositionCodeOneRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hposition : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar
        p.1 p.2.1 (sourcePartrecVarIndex p.2.2) p.2.2) :=
    hrows.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hidx (Primrec.snd.comp Primrec.snd))))
  exact hposition.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    exact (sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
      (c := p.1) (k := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

set_option linter.style.longLine false in
/--
The generated position-code accumulator step computes the bounded-search
one-row branch on the valid Partrec-variable index path.

This is weaker than `SourcePositionCodeOneRowsPrimrec`, which intentionally
keeps the numeric position-code slot independent of the variable.  It is
nevertheless the exact bridge needed to compare the generated position-code
decoder with the older bounded-search source presentation.
-/
theorem sourceSearchCodeOneRowsVar_primrec_of_positionCodeDecoderStep
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hnodup : SourceStatementListNodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hinput : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      (p.2.1, sourcePartrecVarIndex p.2.2,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.snd)
      (Primrec.pair hidx (Primrec.const none))
  have hstate : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeDecoderStep p.1
        (p.2.1, sourcePartrecVarIndex p.2.2,
          (none : Option (List TM0FoldedCompiler.SimStepData)))) :=
    hstep.comp (Primrec.pair Primrec.fst hinput)
  have hrows : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderRows
        (sourcePositionCodeDecoderStep p.1
          (p.2.1, sourcePartrecVarIndex p.2.2,
            (none : Option (List TM0FoldedCompiler.SimStepData))))) :=
    sourceSearchCodeDecoderRows_primrec.comp hstate
  exact hrows.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    simpa only [sourceSearchCodeDecoderRows, sourcePositionCodeDecoderStep,
      sourcePositionCodeDecoderStepNone, hv, Option.getD_some] using
      (sourceSearchCodeOneRowsVar_eq_positionCodeOneRowsIndexVar_of_statementList_nodup
      (c := p.1) (k := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

theorem sourceSearchCodeBoundedInteriorRowsVar_primrec_of_positionCodeBoundedInteriorRows
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hposition : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar
        p.1 p.2.1 (sourcePartrecVarIndex p.2.2) p.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hidx (Primrec.snd.comp Primrec.snd))))
  exact hposition.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    exact (sourceSearchCodeBoundedInteriorRowsVar_eq_positionCodeBoundedInteriorRowsIndexVar
      (c := p.1) (j := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

theorem sourceSearchCodeInteriorRowsVar_primrec_of_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hnodup : ∀ c : Code,
      (TM0Route.partrecStartedTM0StatementList
        (NatPartrecToToPartrec.translate c)).Nodup) :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2) := by
  have hidx : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePartrecVarIndex p.2.2) :=
    sourcePartrecVarIndex_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hposition : Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar
        p.1 p.2.1 (sourcePartrecVarIndex p.2.2) p.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair hidx (Primrec.snd.comp Primrec.snd))))
  exact hposition.of_eq fun p => by
    have hv :
        TM0Route.partrecVarList[sourcePartrecVarIndex p.2.2]? =
          some p.2.2 :=
      sourcePartrecVarIndex_getElem? p.2.2
    exact (sourceSearchCodeInteriorRowsVar_eq_positionCodeInteriorRowsIndexVar
      (c := p.1) (j := p.2.1) (i := sourcePartrecVarIndex p.2.2)
      (v := p.2.2) (hnodup p.1) hv).symm

theorem sourceSimStepDataForLabelIndexStartWithCode_of_block_var_get?
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
    sourceSimStepDataForLabelIndexStartWithCode c
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCode
          (NatPartrecToToPartrec.translate c)
          ((stmt, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        stmt v := by
  rw [← sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode]
  rw [sourceSimStepDataForLabelIndexStartWithSearchCode_of_block_var_get?
    (c := c) (block := block) (i := i) (v := v) hblock hv hstmt]
  have hcode := sourceStateCodeBySupportSearch_eq_stateCode_of_statementAt?
    (c := c) (block := block) (i := i) (v := v) hstmt hv
  simpa [sourceStatementCount] using congrArg
    (fun n => TM0FoldedCompiler.simStepDataForStmtLabelWithCode
      (NatPartrecToToPartrec.translate c) n stmt v) hcode

theorem sourceSimStepDataForLabelIndexStartWithCode_of_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithCode c i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCode
          (NatPartrecToToPartrec.translate c)
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
        (none : Option (Turing.TM1.Stmt
          (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
          (Turing.TM2to1.Λ'
            TM0Route.PartrecStack TM0Route.PartrecStackSymbol
            (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
            TM0Route.PartrecVar)
          TM0Route.PartrecVar))
        v := by
  simpa using
    sourceSimStepDataForLabelIndexStartWithCode_of_block_var_get?
      (c := c) (block := 0) (i := i) (v := v)
      (sourceStatementCount_pos c) hv (sourceStatementAt_zero c)

theorem sourceSimStepDataForLabelIndexStartWithCode_of_one_add_var_get?
    {c : Code} {i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexStartWithCode c
        (TM0Route.partrecVarList.length + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FiniteCompiler.stateCode
          (NatPartrecToToPartrec.translate c)
          ((sourceStatementOne c, v) :
            Turing.TM1to0.Λ'
              (TM0Route.partrecStartedTM1Machine
                (NatPartrecToToPartrec.translate c))))
        (sourceStatementOne c) v := by
  simpa [Nat.mul_one] using
    sourceSimStepDataForLabelIndexStartWithCode_of_block_var_get?
      (c := c) (block := 1) (i := i) (v := v)
      (sourceStatementCount_one_lt c) hv (sourceStatementAt_one c)

theorem sourceLabelAtByStatementFromWithPositionCode_eq_stateCode_of_minimal
    {c : Code} {fuel k i : Nat}
    (hmin : ∀ q :
        TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
          (NatPartrecToToPartrec.translate c) fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList
            (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
        (NatPartrecToToPartrec.translate c) fuel k i =
      TM0FoldedCompiler.labelAtByStatementFromWithStateCode?
        (NatPartrecToToPartrec.translate c) fuel k i :=
  TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_eq_stateCode_of_minimal
    (NatPartrecToToPartrec.translate c) hmin

theorem sourceMem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
    {c : Code} {fuel k i : Nat}
    {p : TM0FoldedCompiler.SimStepData}
    (h : p ∈ sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i) :
    ∃ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
          (NatPartrecToToPartrec.translate c) fuel k i = some q ∧
        p.2.2.1 = q.2 ∧
        (TM0Route.partrecStartedTM0LabelSupportList
          (NatPartrecToToPartrec.translate c))[p.2.2.1]? = some q.1 := by
  exact TM0FoldedCompiler.mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get? h

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
    {c : Code} {fuel k i : Nat}
    (hmin : ∀ q :
        TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
      TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
          (NatPartrecToToPartrec.translate c) fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList
            (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    sourceSimStepDataForLabelIndexFromWithCode
  exact
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
      (NatPartrecToToPartrec.translate c) hmin

theorem sourceSimStepDataForLabelIndexFromWithCode_primrec_of_source_searchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hindex.of_eq fun p =>
    sourceSimStepDataForLabelIndexFromWithSearchCode_eq_withCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

/--
Global primitive recursiveness of the canonical numeric-state decoder implies
the source-specific canonical numeric-state decoder target by precomposing with
the source-code translation.
-/
theorem sourceSimStepDataForLabelIndexStartWithCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexStartWithCode
        rfl

/--
Global primitive recursiveness of the folded descriptor list is enough for the
source-level normalized folded program-data map used by the final reduction.
-/
theorem sourceProgramData_computable_of_global_simStepData
    (hsteps : Primrec TM0FoldedCompiler.simStepData) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepData hsteps).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_simStepData'
    (hsteps : Primrec TM0FoldedCompiler.simStepData) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_simStepData hsteps).of_eq fun _ => rfl

-- The source-level indexed descriptor list is enough for computability of the
-- normalized folded finite-TM0 program data used by the final reduction.
set_option maxHeartbeats 800000 in
-- The final equality unfolds normalized program data and the descriptor rows.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndex
    (hsteps : Primrec sourceSimStepDataByLabelIndex) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndex c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndex_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- The final equality unfolds normalized program data and the descriptor rows.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithCode) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndexWithCode_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- The bounded-search indexed descriptor list is definitionally canonical after
-- the search-code row equality.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithSearchCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithSearchCode) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithSearchCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndexWithSearchCode_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- Position-coded rows need a separate row-equivalence proof because their
-- current-state field is the explicit support position rather than the
-- canonical `idxOf` state code.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithPositionCode)
    (hrows : ∀ c : Code,
      TM0FoldedCompiler.simRowsOfStepData
          (sourceSimStepDataByLabelIndexWithPositionCode c) =
        TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c)) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithPositionCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData sourceStateCount TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [hrows c]).to_comp

set_option maxHeartbeats 800000 in
-- The final equality unfolds generated program data and the position-coded descriptor rows.
/--
The source-level position-coded indexed descriptor list directly computes the
finite program generated from those descriptors.  No row-equivalence proof is
needed here: extra noncanonical rows remain part of this generated program and
are handled by separate semantic lookup lemmas.
-/
theorem sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithPositionCode) :
    Computable sourcePositionProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (sourceStateCount c)
        (sourceSimStepDataByLabelIndexWithPositionCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        sourceStateCount_primrec
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourcePositionProgramData sourceStateCount
      sourceSimStepDataByLabelIndexWithPositionCode
      TM0FoldedCompiler.positionProgramData
    rfl).to_comp

theorem sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_interiorRows hinterior)

theorem sourcePositionProgramData_computable_of_source_positionCodeBoundedInteriorRows
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
    (sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows
      (sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hbounded))

theorem sourcePositionProgramData_computable_of_source_positionCodeOneRows
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_positionCodeInteriorRows
    (sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows hrows)

theorem sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_simStepDataByLabelIndexWithPositionCode
    (sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from hindex)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the generated one-row-at-index decoder is enough
for computability of the source-specialized generated position-coded folded
program.
-/
theorem sourcePositionProgramData_computable_of_source_positionCodeOneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (sourcePositionCodeLabelIndexFromPrimrec_of_oneRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
The source-specialized position-code label-index decoder gives computability
of the source-specialized generated position-coded folded program.
-/
theorem sourcePositionProgramData_computable_of_sourcePositionCodeLabelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    hindex

set_option linter.style.longLine false in
theorem sourcePositionProgramData_computable_of_sourcePositionCodeLabelIndexFrom'
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)) :=
  (sourcePositionProgramData_computable_of_sourcePositionCodeLabelIndexFrom hindex).of_eq
    fun _ => rfl

set_option linter.style.longLine false in
/--
The global position-code label-index decoder gives computability of the
source-specialized generated position-coded folded program.
-/
theorem sourcePositionProgramData_computable_of_globalPositionCodeLabelIndexFrom
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    Computable sourcePositionProgramData :=
  sourcePositionProgramData_computable_of_source_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex)

set_option linter.style.longLine false in
theorem sourcePositionProgramData_computable_of_globalPositionCodeLabelIndexFrom'
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)) :=
  (sourcePositionProgramData_computable_of_globalPositionCodeLabelIndexFrom hindex).of_eq
    fun _ => rfl

/--
Primitive recursiveness of the source-level canonical numeric-state decoder is
enough for computability of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexStartWithCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode hindex)

theorem sourceProgramData_computable_of_source_labelIndexStartWithCode'
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexStartWithCode hindex).of_eq fun _ => rfl

/--
Primitive recursiveness of the source-level bounded-search start decoder is
enough for computability of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithSearchCode
    (sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start hindex)

theorem sourceProgramData_computable_of_source_labelIndexStartWithSearchCode'
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexStartWithSearchCode hindex).of_eq
    fun _ => rfl

/--
The remaining source-level folded computability target: primitive recursiveness
of the translated fully offset decoder implies computability of the normalized
folded finite-TM0 program data used by the final reduction.
-/
theorem sourceProgramData_computable_of_source_labelIndexFrom
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndex
    (sourceSimStepDataByLabelIndex_primrec_of_source_labelIndexFrom hindex)

theorem sourceProgramData_computable_of_source_labelIndexFrom'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFrom hindex).of_eq fun _ => rfl

/--
The numeric-state source-level folded computability target. This is equivalent
to the semantic source decoder target, but exposes the state code fed to the
finite program.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexFromWithCode hindex)

theorem sourceProgramData_computable_of_source_labelIndexFromWithCode'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFromWithCode hindex).of_eq fun _ => rfl

/--
The source-level bounded-search decoder target is enough for computability of
the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithSearchCode
    (sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_from hindex)

theorem sourceProgramData_computable_of_source_labelIndexFromWithSearchCode'
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_source_labelIndexFromWithSearchCode hindex).of_eq
    fun _ => rfl

end TM0FoldedReduction

end LeanWang

end
