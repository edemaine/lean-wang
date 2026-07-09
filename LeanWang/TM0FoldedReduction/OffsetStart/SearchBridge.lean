/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.OffsetStart.Indexed

/-!
Bridges between support-search descriptors, position-code descriptors, and
canonical numeric-state descriptors.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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

end TM0FoldedReduction

end LeanWang
