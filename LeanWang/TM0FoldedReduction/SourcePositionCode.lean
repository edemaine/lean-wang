/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourceCore

/-!
Source-specialized generated position-code descriptor decoder.

The source arithmetic and bounded-search decoder live in `SourceCore`; this
module contains the generated position-coded row decoder that is the current
machine-side proof frontier.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
Source-code version of the offset descriptor decoder whose current-state code
is the explicit statement/variable position.
-/
def sourceSimStepDataForLabelIndexFromWithPositionCode
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_of_split
    {c : Code} {fuel k i stmtIndex : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hsplit : sourceLabelIndexFromSplit? fuel k i = some (stmtIndex, v))
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) stmtIndex = some stmt) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k i =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode stmtIndex
          (i % TM0Route.partrecVarList.length) stmt v) stmt v := by
  unfold sourceSimStepDataForLabelIndexFromWithPositionCode
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
  rw [sourceLabelAtByStatementFromWithPositionCode?_of_split hsplit hstmt]
  rfl

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
    {c : Code} {fuel k block i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hblock : block < fuel)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) (k + block) = some stmt) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c fuel k
        (TM0Route.partrecVarList.length * block + i) =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode (k + block) i stmt v) stmt v := by
  rw [sourceSimStepDataForLabelIndexFromWithPositionCode_of_split
    (sourceLabelIndexFromSplit?_of_block_var_get? hblock hv) hstmt]
  rcases List.getElem?_eq_some_iff.1 hv with ⟨hi, _hget⟩
  have hmod :
      (TM0Route.partrecVarList.length * block + i) %
          TM0Route.partrecVarList.length = i := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  simp [hmod]

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_var_get?
    {c : Code} {fuel i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0 i = [] := by
  simpa using
    (sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
      (c := c) (fuel := fuel + 1) (k := 0) (block := 0)
      (i := i) (v := v) (Nat.zero_lt_succ fuel) hv
      (sourceStatementAt_zero c)).trans
      (TM0FoldedCompiler.simStepDataForStmtLabelWithCode_none
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
        v)

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_eq_nil_of_lt
    {c : Code} {fuel i : Nat}
    (hi : i < TM0Route.partrecVarList.length) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0 i = [] := by
  have hv :
      TM0Route.partrecVarList[i]? = some (TM0Route.partrecVarList[i]) :=
    List.getElem?_eq_getElem hi
  exact sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_var_get? hv

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_range_eq_nil
    (c : Code) (fuel n : Nat) (hn : n ≤ TM0Route.partrecVarList.length) :
    (List.range n).flatMap
        (sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0) =
      [] := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      have hprefix : n ≤ TM0Route.partrecVarList.length := Nat.le_of_succ_le hn
      have hlast : n < TM0Route.partrecVarList.length := hn
      simp [ih hprefix,
        sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_eq_nil_of_lt
          (c := c) (fuel := fuel) hlast]

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_full_range_eq_nil
    (c : Code) (fuel : Nat) :
    (List.range TM0Route.partrecVarList.length).flatMap
        (sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0) =
      [] :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_range_eq_nil
    c fuel TM0Route.partrecVarList.length (le_refl _)

theorem flatMap_range_dropPrefix {α : Type} (f : Nat → List α) {n count : Nat}
    (hn : n ≤ count) :
    (List.range count).flatMap f =
      (List.range n).flatMap f ++ (List.Ico n count).flatMap f := by
  have hsplit :
      List.range count = List.range n ++ List.Ico n count := by
    calc
      List.range count = List.Ico 0 count := by
        exact (List.Ico.zero_bot count).symm
      _ = List.Ico 0 n ++ List.Ico n count := by
        exact (List.Ico.append_consecutive (Nat.zero_le n) hn).symm
      _ = List.range n ++ List.Ico n count := by
        rw [List.Ico.zero_bot]
  rw [hsplit]
  simp [List.flatMap_append]

theorem flatMap_congr_of_mem {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem sourcePartrecVarList_length_le_partrecVarList_length_mul_succ
    (fuel : Nat) :
    TM0Route.partrecVarList.length ≤
      TM0Route.partrecVarList.length * (fuel + 1) := by
  nth_rewrite 1 [← Nat.mul_one TM0Route.partrecVarList.length]
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le fuel))

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_eq_tail_after_zero_block
    (c : Code) (fuel : Nat) :
    (List.range (TM0Route.partrecVarList.length * (fuel + 1))).flatMap
        (sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0) =
      (List.Ico TM0Route.partrecVarList.length
          (TM0Route.partrecVarList.length * (fuel + 1))).flatMap
        (sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0) := by
  rw [flatMap_range_dropPrefix
    (sourceSimStepDataForLabelIndexFromWithPositionCode c (fuel + 1) 0)
    (sourcePartrecVarList_length_le_partrecVarList_length_mul_succ fuel)]
  simp [sourceSimStepDataForLabelIndexFromWithPositionCode_zero_block_full_range_eq_nil c fuel]

def sourcePositionCodeOneRowsIndexVar
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  match TM0Route.partrecStartedTM0StatementAt?
      (NatPartrecToToPartrec.translate c) k with
  | none => []
  | some stmt =>
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode k i stmt v)
        stmt v

theorem sourcePositionCodeOneRowsIndexVar_stmt_none
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = none) :
    sourcePositionCodeOneRowsIndexVar c k i v = [] := by
  simp [sourcePositionCodeOneRowsIndexVar, hstmt]

theorem sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le
    {c : Code} {k i : Nat} (v : TM0Route.PartrecVar)
    (hk : sourceStatementCount c ≤ k) :
    sourcePositionCodeOneRowsIndexVar c k i v = [] := by
  exact sourcePositionCodeOneRowsIndexVar_stmt_none
    (TM0Route.partrecStartedTM0StatementAt?_eq_none_of_count_le
      (NatPartrecToToPartrec.translate c) (by simpa [sourceStatementCount] using hk))

theorem sourcePositionCodeOneRowsIndexVar_statementCount_add
    (c : Code) (offset i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c (sourceStatementCount c + offset) i v = [] :=
  sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le v
    (Nat.le_add_right _ _)

theorem sourcePositionCodeOneRowsIndexVar_statementCount_add_primrec :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1
        (sourceStatementCount p.1 + p.2.1) p.2.2.1 p.2.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourcePositionCodeOneRowsIndexVar_statementCount_add
      p.1 p.2.1 p.2.2.1 p.2.2.2).symm

theorem sourcePositionCodeOneRowsIndexVar_stmt_some
    {c : Code} {k i : Nat} {v : TM0Route.PartrecVar}
    {stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)
      (Turing.TM2to1.Λ'
        TM0Route.PartrecStack TM0Route.PartrecStackSymbol
        (TM0Route.StartedLabel (NatPartrecToToPartrec.translate c))
        TM0Route.PartrecVar)
      TM0Route.PartrecVar)}
    (hstmt : TM0Route.partrecStartedTM0StatementAt?
        (NatPartrecToToPartrec.translate c) k = some stmt) :
    sourcePositionCodeOneRowsIndexVar c k i v =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode k i stmt v)
        stmt v := by
  simp [sourcePositionCodeOneRowsIndexVar, hstmt]

theorem sourcePositionCodeOneRowsIndexVar_zero
    (c : Code) (i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c 0 i v = [] := by
  rw [sourcePositionCodeOneRowsIndexVar_stmt_some (sourceStatementAt_zero c)]
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

theorem sourcePositionCodeOneRowsIndexVar_zero_primrec :
    Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 0 p.2.1 p.2.2) := by
  exact (Primrec.const ([] : List TM0FoldedCompiler.SimStepData)).of_eq fun p =>
    (sourcePositionCodeOneRowsIndexVar_zero p.1 p.2.1 p.2.2).symm

theorem sourcePositionCodeOneRowsIndexVar_one
    (c : Code) (i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c 1 i v =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode 1 i (sourceStatementOne c) v)
        (sourceStatementOne c) v := by
  exact sourcePositionCodeOneRowsIndexVar_stmt_some (sourceStatementAt_one c)

set_option linter.style.longLine false in
/--
For each fixed source code, generated position-code one-row descriptors are
primitive recursive in the row, variable-position, and variable fields.

The final source reduction needs the stronger uniform version over `c`; this
fixed-code lemma isolates the part already supplied by the translated TM0
machine encodings.
-/
theorem sourcePositionCodeOneRowsIndexVar_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar c p.1 p.2.1 p.2.2) := by
  let tc := NatPartrecToToPartrec.translate c
  have hlookup : Primrec (fun p : Nat × Nat × TM0Route.PartrecVar =>
      TM0Route.partrecStartedTM0StatementAt? tc p.1) :=
    (TM0Route.partrecStartedTM0StatementAt?_primrec_fixed tc).comp Primrec.fst
  have hnone : Primrec (fun _p : Nat × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hlabel :=
    TM0FoldedCompiler.simStepDataForStmtLabelWithCode_primrec_fixed tc
  have hcode := TM0FoldedCompiler.labelPositionCode_primrec_fixed tc
  have hsome : Primrec₂
      (fun p : Nat × Nat × TM0Route.PartrecVar =>
        fun stmt : Option (TM0FoldedCompiler.SourceStmt tc) =>
          TM0FoldedCompiler.simStepDataForStmtLabelWithCode tc
            (TM0FoldedCompiler.labelPositionCode p.1 p.2.1 stmt p.2.2)
            stmt p.2.2) := by
    apply Primrec₂.mk
    have hk : Primrec (fun q : (Nat × Nat × TM0Route.PartrecVar) ×
        Option (TM0FoldedCompiler.SourceStmt tc) => q.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hi : Primrec (fun q : (Nat × Nat × TM0Route.PartrecVar) ×
        Option (TM0FoldedCompiler.SourceStmt tc) => q.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hv : Primrec (fun q : (Nat × Nat × TM0Route.PartrecVar) ×
        Option (TM0FoldedCompiler.SourceStmt tc) => q.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hstmt : Primrec (fun q : (Nat × Nat × TM0Route.PartrecVar) ×
        Option (TM0FoldedCompiler.SourceStmt tc) => q.2) :=
      Primrec.snd
    have hqCode : Primrec
        (fun q : (Nat × Nat × TM0Route.PartrecVar) ×
          Option (TM0FoldedCompiler.SourceStmt tc) =>
          TM0FoldedCompiler.labelPositionCode q.1.1 q.1.2.1 q.2 q.1.2.2) :=
      hcode.comp
        (Primrec.pair hk
          (Primrec.pair hi (Primrec.pair hstmt hv)))
    exact hlabel.comp
      (Primrec.pair hqCode (Primrec.pair hstmt hv))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc p.1 <;>
      simp [sourcePositionCodeOneRowsIndexVar, tc, hstmt]

def sourcePositionCodeInteriorRowsIndexVar
    (c : Code) (j i : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  sourcePositionCodeOneRowsIndexVar c (j + 1) i v

def sourcePositionCodeInteriorRowsAtIndex
    (c : Code) (j i : Nat) : List TM0FoldedCompiler.SimStepData :=
  match TM0Route.partrecVarList[i]? with
  | none => []
  | some v => sourcePositionCodeInteriorRowsIndexVar c j i v

theorem sourcePositionCodeInteriorRowsAtIndex_of_var_get?
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v) :
    sourcePositionCodeInteriorRowsAtIndex c j i =
      sourcePositionCodeInteriorRowsIndexVar c j i v := by
  simp [sourcePositionCodeInteriorRowsAtIndex, hv]

theorem sourcePositionCodeInteriorRowsAtIndex_eq_nil_of_var_none
    {c : Code} {j i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    sourcePositionCodeInteriorRowsAtIndex c j i = [] := by
  simp [sourcePositionCodeInteriorRowsAtIndex, hv]

theorem sourcePositionCodeInteriorRowsIndexVar_zero
    (c : Code) (i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeInteriorRowsIndexVar c 0 i v =
      TM0FoldedCompiler.simStepDataForStmtLabelWithCode
        (NatPartrecToToPartrec.translate c)
        (TM0FoldedCompiler.labelPositionCode 1 i (sourceStatementOne c) v)
        (sourceStatementOne c) v := by
  simpa [sourcePositionCodeInteriorRowsIndexVar] using
    sourcePositionCodeOneRowsIndexVar_one c i v

theorem sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows
    (hrows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hj : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar => p.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  exact hrows.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair hj
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

set_option linter.style.longLine false in
/-- Fixed-code primitive-recursiveness of generated position-code interior rows. -/
theorem sourcePositionCodeInteriorRowsIndexVar_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar c p.1 p.2.1 p.2.2) := by
  have hrows := sourcePositionCodeOneRowsIndexVar_primrec_fixed c
  have hj : Primrec (fun p : Nat × Nat × TM0Route.PartrecVar => p.1 + 1) :=
    Primrec.succ.comp Primrec.fst
  exact hrows.comp (Primrec.pair hj Primrec.snd)

theorem sourcePositionCodeInteriorRowsAtIndex_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourcePositionCodeInteriorRowsAtIndex p.1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun _p : Code × Nat × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2 v) := by
    apply Primrec₂.mk
    exact hinterior.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2.2]? <;>
      simp [sourcePositionCodeInteriorRowsAtIndex, h]

def sourcePositionCodeInteriorRowsByTailIndex
    (c : Code) : List TM0FoldedCompiler.SimStepData :=
  (List.Ico TM0Route.partrecVarList.length (sourceLabelCount c)).flatMap
    fun n => sourcePositionCodeInteriorRowsAtIndex c
      (n / TM0Route.partrecVarList.length - 1)
      (n % TM0Route.partrecVarList.length)

def sourcePositionCodeInteriorRowsByTailIndexRange
    (c : Code) : List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c - TM0Route.partrecVarList.length)).flatMap
    fun n =>
      let i := TM0Route.partrecVarList.length + n
      sourcePositionCodeInteriorRowsAtIndex c
        (i / TM0Route.partrecVarList.length - 1)
        (i % TM0Route.partrecVarList.length)

theorem sourcePositionCodeInteriorRowsByTailIndex_eq_range
    (c : Code) :
    sourcePositionCodeInteriorRowsByTailIndex c =
      sourcePositionCodeInteriorRowsByTailIndexRange c := by
  unfold sourcePositionCodeInteriorRowsByTailIndex
    sourcePositionCodeInteriorRowsByTailIndexRange
  have hbound :
      TM0Route.partrecVarList.length ≤ sourceLabelCount c := by
    rw [sourceLabelCount_eq_statementCount_mul]
    nth_rewrite 1 [← Nat.one_mul TM0Route.partrecVarList.length]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (sourceStatementCount_pos c))
  have hIco :
      List.Ico TM0Route.partrecVarList.length (sourceLabelCount c) =
        (List.range (sourceLabelCount c - TM0Route.partrecVarList.length)).map
          (fun n => TM0Route.partrecVarList.length + n) := by
    have hmap := List.Ico.map_add 0
      (sourceLabelCount c - TM0Route.partrecVarList.length)
      TM0Route.partrecVarList.length
    rw [List.Ico.zero_bot] at hmap
    simpa [Nat.add_comm, Nat.sub_add_cancel hbound] using hmap.symm
  rw [hIco]
  simp [List.flatMap_map]

theorem sourcePositionCodeInteriorRowsByTailIndexRange_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourcePositionCodeInteriorRowsByTailIndexRange := by
  unfold sourcePositionCodeInteriorRowsByTailIndexRange
  refine Primrec.list_flatMap
    (Primrec.list_range.comp
      (Primrec.nat_sub.comp sourceLabelCount_primrec
        (Primrec.const TM0Route.partrecVarList.length))) ?_
  apply Primrec₂.mk
  have hidx : Primrec (fun p : Code × Nat =>
      TM0Route.partrecVarList.length + p.2) :=
    Primrec.nat_add.comp (Primrec.const TM0Route.partrecVarList.length) Primrec.snd
  have hblock : Primrec (fun p : Code × Nat =>
      (TM0Route.partrecVarList.length + p.2) /
          TM0Route.partrecVarList.length - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_div.comp hidx (Primrec.const TM0Route.partrecVarList.length))
      (Primrec.const 1)
  have hslot : Primrec (fun p : Code × Nat =>
      (TM0Route.partrecVarList.length + p.2) %
          TM0Route.partrecVarList.length) :=
    Primrec.nat_mod.comp hidx (Primrec.const TM0Route.partrecVarList.length)
  exact (sourcePositionCodeInteriorRowsAtIndex_primrec_of_interior hinterior).comp
    (Primrec.pair Primrec.fst (Primrec.pair hblock hslot))

theorem sourcePositionCodeInteriorRowsByTailIndex_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourcePositionCodeInteriorRowsByTailIndex :=
  (sourcePositionCodeInteriorRowsByTailIndexRange_primrec_of_interior hinterior).of_eq
    fun c => (sourcePositionCodeInteriorRowsByTailIndex_eq_range c).symm

def sourcePositionCodeBoundedInteriorRowsIndexVar
    (c : Code) (j i : Nat) (v : TM0Route.PartrecVar) :
    List TM0FoldedCompiler.SimStepData :=
  if j + 1 < sourceStatementCount c then
    sourcePositionCodeInteriorRowsIndexVar c j i v
  else
    []

theorem sourcePositionCodeBoundedInteriorRowsIndexVar_eq_interior
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hj : j + 1 < sourceStatementCount c) :
    sourcePositionCodeBoundedInteriorRowsIndexVar c j i v =
      sourcePositionCodeInteriorRowsIndexVar c j i v := by
  simp [sourcePositionCodeBoundedInteriorRowsIndexVar, hj]

theorem sourcePositionCodeBoundedInteriorRowsIndexVar_eq_nil
    {c : Code} {j i : Nat} {v : TM0Route.PartrecVar}
    (hj : ¬ j + 1 < sourceStatementCount c) :
    sourcePositionCodeBoundedInteriorRowsIndexVar c j i v = [] := by
  simp [sourcePositionCodeBoundedInteriorRowsIndexVar, hj]

theorem sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hbound : PrimrecPred (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      p.2.1 + 1 < sourceStatementCount p.1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (sourceStatementCount_primrec.comp Primrec.fst)
  have hnil : Primrec (fun _p : Code × Nat × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  exact (Primrec.ite hbound hinterior hnil).of_eq fun p => by
    rfl

set_option linter.style.longLine false in
/-- Fixed-code primitive-recursiveness of bounded generated position-code interior rows. -/
theorem sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar c p.1 p.2.1 p.2.2) := by
  have hinterior := sourcePositionCodeInteriorRowsIndexVar_primrec_fixed c
  have hbound : PrimrecPred (fun p : Nat × Nat × TM0Route.PartrecVar =>
      p.1 + 1 < sourceStatementCount c) :=
    Primrec.nat_lt.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
      (Primrec.const (sourceStatementCount c))
  have hnil : Primrec (fun _p : Nat × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  exact (Primrec.ite hbound hinterior hnil).of_eq fun p => by
    rfl

theorem sourcePositionCodeOneRowsIndexVar_eq_boundedInterior
    (c : Code) (k i : Nat) (v : TM0Route.PartrecVar) :
    sourcePositionCodeOneRowsIndexVar c k i v =
      if k = 0 then
        []
      else
        sourcePositionCodeBoundedInteriorRowsIndexVar c (k - 1) i v := by
  by_cases hzero : k = 0
  · simp [hzero, sourcePositionCodeOneRowsIndexVar_zero]
  · by_cases hlt : k < sourceStatementCount c
    · have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourcePositionCodeBoundedInteriorRowsIndexVar,
        sourcePositionCodeInteriorRowsIndexVar, hkpred, hlt]
    · have hle : sourceStatementCount c ≤ k := Nat.le_of_not_gt hlt
      have hrows : sourcePositionCodeOneRowsIndexVar c k i v = [] :=
        sourcePositionCodeOneRowsIndexVar_eq_nil_of_statementCount_le v hle
      have hkpred : k - 1 + 1 = k := Nat.sub_one_add_one hzero
      simp [hzero, sourcePositionCodeBoundedInteriorRowsIndexVar, hkpred, hlt, hrows]

theorem sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hzero : PrimrecPred (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      p.2.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hnil : Primrec (fun _p : Code × Nat × Nat × TM0Route.PartrecVar =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hkPred : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      p.2.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have helse : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 (p.2.1 - 1) p.2.2.1 p.2.2.2) :=
    hinterior.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair hkPred
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.ite hzero hnil helse).of_eq fun p => by
    exact (sourcePositionCodeOneRowsIndexVar_eq_boundedInterior
      p.1 p.2.1 p.2.2.1 p.2.2.2).symm

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_one_eq_indexVarRows
    (c : Code) (k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithPositionCode c 1 k i =
      match TM0Route.partrecVarList[i]? with
      | none => []
      | some v => sourcePositionCodeOneRowsIndexVar c k i v := by
  cases hv : TM0Route.partrecVarList[i]? with
  | none =>
      unfold sourceSimStepDataForLabelIndexFromWithPositionCode
        TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
      rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_var_none
        (tc := NatPartrecToToPartrec.translate c) (fuel := 0) (k := k) (i := i) hv]
      simp [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_zero]
  | some v =>
      change sourceSimStepDataForLabelIndexFromWithPositionCode c 1 k i =
        sourcePositionCodeOneRowsIndexVar c k i v
      cases hstmt : TM0Route.partrecStartedTM0StatementAt?
          (NatPartrecToToPartrec.translate c) k with
      | none =>
          unfold sourceSimStepDataForLabelIndexFromWithPositionCode
            TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
          rw [TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?_succ_of_stmt_none
            (tc := NatPartrecToToPartrec.translate c) (fuel := 0)
            (k := k) (i := i) (v := v) hv hstmt]
          simp [sourcePositionCodeOneRowsIndexVar_stmt_none hstmt]
      | some stmt =>
          rw [sourcePositionCodeOneRowsIndexVar_stmt_some hstmt]
          simpa using
            sourceSimStepDataForLabelIndexFromWithPositionCode_of_block_var_get?
              (c := c) (fuel := 1) (k := k) (block := 0)
              (i := i) (v := v) (stmt := stmt) (by omega) hv (by simpa using hstmt)

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_one_primrec_of_indexVarRows
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 1 p.2.1 p.2.2) := by
  have hlookup : Primrec (fun p : Code × Nat × Nat =>
      TM0Route.partrecVarList[p.2.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp (Primrec.snd.comp Primrec.snd)
  have hnone : Primrec (fun _p : Code × Nat × Nat =>
      ([] : List TM0FoldedCompiler.SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun p : Code × Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2 v) := by
    apply Primrec₂.mk
    exact hvarRows.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    rw [sourceSimStepDataForLabelIndexFromWithPositionCode_one_eq_indexVarRows]
    cases TM0Route.partrecVarList[p.2.2]? <;> rfl

def sourcePositionCodeDecoderStepNone (c : Code) (k i : Nat) :
    SourceSearchCodeDecoderState :=
  match TM0Route.partrecVarList[i]? with
  | none => (k + 1, i - TM0Route.partrecVarList.length, none)
  | some v => (k, i, some (sourcePositionCodeOneRowsIndexVar c k i v))

def sourcePositionCodeDecoderStep (c : Code)
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

def sourcePositionCodeDecoderStateFrom
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

def sourcePositionCodeDecoderState (c : Code) (fuel k i : Nat) :
    SourceSearchCodeDecoderState :=
  sourcePositionCodeDecoderStateFrom c fuel (sourceSearchCodeDecoderInit k i)

def sourcePositionCodeDecoder (c : Code) (fuel k i : Nat) :
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


end TM0FoldedReduction

end LeanWang

end
