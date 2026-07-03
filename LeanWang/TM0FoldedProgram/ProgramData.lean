/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.PositionCode

/-!
Folded finite program data and transition facts.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

/--
Indexed mirror of `simStepData`. This is definitionally driven by the
primitive-recursive label count; the theorem below connects it to the semantic
label-list enumeration.
-/
def simStepDataByLabelIndex (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndex tc)

/-- Indexed descriptor enumeration through the numeric-state decoder path. -/
def simStepDataByLabelIndexWithCode (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndexStartWithCode tc)

/-- Indexed descriptor enumeration through the bounded-search decoder path. -/
def simStepDataByLabelIndexWithSearchCode
    (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndexStartWithSearchCode tc)

/-- Indexed descriptor enumeration through the position-coded decoder path. -/
def simStepDataByLabelIndexWithPositionCode
    (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndexStartWithPositionCode tc)

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_index
    {tc : Turing.ToPartrec.Code} {n : Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {e : PostTransition}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hcode : ∀ i, i < n → ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target)
    (hblock :
      (simRowsOfStepData (simStepDataForLabelIndexStartWithPositionCode tc n)).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side target)
              (foldedSymbolCode marked left right)) = some e) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      some e := by
  unfold simStepDataByLabelIndexWithPositionCode
  rw [program_flatMap_range_split
    (simStepDataForLabelIndexStartWithPositionCode tc) hn]
  exact simRowsOfStepDataForPositionCodeIndexRange_append_find?_eq_some
    (tc := tc) (n := n) (target := target) (side := side)
    (marked := marked) (left := left) (right := right)
    (suffix := (List.Ico (n + 1) (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
      (simStepDataForLabelIndexStartWithPositionCode tc))
    hcode hblock

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_index_decode
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {q : SourceLabel tc × Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {e : PostTransition}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hprefix : ∀ i, i < n → ∀ r : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some r →
        r.2 ≠ TM0FiniteCompiler.stateCode tc target)
    (hdecode : labelAtByStatementFromWithPositionCode? tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 n = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target)
    (hcanonical :
      (simRowsOfStepData
        (simStepDataForStmtLabelWithCode tc
          (TM0FiniteCompiler.stateCode tc target) target.1 target.2)).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side target)
              (foldedSymbolCode marked left right)) = some e) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      some e := by
  refine simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_index
    (tc := tc) (n := n) (target := target) (side := side)
    (marked := marked) (left := left) (right := right)
    hn hprefix ?_
  rw [simRowsOfStepDataForPositionCodeStart_find?_eq_target
    hdecode htarget hcode]
  exact hcanonical

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_succ_code
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {q : SourceLabel tc × Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {e : PostTransition}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hdecode : labelAtByStatementFromWithPositionCode? tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 n = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target)
    (hsucc : TM0FiniteCompiler.stateCode tc target = n + 1)
    (hcanonical :
      (simRowsOfStepData
        (simStepDataForStmtLabelWithCode tc
          (TM0FiniteCompiler.stateCode tc target) target.1 target.2)).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side target)
              (foldedSymbolCode marked left right)) = some e) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      some e := by
  refine simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_index_decode
    (tc := tc) (n := n) (q := q) (target := target) (side := side)
    (marked := marked) (left := left) (right := right)
    hn ?_ hdecode htarget hcode hcanonical
  intro i hi r hr
  rw [hsucc]
  exact labelAtByStatementFromWithPositionCode?_start_currentCode_ne_succ_of_lt
    tc hi hr

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_support_succ_stateCode
    {tc : Turing.ToPartrec.Code} {n : Nat} {target : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {e : PostTransition}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some target)
    (hstate : TM0FiniteCompiler.stateCode tc target = n + 1)
    (hcanonical :
      (simRowsOfStepData
        (simStepDataForStmtLabelWithCode tc
          (TM0FiniteCompiler.stateCode tc target) target.1 target.2)).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side target)
              (foldedSymbolCode marked left right)) = some e) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      some e := by
  rcases labelAtByStatementFromWithPositionCode?_start_of_support_succ_stateCode
      tc hsupport hstate with ⟨q, hdecode, _hqtarget, hqcode⟩
  have htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc :=
    List.mem_iff_getElem?.2 ⟨n + 1, hsupport⟩
  exact simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_succ_code
    (tc := tc) (n := n) (q := q) (target := target) (side := side)
    (marked := marked) (left := left) (right := right)
    hn hdecode htarget hqcode hstate hcanonical

theorem simStepDataByLabelIndex_primrec_of_forLabelIndex
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndex p.1 p.2)) :
    Primrec simStepDataByLabelIndex := by
  unfold simStepDataByLabelIndex
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem simStepDataByLabelIndexWithCode_primrec_of_forLabelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec simStepDataByLabelIndexWithCode := by
  unfold simStepDataByLabelIndexWithCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem simStepDataByLabelIndexWithSearchCode_primrec_of_forLabelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec simStepDataByLabelIndexWithSearchCode := by
  unfold simStepDataByLabelIndexWithSearchCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem simStepDataByLabelIndexWithPositionCode_primrec_of_forLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec simStepDataByLabelIndexWithPositionCode := by
  unfold simStepDataByLabelIndexWithPositionCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

def simRowsForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List PostTransition :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simTransitionOfStep tc q side marked left right

theorem simRowsForLabel_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (simRowsForLabel tc q).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold simRowsForLabel
  exact program_find?_flatMap_simTransition_side_of_step_aux
    foldSideList (mem_foldSideList side) hstep

theorem simRowsForLabel_find?_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (simRowsForLabel tc q).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  unfold simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨s, _hs, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨m, _hm, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨l, _hl, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨r, _hr, hrow⟩
  by_cases hside : s = side
  · subst s
    by_cases hread :
        foldedSymbolCode m l r = foldedSymbolCode marked left right
    · have hparts := foldedSymbolCode_eq hread
      cases hparts.1
      cases hparts.2.1
      cases hparts.2.2
      have hnone := simTransitionOfStep_eq_none_of_no_step
        (tc := tc) (q := q) (side := side) (marked := marked)
        (left := left) (right := right) hstep
      rw [hnone] at hrow
      cases hrow
    · exact simTransitionOfStep_matchesInput_of_read_ne
        (tc := tc) (q := q) (side := side) (marked := marked)
        (marked' := m) (left := left) (right := right)
        (left' := l) (right' := r) hread hrow
  · exact simTransitionOfStep_matchesInput_of_side_ne
      (tc := tc) (q := q) (side := side) (side' := s)
      (marked := marked) (marked' := m) (left := left) (right := right)
      (left' := l) (right' := r) hside hrow

def simRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q => simRowsForLabel tc q

theorem simRowsForLabel_eq_stepData (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    simRowsForLabel tc q = simRowsOfStepData (simStepDataForLabel tc q) := by
  unfold simRowsForLabel simStepDataForLabel
  simp only [simTransitionOfStep_eq_map_stepData]
  simp [simRowsOfStepData, program_filterMap_simTransition_eq_map_stepData,
    List.map_flatMap]

theorem simRowsOfStepDataForStmtLabelWithCode_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        some (q', stmt)) :
    (simRowsOfStepData
      (simStepDataForStmtLabelWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmtOpt, v)) stmtOpt v)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked (stmtOpt, v) q' left right stmt) := by
  rw [← simStepDataForStmtLabel_eq_withCode tc stmtOpt v]
  rw [simStepDataForStmtLabel_eq_of_label tc (stmtOpt, v)]
  rw [← simRowsForLabel_eq_stepData tc (stmtOpt, v)]
  exact simRowsForLabel_find?_of_step hstep

theorem simRowsOfStepDataForStmtLabelWithCode_find?_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        none) :
    (simRowsOfStepData
      (simStepDataForStmtLabelWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmtOpt, v)) stmtOpt v)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
            (foldedSymbolCode marked left right)) =
      none := by
  rw [← simStepDataForStmtLabel_eq_withCode tc stmtOpt v]
  rw [simStepDataForStmtLabel_eq_of_label tc (stmtOpt, v)]
  rw [← simRowsForLabel_eq_stepData tc (stmtOpt, v)]
  exact simRowsForLabel_find?_eq_none_of_no_step hstep

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_support_succ_step
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some (stmtOpt, v))
    (hstate : TM0FiniteCompiler.stateCode tc (stmtOpt, v) = n + 1)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        some (q', stmt)) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked (stmtOpt, v) q' left right stmt) := by
  exact simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_support_succ_stateCode
    (tc := tc) (n := n) (target := (stmtOpt, v)) (side := side)
    (marked := marked) (left := left) (right := right)
    hn hsupport hstate
    (simRowsOfStepDataForStmtLabelWithCode_find?_of_step
      (tc := tc) (stmtOpt := stmtOpt) (v := v) (q' := q') (side := side)
      (marked := marked) (left := left) (right := right) (stmt := stmt) hstep)

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_sourceDefault_step
    {tc : Turing.ToPartrec.Code} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        some (q', stmt)) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (sourceDefaultLabel tc))
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked (sourceDefaultLabel tc) q' left right stmt) := by
  have htarget :
      sourceDefaultLabel tc ∈ TM0Route.partrecStartedTM0LabelSupportList tc := by
    simpa [sourceDefaultLabel_eq_default tc] using
      TM0Route.partrecStartedTM0_default_mem_labelSupportList tc
  have hstate : TM0FiniteCompiler.stateCode tc (sourceDefaultLabel tc) = 0 := by
    simpa [sourceDefaultLabel_eq_default tc, TM0Route.partrecStartedTM0Start] using
      TM0FiniteCompiler.stateCode_default tc
  refine simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_index_decode
    (tc := tc) (n := sourceDefaultLabelIndex tc)
    (q := (sourceDefaultLabel tc, 0)) (target := sourceDefaultLabel tc)
    (side := side) (marked := marked) (left := left) (right := right)
    (sourceDefaultLabelIndex_lt_labelCount tc) ?_
    (labelAtByStatementFromWithPositionCode?_sourceDefaultLabelIndex tc)
    htarget ?_ ?_
  · intro i hi r hr
    rw [hstate]
    exact labelAtByStatementFromWithPositionCode?_prefix_sourceDefaultLabelIndex_code_ne_zero
      tc hi hr
  · simp [hstate]
  · have hcanonical :=
      simRowsOfStepDataForStmtLabelWithCode_find?_of_step
        (tc := tc) (stmtOpt := (sourceDefaultLabel tc).1)
        (v := (sourceDefaultLabel tc).2) (q' := q') (side := side)
        (marked := marked) (left := left) (right := right) (stmt := stmt)
        (by simpa using hstep)
    simpa using hcanonical

theorem simRowsOfStepDataForLabelIndexStartWithPositionCode_find?_eq_none_of_sourceDefault_no_step
    {tc : Turing.ToPartrec.Code} {i : Nat}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        none) :
    (simRowsOfStepData (simStepDataForLabelIndexStartWithPositionCode tc i)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (sourceDefaultLabel tc))
            (foldedSymbolCode marked left right)) =
      none := by
  have htarget :
      sourceDefaultLabel tc ∈ TM0Route.partrecStartedTM0LabelSupportList tc := by
    simpa [sourceDefaultLabel_eq_default tc] using
      TM0Route.partrecStartedTM0_default_mem_labelSupportList tc
  have hstate : TM0FiniteCompiler.stateCode tc (sourceDefaultLabel tc) = 0 := by
    simpa [sourceDefaultLabel_eq_default tc, TM0Route.partrecStartedTM0Start] using
      TM0FiniteCompiler.stateCode_default tc
  unfold simStepDataForLabelIndexStartWithPositionCode
  cases hdecode : labelAtByStatementFromWithPositionCode? tc
      (TM0Route.partrecStartedTM0StatementCount tc) 0 i with
  | none =>
      simp [simStepDataForLabelIndexFromWithPositionCode, hdecode, simRowsOfStepData]
  | some q =>
      by_cases hcode : q.2 = TM0FiniteCompiler.stateCode tc (sourceDefaultLabel tc)
      · rw [simRowsOfStepDataForPositionCode_find?_eq_target
          (tc := tc) (fuel := TM0Route.partrecStartedTM0StatementCount tc)
          (k := 0) (i := i) (q := q) (target := sourceDefaultLabel tc)
          (side := side) (marked := marked) (left := left) (right := right)
          hdecode htarget hcode]
        exact simRowsOfStepDataForStmtLabelWithCode_find?_eq_none_of_no_step
          (tc := tc) (stmtOpt := (sourceDefaultLabel tc).1)
          (v := (sourceDefaultLabel tc).2) (side := side)
          (marked := marked) (left := left) (right := right)
          (by simpa using hstep)
      · exact simRowsOfStepDataForLabelIndexFromWithPositionCode_find?_eq_none_of_currentCode_ne
          (tc := tc) (fuel := TM0Route.partrecStartedTM0StatementCount tc)
          (k := 0) (i := i) (target := sourceDefaultLabel tc)
          (side := side) (marked := marked) (left := left) (right := right)
          (by
            intro r hr
            rw [hdecode] at hr
            cases hr
            exact hcode)

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_none_of_sourceDefault_no_step
    {tc : Turing.ToPartrec.Code}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        none) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (sourceDefaultLabel tc))
            (foldedSymbolCode marked left right)) =
      none := by
  unfold simStepDataByLabelIndexWithPositionCode
  rw [show simRowsOfStepData
        ((List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc)) =
      (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
        (fun i => simRowsOfStepData
          (simStepDataForLabelIndexStartWithPositionCode tc i)) by
    simp [simRowsOfStepData, List.map_flatMap]]
  exact program_find?_flatMap_eq_none_of_forall (fun i _hi =>
    simRowsOfStepDataForLabelIndexStartWithPositionCode_find?_eq_none_of_sourceDefault_no_step
      (tc := tc) (i := i) (side := side) (marked := marked)
      (left := left) (right := right) hstep)

theorem simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_none_of_support_succ_no_step
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some (stmtOpt, v))
    (hstate : TM0FiniteCompiler.stateCode tc (stmtOpt, v) = n + 1)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        none) :
    (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
            (foldedSymbolCode marked left right)) =
      none := by
  rcases labelAtByStatementFromWithPositionCode?_start_of_support_succ_stateCode
      tc hsupport hstate with ⟨q, hdecode, _hqtarget, hqcode⟩
  have htarget : (stmtOpt, v) ∈ TM0Route.partrecStartedTM0LabelSupportList tc :=
    List.mem_iff_getElem?.2 ⟨n + 1, hsupport⟩
  have hpref :
      (simRowsOfStepData
        ((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc))).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
              (foldedSymbolCode marked left right)) = none := by
    exact simRowsOfStepDataForPositionCodeIndexRange_find?_eq_none
      (tc := tc) (n := n) (target := (stmtOpt, v)) (side := side)
      (marked := marked) (left := left) (right := right)
      (by
        intro i hi r hr
        rw [hstate]
        exact labelAtByStatementFromWithPositionCode?_start_currentCode_ne_succ_of_lt
          tc hi hr)
  have hblock :
      (simRowsOfStepData (simStepDataForLabelIndexStartWithPositionCode tc n)).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
              (foldedSymbolCode marked left right)) = none := by
    rw [simRowsOfStepDataForPositionCodeStart_find?_eq_target
      hdecode htarget hqcode]
    exact simRowsOfStepDataForStmtLabelWithCode_find?_eq_none_of_no_step
      (tc := tc) (stmtOpt := stmtOpt) (v := v) (side := side)
      (marked := marked) (left := left) (right := right) hstep
  have hsuffix :
      (simRowsOfStepData
        ((List.Ico (n + 1) (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc))).find?
          (fun e =>
            e.matchesInput (foldedSimStateCode tc side (stmtOpt, v))
              (foldedSymbolCode marked left right)) = none :=
    simRowsOfStepDataForPositionCodeIndexIco_find?_eq_none_of_stateCode_succ
      (tc := tc) (n := n) (count := TM0Route.partrecStartedTM0LabelCount tc)
      (target := (stmtOpt, v)) (side := side) (marked := marked)
      (left := left) (right := right) hstate
  unfold simStepDataByLabelIndexWithPositionCode
  rw [program_flatMap_range_split
    (simStepDataForLabelIndexStartWithPositionCode tc) hn]
  rw [show simRowsOfStepData
        (((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc)) ++
            simStepDataForLabelIndexStartWithPositionCode tc n ++
              (List.Ico (n + 1) (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
                (simStepDataForLabelIndexStartWithPositionCode tc)) =
      simRowsOfStepData
        ((List.range n).flatMap
          (simStepDataForLabelIndexStartWithPositionCode tc)) ++
      (simRowsOfStepData
        (simStepDataForLabelIndexStartWithPositionCode tc n) ++
          simRowsOfStepData
            ((List.Ico (n + 1) (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
              (simStepDataForLabelIndexStartWithPositionCode tc))) by
    simp [simRowsOfStepData, List.map_append]]
  rw [program_find?_append_of_eq_none hpref]
  rw [program_find?_append_of_eq_none hblock]
  exact hsuffix

/-- Descriptor-level folded simulation rows. -/
def simStepData (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q => simStepDataForLabel tc q

theorem simStepDataByLabelIndex_eq (tc : Turing.ToPartrec.Code) :
    simStepDataByLabelIndex tc = simStepData tc := by
  unfold simStepDataByLabelIndex simStepDataForLabelIndex simStepData
  rw [← TM0Route.partrecStartedTM0LabelList_length tc]
  exact program_flatMap_getElem?_range_length
    (TM0Route.partrecStartedTM0LabelList tc) (fun q => simStepDataForLabel tc q)

theorem simStepDataByLabelIndexWithCode_eq (tc : Turing.ToPartrec.Code) :
    simStepDataByLabelIndexWithCode tc = simStepData tc := by
  unfold simStepDataByLabelIndexWithCode
  rw [← simStepDataByLabelIndex_eq tc]
  unfold simStepDataByLabelIndex
  apply List.flatMap_congr
  intro i _hi
  exact simStepDataForLabelIndexStartWithCode_eq tc i

theorem simStepDataByLabelIndexWithSearchCode_eq (tc : Turing.ToPartrec.Code) :
    simStepDataByLabelIndexWithSearchCode tc = simStepData tc := by
  unfold simStepDataByLabelIndexWithSearchCode
  rw [← simStepDataByLabelIndexWithCode_eq tc]
  unfold simStepDataByLabelIndexWithCode
  apply List.flatMap_congr
  intro i _hi
  exact simStepDataForLabelIndexStartWithSearchCode_eq_withCode tc i

theorem simStepDataForLabelIndexStartWithPositionCode_eq_withCode_of_minimal
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hmin : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simStepDataForLabelIndexStartWithPositionCode tc i =
      simStepDataForLabelIndexStartWithCode tc i := by
  unfold simStepDataForLabelIndexStartWithPositionCode
    simStepDataForLabelIndexStartWithCode
  exact simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
    tc hmin

theorem simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
    (tc : Turing.ToPartrec.Code)
    (hmin : ∀ i, i < TM0Route.partrecStartedTM0LabelCount tc →
      ∀ q : SourceLabel tc × Nat,
        labelAtByStatementFromWithPositionCode? tc
            (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simStepDataByLabelIndexWithPositionCode tc =
      simStepDataByLabelIndexWithCode tc := by
  unfold simStepDataByLabelIndexWithPositionCode simStepDataByLabelIndexWithCode
  apply List.flatMap_congr
  intro i hi
  have hiCount : i < TM0Route.partrecStartedTM0LabelCount tc := by
    simpa [List.mem_range] using hi
  exact simStepDataForLabelIndexStartWithPositionCode_eq_withCode_of_minimal
    tc (hmin i hiCount)

theorem simRows_eq_stepData (tc : Turing.ToPartrec.Code) :
    simRows tc = simRowsOfStepData (simStepData tc) := by
  unfold simRows simStepData
  simp [simRowsForLabel_eq_stepData, simRowsOfStepData, List.map_flatMap]

theorem simRowsOfStepDataByLabelIndexWithPositionCode_eq_of_minimal
    (tc : Turing.ToPartrec.Code)
    (hmin : ∀ i, i < TM0Route.partrecStartedTM0LabelCount tc →
      ∀ q : SourceLabel tc × Nat,
        labelAtByStatementFromWithPositionCode? tc
            (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) =
      simRows tc := by
  rw [simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal tc hmin]
  rw [simStepDataByLabelIndexWithCode_eq]
  exact (simRows_eq_stepData tc).symm

def programOfParts (qCodes : List Nat) (init sim : List PostTransition) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateListOfCodes qCodes
  blank := foldedBlank
  start := foldedStartState
  table := init ++ sim

theorem programOfParts_primrec :
    Primrec (fun p : List Nat × List PostTransition × List PostTransition =>
      programOfParts p.1 p.2.1 p.2.2) := by
  unfold programOfParts
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const foldedSymbolList)
      (Primrec.pair (foldedStateListOfCodes_primrec.comp Primrec.fst)
        (Primrec.pair (Primrec.const foldedBlank)
          (Primrec.pair (Primrec.const foldedStartState)
            (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
              (Primrec.snd.comp Primrec.snd))))))

def programOfCountAndRows (stateCount : Nat) (init sim : List PostTransition) :
    FiniteTM0Program :=
  programOfParts (List.range stateCount) init sim

theorem programOfCountAndRows_primrec :
    Primrec (fun p : Nat × List PostTransition × List PostTransition =>
      programOfCountAndRows p.1 p.2.1 p.2.2) := by
  unfold programOfCountAndRows
  exact programOfParts_primrec.comp
    (Primrec.pair (Primrec.list_range.comp Primrec.fst) Primrec.snd)

def programOfCountAndSimRows (stateCount : Nat) (sim : List PostTransition) :
    FiniteTM0Program :=
  programOfCountAndRows stateCount initRowsData sim

theorem programOfCountAndSimRows_primrec :
    Primrec (fun p : Nat × List PostTransition =>
      programOfCountAndSimRows p.1 p.2) := by
  unfold programOfCountAndSimRows
  exact programOfCountAndRows_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.const initRowsData) Primrec.snd))

theorem programOfCountAndSimRows_computable :
    Computable (fun p : Nat × List PostTransition =>
      programOfCountAndSimRows p.1 p.2) :=
  programOfCountAndSimRows_primrec.to_comp

/--
Build normalized folded program data from a numeric state count and a list of
numeric simulation-step descriptors.
-/
def programDataOfStepData (stateCount : Nat) (steps : List SimStepData) :
    FiniteTM0Program :=
  programOfCountAndSimRows stateCount (simRowsOfStepData steps)

theorem programDataOfStepData_primrec :
    Primrec (fun p : Nat × List SimStepData =>
      programDataOfStepData p.1 p.2) := by
  unfold programDataOfStepData
  exact programOfCountAndSimRows_primrec.comp
    (Primrec.pair Primrec.fst (simRowsOfStepData_primrec.comp Primrec.snd))

theorem programDataOfStepData_computable :
    Computable (fun p : Nat × List SimStepData =>
      programDataOfStepData p.1 p.2) :=
  programDataOfStepData_primrec.to_comp

def appendSimRows (P : FiniteTM0Program) (sim : List PostTransition) : FiniteTM0Program :=
  { P with table := P.table ++ sim }

theorem appendSimRows_primrec :
    Primrec (fun p : FiniteTM0Program × List PostTransition =>
      appendSimRows p.1 p.2) := by
  unfold appendSimRows
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (PostProgram.symbols_primrec.comp Primrec.fst)
      (Primrec.pair (PostProgram.states_primrec.comp Primrec.fst)
        (Primrec.pair (PostProgram.blank_primrec.comp Primrec.fst)
          (Primrec.pair (PostProgram.start_primrec.comp Primrec.fst)
            (Primrec.list_append.comp
              (PostProgram.table_primrec.comp Primrec.fst) Primrec.snd)))))

theorem appendSimRows_computable :
    Computable (fun p : FiniteTM0Program × List PostTransition =>
      appendSimRows p.1 p.2) :=
  appendSimRows_primrec.to_comp

def program (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programOfCountAndRows (TM0Route.partrecStartedTM0StateCount tc) (initRows tc) (simRows tc)

theorem program_eq_programOfParts (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfParts (TM0Route.partrecStartedTM0States tc) (initRows tc) (simRows tc) := rfl

theorem program_eq_programOfCountAndRows (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfCountAndRows (TM0Route.partrecStartedTM0StateCount tc)
        (initRows tc) (simRows tc) := rfl

theorem program_eq_programOfCountAndSimRows (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfCountAndSimRows (TM0Route.partrecStartedTM0StateCount tc) (simRows tc) := by
  rw [program_eq_programOfCountAndRows, programOfCountAndSimRows, initRows_eq_data]

/--
Normalized form of `program` that exposes the constant initial rows
definitionally.
-/
def programData (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programOfCountAndSimRows (TM0Route.partrecStartedTM0StateCount tc) (simRows tc)

theorem programData_eq_program (tc : Turing.ToPartrec.Code) :
    programData tc = program tc :=
  (program_eq_programOfCountAndSimRows tc).symm

/--
Finite folded program generated from position-coded descriptors.

Unlike `programData`, this may contain extra noncanonical simulation rows when
the statement support list has duplicates.  Those rows are intended to be
handled semantically by proving that canonical execution never selects them.
-/
def positionProgramData (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programDataOfStepData (TM0Route.partrecStartedTM0StateCount tc)
    (simStepDataByLabelIndexWithPositionCode tc)

@[simp]
theorem positionProgramData_symbols (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).symbols = foldedSymbolList :=
  rfl

@[simp]
theorem positionProgramData_states (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).states = foldedStateList tc :=
  rfl

@[simp]
theorem positionProgramData_blank (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).blank = foldedBlank :=
  rfl

@[simp]
theorem positionProgramData_start (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).start = foldedStartState :=
  rfl

@[simp]
theorem positionProgramData_table (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).table =
      initRowsData ++ simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) :=
  rfl

/-- The generated position-coded program starts with the normalized origin row. -/
theorem positionProgramData_transition?_start_blank (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).transition? foldedStartState foldedBlank =
      some initWriteOriginRow := by
  unfold PostProgram.transition?
  change (initRowsData ++
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
      (fun e => e.matchesInput foldedStartState foldedBlank) =
    some initWriteOriginRow
  apply program_find?_append_of_eq_some
  have hmatch :
      initWriteOriginRow.matchesInput foldedStartState foldedBlank = true := by
    unfold initWriteOriginRow foldedStartState
    simp [mkRow, PostTransition.matchesInput]
  change (initWriteOriginRow ::
      (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData))).find?
      (fun e => e.matchesInput foldedStartState foldedBlank) =
    some initWriteOriginRow
  simp [hmatch]

/-- The first generated position-coded program step writes the folded origin. -/
theorem positionProgramData_step_start_blank (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).step foldedStartState foldedBlank =
      some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
  have hfind := positionProgramData_transition?_start_blank tc
  have hnext : nextAfterOrigin ∈ foldedStateList tc :=
    nextAfterOrigin_mem_states tc
  have hwrite : foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols (inputSymbol 0)
  simp [PostProgram.step, hfind, initWriteOriginRow, mkRow, hnext, hwrite]

theorem positionProgramData_eq_programOfCountAndSimRows
    (tc : Turing.ToPartrec.Code) :
    positionProgramData tc =
      programOfCountAndSimRows (TM0Route.partrecStartedTM0StateCount tc)
        (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)) := by
  rfl

theorem positionProgramData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode) :
    Primrec positionProgramData := by
  unfold positionProgramData
  exact programDataOfStepData_primrec.comp
    (Primrec.pair TM0Route.partrecStartedTM0StateCount_primrec hsteps)

theorem positionProgramData_computable_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode) :
    Computable positionProgramData :=
  (positionProgramData_primrec_of_simStepDataByLabelIndexWithPositionCode hsteps).to_comp

theorem positionProgramData_primrec_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec positionProgramData :=
  positionProgramData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (simStepDataByLabelIndexWithPositionCode_primrec_of_forLabelIndexStartWithPositionCode
      hindex)

theorem positionProgramData_computable_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Computable positionProgramData :=
  (positionProgramData_primrec_of_simStepDataForLabelIndexStartWithPositionCode hindex).to_comp

theorem positionProgramData_primrec_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec positionProgramData :=
  positionProgramData_primrec_of_simStepDataForLabelIndexStartWithPositionCode <| by
    unfold simStepDataForLabelIndexStartWithPositionCode
    exact hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (TM0Route.partrecStartedTM0StatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))

theorem positionProgramData_computable_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable positionProgramData :=
  (positionProgramData_primrec_of_simStepDataForLabelIndexFromWithPositionCode hindex).to_comp

/--
The remaining computability obligation for `programData` can be reduced to a
primitive-recursive list of numeric step descriptors whose generated rows are
exactly the semantic `simRows`.
-/
theorem programData_primrec_of_stepData
    (stepData : Turing.ToPartrec.Code → List SimStepData)
    (hsteps : Primrec stepData)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (stepData tc) = simRows tc) :
    Primrec programData := by
  have hdata : Primrec fun tc : Turing.ToPartrec.Code =>
      programDataOfStepData (TM0Route.partrecStartedTM0StateCount tc) (stepData tc) :=
    programDataOfStepData_primrec.comp
      (Primrec.pair TM0Route.partrecStartedTM0StateCount_primrec hsteps)
  exact hdata.of_eq fun tc => by
    unfold programData programDataOfStepData
    rw [hrows tc]

theorem programData_computable_of_stepData
    (stepData : Turing.ToPartrec.Code → List SimStepData)
    (hsteps : Primrec stepData)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (stepData tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_stepData stepData hsteps hrows).to_comp

/--
The remaining global computability target for normalized folded program data is
the primitive recursiveness of the descriptor list `simStepData`.
-/
theorem programData_primrec_of_simStepData
    (hsteps : Primrec simStepData) :
    Primrec programData :=
  programData_primrec_of_stepData simStepData hsteps
    fun tc => (simRows_eq_stepData tc).symm

theorem programData_computable_of_simStepData
    (hsteps : Primrec simStepData) :
    Computable programData :=
  (programData_primrec_of_simStepData hsteps).to_comp

/--
Indexed descriptor enumeration is enough for computability of normalized
folded program data.
-/
theorem programData_primrec_of_simStepDataByLabelIndex
    (hsteps : Primrec simStepDataByLabelIndex) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndex hsteps fun tc => by
    rw [simStepDataByLabelIndex_eq, ← simRows_eq_stepData]

theorem programData_computable_of_simStepDataByLabelIndex
    (hsteps : Primrec simStepDataByLabelIndex) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndex hsteps).to_comp

theorem programData_primrec_of_simStepDataByLabelIndexWithCode
    (hsteps : Primrec simStepDataByLabelIndexWithCode) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndexWithCode hsteps fun tc => by
    rw [simStepDataByLabelIndexWithCode_eq, ← simRows_eq_stepData]

theorem programData_computable_of_simStepDataByLabelIndexWithCode
    (hsteps : Primrec simStepDataByLabelIndexWithCode) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndexWithCode hsteps).to_comp

theorem programData_primrec_of_simStepDataByLabelIndexWithSearchCode
    (hsteps : Primrec simStepDataByLabelIndexWithSearchCode) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndexWithSearchCode hsteps fun tc => by
    rw [simStepDataByLabelIndexWithSearchCode_eq, ← simRows_eq_stepData]

theorem programData_computable_of_simStepDataByLabelIndexWithSearchCode
    (hsteps : Primrec simStepDataByLabelIndexWithSearchCode) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndexWithSearchCode hsteps).to_comp

/--
Position-coded indexed descriptors are enough for computability once their
generated rows are proved to be the semantic folded simulation rows. This
isolates the remaining equality/uniqueness work for the position-code route.
-/
theorem programData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndexWithPositionCode hsteps hrows

theorem programData_computable_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndexWithPositionCode hsteps hrows).to_comp

theorem programData_primrec_of_simStepDataForLabelIndex
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndex p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndex
    (simStepDataByLabelIndex_primrec_of_forLabelIndex hindex)

theorem programData_computable_of_simStepDataForLabelIndex
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndex p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndex hindex).to_comp

/--
The offset-start descriptor enumeration is enough for computability of
normalized folded program data. This is the form targeted by the remaining
structural decoder proof.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStart
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStart p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndex
    (hindex.of_eq fun p => by
      exact simStepDataForLabelIndexStart_eq p.1 p.2)

theorem programData_computable_of_simStepDataForLabelIndexStart
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStart p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStart hindex).to_comp

/--
The canonical numeric-state indexed descriptor decoder is enough for primitive
recursiveness of normalized folded program data.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndexWithCode
    (simStepDataByLabelIndexWithCode_primrec_of_forLabelIndexStartWithCode hindex)

theorem programData_computable_of_simStepDataForLabelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStartWithCode hindex).to_comp

/--
The bounded-search numeric-state offset-start decoder is enough for primitive
recursiveness of normalized folded program data.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndexWithSearchCode
    (simStepDataByLabelIndexWithSearchCode_primrec_of_forLabelIndexStartWithSearchCode
      hindex)

theorem programData_computable_of_simStepDataForLabelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStartWithSearchCode hindex).to_comp

/--
The position-coded offset-start descriptor decoder is enough for primitive
recursiveness of normalized folded program data once the resulting indexed rows
are identified with the semantic folded simulation rows.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (simStepDataByLabelIndexWithPositionCode_primrec_of_forLabelIndexStartWithPositionCode
      hindex)
    hrows

theorem programData_computable_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStartWithPositionCode hindex hrows).to_comp

/--
The fully offset descriptor decoder is enough for primitive recursiveness of
normalized folded program data. This isolates the remaining local recursion:
given `(tc, fuel, statementOffset, residualIndex)`, produce the descriptor rows
for the decoded label.
-/
theorem programData_primrec_of_simStepDataForLabelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexStart <| by
    unfold simStepDataForLabelIndexStart
    exact hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (TM0Route.partrecStartedTM0StatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))

theorem programData_computable_of_simStepDataForLabelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFrom hindex).to_comp

/--
The numeric-state fully offset descriptor decoder is enough for primitive
recursiveness of normalized folded program data.
-/
theorem programData_primrec_of_simStepDataForLabelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexFrom
    (hindex.of_eq fun p =>
      (simStepDataForLabelIndexFrom_eq_withCode p.1 p.2.1 p.2.2.1 p.2.2.2).symm)

theorem programData_computable_of_simStepDataForLabelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFromWithCode hindex).to_comp

theorem programData_primrec_of_simStepDataForLabelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexFromWithCode
    (hindex.of_eq fun p =>
      simStepDataForLabelIndexFromWithSearchCode_eq_withCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)

theorem programData_computable_of_simStepDataForLabelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFromWithSearchCode hindex).to_comp

theorem programData_primrec_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexStartWithPositionCode
    (by
      unfold simStepDataForLabelIndexStartWithPositionCode
      exact hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (TM0Route.partrecStartedTM0StatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd))))
    hrows

theorem programData_computable_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFromWithPositionCode hindex hrows).to_comp

theorem programData_symbols (tc : Turing.ToPartrec.Code) :
    (programData tc).symbols = foldedSymbolList :=
  rfl

theorem programData_states (tc : Turing.ToPartrec.Code) :
    (programData tc).states = foldedStateList tc :=
  rfl

theorem programData_blank (tc : Turing.ToPartrec.Code) :
    (programData tc).blank = foldedBlank :=
  rfl

theorem programData_start (tc : Turing.ToPartrec.Code) :
    (programData tc).start = foldedStartState :=
  rfl

theorem programData_table (tc : Turing.ToPartrec.Code) :
    (programData tc).table = initRowsData ++ simRows tc :=
  rfl

def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc

theorem programHeader_primrec : Primrec programHeader := by
  unfold programHeader
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const foldedSymbolList)
      (Primrec.pair foldedStateList_primrec
        (Primrec.pair (Primrec.const foldedBlank)
          (Primrec.pair (Primrec.const foldedStartState) initRows_primrec))))

theorem programHeader_computable : Computable programHeader :=
  programHeader_primrec.to_comp

theorem programData_eq_programHeader_with_simRows (tc : Turing.ToPartrec.Code) :
    programData tc =
      { programHeader tc with table := (programHeader tc).table ++ simRows tc } := by
  rfl

theorem programData_eq_appendSimRows_programHeader (tc : Turing.ToPartrec.Code) :
    programData tc = appendSimRows (programHeader tc) (simRows tc) := by
  rfl

def programDataFromSimRows (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  appendSimRows (programHeader tc) (simRows tc)

theorem programDataFromSimRows_eq_programData (tc : Turing.ToPartrec.Code) :
    programDataFromSimRows tc = programData tc :=
  (programData_eq_appendSimRows_programHeader tc).symm

theorem positionProgramData_eq_appendSimRows_programHeader
    (tc : Turing.ToPartrec.Code) :
    positionProgramData tc =
      appendSimRows (programHeader tc)
        (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)) := by
  rfl

theorem positionProgramData_transition?_sim_eq_generated
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} :
    (positionProgramData tc).transition? (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) := by
  have hinit := initRowsData_find?_eq_none_of_foldedSimStateCode tc side q
    (foldedSymbolCode marked left right)
  unfold PostProgram.transition?
  change (initRowsData ++
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right))
  exact program_find?_append_of_eq_none hinit

theorem positionProgramData_transition?_sim_eq_some_of_support_succ_step
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some (stmtOpt, v))
    (hstate : TM0FiniteCompiler.stateCode tc (stmtOpt, v) = n + 1)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        some (q', stmt)) :
    (positionProgramData tc).transition?
        (foldedSimStateCode tc side (stmtOpt, v))
        (foldedSymbolCode marked left right) =
      some (simRowOfStep tc side marked (stmtOpt, v) q' left right stmt) := by
  rw [positionProgramData_transition?_sim_eq_generated]
  exact simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_support_succ_step
    (tc := tc) (n := n) (stmtOpt := stmtOpt) (v := v) (q' := q') (side := side)
    (marked := marked) (left := left) (right := right) (stmt := stmt)
    hn hsupport hstate hstep

theorem positionProgramData_step_sim_eq_some_of_support_succ_step
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hqlist : (stmtOpt, v) ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some (stmtOpt, v))
    (hstate : TM0FiniteCompiler.stateCode tc (stmtOpt, v) = n + 1)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        some (q', stmt)) :
    (positionProgramData tc).step
        (foldedSimStateCode tc side (stmtOpt, v))
        (foldedSymbolCode marked left right) =
      some ((simRowOfStep tc side marked (stmtOpt, v) q' left right stmt).next,
        (simRowOfStep tc side marked (stmtOpt, v) q' left right stmt).stmt) := by
  have hfind := positionProgramData_transition?_sim_eq_some_of_support_succ_step
    (tc := tc) (n := n) (stmtOpt := stmtOpt) (v := v) (q' := q') (side := side)
    (marked := marked) (left := left) (right := right) (stmt := stmt)
    hn hsupport hstate hstep
  have hqset : (stmtOpt, v) ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc (stmtOpt, v)).1 hqlist
  have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
    TM0FiniteCompiler.next_label_mem_of_step hqset hstep
  have hq'list : q' ∈ TM0Route.partrecStartedTM0LabelList tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  have hnext :
      (simRowOfStep tc side marked (stmtOpt, v) q' left right stmt).next ∈
        foldedStateList tc :=
    simRowOfStep_next_mem_states tc side marked (stmtOpt, v) hq'list left right stmt
  have hwrite := simRowOfStep_write_mem_symbols
    tc side marked (stmtOpt, v) q' left right stmt
  unfold PostProgram.step
  rw [hfind]
  simp only [positionProgramData, programDataOfStepData, programOfCountAndSimRows,
    programOfCountAndRows, programOfParts, dite_eq_ite, Option.ite_none_right_eq_some]
  constructor
  · exact hnext
  cases hstmt : (simRowOfStep tc side marked (stmtOpt, v) q' left right stmt).stmt with
  | move m =>
      simp
  | write b =>
      have hb : b ∈ foldedSymbolList := by
        simpa [hstmt] using hwrite
      simp [hb]

theorem positionProgramData_transition?_sim_eq_some_of_sourceDefault_step
    {tc : Turing.ToPartrec.Code} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        some (q', stmt)) :
    (positionProgramData tc).transition?
        (foldedSimStateCode tc side (sourceDefaultLabel tc))
        (foldedSymbolCode marked left right) =
      some (simRowOfStep tc side marked (sourceDefaultLabel tc) q' left right stmt) := by
  rw [positionProgramData_transition?_sim_eq_generated]
  exact simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_some_of_sourceDefault_step
    (tc := tc) (q' := q') (side := side) (marked := marked)
    (left := left) (right := right) (stmt := stmt) hstep

theorem positionProgramData_step_sim_eq_some_of_sourceDefault_step
    {tc : Turing.ToPartrec.Code} {q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        some (q', stmt)) :
    (positionProgramData tc).step
        (foldedSimStateCode tc side (sourceDefaultLabel tc))
        (foldedSymbolCode marked left right) =
      some ((simRowOfStep tc side marked (sourceDefaultLabel tc) q' left right stmt).next,
        (simRowOfStep tc side marked (sourceDefaultLabel tc) q' left right stmt).stmt) := by
  have hfind := positionProgramData_transition?_sim_eq_some_of_sourceDefault_step
    (tc := tc) (q' := q') (side := side) (marked := marked)
    (left := left) (right := right) (stmt := stmt) hstep
  have hqset : sourceDefaultLabel tc ∈ TM0Route.partrecStartedTM0Labels tc := by
    exact (TM0Route.mem_partrecStartedTM0LabelList tc (sourceDefaultLabel tc)).1
      (sourceDefaultLabel_mem_partrecStartedTM0LabelList tc)
  have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
    TM0FiniteCompiler.next_label_mem_of_step hqset hstep
  have hq'list : q' ∈ TM0Route.partrecStartedTM0LabelList tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  have hnext :
      (simRowOfStep tc side marked (sourceDefaultLabel tc) q' left right stmt).next ∈
        foldedStateList tc :=
    simRowOfStep_next_mem_states tc side marked (sourceDefaultLabel tc) hq'list
      left right stmt
  have hwrite := simRowOfStep_write_mem_symbols
    tc side marked (sourceDefaultLabel tc) q' left right stmt
  unfold PostProgram.step
  rw [hfind]
  simp only [positionProgramData, programDataOfStepData, programOfCountAndSimRows,
    programOfCountAndRows, programOfParts, dite_eq_ite, Option.ite_none_right_eq_some]
  constructor
  · exact hnext
  cases hstmt : (simRowOfStep tc side marked (sourceDefaultLabel tc) q' left right stmt).stmt with
  | move m =>
      simp
  | write b =>
      have hb : b ∈ foldedSymbolList := by
        simpa [hstmt] using hwrite
      simp [hb]

theorem positionProgramData_transition?_sim_eq_none_of_sourceDefault_no_step
    {tc : Turing.ToPartrec.Code}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        none) :
    (positionProgramData tc).transition?
        (foldedSimStateCode tc side (sourceDefaultLabel tc))
        (foldedSymbolCode marked left right) =
      none := by
  rw [positionProgramData_transition?_sim_eq_generated]
  exact simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_none_of_sourceDefault_no_step
    (tc := tc) (side := side) (marked := marked)
    (left := left) (right := right) hstep

theorem positionProgramData_step_sim_eq_none_of_sourceDefault_no_step
    {tc : Turing.ToPartrec.Code}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (sourceDefaultLabel tc)
          (foldedRead side left right) =
        none) :
    (positionProgramData tc).step
        (foldedSimStateCode tc side (sourceDefaultLabel tc))
        (foldedSymbolCode marked left right) =
      none := by
  have hfind := positionProgramData_transition?_sim_eq_none_of_sourceDefault_no_step
    (tc := tc) (side := side) (marked := marked)
    (left := left) (right := right) hstep
  simp [PostProgram.step, hfind]

theorem positionProgramData_transition?_sim_eq_none_of_support_succ_no_step
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some (stmtOpt, v))
    (hstate : TM0FiniteCompiler.stateCode tc (stmtOpt, v) = n + 1)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        none) :
    (positionProgramData tc).transition?
        (foldedSimStateCode tc side (stmtOpt, v))
        (foldedSymbolCode marked left right) =
      none := by
  rw [positionProgramData_transition?_sim_eq_generated]
  exact simRowsOfStepDataByLabelIndexWithPositionCode_find?_eq_none_of_support_succ_no_step
    (tc := tc) (n := n) (stmtOpt := stmtOpt) (v := v) (side := side)
    (marked := marked) (left := left) (right := right)
    hn hsupport hstate hstep

theorem positionProgramData_step_sim_eq_none_of_support_succ_no_step
    {tc : Turing.ToPartrec.Code} {n : Nat}
    {stmtOpt : Option (SourceStmt tc)} {v : PartrecVar}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    (hn : n < TM0Route.partrecStartedTM0LabelCount tc)
    (hsupport :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[n + 1]? = some (stmtOpt, v))
    (hstate : TM0FiniteCompiler.stateCode tc (stmtOpt, v) = n + 1)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc (stmtOpt, v) (foldedRead side left right) =
        none) :
    (positionProgramData tc).step
        (foldedSimStateCode tc side (stmtOpt, v))
        (foldedSymbolCode marked left right) =
      none := by
  have hfind := positionProgramData_transition?_sim_eq_none_of_support_succ_no_step
    (tc := tc) (n := n) (stmtOpt := stmtOpt) (v := v) (side := side)
    (marked := marked) (left := left) (right := right)
    hn hsupport hstate hstep
  simp [PostProgram.step, hfind]

theorem positionProgramData_step_sim_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (positionProgramData tc).step
        (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      some ((simRowOfStep tc side marked q q' left right stmt).next,
        (simRowOfStep tc side marked q q' left right stmt).stmt) := by
  by_cases hdefault : q = sourceDefaultLabel tc
  · subst q
    exact positionProgramData_step_sim_eq_some_of_sourceDefault_step
      (tc := tc) (q' := q') (side := side) (marked := marked)
      (left := left) (right := right) (stmt := stmt) hstep
  · rcases q with ⟨stmtOpt, v⟩
    rcases exists_support_succ_of_labelList_ne_sourceDefault
        (tc := tc) (q := (stmtOpt, v)) hq hdefault with
      ⟨n, hn, hsupport, hstate⟩
    exact positionProgramData_step_sim_eq_some_of_support_succ_step
      (tc := tc) (n := n) (stmtOpt := stmtOpt) (v := v)
      (q' := q') (side := side) (marked := marked)
      (left := left) (right := right) (stmt := stmt)
      hn hq hsupport hstate hstep

theorem positionProgramData_step_sim_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        none) :
    (positionProgramData tc).step
        (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      none := by
  by_cases hdefault : q = sourceDefaultLabel tc
  · subst q
    exact positionProgramData_step_sim_eq_none_of_sourceDefault_no_step
      (tc := tc) (side := side) (marked := marked)
      (left := left) (right := right) hstep
  · rcases q with ⟨stmtOpt, v⟩
    rcases exists_support_succ_of_labelList_ne_sourceDefault
        (tc := tc) (q := (stmtOpt, v)) hq hdefault with
      ⟨n, hn, hsupport, hstate⟩
    exact positionProgramData_step_sim_eq_none_of_support_succ_no_step
      (tc := tc) (n := n) (stmtOpt := stmtOpt) (v := v)
      (side := side) (marked := marked) (left := left) (right := right)
      hn hsupport hstate hstep

end TM0FoldedCompiler

end LeanWang
