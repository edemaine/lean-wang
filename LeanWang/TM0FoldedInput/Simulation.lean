/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.InitRelation
import LeanWang.TM0FoldedPositionCorrect.LocalStep

/-!
Position-coded simulation correctness with a varying initialization prefix.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

theorem foldedSimStateCode_mem_statesOnInput
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol)
    (side : FoldSide) {q : SourceLabel tc}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc) :
    foldedSimStateCode tc side q ∈
      (positionProgramDataOnInput tc input).states := by
  unfold positionProgramDataOnInput positionProgramDataForInput
    foldedStateListForInput foldedSimStateListOfCodes
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨TM0FiniteCompiler.stateCode tc q, ?_, ?_⟩
  · exact TM0FiniteCompiler.stateCode_mem_states tc q
      ((TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq)
  · exact List.mem_map_of_mem (mem_foldSideList side)

theorem initRowsForInput_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol)
    (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    (initRowsForInput input).find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  unfold initRowsForInput at he
  simp only [List.mem_cons, List.mem_append] at he
  rcases he with rfl | he
  · exact mkRow_matchesInput_of_state_ne_data
      (initWriteOriginState_ne_foldedSimStateCode_data tc side q)
  rcases he with he | he
  · unfold initMoveRightRowsFor at he
    rw [List.mem_flatMap] at he
    rcases he with ⟨i, _hi, he⟩
    rw [List.mem_map] at he
    rcases he with ⟨r, _hr, rfl⟩
    exact mkRow_matchesInput_of_state_ne_data
      (initMoveRightState_ne_foldedSimStateCode_data tc i side q)
  rcases he with he | he
  · unfold initWriteRightRowsFor at he
    rw [List.mem_map] at he
    rcases he with ⟨i, _hi, rfl⟩
    exact mkRow_matchesInput_of_state_ne_data
      (initWriteRightState_ne_foldedSimStateCode_data tc i side q)
  · unfold initReturnRowsFor at he
    rw [List.mem_flatMap] at he
    rcases he with ⟨i, _hi, he⟩
    rw [List.mem_map] at he
    rcases he with ⟨r, _hr, rfl⟩
    by_cases hi0 : i = 0
    · subst i
      exact mkRow_matchesInput_of_state_ne_data
        (initReturnState_ne_foldedSimStateCode_data tc 0 side q)
    · unfold initReturnRow
      rw [if_neg hi0]
      exact mkRow_matchesInput_of_state_ne_data
        (initReturnState_ne_foldedSimStateCode_data tc i side q)

theorem positionProgramDataOnInput_transition?_sim_eq_position
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol)
    (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    (positionProgramDataOnInput tc input).transition?
        (foldedSimStateCode tc side q) read =
      (positionProgramData tc).transition?
        (foldedSimStateCode tc side q) read := by
  have hnew := initRowsForInput_find?_eq_none_of_foldedSimStateCode
    tc input side q read
  have hold := initRowsData_find?_eq_none_of_foldedSimStateCode tc side q read
  unfold positionProgramDataOnInput positionProgramDataForInput
    positionProgramData programDataOfStepData programOfCountAndSimRows
    programOfCountAndRows programOfParts PostProgram.transition?
  rw [program_find?_append_of_eq_none hnew]
  rw [program_find?_append_of_eq_none hold]

private theorem positionProgramData_transition?_sim_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q
      (foldedRead side left right) = some (q', stmt)) :
    (positionProgramData tc).transition?
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  by_cases hdefault : q = sourceDefaultLabel tc
  · subst q
    exact positionProgramData_transition?_sim_eq_some_of_sourceDefault_step hstep
  · rcases q with ⟨stmtOpt, v⟩
    rcases exists_support_succ_of_labelList_ne_sourceDefault
        hq hdefault with ⟨n, hn, hsupport, hstate⟩
    exact positionProgramData_transition?_sim_eq_some_of_support_succ_step
      hn hsupport hstate hstep

private theorem positionProgramData_transition?_sim_of_no_step
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q
      (foldedRead side left right) = none) :
    (positionProgramData tc).transition?
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = none := by
  by_cases hdefault : q = sourceDefaultLabel tc
  · subst q
    exact positionProgramData_transition?_sim_eq_none_of_sourceDefault_no_step hstep
  · rcases q with ⟨stmtOpt, v⟩
    rcases exists_support_succ_of_labelList_ne_sourceDefault
        hq hdefault with ⟨n, hn, hsupport, hstate⟩
    exact positionProgramData_transition?_sim_eq_none_of_support_succ_no_step
      hn hsupport hstate hstep

theorem positionProgramDataOnInput_step_sim_of_step
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q
      (foldedRead side left right) = some (q', stmt)) :
    (positionProgramDataOnInput tc input).step
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      some ((simRowOfStep tc side marked q q' left right stmt).next,
        (simRowOfStep tc side marked q q' left right stmt).stmt) := by
  have hold := positionProgramData_transition?_sim_of_step
    (side := side) (marked := marked) (left := left) (right := right) hq hstep
  have hfind : (positionProgramDataOnInput tc input).transition?
      (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
    rw [positionProgramDataOnInput_transition?_sim_eq_position]
    exact hold
  have hqset := (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq
  have hq'set := TM0FiniteCompiler.next_label_mem_of_step hqset hstep
  have hq'list := (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  have hnext : (simRowOfStep tc side marked q q' left right stmt).next ∈
      (positionProgramDataOnInput tc input).states := by
    cases stmt with
    | move dir =>
        have hm := foldedSimStateCode_mem_statesOnInput tc input
          (foldedMoveNextSide side marked dir) hq'list
        simpa [simRowOfStep, mkRow] using hm
    | write new =>
        have hm := foldedSimStateCode_mem_statesOnInput tc input side hq'list
        simpa [simRowOfStep, mkRow] using hm
  have hwrite := simRowOfStep_write_mem_symbols
    tc side marked q q' left right stmt
  unfold PostProgram.step
  rw [hfind]
  simp only [dite_eq_ite, Option.ite_none_right_eq_some]
  constructor
  · exact hnext
  cases hstmt : (simRowOfStep tc side marked q q' left right stmt).stmt with
  | move m => simp
  | write b =>
      have hb : b ∈ foldedSymbolList := by simpa [hstmt] using hwrite
      simpa using hb

theorem positionProgramDataOnInput_step_sim_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q
      (foldedRead side left right) = none) :
    (positionProgramDataOnInput tc input).step
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = none := by
  have hold := positionProgramData_transition?_sim_of_no_step
    (side := side) (marked := marked) (left := left) (right := right) hq hstep
  have hfind : (positionProgramDataOnInput tc input).transition?
      (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = none := by
    rw [positionProgramDataOnInput_transition?_sim_eq_position]
    exact hold
  simp [PostProgram.step, hfind]

end TM0FoldedCompiler

end LeanWang
