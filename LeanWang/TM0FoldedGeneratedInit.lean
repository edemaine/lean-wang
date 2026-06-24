/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram

/-!
Initialization lemmas for the generated folded program data.

`TM0FoldedCompiler` proves the semantic initialization path for the canonical
finite program. This file records the matching facts for `positionProgramData`,
the generated program used while bridging semantic correctness to the executable
reduction data.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

private theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx] at h
      · simp [hx]
        have hxs : xs.find? p = none := by
          simpa [hx] using h
        simpa [hx] using ih hxs

private theorem find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool}
    {a : α} (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa : x = a := by
          simpa [hx] using h
        subst a
        simp [hx]
      · have hxs : xs.find? p = some a := by
          simpa [hx] using h
        simp [hx, hxs]

@[simp]
theorem positionProgramData_symbols (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).symbols = foldedSymbolList :=
  rfl

@[simp]
theorem positionProgramData_states (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).states =
      foldedStateListForCount (TM0Route.partrecStartedTM0StateCount tc) :=
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

theorem foldedStartState_mem_stateListForCount (tc : Turing.ToPartrec.Code) :
    foldedStartState ∈
      foldedStateListForCount (TM0Route.partrecStartedTM0StateCount tc) := by
  unfold foldedStateListForCount foldedStateListOfCodes
  apply List.mem_append_left
  simp [foldedInitStateList, foldedStartState, initWriteOriginState]

theorem initReturnState_zero_mem_stateListForCount (tc : Turing.ToPartrec.Code) :
    initReturnState 0 ∈
      foldedStateListForCount (TM0Route.partrecStartedTM0StateCount tc) := by
  unfold foldedStateListForCount foldedStateListOfCodes
  apply List.mem_append_left
  simp [foldedInitStateList]

theorem foldedSimStartState_mem_stateListForCount (tc : Turing.ToPartrec.Code) :
    foldedSimStartState tc ∈
      foldedStateListForCount (TM0Route.partrecStartedTM0StateCount tc) := by
  unfold foldedStateListForCount foldedStateListOfCodes foldedSimStateListOfCodes
  rw [List.mem_append]
  apply Or.inr
  rw [List.mem_flatMap]
  refine ⟨TM0Route.partrecStartedTM0Start, ?_, ?_⟩
  · exact TM0Route.partrecStartedTM0Start_mem_states tc
  · simpa [foldedSimStartState, foldedSimStartStateCode] using
      List.mem_map_of_mem (mem_foldSideList FoldSide.right)

theorem partrecStartedTM0Input_length :
    TM0Route.partrecStartedTM0Input.length = 1 := by
  simp [TM0Route.partrecStartedTM0Input, TM0Route.partrecStartedTM2Input,
    Turing.TM2to1.trInit, Turing.PartrecToTM2.trList]

theorem nextAfterOrigin_eq_initReturnState_zero :
    nextAfterOrigin = initReturnState 0 := by
  unfold nextAfterOrigin
  rw [partrecStartedTM0Input_length]
  simp

private theorem initWriteOriginState_ne_initReturnState_data (i : Nat) :
    initWriteOriginState ≠ initReturnState i := by
  intro h
  unfold initWriteOriginState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

private theorem initMoveRightRows_find?_eq_none_of_initReturnState_data
    (i read : Nat) :
    initMoveRightRows.find? (fun e => e.matchesInput (initReturnState i) read) = none := by
  simp [initMoveRightRows, partrecStartedTM0Input_length]

private theorem initWriteRightRows_find?_eq_none_of_initReturnState_data
    (i read : Nat) :
    initWriteRightRows.find? (fun e => e.matchesInput (initReturnState i) read) = none := by
  simp [initWriteRightRows, partrecStartedTM0Input_length]

private theorem find?_map_initReturnRow_zero_of_read_aux
    (reads : List Nat) {read : Nat} (hread : read ∈ reads) :
    (reads.map fun r => initReturnRow default 0 r).find?
        (fun e => e.matchesInput (initReturnState 0) read) =
      some (initReturnRow default 0 read) := by
  induction reads with
  | nil =>
      simp at hread
  | cons r reads ih =>
      by_cases hr : r = read
      · subst r
        simp [initReturnRow, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := by
          have hreadOr : read = r ∨ read ∈ reads := by
            simpa using hread
          rcases hreadOr with hhead | htail
          · exact False.elim (hr hhead.symm)
          · exact htail
        have hmiss :
            (initReturnRow default 0 r).matchesInput (initReturnState 0) read = false := by
          simp [initReturnRow, mkRow, PostTransition.matchesInput, hr]
        simp [hmiss, ih htail]

private theorem initReturnRowsData_find?_zero {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    initReturnRowsData.find? (fun e => e.matchesInput (initReturnState 0) read) =
      some (initReturnRow default 0 read) := by
  unfold initReturnRowsData initReturnIndexList
  exact find?_append_of_eq_some
    (find?_map_initReturnRow_zero_of_read_aux foldedSymbolList hread)

private theorem initRowsData_find?_start_blank :
    initRowsData.find? (fun e => e.matchesInput foldedStartState foldedBlank) =
      some initWriteOriginRow := by
  unfold initRowsData
  have hmatch :
      initWriteOriginRow.matchesInput foldedStartState foldedBlank = true := by
    simp [initWriteOriginRow, foldedStartState, mkRow, PostTransition.matchesInput]
  simp [hmatch]

private theorem initRowsData_find?_initReturn_zero {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    initRowsData.find? (fun e => e.matchesInput (initReturnState 0) read) =
      some (initReturnRow default 0 read) := by
  have horigin :
      initWriteOriginRow.matchesInput (initReturnState 0) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne_data
      (initWriteOriginState_ne_initReturnState_data 0)
  have hmove := initMoveRightRows_find?_eq_none_of_initReturnState_data 0 read
  have hwrite := initWriteRightRows_find?_eq_none_of_initReturnState_data 0 read
  have hreturn := initReturnRowsData_find?_zero hread
  unfold initRowsData
  have htail :
      (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData)).find?
          (fun e => e.matchesInput (initReturnState 0) read) =
        some (initReturnRow default 0 read) := by
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

theorem positionProgramData_transition?_start_blank
    (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).transition? foldedStartState foldedBlank =
      some initWriteOriginRow := by
  unfold PostProgram.transition?
  change (initRowsData ++
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e => e.matchesInput foldedStartState foldedBlank) =
      some initWriteOriginRow
  exact find?_append_of_eq_some initRowsData_find?_start_blank

theorem positionProgramData_step_start_blank
    (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).step foldedStartState foldedBlank =
      some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
  have hfind := positionProgramData_transition?_start_blank tc
  have hnext :
      nextAfterOrigin ∈
        foldedStateListForCount (TM0Route.partrecStartedTM0StateCount tc) := by
    rw [nextAfterOrigin_eq_initReturnState_zero]
    exact initReturnState_zero_mem_stateListForCount tc
  have hwrite : foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedSymbolCode_mem_symbols true default (inputSymbol 0)
  have hnext' :
      nextAfterOrigin ∈
        foldedStateListOfCodes (List.range (TM0Route.partrecStartedTM0StateCount tc)) := by
    simpa [foldedStateListForCount] using hnext
  unfold PostProgram.step
  rw [hfind]
  simp [positionProgramData, programDataOfStepData, programOfCountAndSimRows,
    programOfCountAndRows, programOfParts, initWriteOriginRow, mkRow, hnext', hwrite]

theorem positionProgramData_transition?_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (positionProgramData tc).transition? (initReturnState 0) read =
      some (initReturnRow default 0 read) := by
  unfold PostProgram.transition?
  change (initRowsData ++
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e => e.matchesInput (initReturnState 0) read) =
      some (initReturnRow default 0 read)
  exact find?_append_of_eq_some (initRowsData_find?_initReturn_zero hread)

theorem positionProgramData_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (positionProgramData tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have hfind := positionProgramData_transition?_initReturn_zero tc hread
  have hnext :
      foldedSimStartState tc ∈
        foldedStateListForCount (TM0Route.partrecStartedTM0StateCount tc) :=
    foldedSimStartState_mem_stateListForCount tc
  have hnext' :
      foldedSimStartState tc ∈
        foldedStateListOfCodes (List.range (TM0Route.partrecStartedTM0StateCount tc)) := by
    simpa [foldedStateListForCount] using hnext
  have hnextCode :
      foldedSimStartStateCode ∈
        foldedStateListOfCodes (List.range (TM0Route.partrecStartedTM0StateCount tc)) := by
    simpa [foldedSimStartState] using hnext'
  unfold PostProgram.step
  rw [hfind]
  simp [positionProgramData, programDataOfStepData, programOfCountAndSimRows,
    programOfCountAndRows, programOfParts, foldedSimStartState, initReturnRow,
    mkRow, hnextCode, hread]

end TM0FoldedCompiler

end LeanWang
