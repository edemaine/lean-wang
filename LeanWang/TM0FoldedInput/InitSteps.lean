/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.InitSearchWriteReturn

/-!
Guarded step equations for the data-parameterized initializer.
-/

namespace LeanWang

namespace TM0FoldedCompiler

theorem foldedSimStartState_mem_statesOnInput
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    foldedSimStartStateCode ∈
      (positionProgramDataOnInput tc input).states := by
  unfold positionProgramDataOnInput positionProgramDataForInput
    foldedStateListForInput foldedSimStartStateCode foldedSimStateOfCode
    foldedSimStateListOfCodes
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨TM0Route.partrecStartedTM0Start, ?_, ?_⟩
  · exact TM0Route.partrecStartedTM0Start_mem_states tc
  · exact List.mem_map_of_mem (mem_foldSideList FoldSide.right)

private theorem transition?_of_init_find?_eq_some
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {q read : Nat} {row : PostTransition}
    (hfind : (initRowsForInput input).find?
      (fun e => e.matchesInput q read) = some row) :
    (positionProgramDataOnInput tc input).transition? q read = some row := by
  unfold positionProgramDataOnInput positionProgramDataForInput
    PostProgram.transition?
  exact program_find?_append_of_eq_some hfind

theorem positionProgramDataOnInput_step_start
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    (positionProgramDataOnInput tc input).step foldedStartState foldedBlank =
      some (nextAfterOriginFor input,
        PostStmt.write (foldedOriginSymbol (inputSymbolFor input 0))) := by
  have hfind := transition?_of_init_find?_eq_some
    (tc := tc) (initRowsForInput_find?_start_blank input)
  have hnext := nextAfterOriginFor_mem_statesForInput
    (TM0Route.partrecStartedTM0StateCount tc) input
  have hsymbol :
      foldedOriginSymbol (inputSymbolFor input 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols _
  simp [PostProgram.step, hfind, initWriteOriginRowFor, mkRow, hnext, hsymbol]

theorem positionProgramDataOnInput_step_move
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {i read : Nat}
    (hi : i < input.length - 1) (hread : read ∈ foldedSymbolList) :
    (positionProgramDataOnInput tc input).step (initMoveRightState i) read =
      some (initWriteRightState i, PostStmt.move Move.right) := by
  have hfind := transition?_of_init_find?_eq_some
    (tc := tc) (initRowsForInput_find?_move hi hread)
  have hnext := initWriteRightState_mem_statesForInput
    (TM0Route.partrecStartedTM0StateCount tc)
      (input := input) (i := i) (by omega)
  simp [PostProgram.step, hfind, initMoveRightRow, mkRow, hnext]

theorem positionProgramDataOnInput_step_write
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {i : Nat}
    (hi : i < input.length - 1) :
    (positionProgramDataOnInput tc input).step
        (initWriteRightState i) foldedBlank =
      some (nextAfterWriteRightFor input i,
        PostStmt.write
          (foldedSymbolCode false default (inputSymbolFor input (i + 1)))) := by
  have hfind := transition?_of_init_find?_eq_some
    (tc := tc) (initRowsForInput_find?_write hi)
  have hnext := nextAfterWriteRightFor_mem_statesForInput
    (TM0Route.partrecStartedTM0StateCount tc)
      (input := input) (i := i) (by omega)
  have hsymbol :
      foldedSymbolCode false default (inputSymbolFor input (i + 1)) ∈
        foldedSymbolList :=
    foldedSymbolCode_mem_symbols _ _ _
  simp [PostProgram.step, hfind, initWriteRightRowFor, mkRow, hnext, hsymbol]

theorem positionProgramDataOnInput_step_return_zero
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (positionProgramDataOnInput tc input).step (initReturnState 0) read =
      some (foldedSimStartStateCode, PostStmt.write read) := by
  have hindex : 0 ∈ initReturnIndexListFor input := by
    simp [initReturnIndexListFor]
  have hfind := transition?_of_init_find?_eq_some
    (tc := tc) (initRowsForInput_find?_return hindex hread)
  have hnext := foldedSimStartState_mem_statesOnInput tc input
  have hnext' : foldedSimStartStateCode ∈
      foldedStateListForInput (TM0Route.partrecStartedTM0StateCount tc) input := by
    simpa using hnext
  simp [PostProgram.step, hfind, initReturnRow, mkRow, hnext', hread]

theorem positionProgramDataOnInput_step_return_succ
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {i read : Nat}
    (hi : i + 1 < input.length) (hread : read ∈ foldedSymbolList) :
    (positionProgramDataOnInput tc input).step (initReturnState (i + 1)) read =
      some (initReturnState i, PostStmt.move Move.left) := by
  have hindex : i + 1 ∈ initReturnIndexListFor input := by
    simp [initReturnIndexListFor, List.mem_range, hi]
  have hfind := transition?_of_init_find?_eq_some
    (tc := tc) (initRowsForInput_find?_return hindex hread)
  have hnext := initReturnState_mem_statesForInput
    (TM0Route.partrecStartedTM0StateCount tc) input i
      (by omega)
  simp [PostProgram.step, hfind, initReturnRow, mkRow, hnext]

end TM0FoldedCompiler

end LeanWang
