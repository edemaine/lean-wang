/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput

/-!
Primitive-recursion facts for the data-parameterized folded initializer.
-/

namespace LeanWang

namespace TM0FoldedCompiler

private def initStateBlock (i : Nat) : List Nat :=
  [initMoveRightState i, initWriteRightState i, initReturnState i]

private theorem initStateBlock_primrec : Primrec initStateBlock := by
  unfold initStateBlock
  exact Primrec.list_cons.comp initMoveRightState_primrec
    (Primrec.list_cons.comp initWriteRightState_primrec
      (Primrec.list_cons.comp initReturnState_primrec
        (Primrec.const ([] : List Nat))))

theorem foldedInitStateListFor_primrec : Primrec foldedInitStateListFor := by
  unfold foldedInitStateListFor
  have hrange : Primrec (fun input : List SourceSymbol => List.range input.length) :=
    Primrec.list_range.comp Primrec.list_length
  have hblocks : Primrec (fun input : List SourceSymbol =>
      (List.range input.length).flatMap initStateBlock) := by
    refine Primrec.list_flatMap hrange ?_
    apply Primrec₂.mk
    exact initStateBlock_primrec.comp Primrec.snd
  exact (Primrec.list_append.comp
    (Primrec.const [initWriteOriginState, initReturnState 0]) hblocks).of_eq
      fun _ => rfl

theorem foldedStateListForInput_primrec :
    Primrec (fun p : Nat × List SourceSymbol =>
      foldedStateListForInput p.1 p.2) := by
  unfold foldedStateListForInput
  exact Primrec.list_append.comp
    (foldedInitStateListFor_primrec.comp Primrec.snd)
    (foldedSimStateListOfCodes_primrec.comp
      (Primrec.list_range.comp Primrec.fst))

theorem inputSymbolFor_primrec :
    Primrec (fun p : List SourceSymbol × Nat => inputSymbolFor p.1 p.2) := by
  exact Primrec.list_getI

theorem nextAfterOriginFor_primrec : Primrec nextAfterOriginFor := by
  unfold nextAfterOriginFor
  have hshort : PrimrecPred (fun input : List SourceSymbol => input.length ≤ 1) :=
    Primrec.nat_le.comp Primrec.list_length (Primrec.const 1)
  exact Primrec.ite hshort (Primrec.const (initReturnState 0))
    (Primrec.const (initMoveRightState 0))

theorem initWriteOriginRowFor_primrec : Primrec initWriteOriginRowFor := by
  unfold initWriteOriginRowFor
  have hinput : Primrec (fun input : List SourceSymbol => inputSymbolFor input 0) :=
    inputSymbolFor_primrec.comp (Primrec.pair Primrec.id (Primrec.const 0))
  have hsymbol : Primrec (fun input : List SourceSymbol =>
      foldedOriginSymbol (inputSymbolFor input 0)) :=
    foldedOriginSymbol_primrec.comp hinput
  have hstmt : Primrec (fun input : List SourceSymbol =>
      PostStmt.write (foldedOriginSymbol (inputSymbolFor input 0))) :=
    postStmtWrite_primrec.comp hsymbol
  exact mkRow_primrec.comp
    (Primrec.pair (Primrec.const initWriteOriginState)
      (Primrec.pair (Primrec.const foldedBlank)
        (Primrec.pair nextAfterOriginFor_primrec hstmt)))

theorem nextAfterWriteRightFor_primrec :
    Primrec (fun p : List SourceSymbol × Nat =>
      nextAfterWriteRightFor p.1 p.2) := by
  unfold nextAfterWriteRightFor
  have hi : Primrec (fun p : List SourceSymbol × Nat => p.2) := Primrec.snd
  have hnext : Primrec (fun p : List SourceSymbol × Nat => p.2 + 1) :=
    Primrec.succ.comp hi
  have hlt : PrimrecPred (fun p : List SourceSymbol × Nat =>
      p.2 + 2 < p.1.length) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp hi (Primrec.const 2))
      (Primrec.list_length.comp Primrec.fst)
  exact Primrec.ite hlt
    (initMoveRightState_primrec.comp hnext)
    (initReturnState_primrec.comp hnext)

set_option maxHeartbeats 800000 in
-- Elaborating the nested finite-symbol encoder needs more than the default budget.
theorem initWriteRightRowFor_primrec :
    Primrec (fun p : List SourceSymbol × Nat =>
      initWriteRightRowFor p.1 p.2) := by
  unfold initWriteRightRowFor
  have hi : Primrec (fun p : List SourceSymbol × Nat => p.2) := Primrec.snd
  have hinput : Primrec (fun p : List SourceSymbol × Nat =>
      inputSymbolFor p.1 (p.2 + 1)) :=
    inputSymbolFor_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd))
  have hsymbol : Primrec (fun p : List SourceSymbol × Nat =>
      foldedSymbolCode false default (inputSymbolFor p.1 (p.2 + 1))) :=
    foldedSymbolCode_primrec.comp
      (Primrec.pair (Primrec.const false)
        (Primrec.pair (Primrec.const default) hinput))
  have hstmt : Primrec (fun p : List SourceSymbol × Nat =>
      PostStmt.write
        (foldedSymbolCode false default (inputSymbolFor p.1 (p.2 + 1)))) :=
    postStmtWrite_primrec.comp hsymbol
  exact mkRow_primrec.comp
    (Primrec.pair (initWriteRightState_primrec.comp hi)
      (Primrec.pair (Primrec.const foldedBlank)
        (Primrec.pair nextAfterWriteRightFor_primrec hstmt)))

private theorem initMoveRightRowsForIndex_primrec :
    Primrec (fun i : Nat =>
      foldedSymbolList.map fun read => initMoveRightRow i read) := by
  refine Primrec.list_map (Primrec.const foldedSymbolList) ?_
  apply Primrec₂.mk
  exact initMoveRightRow_primrec.comp
    (Primrec.pair Primrec.fst Primrec.snd)

theorem initMoveRightRowsFor_primrec : Primrec initMoveRightRowsFor := by
  unfold initMoveRightRowsFor
  have hrange : Primrec (fun input : List SourceSymbol =>
      List.range (input.length - 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
  refine Primrec.list_flatMap hrange ?_
  apply Primrec₂.mk
  exact initMoveRightRowsForIndex_primrec.comp Primrec.snd

theorem initWriteRightRowsFor_primrec : Primrec initWriteRightRowsFor := by
  unfold initWriteRightRowsFor
  have hrange : Primrec (fun input : List SourceSymbol =>
      List.range (input.length - 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
  refine Primrec.list_map hrange ?_
  apply Primrec₂.mk
  exact initWriteRightRowFor_primrec.comp
    (Primrec.pair Primrec.fst Primrec.snd)

theorem initReturnIndexListFor_primrec : Primrec initReturnIndexListFor := by
  unfold initReturnIndexListFor
  exact Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_range.comp Primrec.list_length)

private theorem initReturnRowsForIndex_primrec :
    Primrec (fun i : Nat =>
      foldedSymbolList.map fun read => initReturnRow default i read) := by
  refine Primrec.list_map (Primrec.const foldedSymbolList) ?_
  apply Primrec₂.mk
  exact initReturnRow_primrec.comp
    (Primrec.pair (Primrec.const (default : Turing.ToPartrec.Code))
      (Primrec.pair Primrec.fst Primrec.snd))

theorem initReturnRowsFor_primrec : Primrec initReturnRowsFor := by
  unfold initReturnRowsFor
  refine Primrec.list_flatMap initReturnIndexListFor_primrec ?_
  apply Primrec₂.mk
  exact initReturnRowsForIndex_primrec.comp Primrec.snd

theorem initRowsForInput_primrec : Primrec initRowsForInput := by
  unfold initRowsForInput
  exact Primrec.list_cons.comp initWriteOriginRowFor_primrec
    (Primrec.list_append.comp initMoveRightRowsFor_primrec
      (Primrec.list_append.comp initWriteRightRowsFor_primrec
        initReturnRowsFor_primrec))

theorem positionProgramDataForInput_primrec :
    Primrec (fun p : Nat × List SimStepData × List SourceSymbol =>
      positionProgramDataForInput p.1 p.2.1 p.2.2) := by
  unfold positionProgramDataForInput
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const foldedSymbolList)
      (Primrec.pair
        (foldedStateListForInput_primrec.comp
          (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)))
        (Primrec.pair (Primrec.const foldedBlank)
          (Primrec.pair (Primrec.const foldedStartState)
            (Primrec.list_append.comp
              (initRowsForInput_primrec.comp (Primrec.snd.comp Primrec.snd))
              (simRowsOfStepData_primrec.comp
                (Primrec.fst.comp Primrec.snd)))))))

theorem positionProgramDataForInput_primrec_fixed
    (stateCount : Nat) (steps : List SimStepData) :
    Primrec (positionProgramDataForInput stateCount steps) := by
  exact positionProgramDataForInput_primrec.comp
    (Primrec.pair (Primrec.const stateCount)
      (Primrec.pair (Primrec.const steps) Primrec.id))

theorem positionProgramDataForInput_computable_fixed
    (stateCount : Nat) (steps : List SimStepData) :
    Computable (positionProgramDataForInput stateCount steps) :=
  (positionProgramDataForInput_primrec_fixed stateCount steps).to_comp

end TM0FoldedCompiler

end LeanWang
