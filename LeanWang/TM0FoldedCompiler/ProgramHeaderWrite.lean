/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramHeaderStartMove

/-!
Header-program write-right initialization steps.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem programHeader_transition?_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (programHeader tc).transition? (initWriteRightState i) foldedBlank =
      some (initWriteRightRow i) := by
  have horigin :
      initWriteOriginRow.matchesInput (initWriteRightState i) foldedBlank = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne (initWriteOriginState_ne_initWriteRightState i)
  have hmove := initMoveRightRows_find?_eq_none_of_initWriteRightState i foldedBlank
  have hwrite := initWriteRightRows_find?_of_mem hi
  unfold PostProgram.transition?
  change (initRows tc).find?
      (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
    some (initWriteRightRow i)
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
        some (initWriteRightRow i) := by
    rw [show initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc =
        initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc) by
      rw [List.append_assoc]]
    rw [find?_append_of_eq_none hmove]
    exact find?_append_of_eq_some (ys := initReturnRows tc) hwrite
  simpa [horigin] using htail

theorem programHeader_step_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (programHeader tc).step (initWriteRightState i) foldedBlank =
      some (nextAfterWriteRight i,
        PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1)))) := by
  have hfind := programHeader_transition?_initWriteRight tc hi
  have hnext : nextAfterWriteRight i ∈ foldedStateList tc :=
    nextAfterWriteRight_mem_states tc hi
  have hwrite : foldedSymbolCode false default (inputSymbol (i + 1)) ∈ foldedSymbolList :=
    initWriteRightRow_write_mem_symbols i
  simp [PostProgram.step, hfind, initWriteRightRow, mkRow, hnext, hwrite]

end TM0FoldedCompiler

end LeanWang
