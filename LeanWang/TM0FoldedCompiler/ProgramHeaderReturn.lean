/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramHeaderWrite

/-!
Header-program return initialization steps.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem programHeader_transition?_initReturn
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).transition? (initReturnState i) read =
      some (initReturnRow tc i read) := by
  have horigin :
      initWriteOriginRow.matchesInput (initReturnState i) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne (initWriteOriginState_ne_initReturnState i)
  have hmove := initMoveRightRows_find?_eq_none_of_initReturnState i read
  have hwrite := initWriteRightRows_find?_eq_none_of_initReturnState i read
  have hreturn := initReturnRows_find?_of_mem tc hi hread
  unfold PostProgram.transition?
  change (initRows tc).find?
      (fun e => e.matchesInput (initReturnState i) read) =
    some (initReturnRow tc i read)
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (initReturnState i) read) =
        some (initReturnRow tc i read) := by
    rw [show initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc =
        initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc) by
      rw [List.append_assoc]]
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

theorem programHeader_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (programHeader tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have hfind := programHeader_transition?_initReturn tc
    (i := 0) (read := read)
    (by
      unfold initReturnIndexList
      exact List.mem_cons_self)
    hread
  have hnext : foldedSimStartState tc ∈ foldedStateList tc :=
    foldedSimStartState_mem_states tc
  have hnextCode : foldedSimStartStateCode ∈ foldedStateList tc := by
    simpa [foldedSimStartState] using hnext
  simp [PostProgram.step, hfind, initReturnRow, mkRow, foldedSimStartState,
    hnextCode, hread]

theorem programHeader_step_initReturn_succ
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i + 1 < TM0Route.partrecStartedTM0Input.length)
    (_hread : read ∈ foldedSymbolList) :
    (programHeader tc).step (initReturnState (i + 1)) read =
      some (initReturnState i, PostStmt.move Move.left) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse


end TM0FoldedCompiler

end LeanWang
