/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramInitVacuous

/-!
Full-program return initialization transition and step lemmas.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem program_transition?_initReturn
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    (program tc).transition? (initReturnState i) read =
      some (initReturnRow tc i read) := by
  have hheader := programHeader_transition?_initReturn tc hi hread
  unfold PostProgram.transition? at hheader ⊢
  change (initRows tc).find?
      (fun e => e.matchesInput (initReturnState i) read) =
    some (initReturnRow tc i read) at hheader
  change (initRows tc ++ simRows tc).find?
      (fun e => e.matchesInput (initReturnState i) read) =
    some (initReturnRow tc i read)
  exact find?_append_of_eq_some hheader

theorem program_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (program tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have hfind := program_transition?_initReturn tc
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

theorem program_step_initReturn_succ
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i + 1 < TM0Route.partrecStartedTM0Input.length)
    (_hread : read ∈ foldedSymbolList) :
    (program tc).step (initReturnState (i + 1)) read =
      some (initReturnState i, PostStmt.move Move.left) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse

end TM0FoldedCompiler

end LeanWang
