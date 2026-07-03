/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramInitStart

/-!
Vacuous full-program move/write initialization paths for the one-symbol input.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem program_transition?_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (_hread : read ∈ foldedSymbolList) :
    (program tc).transition? (initMoveRightState i) read =
      some (initMoveRightRow i read) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse

theorem program_step_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (_hread : read ∈ foldedSymbolList) :
    (program tc).step (initMoveRightState i) read =
      some (initWriteRightState i, PostStmt.move Move.right) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse

theorem program_transition?_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (program tc).transition? (initWriteRightState i) foldedBlank =
      some (initWriteRightRow i) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse

theorem program_step_initWriteRight
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    (program tc).step (initWriteRightState i) foldedBlank =
      some (nextAfterWriteRight i,
        PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1)))) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse

end TM0FoldedCompiler

end LeanWang
