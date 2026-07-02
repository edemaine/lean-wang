/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramHeaderMoveTransition

/-!
Header-program move-right step lemma.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem programHeader_step_initMoveRight
    (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (_hread : read ∈ foldedSymbolList) :
    (programHeader tc).step (initMoveRightState i) read =
      some (initWriteRightState i, PostStmt.move Move.right) := by
  have hfalse : False := by
    have hlen := partrecStartedTM0Input_length
    omega
  exact False.elim hfalse

end TM0FoldedCompiler

end LeanWang
