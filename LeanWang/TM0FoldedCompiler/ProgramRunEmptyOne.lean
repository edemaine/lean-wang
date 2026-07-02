/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramInitReturn

/-!
First empty-run state for the folded program.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem program_runEmpty_one (tc : Turing.ToPartrec.Code) :
    (program tc).runEmpty 1 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  rw [show 1 = 0 + 1 by rfl, PostProgram.runEmpty_succ, PostProgram.runEmpty_zero]
  change (program tc).nextID (program tc).initialID =
    { tape := Function.update (fun _ => foldedBlank) 0
        (foldedOriginSymbol (inputSymbol 0)),
      head := 0,
      state := some (initReturnState 0) }
  unfold PostProgram.nextID PostProgram.initialID
  rw [program_step_start_blank]
  ext x <;> simp only [PostProgram.applyStmt, nextAfterOrigin_eq_initReturnState_zero,
    Function.update, Nat.beq_eq]

end TM0FoldedCompiler

end LeanWang
