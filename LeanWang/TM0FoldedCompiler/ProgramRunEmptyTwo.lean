/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramRunEmptyOne

/-!
Second empty-run state for the folded program.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem program_runEmpty_two (tc : Turing.ToPartrec.Code) :
    (program tc).runEmpty 2 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) } := by
  rw [show 2 = 1 + 1 by rfl, PostProgram.runEmpty_succ, program_runEmpty_one]
  have hread :
      foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols (inputSymbol 0)
  have hstep := program_step_initReturn_zero (tc := tc)
    (read := foldedOriginSymbol (inputSymbol 0)) hread
  simp [PostProgram.nextID, hstep, PostProgram.applyStmt]

end TM0FoldedCompiler

end TM0FoldedCompiler

end LeanWang
