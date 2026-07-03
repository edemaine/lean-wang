/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramHeaderSteps

/-!
Full-program start transition and first step.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem program_transition?_start_blank (tc : Turing.ToPartrec.Code) :
    (program tc).transition? foldedStartState foldedBlank =
      some initWriteOriginRow := by
  have hheader := programHeader_transition?_start_blank tc
  unfold PostProgram.transition? at hheader ⊢
  change (initRows tc).find? (fun e => e.matchesInput foldedStartState foldedBlank) =
    some initWriteOriginRow at hheader
  change (initRows tc ++ simRows tc).find?
      (fun e => e.matchesInput foldedStartState foldedBlank) =
    some initWriteOriginRow
  exact find?_append_of_eq_some hheader

theorem program_step_start_blank (tc : Turing.ToPartrec.Code) :
    (program tc).step foldedStartState foldedBlank =
      some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
  have hfind := program_transition?_start_blank tc
  have hnext : nextAfterOrigin ∈ foldedStateList tc :=
    nextAfterOrigin_mem_states tc
  have hwrite : foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols (inputSymbol 0)
  simp [PostProgram.step, hfind, initWriteOriginRow, mkRow, hnext, hwrite]

end TM0FoldedCompiler

end LeanWang
