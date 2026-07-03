/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramFacts

/-!
Header-program start transition and step.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem programHeader_transition?_start_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).transition? foldedStartState foldedBlank =
      some initWriteOriginRow := by
  simp [PostProgram.transition?, initRows, initWriteOriginRow, foldedStartState]

theorem programHeader_step_start_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).step foldedStartState foldedBlank =
      some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
  have hfind := programHeader_transition?_start_blank tc
  have hnext : nextAfterOrigin ∈ foldedStateList tc :=
    nextAfterOrigin_mem_states tc
  have hwrite : foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedOriginSymbol_mem_symbols (inputSymbol 0)
  simp [PostProgram.step, hfind, initWriteOriginRow, mkRow, hnext, hwrite]

end TM0FoldedCompiler

end LeanWang
