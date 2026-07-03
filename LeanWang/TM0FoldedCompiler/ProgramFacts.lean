/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.SimRows

/-!
Basic field and support facts for the folded program and header program.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

@[simp]
theorem program_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).symbols = foldedSymbolList := rfl

@[simp]
theorem program_states (tc : Turing.ToPartrec.Code) :
    (program tc).states = foldedStateList tc := rfl

@[simp]
theorem program_blank (tc : Turing.ToPartrec.Code) :
    (program tc).blank = foldedBlank := rfl

@[simp]
theorem program_start (tc : Turing.ToPartrec.Code) :
    (program tc).start = foldedStartState := rfl

@[simp]
theorem program_table (tc : Turing.ToPartrec.Code) :
    (program tc).table = initRows tc ++ simRows tc := rfl

theorem program_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (program tc).blank ∈ (program tc).symbols := by
  simp [foldedBlank_mem_symbols]

theorem program_start_mem_states (tc : Turing.ToPartrec.Code) :
    (program tc).start ∈ (program tc).states := by
  simp [foldedStartState_mem_states tc]

/--
Initialization-only folded finite one-sided TM0 program header.

The full folded program above appends the simulation rows. This smaller header
is retained for the initialization transition lemmas.
-/
@[simp]
theorem programHeader_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).symbols = foldedSymbolList := rfl

@[simp]
theorem programHeader_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).states = foldedStateList tc := rfl

@[simp]
theorem programHeader_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank = foldedBlank := rfl

@[simp]
theorem programHeader_start (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start = foldedStartState := rfl

@[simp]
theorem programHeader_table (tc : Turing.ToPartrec.Code) :
    (programHeader tc).table = initRows tc := rfl

theorem programHeader_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank ∈ (programHeader tc).symbols := by
  simp [foldedBlank_mem_symbols]

theorem programHeader_start_mem_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start ∈ (programHeader tc).states := by
  simp [foldedStartState_mem_states tc]

end TM0FoldedCompiler

end LeanWang
