/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.Correctness

/-!
Semantic correctness for the folded finite one-sided TM0 program.

This module is an import wrapper. The proof is split across
LeanWang.TM0FoldedCompiler.* submodules so Lake can cache and rebuild the
initialization, row-search, program-step, folded-tape, and final correctness
layers separately.
-/
