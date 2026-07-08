/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.CorrectnessInvariants

/-!
Semantic correctness for the folded finite one-sided TM0 program.
This module is an import wrapper. The halting equivalence and invariant
projection lemmas live in smaller submodules so edits to later theorem surfaces
do not force rechecking the whole semantic correctness file.
-/
