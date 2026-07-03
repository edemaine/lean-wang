/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.ProgramData

/-!
Executable finite one-sided TM0 program data for a folded simulation of Mathlib's TM0.

This module is an import wrapper. The implementation is split across
LeanWang.TM0FoldedProgram.* submodules so Lake can cache and rebuild the
source-machine setup, folded alphabet, initialization rows, simulation rows,
position-coded decoder, and final program data separately.
-/
