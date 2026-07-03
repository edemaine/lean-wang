/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Theorems

/-!
Import wrapper for the folded finite-TM0 machine-side reduction.

The implementation lives in `LeanWang.TM0FoldedReduction.*` submodules so Lake
can cache and rebuild the source decoder, obligation, and theorem layers
separately while preserving this public import path.
-/
