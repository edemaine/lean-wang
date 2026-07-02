/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems

/-!
Semantic final packaging for the generated position-coded folded reduction.

This module is an import wrapper.  The source-obligation constructors and
theorem-facing wrappers live in `LeanWang.TM0FoldedPositionReduction.*`
submodules so Lake can cache and rebuild them separately while preserving the
old public import path.
-/
