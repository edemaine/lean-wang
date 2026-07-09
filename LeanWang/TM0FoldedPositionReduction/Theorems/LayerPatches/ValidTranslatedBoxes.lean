/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.ValidTranslatedBoxes.CheckedStacks
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.ValidTranslatedBoxes.CanonicalFreeSite

/-!
Valid-translated-box final theorem wrappers for the generated position-coded
folded reduction.

This module is an import wrapper. Checked-stack and canonical-free-site theorem
wrappers live in submodules so Lake can cache and rebuild those surfaces
independently while preserving the old public import path.
-/
