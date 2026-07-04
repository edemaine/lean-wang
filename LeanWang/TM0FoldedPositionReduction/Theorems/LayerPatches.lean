/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.L2C1LayerPatches
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.L2C1PositiveBoxes
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.L2C2LayerPatches
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.L2C2PositiveBoxes

/-!
Layer-patch final theorem wrappers for the generated position-coded folded
reduction.

This module is an import wrapper; the L2C1/L2C2 layer-patch and positive-box
theorem families live in submodules so edits to one family do not force Lean to
recheck the full wrapper file.
-/
