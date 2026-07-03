/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.Scaffold
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches
import LeanWang.TM0FoldedPositionReduction.Theorems.PresentedFlexible
import LeanWang.TM0FoldedPositionReduction.Theorems.CheckedTranscription

/-!
Semantic final theorem wrappers for the generated position-coded folded
reduction.

This module is an import wrapper.  The theorem-facing wrappers live in
`LeanWang.TM0FoldedPositionReduction.Theorems.*` submodules so edits to one
surface do not require rechecking every final wrapper.
-/
