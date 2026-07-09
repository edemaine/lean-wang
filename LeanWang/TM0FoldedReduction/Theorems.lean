/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Theorems.SourceProgramData
import LeanWang.TM0FoldedReduction.Theorems.SourceScaffold
import LeanWang.TM0FoldedReduction.Theorems.PositionScaffold
import LeanWang.TM0FoldedReduction.Theorems.Presented
import LeanWang.TM0FoldedReduction.Theorems.PositionCode
import LeanWang.TM0FoldedReduction.Theorems.InteriorRows

/-!
Machine-side theorem packaging for the folded finite-TM0 reduction.

This module is an import wrapper.  The source-route, position-route, presented
scaffold, and decoder-frontier theorem families live in
`LeanWang.TM0FoldedReduction.Theorems.*` submodules so Lake can cache and rebuild
them separately while preserving this public import path.
-/
