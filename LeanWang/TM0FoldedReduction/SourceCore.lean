/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourceCore.SearchCode

/-!
Source-specialized folded reduction core.

This module is an import wrapper. Shared source descriptor infrastructure
and the bounded-search decoder layer live in `LeanWang.TM0FoldedReduction.SourceCore.*`
submodules so Lake can cache and rebuild them separately.
-/
