/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Obligations.Search
import LeanWang.TM0FoldedReduction.Obligations.Position

/-!
This module preserves the old public import path for the folded TM0 source
obligation constructors. The theorem-facing implementation lives in the
`LeanWang.TM0FoldedReduction.Obligations.*` submodules so Lake can cache the
search-code and position-code surfaces separately.
-/
