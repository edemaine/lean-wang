/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionCorrect.Halting

/-!
Semantic correctness of the generated position-coded folded program.

This module is an import wrapper.  The local simulation/reachability lemmas and
the final halting equivalences live in `LeanWang.TM0FoldedPositionCorrect.*`
submodules so Lake can cache and rebuild those layers separately.
-/
