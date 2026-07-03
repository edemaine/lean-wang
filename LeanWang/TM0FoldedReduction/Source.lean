/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourceTargets

/-!
Import wrapper for the source-specialized folded reduction layer.

The implementation is split between `SourceCore` for the descriptor decoders and
`SourceTargets` for the public primitive-recursion theorem surface.  Keeping
this wrapper preserves the old import path while letting Lake cache the layers
separately.
-/
