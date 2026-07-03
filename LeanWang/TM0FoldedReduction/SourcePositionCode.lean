/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourcePositionCode.Decoder

/-!
Import wrapper for the source-specialized generated position-code descriptor
decoder.

The implementation is split between `SourcePositionCode.OneRows` for one-row
and interior-row data and `SourcePositionCode.Decoder` for the accumulator and
iterated decoder. Keeping this wrapper preserves the old import path.
-/
