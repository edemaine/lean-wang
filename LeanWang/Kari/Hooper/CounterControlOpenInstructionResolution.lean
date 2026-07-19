/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenDecrementResolution

/-!
# Resolving instructions on a target-free open counter core

Compatibility aggregate for the open-core instruction semantics:

* `CounterControlOpenIncrementResolution` proves validation and increment
  resolution without a finite outer target;
* `CounterControlOpenDecrementResolution` proves the positive and zero
  conditional-decrement branches and the uniform abstract-step laws.

The declarations retain their original namespace,
`CounterControlOpenInstructionResolution`.
-/
