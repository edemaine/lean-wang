/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionOutcome

/-!
# Complete counter-controller instruction semantics

Compatibility aggregate for the instruction semantics, which are organized
by proof phase in the following modules:

* `CounterControlInstructionSearchSemantics` for bounded searches, shifts,
  preserving routes, and validation;
* `CounterControlIncrementInstructionSemantics` for ordinary increments;
* `CounterControlDecrementInstructionSemantics` for conditional decrements;
* `CounterControlInstructionOutcome` for cleanup, collision, and the uniform
  abstract-step interface.

All declarations remain in the namespace
`CounterControlInstructionSemantics`.
-/
