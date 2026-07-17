/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Halting

/-!
# A universal partial function

The machine reduction compiles one universal partial function and varies only
its input.  Mathlib's Turing completeness theorem chooses the fixed machine
code later, directly in `LeanWang.Robinson.Machine.UniversalTM0.Semantic`.
-/

noncomputable section

namespace LeanWang

namespace UniversalCode

open Nat.Partrec
open Encodable Denumerable

/-- The universal unary partial function on an encoded `(program, input)` pair. -/
def universalEval : Nat →. Nat :=
  Nat.unpaired fun c n => Code.eval (ofNat Code c) n

theorem universalEval_partrec : Nat.Partrec universalEval := by
  exact Partrec₂.unpaired'.2
    (Code.eval_part.comp
      ((Computable.ofNat Code).comp Computable.fst) Computable.snd).to₂

end UniversalCode

end LeanWang
