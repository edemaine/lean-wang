/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Halting

/-!
# A fixed universal source program

The machine reduction does not need to compile an arbitrary partial-recursive
program.  It is enough to compile one universal evaluator and vary the data
given to that evaluator.

This file isolates that standard computability argument.  `universalCode` is a
single `Nat.Partrec.Code` evaluating a pair `(program code, input)`, and
`specializeUniversalCode c` is the primitive-recursive s-m-n specialization
which fixes the program component to `c`.  Consequently the halting problem is
already undecidable on this fixed-control family.
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

/-- One fixed source code implementing `universalEval`. -/
def universalCode : Code :=
  Classical.choose (Code.exists_code.1 universalEval_partrec)

theorem universalCode_correct :
    Code.eval universalCode = universalEval :=
  Classical.choose_spec (Code.exists_code.1 universalEval_partrec)

theorem universalCode_eval (c : Code) (n : Nat) :
    Code.eval universalCode (Nat.pair (encode c) n) = Code.eval c n := by
  rw [universalCode_correct]
  simp [universalEval]

/--
Specialize the fixed universal evaluator to a source code.  Only the constant
data in the s-m-n wrapper varies; the evaluator itself remains fixed.
-/
def specializeUniversalCode (c : Code) : Code :=
  Code.curry universalCode (encode c)

theorem specializeUniversalCode_primrec :
    Primrec specializeUniversalCode := by
  unfold specializeUniversalCode
  exact Code.primrec₂_curry.comp (Primrec.const universalCode) Primrec.encode

theorem specializeUniversalCode_computable :
    Computable specializeUniversalCode :=
  specializeUniversalCode_primrec.to_comp

theorem specializeUniversalCode_eval (c : Code) (n : Nat) :
    Code.eval (specializeUniversalCode c) n = Code.eval c n := by
  rw [specializeUniversalCode, Code.eval_curry, universalCode_eval]

theorem specializeUniversalCode_eval_dom (c : Code) (n : Nat) :
    (Code.eval (specializeUniversalCode c) n).Dom ↔ (Code.eval c n).Dom := by
  rw [specializeUniversalCode_eval]

/--
The halting problem remains undecidable after restricting programs to
specializations of one fixed universal evaluator.
-/
theorem specialized_halting_problem (n : Nat) :
    ¬ ComputablePred
      (fun c : Code => (Code.eval (specializeUniversalCode c) n).Dom) := by
  intro h
  apply ComputablePred.halting_problem n
  exact h.of_eq fun c => specializeUniversalCode_eval_dom c n

/-- Complemented form used by the Wang-tiling reduction. -/
theorem specialized_nonhalting_problem (n : Nat) :
    ¬ ComputablePred
      (fun c : Code => ¬ (Code.eval (specializeUniversalCode c) n).Dom) := by
  intro h
  exact specialized_halting_problem n
    ((h.not).of_eq fun _ => not_not)

end UniversalCode

end LeanWang
