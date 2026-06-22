/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.ToPartrecHelpers

/-!
A syntactic translation from Mathlib's unary `Nat.Partrec.Code` language to
Mathlib's list-based `Turing.ToPartrec.Code` language.

The intended invariant is that `translate c` maps a singleton input `[n]` to a
singleton output `[x]` exactly when `Nat.Partrec.Code.eval c n = x`. This file
starts by making the translation itself explicit. The hard proof work is the
semantic correctness theorem for the recursive and minimization constructors.
-/

noncomputable section

namespace LeanWang

namespace NatPartrecToToPartrec

namespace TCode

open Turing.ToPartrec

/-- The constant-one singleton function. -/
def one : Code :=
  Code.succ.comp Code.zero

@[simp]
theorem one_eval (v : List Nat) :
    one.eval v = pure [1] := by
  simp [one]

/--
The body used to implement `Nat.Partrec.Code.rfind'`.

On state `[n, m, a]`, the body evaluates the translated predicate at
`[Nat.pair a (n + m)]`. If the predicate returns zero, `Code.fix` stops with
state `[n, m, a]`; otherwise the next state is `[n + 1, m, a]`.
-/
def rfindBody (test : Code) : Code :=
  let condition := test.comp Code.rfindTestArg
  let found := Code.zero'
  let nextState := Code.cons (Code.succ.comp Code.second) (Code.tail.comp Code.tail)
  let step := Code.cons one nextState
  (Code.case found step).comp (Code.cons condition Code.id)

theorem rfindBody_eval_zero {test : Code} {n m a : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [0]) :
    (rfindBody test).eval [n, m, a] = pure [0, n, m, a] := by
  simp [rfindBody, htest]

theorem rfindBody_eval_succ {test : Code} {n m a k : Nat}
    (htest : test.eval [Nat.pair a (n + m)] = pure [k.succ]) :
    (rfindBody test).eval [n, m, a] = pure [1, n.succ, m, a] := by
  simp [rfindBody, htest]

/--
Implementation of the `Nat.Partrec.Code.rfind'` constructor from a translated
predicate.

The input `[Nat.pair a m]` is first rearranged to `[m, a]`, then `0` is prepended
to start the search state `[0, m, a]`. The final state `[n, m, a]` is mapped to
the singleton `[n + m]`, matching the offset minimization semantics.
-/
def rfindFrom (test : Code) : Code :=
  Code.addFirstSecond.comp
    ((Code.fix (rfindBody test)).comp (Code.zero'.comp Code.unpairListSwap))

end TCode

open Turing.ToPartrec

/--
Translate unary `Nat.Partrec.Code` syntax to list-based `Turing.ToPartrec.Code`
syntax.
-/
def translate : Nat.Partrec.Code → Code
  | .zero => Code.zero
  | .succ => Code.succ
  | .left => Code.unpairLeft
  | .right => Code.unpairRight
  | .pair cf cg => Code.singletonPair (translate cf) (translate cg)
  | .comp cf cg => (translate cf).comp (translate cg)
  | .prec cf cg =>
      (Code.prec (translate cf) ((translate cg).comp Code.precStepArg)).comp
        Code.unpairListSwap
  | .rfind' cf => TCode.rfindFrom (translate cf)

@[simp]
theorem translate_zero : translate .zero = Code.zero :=
  rfl

@[simp]
theorem translate_succ : translate .succ = Code.succ :=
  rfl

@[simp]
theorem translate_left : translate .left = Code.unpairLeft :=
  rfl

@[simp]
theorem translate_right : translate .right = Code.unpairRight :=
  rfl

@[simp]
theorem translate_pair (cf cg : Nat.Partrec.Code) :
    translate (.pair cf cg) = Code.singletonPair (translate cf) (translate cg) :=
  rfl

@[simp]
theorem translate_comp (cf cg : Nat.Partrec.Code) :
    translate (.comp cf cg) = (translate cf).comp (translate cg) :=
  rfl

@[simp]
theorem translate_prec (cf cg : Nat.Partrec.Code) :
    translate (.prec cf cg) =
      (Code.prec (translate cf) ((translate cg).comp Code.precStepArg)).comp
        Code.unpairListSwap :=
  rfl

@[simp]
theorem translate_rfind' (cf : Nat.Partrec.Code) :
    translate (.rfind' cf) = TCode.rfindFrom (translate cf) :=
  rfl

end NatPartrecToToPartrec

end LeanWang
