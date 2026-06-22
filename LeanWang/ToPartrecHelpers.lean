/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.ToPartrecEncoding
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Fixed helper programs for `Turing.ToPartrec.Code`.

`Nat.Partrec.Code` uses `Nat.pair` to encode multiple arguments in one natural
number, while `Turing.ToPartrec.Code` computes over lists of naturals. The
translation from unary partial-recursive codes to `ToPartrec` code therefore
needs small total programs that bridge these representations. This file records
those helper programs and their evaluator equations.
-/

noncomputable section

namespace Turing
namespace ToPartrec
namespace Code

/--
Choose a `ToPartrec` program for a primitive-recursive total vector function.

The choice is noncomputable, but the resulting code is a fixed finite syntax
tree. Later computability proofs can still use these fixed values as constants.
-/
def codeOfPrimrec {n : Nat} (f : List.Vector Nat n → Nat) (hf : Nat.Primrec' f) : Code :=
  Classical.choose (exists_code (Nat.Partrec'.prim hf))

theorem codeOfPrimrec_eval {n : Nat} (f : List.Vector Nat n → Nat)
    (hf : Nat.Primrec' f) (v : List.Vector Nat n) :
    (codeOfPrimrec f hf).eval v.1 = pure [f v] := by
  simpa [codeOfPrimrec] using
    Classical.choose_spec (exists_code (Nat.Partrec'.prim hf)) v

/-- Code computing `Nat.pair` from a two-element input list. -/
def pairNat : Code :=
  codeOfPrimrec (fun v : List.Vector Nat 2 => Nat.pair v.head v.tail.head)
    Nat.Primrec'.natPair

@[simp]
theorem pairNat_eval (a b : Nat) :
    pairNat.eval [a, b] = pure [Nat.pair a b] := by
  let v : List.Vector Nat 2 := ⟨[a, b], by simp⟩
  have hv_head : v.head = a := rfl
  have hv_tail_head : v.tail.head = b := rfl
  change pairNat.eval v.1 = pure [Nat.pair a b]
  simpa [pairNat, hv_head, hv_tail_head] using
    codeOfPrimrec_eval
      (fun v : List.Vector Nat 2 => Nat.pair v.head v.tail.head)
      Nat.Primrec'.natPair
      v

/-- Code computing the left component of `Nat.unpair` from a singleton input list. -/
def unpairLeft : Code :=
  codeOfPrimrec (fun v : List.Vector Nat 1 => v.head.unpair.1)
    (Nat.Primrec'.unpair₁ Nat.Primrec'.head)

@[simp]
theorem unpairLeft_eval (n : Nat) :
    unpairLeft.eval [n] = pure [n.unpair.1] := by
  let v : List.Vector Nat 1 := ⟨[n], by simp⟩
  have hv_head : v.head = n := rfl
  change unpairLeft.eval v.1 = pure [n.unpair.1]
  simpa [unpairLeft, hv_head] using
    codeOfPrimrec_eval
      (fun v : List.Vector Nat 1 => v.head.unpair.1)
      (Nat.Primrec'.unpair₁ Nat.Primrec'.head)
      v

/-- Code computing the right component of `Nat.unpair` from a singleton input list. -/
def unpairRight : Code :=
  codeOfPrimrec (fun v : List.Vector Nat 1 => v.head.unpair.2)
    (Nat.Primrec'.unpair₂ Nat.Primrec'.head)

@[simp]
theorem unpairRight_eval (n : Nat) :
    unpairRight.eval [n] = pure [n.unpair.2] := by
  let v : List.Vector Nat 1 := ⟨[n], by simp⟩
  have hv_head : v.head = n := rfl
  change unpairRight.eval v.1 = pure [n.unpair.2]
  simpa [unpairRight, hv_head] using
    codeOfPrimrec_eval
      (fun v : List.Vector Nat 1 => v.head.unpair.2)
      (Nat.Primrec'.unpair₂ Nat.Primrec'.head)
      v

/-- Code computing addition from a two-element input list. -/
def natAdd : Code :=
  codeOfPrimrec (fun v : List.Vector Nat 2 => v.head + v.tail.head)
    Nat.Primrec'.add

@[simp]
theorem natAdd_eval (a b : Nat) :
    natAdd.eval [a, b] = pure [a + b] := by
  let v : List.Vector Nat 2 := ⟨[a, b], by simp⟩
  have hv_head : v.head = a := rfl
  have hv_tail_head : v.tail.head = b := rfl
  change natAdd.eval v.1 = pure [a + b]
  simpa [natAdd, hv_head, hv_tail_head] using
    codeOfPrimrec_eval
      (fun v : List.Vector Nat 2 => v.head + v.tail.head)
      Nat.Primrec'.add
      v

end Code
end ToPartrec
end Turing
