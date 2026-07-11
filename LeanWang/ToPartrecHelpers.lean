/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
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

/-- Combine two singleton-valued codes into a two-element list. -/
def listPair (f g : Code) : Code :=
  cons f (cons g nil)

theorem listPair_eval {f g : Code} {v : List Nat} {a b : Nat}
    (hf : f.eval v = pure [a]) (hg : g.eval v = pure [b]) :
    (listPair f g).eval v = pure [a, b] := by
  simp [listPair, hf, hg]

/-- Pair the singleton outputs of two codes using `Nat.pair`. -/
def singletonPair (f g : Code) : Code :=
  pairNat.comp (listPair f g)

theorem singletonPair_eval {f g : Code} {v : List Nat} {a b : Nat}
    (hf : f.eval v = pure [a]) (hg : g.eval v = pure [b]) :
    (singletonPair f g).eval v = pure [Nat.pair a b] := by
  simp [singletonPair, listPair_eval hf hg]

/-- Convert a singleton encoded pair `[Nat.pair a b]` to the list `[b, a]`. -/
def unpairListSwap : Code :=
  listPair unpairRight unpairLeft

@[simp]
theorem unpairListSwap_eval (a b : Nat) :
    unpairListSwap.eval [Nat.pair a b] = pure [b, a] := by
  simp [unpairListSwap, listPair_eval]

/-- Get the second element of the input list as a singleton, defaulting as Mathlib does. -/
def second : Code :=
  head.comp tail

@[simp]
theorem second_eval (a b : Nat) (v : List Nat) :
    second.eval (a :: b :: v) = pure [b] := by
  simp [second]

/-- Get the third element of the input list as a singleton, defaulting as Mathlib does. -/
def third : Code :=
  head.comp (tail.comp tail)

@[simp]
theorem third_eval (a b c : Nat) (v : List Nat) :
    third.eval (a :: b :: c :: v) = pure [c] := by
  simp [third]

/--
Build the argument expected by the step function in `Nat.Partrec.Code.prec`.

On input `[y, ih, a]`, this returns `[Nat.pair a (Nat.pair y ih)]`.
-/
def precStepArg : Code :=
  singletonPair third (singletonPair head second)

@[simp]
theorem precStepArg_eval (y ih a : Nat) :
    precStepArg.eval [y, ih, a] = pure [Nat.pair a (Nat.pair y ih)] := by
  simp [precStepArg, singletonPair_eval]

/-- Add the first two entries of the input list and return the singleton result. -/
def addFirstSecond : Code :=
  natAdd.comp (listPair head second)

@[simp]
theorem addFirstSecond_eval (a b : Nat) (v : List Nat) :
    addFirstSecond.eval (a :: b :: v) = pure [a + b] := by
  simp [addFirstSecond, listPair_eval]

/--
Build the test argument for the `Nat.Partrec.Code.rfind'` body.

On input `[n, m, a]`, this returns `[Nat.pair a (n + m)]`.
-/
def rfindTestArg : Code :=
  singletonPair third addFirstSecond

@[simp]
theorem rfindTestArg_eval (n m a : Nat) :
    rfindTestArg.eval [n, m, a] = pure [Nat.pair a (n + m)] := by
  simp [rfindTestArg, singletonPair_eval]

end Code
end ToPartrec
end Turing
