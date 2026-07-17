/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.Partrec
import Mathlib.Data.PNat.Basic

/-!
# Primitive-recursive signed integer arithmetic

Mathlib's standard encoding of `Int` alternates nonnegative and negative
integers:

* `Int.ofNat n` has code `2 * n`;
* `Int.negSucc n` has code `2 * n + 1`.

This file records the primitive-recursive closure lemmas for the integer
operations needed by Kari's effective affine-transducer construction.  They
are proved against that standard encoding, rather than by installing a second
encoding of signed integers.
-/

namespace LeanWang
namespace Kari
namespace SignedPrimrec

/-- The nonnegative integer constructor is primitive recursive under
Mathlib's alternating encoding. -/
theorem intOfNat : Primrec Int.ofNat := by
  rw [← Primrec.encode_iff]
  exact Primrec.nat_double.of_eq fun _ => rfl

/-- The negative integer constructor is primitive recursive under Mathlib's
alternating encoding. -/
theorem intNegSucc : Primrec Int.negSucc := by
  rw [← Primrec.encode_iff]
  exact Primrec.nat_double_succ.of_eq fun _ => rfl

/-- Primitive recursion may split an integer produced by primitive-recursive
data into its two standard constructors. -/
theorem intCasesOn {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → Int} {g h : α → Nat → σ}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec fun a => match f a with
      | .ofNat n => g a n
      | .negSucc n => h a n := by
  let toSum : Int → Nat ⊕ Nat := Equiv.intEquivNatSumNat
  have htoSum : Primrec toSum := by
    rw [← Primrec.encode_iff]
    exact Primrec.encode.of_eq fun z => by cases z <;> rfl
  exact (Primrec.sumCasesOn (htoSum.comp hf) hg hh).of_eq fun a => by
    cases f a <;> rfl

/-- Lean's nontruncating subtraction of naturals is primitive recursive. -/
theorem intSubNatNat : Primrec₂ Int.subNatNat := by
  let h :=
    Primrec.nat_casesOn
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (intOfNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (intNegSucc.comp Primrec.snd).to₂
  exact h.to₂.of_eq fun m n => by
    simp only [Int.subNatNat]
    generalize hn : n - m = k
    cases k <;> simp

/-- Negation of a natural number, viewed as an integer, is primitive
recursive. -/
theorem intNegOfNat : Primrec Int.negOfNat := by
  exact (Primrec.nat_casesOn Primrec.id (Primrec.const 0)
    (intNegSucc.comp Primrec.snd).to₂).of_eq fun n => by
      cases n <;> rfl

/-- Integer negation is primitive recursive. -/
theorem intNeg : Primrec Int.neg := by
  exact (intCasesOn Primrec.id
    (intNegOfNat.comp Primrec.snd).to₂
    (intOfNat.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq fun z => by
      cases z <;> rfl

/-- Addition of a nonnegative integer to an arbitrary integer is primitive
recursive. -/
private theorem intOfNatAdd : Primrec₂ fun m z => Int.ofNat m + z := by
  let h :=
    intCasesOn Primrec.snd
      (intOfNat.comp (Primrec.nat_add.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (intSubNatNat.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp Primrec.snd)).to₂
  exact h.to₂.of_eq fun m z => by cases z <;> rfl

/-- Addition of a negative integer to an arbitrary integer is primitive
recursive. -/
private theorem intNegSuccAdd : Primrec₂ fun m z => Int.negSucc m + z := by
  let h :=
    intCasesOn Primrec.snd
      (intSubNatNat.comp Primrec.snd
        (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))).to₂
      (intNegSucc.comp (Primrec.succ.comp (Primrec.nat_add.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂
  exact h.to₂.of_eq fun m z => by cases z <;> rfl

/-- Integer addition is primitive recursive. -/
theorem intAdd : Primrec₂ ((· + ·) : Int → Int → Int) := by
  let h :=
    intCasesOn Primrec.fst
      (intOfNatAdd.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
      (intNegSuccAdd.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
  exact h.of_eq fun p => by cases p.1 <;> rfl

/-- Multiplication of a nonnegative integer by an arbitrary integer is
primitive recursive. -/
private theorem intOfNatMul : Primrec₂ fun m z => Int.ofNat m * z := by
  let h :=
    intCasesOn Primrec.snd
      (intOfNat.comp (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (intNegOfNat.comp (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp Primrec.snd))).to₂
  exact h.to₂.of_eq fun m z => by cases z <;> rfl

/-- Multiplication of a negative integer by an arbitrary integer is primitive
recursive. -/
private theorem intNegSuccMul : Primrec₂ fun m z => Int.negSucc m * z := by
  let h :=
    intCasesOn Primrec.snd
      (intNegOfNat.comp (Primrec.nat_mul.comp
        (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)).to₂
      (intOfNat.comp (Primrec.nat_mul.comp
        (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.succ.comp Primrec.snd))).to₂
  exact h.to₂.of_eq fun m z => by cases z <;> rfl

/-- Integer multiplication is primitive recursive. -/
theorem intMul : Primrec₂ ((· * ·) : Int → Int → Int) := by
  let h :=
    intCasesOn Primrec.fst
      (intOfNatMul.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
      (intNegSuccMul.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
  exact h.of_eq fun p => by cases p.1 <;> rfl

/-- Equality of integers is a primitive-recursive relation. -/
theorem intEq : PrimrecRel ((· = ·) : Int → Int → Prop) :=
  Primrec.eq

/-- The underlying natural number of a positive natural is primitive
recursive under Mathlib's predecessor encoding of `PNat`. -/
theorem pnatVal : Primrec PNat.val := by
  exact (Primrec.succ.comp Primrec.encode).of_eq fun n => by
    change n.natPred + 1 = n.val
    exact PNat.natPred_add_one n

end SignedPrimrec
end Kari
end LeanWang
