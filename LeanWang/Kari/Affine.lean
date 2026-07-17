/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Transducer
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-!
# Rational affine maps and transducer rows

Section 5.2 of Jeandel and Vanier, *The Undecidability of the Domino Problem*
(2020), implements multiplication of balanced representations by the local
carry equation `cᵢ + q aᵢ = bᵢ + cᵢ₊₁`.  This file records the same
telescoping algebra for a rational affine endomorphism of an arbitrary
`ℚ`-module.  It is independent of the later choice of digit and carry
encodings.
-/

namespace LeanWang
namespace Kari

open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- A rational affine endomorphism, represented by its linear part and offset. -/
structure RationalAffineMap (V : Type u) [AddCommGroup V] [Module ℚ V] where
  linear : Module.End ℚ V
  offset : V

namespace RationalAffineMap

/-- Evaluate a rational affine map. -/
def apply (f : RationalAffineMap V) (x : V) : V :=
  f.linear x + f.offset

instance : CoeFun (RationalAffineMap V) (fun _ => V → V) :=
  ⟨apply⟩

@[simp]
theorem apply_eq (f : RationalAffineMap V) (x : V) :
    f x = f.linear x + f.offset :=
  rfl

/-- Applying an affine map termwise separates into the linear image of the
sum and one copy of the offset per term. -/
theorem sum_apply_range (f : RationalAffineMap V) (input : Nat → V) (n : Nat) :
    ∑ i ∈ Finset.range n, f (input i) =
      f.linear (∑ i ∈ Finset.range n, input i) + (n : ℚ) • f.offset := by
  simp only [apply_eq, Finset.sum_add_distrib, map_sum, Finset.sum_const,
    Finset.card_range, ← Nat.cast_smul_eq_nsmul ℚ]

/-- Local carry equations telescope over an arbitrary finite segment. -/
theorem telescope (f : RationalAffineMap V)
    (input output carry : Nat → V) (n : Nat)
    (hlocal : ∀ i < n, carry i + f (input i) = output i + carry (i + 1)) :
    carry 0 +
        (f.linear (∑ i ∈ Finset.range n, input i) + (n : ℚ) • f.offset) =
      (∑ i ∈ Finset.range n, output i) + carry n := by
  rw [← f.sum_apply_range input n]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        carry 0 +
            ((∑ i ∈ Finset.range n, f (input i)) + f (input n)) =
            (carry 0 + ∑ i ∈ Finset.range n, f (input i)) + f (input n) := by
              abel
        _ = ((∑ i ∈ Finset.range n, output i) + carry n) + f (input n) := by
              rw [ih (fun i hi => hlocal i (Nat.lt_succ_of_lt hi))]
        _ = (∑ i ∈ Finset.range n, output i) +
            (carry n + f (input n)) := by
              abel
        _ = (∑ i ∈ Finset.range n, output i) +
            (output n + carry (n + 1)) := by
              rw [hlocal n (Nat.lt_succ_self n)]
        _ = ((∑ i ∈ Finset.range n, output i) + output n) +
            carry (n + 1) := by
              abel

end RationalAffineMap

namespace Transition

/-- A transition obeys the affine carry equation after digit and carry colors
are interpreted in the ambient module. -/
def SatisfiesAffine (t : Transition) (f : RationalAffineMap V)
    (digitValue carryValue : Nat → V) : Prop :=
  carryValue t.left + f (digitValue t.input) =
    digitValue t.output + carryValue t.right

end Transition

/-- The affine carry equations telescope along every finite segment of every
row in a transducer plane diagram. -/
theorem Transducer.IsPlaneDiagram.affine_telescope
    {M : Transducer} {digits carries : Int × Int → Nat}
    (hdiagram : M.IsPlaneDiagram digits carries)
    (f : RationalAffineMap V) (digitValue carryValue : Nat → V)
    (hsatisfies : ∀ t ∈ M, t.SatisfiesAffine f digitValue carryValue)
    (x y : Int) (n : Nat) :
    carryValue (carries (x, y)) +
        (f.linear
            (∑ i ∈ Finset.range n,
              digitValue (digits (x + (i : Int), y))) +
          (n : ℚ) • f.offset) =
      (∑ i ∈ Finset.range n,
          digitValue (digits (x + (i : Int), y + 1))) +
        carryValue (carries (x + (n : Int), y)) := by
  let input : Nat → V := fun i =>
    digitValue (digits (x + (i : Int), y))
  let output : Nat → V := fun i =>
    digitValue (digits (x + (i : Int), y + 1))
  let carry : Nat → V := fun i =>
    carryValue (carries (x + (i : Int), y))
  have hlocal : ∀ i < n,
      carry i + f (input i) = output i + carry (i + 1) := by
    intro i hi
    rcases hdiagram (x + (i : Int), y) with
      ⟨t, ht, hinput, houtput, hleft, hright⟩
    have h := hsatisfies t ht
    rw [Transition.SatisfiesAffine, hinput, houtput, hleft, hright] at h
    simpa [input, output, carry, Nat.cast_succ, Int.add_assoc] using h
  simpa [input, output, carry] using f.telescope input output carry n hlocal

end Kari
end LeanWang
