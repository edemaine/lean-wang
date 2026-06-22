/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Natural-number encoding for Mathlib's `Turing.ToPartrec.Code` syntax.

Mathlib gives `Nat.Partrec.Code` a `Denumerable` instance, but
`Turing.ToPartrec.Code` currently only has the syntax and evaluator. The
compiler/reduction interfaces in this project need `Computable` maps into this
type, so we provide the same kind of explicit tree encoding here.
-/

namespace Turing

namespace ToPartrec

namespace Code

/-- An encoding of `Turing.ToPartrec.Code` as a natural number. -/
def encodeCode : Code → Nat
  | zero' => 0
  | succ => 1
  | tail => 2
  | cons cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 3
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 3
  | case cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 3
  | fix cf => (2 * (2 * encodeCode cf + 1) + 1) + 3

/-- Decode a natural number into `Turing.ToPartrec.Code`. -/
def ofNatCode : Nat → Code
  | 0 => zero'
  | 1 => succ
  | 2 => tail
  | n + 3 =>
    let m := n.div2.div2
    have hm : m < n + 3 := by
      simp only [m, Nat.div2_val]
      exact lt_of_le_of_lt
        (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
        (by omega)
    have _m1 : m.unpair.1 < n + 3 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 3 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => cons (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => case (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => fix (ofNatCode m)

set_option backward.privateInPublic true in
/-- `ofNatCode` is a right inverse for `encodeCode`. -/
private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by
      simp [ofNatCode, encodeCode]
  | 1 => by
      simp [ofNatCode, encodeCode]
  | 2 => by
      simp [ofNatCode, encodeCode]
  | n + 3 => by
      let m := n.div2.div2
      have hm : m < n + 3 := by
        simp only [m, Nat.div2_val]
        exact lt_of_le_of_lt
          (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (by omega)
      have _m1 : m.unpair.1 < n + 3 := lt_of_le_of_lt m.unpair_left_le hm
      have _m2 : m.unpair.2 < n + 3 := lt_of_le_of_lt m.unpair_right_le hm
      have IH := encode_ofNatCode m
      have IH1 := encode_ofNatCode m.unpair.1
      have IH2 := encode_ofNatCode m.unpair.2
      conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
      simp only [ofNatCode.eq_4]
      cases n.bodd <;> cases n.div2.bodd <;>
        simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instDenumerable : Denumerable Code :=
  Denumerable.mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

theorem encodeCode_eq : Encodable.encode = encodeCode :=
  rfl

theorem ofNatCode_eq : Denumerable.ofNat Code = ofNatCode :=
  rfl

end Code

end ToPartrec

end Turing
