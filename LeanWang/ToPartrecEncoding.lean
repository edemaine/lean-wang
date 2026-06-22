/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PartrecToTM2Support
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Natural-number encoding for Mathlib's `Turing.ToPartrec.Code` syntax.

Mathlib gives `Nat.Partrec.Code` a `Denumerable` instance, but
`Turing.ToPartrec.Code` currently only has the syntax and evaluator. The
reduction interfaces in this project need `Computable` maps into this type, so
we provide the same kind of explicit tree encoding here.
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

theorem ofNatCode_encodeCode (c : Code) : ofNatCode (encodeCode c) = c := by
  simpa [encodeCode_eq, ofNatCode_eq] using Denumerable.ofNat_encode c

open Primrec

theorem primrec₂_cons : Primrec₂ Code.cons :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 3)

theorem primrec₂_comp : Primrec₂ Code.comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 3)

theorem primrec₂_case : Primrec₂ Code.case :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 3)

theorem primrec_fix : Primrec Code.fix :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          encode_iff.2 <| Primrec.ofNat Code)
        (const 3)

end Code

end ToPartrec

namespace PartrecToTM2

/-- Finite Boolean predicates on the stack alphabet, encoded by their four values. -/
def stackPredicateEquivTuple : (Γ' → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun f := (f Γ'.consₗ, f Γ'.cons, f Γ'.bit0, f Γ'.bit1)
  invFun t
    | Γ'.consₗ => t.1
    | Γ'.cons => t.2.1
    | Γ'.bit0 => t.2.2.1
    | Γ'.bit1 => t.2.2.2
  left_inv := by
    intro f
    funext a
    cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d⟩
    rfl

instance instPrimcodableStackPredicate : Primcodable (Γ' → Bool) :=
  Primcodable.ofEquiv (Bool × Bool × Bool × Bool) stackPredicateEquivTuple

/--
Finite local-store actions used by `Λ'.push`, encoded by their five values on
`none` and the four stack symbols.
-/
def localActionEquivTuple :
    (Option Γ' → Option Γ') ≃
      Option Γ' × Option Γ' × Option Γ' × Option Γ' × Option Γ' where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance instPrimcodableLocalAction : Primcodable (Option Γ' → Option Γ') :=
  Primcodable.ofEquiv
    (Option Γ' × Option Γ' × Option Γ' × Option Γ' × Option Γ')
    localActionEquivTuple

/-- Dense numeric code for the four `PartrecToTM2` stack names. -/
def stackNameCode : K' → Nat
  | K'.main => 0
  | K'.rev => 1
  | K'.aux => 2
  | K'.stack => 3

/-- Decode a natural number modulo four into a `PartrecToTM2` stack name. -/
def stackNameOfCode (n : Nat) : K' :=
  match n % 4 with
  | 0 => K'.main
  | 1 => K'.rev
  | 2 => K'.aux
  | _ => K'.stack

theorem stackNameCode_lt_four (k : K') : stackNameCode k < 4 := by
  cases k <;> decide

theorem stackNameCode_ofCode (n : Nat) : stackNameCode (stackNameOfCode n) = n % 4 := by
  unfold stackNameOfCode
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
  generalize h : n % 4 = r at hlt ⊢
  rcases r with _ | r
  · simp [stackNameCode]
  rcases r with _ | r
  · simp [stackNameCode]
  rcases r with _ | r
  · simp [stackNameCode]
  rcases r with _ | r
  · simp [stackNameCode]
  · omega

theorem stackNameOfCode_stackNameCode (k : K') : stackNameOfCode (stackNameCode k) = k := by
  cases k <;> rfl

/-- Partial decoder for dense stack-name codes. -/
def decodeStackNameCode : Nat → Option K'
  | 0 => some K'.main
  | 1 => some K'.rev
  | 2 => some K'.aux
  | 3 => some K'.stack
  | _ => none

theorem decodeStackNameCode_stackNameCode (k : K') :
    decodeStackNameCode (stackNameCode k) = some k := by
  cases k <;> rfl

/-- Dense numeric code for `Option Γ'`, using zero for blank and one through four for symbols. -/
def optionStackSymbolCode : Option Γ' → Nat
  | none => 0
  | some Γ'.consₗ => 1
  | some Γ'.cons => 2
  | some Γ'.bit0 => 3
  | some Γ'.bit1 => 4

/-- Decode a natural number modulo five into an optional stack symbol. -/
def optionStackSymbolOfCode (n : Nat) : Option Γ' :=
  match n % 5 with
  | 0 => none
  | 1 => some Γ'.consₗ
  | 2 => some Γ'.cons
  | 3 => some Γ'.bit0
  | _ => some Γ'.bit1

theorem optionStackSymbolCode_lt_five (s : Option Γ') :
    optionStackSymbolCode s < 5 := by
  cases s with
  | none => decide
  | some a => cases a <;> decide

theorem optionStackSymbolCode_ofCode (n : Nat) :
    optionStackSymbolCode (optionStackSymbolOfCode n) = n % 5 := by
  unfold optionStackSymbolOfCode
  have hlt : n % 5 < 5 := Nat.mod_lt n (by decide)
  generalize h : n % 5 = r at hlt ⊢
  rcases r with _ | r
  · simp [optionStackSymbolCode]
  rcases r with _ | r
  · simp [optionStackSymbolCode]
  rcases r with _ | r
  · simp [optionStackSymbolCode]
  rcases r with _ | r
  · simp [optionStackSymbolCode]
  rcases r with _ | r
  · simp [optionStackSymbolCode]
  · omega

theorem optionStackSymbolOfCode_optionStackSymbolCode (s : Option Γ') :
    optionStackSymbolOfCode (optionStackSymbolCode s) = s := by
  cases s with
  | none => rfl
  | some a => cases a <;> rfl

theorem optionStackSymbolOfCode_eq_of_mod {n : Nat} {s : Option Γ'}
    (h : n % 5 = optionStackSymbolCode s) :
    optionStackSymbolOfCode n = s := by
  cases s with
  | none =>
      unfold optionStackSymbolOfCode
      simp [h, optionStackSymbolCode]
  | some a =>
      cases a <;> unfold optionStackSymbolOfCode <;>
        simp [h, optionStackSymbolCode]

/-- Dense numeric code for booleans, used as binary digits in finite fields. -/
def boolCode : Bool → Nat
  | false => 0
  | true => 1

/-- Decode a natural number modulo two as a boolean. -/
def boolOfCode (n : Nat) : Bool :=
  n % 2 = 1

theorem boolCode_lt_two (b : Bool) : boolCode b < 2 := by
  cases b <;> decide

theorem boolCode_ofCode (n : Nat) : boolCode (boolOfCode n) = n % 2 := by
  unfold boolOfCode
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  generalize h : n % 2 = r at hlt ⊢
  rcases r with _ | r
  · simp [boolCode]
  rcases r with _ | r
  · simp [boolCode]
  · omega

theorem boolOfCode_boolCode (b : Bool) : boolOfCode (boolCode b) = b := by
  cases b <;> rfl

/-- Dense numeric code for Boolean predicates on the four stack symbols. -/
def stackPredicateCode (p : Γ' → Bool) : Nat :=
  boolCode (p Γ'.consₗ) + 2 * (boolCode (p Γ'.cons) +
    2 * (boolCode (p Γ'.bit0) + 2 * boolCode (p Γ'.bit1)))

/-- Decode a natural number modulo sixteen into a Boolean predicate on stack symbols. -/
def stackPredicateOfCode (n : Nat) : Γ' → Bool
  | Γ'.consₗ => boolOfCode n
  | Γ'.cons => boolOfCode (n / 2)
  | Γ'.bit0 => boolOfCode (n / 4)
  | Γ'.bit1 => boolOfCode (n / 8)

theorem stackPredicateCode_lt_sixteen (p : Γ' → Bool) :
    stackPredicateCode p < 16 := by
  cases h₀ : p Γ'.consₗ <;> cases h₁ : p Γ'.cons <;>
    cases h₂ : p Γ'.bit0 <;> cases h₃ : p Γ'.bit1 <;>
    simp [stackPredicateCode, boolCode, h₀, h₁, h₂, h₃]

theorem stackPredicateCode_ofCode (n : Nat) :
    stackPredicateCode (stackPredicateOfCode n) = n % 16 := by
  unfold stackPredicateCode stackPredicateOfCode
  simp [boolCode_ofCode]
  omega

theorem stackPredicateOfCode_stackPredicateCode (p : Γ' → Bool) :
    stackPredicateOfCode (stackPredicateCode p) = p := by
  funext a
  cases a <;> cases h₀ : p Γ'.consₗ <;> cases h₁ : p Γ'.cons <;>
    cases h₂ : p Γ'.bit0 <;> cases h₃ : p Γ'.bit1 <;>
    simp [stackPredicateOfCode, stackPredicateCode, boolOfCode, boolCode, h₀, h₁, h₂, h₃]

/-- Partial decoder for dense stack-predicate codes. -/
def decodeStackPredicateCode (n : Nat) : Option (Γ' → Bool) :=
  if n < 16 then some (stackPredicateOfCode n) else none

theorem decodeStackPredicateCode_stackPredicateCode (p : Γ' → Bool) :
    decodeStackPredicateCode (stackPredicateCode p) = some p := by
  simp [decodeStackPredicateCode, stackPredicateCode_lt_sixteen,
    stackPredicateOfCode_stackPredicateCode]

/-- Dense numeric code for local-store actions used by `Λ'.push`. -/
def localActionCode (f : Option Γ' → Option Γ') : Nat :=
  optionStackSymbolCode (f none) + 5 * (optionStackSymbolCode (f (some Γ'.consₗ)) +
    5 * (optionStackSymbolCode (f (some Γ'.cons)) +
      5 * (optionStackSymbolCode (f (some Γ'.bit0)) +
        5 * optionStackSymbolCode (f (some Γ'.bit1)))))

/-- Decode a natural number modulo `5^5` into a local-store action. -/
def localActionOfCode (n : Nat) : Option Γ' → Option Γ'
  | none => optionStackSymbolOfCode n
  | some Γ'.consₗ => optionStackSymbolOfCode (n / 5)
  | some Γ'.cons => optionStackSymbolOfCode (n / 25)
  | some Γ'.bit0 => optionStackSymbolOfCode (n / 125)
  | some Γ'.bit1 => optionStackSymbolOfCode (n / 625)

theorem localActionCode_lt (f : Option Γ' → Option Γ') :
    localActionCode f < 3125 := by
  unfold localActionCode
  have h₀ := optionStackSymbolCode_lt_five (f none)
  have h₁ := optionStackSymbolCode_lt_five (f (some Γ'.consₗ))
  have h₂ := optionStackSymbolCode_lt_five (f (some Γ'.cons))
  have h₃ := optionStackSymbolCode_lt_five (f (some Γ'.bit0))
  have h₄ := optionStackSymbolCode_lt_five (f (some Γ'.bit1))
  omega

theorem localActionCode_ofCode (n : Nat) :
    localActionCode (localActionOfCode n) = n % 3125 := by
  unfold localActionCode localActionOfCode
  simp [optionStackSymbolCode_ofCode]
  omega

theorem localActionOfCode_localActionCode (f : Option Γ' → Option Γ') :
    localActionOfCode (localActionCode f) = f := by
  funext s
  have h₀ := optionStackSymbolCode_lt_five (f none)
  have h₁ := optionStackSymbolCode_lt_five (f (some Γ'.consₗ))
  have h₂ := optionStackSymbolCode_lt_five (f (some Γ'.cons))
  have h₃ := optionStackSymbolCode_lt_five (f (some Γ'.bit0))
  have h₄ := optionStackSymbolCode_lt_five (f (some Γ'.bit1))
  cases s with
  | none =>
      apply optionStackSymbolOfCode_eq_of_mod
      unfold localActionCode
      omega
  | some a =>
      cases a
      · apply optionStackSymbolOfCode_eq_of_mod
        unfold localActionCode
        omega
      · apply optionStackSymbolOfCode_eq_of_mod
        unfold localActionCode
        omega
      · apply optionStackSymbolOfCode_eq_of_mod
        unfold localActionCode
        omega
      · apply optionStackSymbolOfCode_eq_of_mod
        unfold localActionCode
        omega

/-- Partial decoder for dense local-store action codes. -/
def decodeLocalActionCode (n : Nat) : Option (Option Γ' → Option Γ') :=
  if n < 3125 then some (localActionOfCode n) else none

theorem decodeLocalActionCode_localActionCode (f : Option Γ' → Option Γ') :
    decodeLocalActionCode (localActionCode f) = some f := by
  simp [decodeLocalActionCode, localActionCode_lt, localActionOfCode_localActionCode]

namespace Λ'

/--
Finite branch tables for `Λ'.read`, encoded by their five target labels on
`none` and the four stack symbols.
-/
def readBranchEquivTuple :
    (Option Γ' → Λ') ≃ Λ' × Λ' × Λ' × Λ' × Λ' where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

end Λ'

namespace Cont'

/-- An encoding of `Turing.PartrecToTM2.Cont'` as a natural number. -/
def encodeCont : Cont' → Nat
  | halt => 0
  | cons₁ c k =>
      Nat.bit false (Nat.bit false (Nat.pair (ToPartrec.Code.encodeCode c) (encodeCont k))) + 1
  | cons₂ k => Nat.bit true (Nat.bit false (encodeCont k)) + 1
  | comp c k =>
      Nat.bit false (Nat.bit true (Nat.pair (ToPartrec.Code.encodeCode c) (encodeCont k))) + 1
  | fix c k =>
      Nat.bit true (Nat.bit true (Nat.pair (ToPartrec.Code.encodeCode c) (encodeCont k))) + 1

/-- Decode a natural number into `Turing.PartrecToTM2.Cont'`. -/
def ofNatCont : Nat → Cont'
  | 0 => halt
  | n + 1 =>
    let m := n.div2.div2
    have hm : m < n + 1 := by
      simp only [m, Nat.div2_val]
      exact lt_of_le_of_lt
        (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
        (Nat.lt_succ_self _)
    have hm1 : m.unpair.1 < n + 1 := lt_of_le_of_lt m.unpair_left_le hm
    have hm2 : m.unpair.2 < n + 1 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => cons₁ (ToPartrec.Code.ofNatCode m.unpair.1) (ofNatCont m.unpair.2)
    | true, false => cons₂ (ofNatCont m)
    | false, true => comp (ToPartrec.Code.ofNatCode m.unpair.1) (ofNatCont m.unpair.2)
    | true, true => fix (ToPartrec.Code.ofNatCode m.unpair.1) (ofNatCont m.unpair.2)

set_option backward.privateInPublic true in
/-- `ofNatCont` is a right inverse for `encodeCont`. -/
private theorem encode_ofNatCont : ∀ n, encodeCont (ofNatCont n) = n
  | 0 => by
      simp [ofNatCont, encodeCont]
  | n + 1 => by
      let m := n.div2.div2
      have hm : m < n + 1 := by
        simp only [m, Nat.div2_val]
        exact lt_of_le_of_lt
          (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.lt_succ_self _)
      have hm1 : m.unpair.1 < n + 1 := lt_of_le_of_lt m.unpair_left_le hm
      have hm2 : m.unpair.2 < n + 1 := lt_of_le_of_lt m.unpair_right_le hm
      have IH := encode_ofNatCont m
      have IH2 := encode_ofNatCont m.unpair.2
      conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
      simp only [ofNatCont.eq_2]
      cases n.bodd <;> cases n.div2.bodd <;>
        simp [m, encodeCont, IH, IH2, ToPartrec.Code.encode_ofNatCode,
          Nat.bit_val]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instDenumerable : Denumerable Cont' :=
  Denumerable.mk'
    ⟨encodeCont, ofNatCont, fun k => by
        induction k with
        | halt =>
            simp [encodeCont, ofNatCont]
        | cons₁ c k ih =>
            simp [encodeCont, ofNatCont, ih, ToPartrec.Code.ofNatCode_encodeCode,
              Nat.div2_val, Nat.bit_val]
        | cons₂ k ih =>
            simp [encodeCont, ofNatCont, ih, Nat.div2_val, Nat.bit_val]
        | comp c k ih =>
            simp [encodeCont, ofNatCont, ih, ToPartrec.Code.ofNatCode_encodeCode,
              Nat.div2_val, Nat.bit_val]
        | fix c k ih =>
            simp [encodeCont, ofNatCont, ih, ToPartrec.Code.ofNatCode_encodeCode,
              Nat.div2_val, Nat.bit_val],
      encode_ofNatCont⟩

theorem encodeCont_eq : Encodable.encode = encodeCont :=
  rfl

theorem ofNatCont_eq : Denumerable.ofNat Cont' = ofNatCont :=
  rfl

open Primrec

theorem primrec₂_cons₁ : Primrec₂ Cont'.cons₁ :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_double_succ.comp <|
        nat_double.comp <|
          Primrec₂.natPair.comp
            (encode_iff.2 <| (Primrec.ofNat ToPartrec.Code).comp fst)
            (encode_iff.2 <| (Primrec.ofNat Cont').comp snd)

theorem primrec_cons₂ : Primrec Cont'.cons₂ :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      succ.comp <| nat_double_succ.comp <| nat_double.comp <|
        encode_iff.2 <| Primrec.ofNat Cont'

theorem primrec₂_comp : Primrec₂ Cont'.comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_double_succ.comp <|
        nat_double_succ.comp <|
          Primrec₂.natPair.comp
            (encode_iff.2 <| (Primrec.ofNat ToPartrec.Code).comp fst)
            (encode_iff.2 <| (Primrec.ofNat Cont').comp snd)

theorem primrec₂_fix : Primrec₂ Cont'.fix :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      succ.comp <| nat_double_succ.comp <|
        nat_double_succ.comp <|
          Primrec₂.natPair.comp
            (encode_iff.2 <| (Primrec.ofNat ToPartrec.Code).comp fst)
            (encode_iff.2 <| (Primrec.ofNat Cont').comp snd)

end Cont'

namespace Λ'

/-- Encode the eight `PartrecToTM2` label constructors by a tag and a payload. -/
def encodeLabel : Λ' → Nat
  | move p k₁ k₂ q =>
      8 * (Nat.pair (stackPredicateCode p)
        (Nat.pair (stackNameCode k₁) (Nat.pair (stackNameCode k₂) (encodeLabel q)))) + 1
  | clear p k q =>
      8 * (Nat.pair (stackPredicateCode p)
        (Nat.pair (stackNameCode k) (encodeLabel q))) + 2
  | copy q => 8 * encodeLabel q + 3
  | push k f q =>
      8 * (Nat.pair (stackNameCode k) (Nat.pair (localActionCode f) (encodeLabel q))) + 4
  | read f =>
      8 * (Nat.pair (encodeLabel (f none))
        (Nat.pair (encodeLabel (f (some Γ'.consₗ)))
          (Nat.pair (encodeLabel (f (some Γ'.cons)))
            (Nat.pair (encodeLabel (f (some Γ'.bit0))) (encodeLabel (f (some Γ'.bit1))))))) + 5
  | succ q => 8 * encodeLabel q + 6
  | pred q₁ q₂ => 8 * Nat.pair (encodeLabel q₁) (encodeLabel q₂) + 7
  | ret k => 8 * Cont'.encodeCont k + 8

/-- Payload code for `Λ'.move`, keeping the recursive target as an already encoded label. -/
def movePayloadCode (p : Γ' → Bool) (k₁ k₂ : K') (qCode : Nat) : Nat :=
  Nat.pair (stackPredicateCode p)
    (Nat.pair (stackNameCode k₁) (Nat.pair (stackNameCode k₂) qCode))

/-- Decode the nonrecursive fields of a `Λ'.move` payload. -/
def decodeMovePayload (m : Nat) : Option ((Γ' → Bool) × K' × K' × Nat) :=
  match decodeStackPredicateCode m.unpair.1,
      decodeStackNameCode m.unpair.2.unpair.1,
      decodeStackNameCode m.unpair.2.unpair.2.unpair.1 with
  | some p, some k₁, some k₂ => some (p, k₁, k₂, m.unpair.2.unpair.2.unpair.2)
  | _, _, _ => none

theorem decodeMovePayload_movePayloadCode
    (p : Γ' → Bool) (k₁ k₂ : K') (qCode : Nat) :
    decodeMovePayload (movePayloadCode p k₁ k₂ qCode) = some (p, k₁, k₂, qCode) := by
  simp [decodeMovePayload, movePayloadCode, decodeStackPredicateCode_stackPredicateCode,
    decodeStackNameCode_stackNameCode]

/-- Payload code for `Λ'.clear`, keeping the recursive target as an already encoded label. -/
def clearPayloadCode (p : Γ' → Bool) (k : K') (qCode : Nat) : Nat :=
  Nat.pair (stackPredicateCode p) (Nat.pair (stackNameCode k) qCode)

/-- Decode the nonrecursive fields of a `Λ'.clear` payload. -/
def decodeClearPayload (m : Nat) : Option ((Γ' → Bool) × K' × Nat) :=
  match decodeStackPredicateCode m.unpair.1, decodeStackNameCode m.unpair.2.unpair.1 with
  | some p, some k => some (p, k, m.unpair.2.unpair.2)
  | _, _ => none

theorem decodeClearPayload_clearPayloadCode
    (p : Γ' → Bool) (k : K') (qCode : Nat) :
    decodeClearPayload (clearPayloadCode p k qCode) = some (p, k, qCode) := by
  simp [decodeClearPayload, clearPayloadCode, decodeStackPredicateCode_stackPredicateCode,
    decodeStackNameCode_stackNameCode]

/-- Payload code for `Λ'.push`, keeping the recursive target as an already encoded label. -/
def pushPayloadCode (k : K') (f : Option Γ' → Option Γ') (qCode : Nat) : Nat :=
  Nat.pair (stackNameCode k) (Nat.pair (localActionCode f) qCode)

/-- Decode the nonrecursive fields of a `Λ'.push` payload. -/
def decodePushPayload (m : Nat) : Option (K' × (Option Γ' → Option Γ') × Nat) :=
  match decodeStackNameCode m.unpair.1, decodeLocalActionCode m.unpair.2.unpair.1 with
  | some k, some f => some (k, f, m.unpair.2.unpair.2)
  | _, _ => none

theorem decodePushPayload_pushPayloadCode
    (k : K') (f : Option Γ' → Option Γ') (qCode : Nat) :
    decodePushPayload (pushPayloadCode k f qCode) = some (k, f, qCode) := by
  simp [decodePushPayload, pushPayloadCode, decodeStackNameCode_stackNameCode,
    decodeLocalActionCode_localActionCode]

/-- Payload code for `Λ'.read`, storing the five branch labels as encoded labels. -/
def readPayloadCode (q₀ q₁ q₂ q₃ q₄ : Nat) : Nat :=
  Nat.pair q₀ (Nat.pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄)))

/-- Decode a `Λ'.read` payload into the five encoded branch labels. -/
def decodeReadPayload (m : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (m.unpair.1, m.unpair.2.unpair.1, m.unpair.2.unpair.2.unpair.1,
    m.unpair.2.unpair.2.unpair.2.unpair.1, m.unpair.2.unpair.2.unpair.2.unpair.2)

theorem decodeReadPayload_readPayloadCode (q₀ q₁ q₂ q₃ q₄ : Nat) :
    decodeReadPayload (readPayloadCode q₀ q₁ q₂ q₃ q₄) = (q₀, q₁, q₂, q₃, q₄) := by
  simp [decodeReadPayload, readPayloadCode]

/-- Payload code for `Λ'.pred`, storing the two branch labels as encoded labels. -/
def predPayloadCode (q₁ q₂ : Nat) : Nat :=
  Nat.pair q₁ q₂

/-- Decode a `Λ'.pred` payload into the two encoded branch labels. -/
def decodePredPayload (m : Nat) : Nat × Nat :=
  (m.unpair.1, m.unpair.2)

theorem decodePredPayload_predPayloadCode (q₁ q₂ : Nat) :
    decodePredPayload (predPayloadCode q₁ q₂) = (q₁, q₂) := by
  simp [decodePredPayload, predPayloadCode]

theorem ofNatCont_encodeCont (k : Cont') : Cont'.ofNatCont (Cont'.encodeCont k) = k := by
  simpa [Cont'.encodeCont_eq, Cont'.ofNatCont_eq] using Denumerable.ofNat_encode k

theorem encodeLabel_move (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ') :
    encodeLabel (move p k₁ k₂ q) = 8 * movePayloadCode p k₁ k₂ (encodeLabel q) + 1 :=
  rfl

theorem encodeLabel_clear (p : Γ' → Bool) (k : K') (q : Λ') :
    encodeLabel (clear p k q) = 8 * clearPayloadCode p k (encodeLabel q) + 2 :=
  rfl

theorem encodeLabel_copy (q : Λ') :
    encodeLabel (copy q) = 8 * encodeLabel q + 3 :=
  rfl

theorem encodeLabel_push (k : K') (f : Option Γ' → Option Γ') (q : Λ') :
    encodeLabel (push k f q) = 8 * pushPayloadCode k f (encodeLabel q) + 4 :=
  rfl

theorem encodeLabel_read (f : Option Γ' → Λ') :
    encodeLabel (read f) =
      8 * readPayloadCode (encodeLabel (f none)) (encodeLabel (f (some Γ'.consₗ)))
        (encodeLabel (f (some Γ'.cons))) (encodeLabel (f (some Γ'.bit0)))
        (encodeLabel (f (some Γ'.bit1))) + 5 :=
  rfl

theorem encodeLabel_succ (q : Λ') :
    encodeLabel (succ q) = 8 * encodeLabel q + 6 :=
  rfl

theorem encodeLabel_pred (q₁ q₂ : Λ') :
    encodeLabel (pred q₁ q₂) = 8 * predPayloadCode (encodeLabel q₁) (encodeLabel q₂) + 7 :=
  rfl

theorem encodeLabel_ret (k : Cont') :
    encodeLabel (ret k) = 8 * Cont'.encodeCont k + 8 :=
  rfl

/-- Fuelled partial decoder for `PartrecToTM2` labels. -/
def decodeLabelFuel : Nat → Nat → Option Λ'
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, n + 1 =>
      let payload := n / 8
      match n % 8 with
      | 0 => do
          let fields ← decodeMovePayload payload
          let q ← decodeLabelFuel fuel fields.2.2.2
          some (move fields.1 fields.2.1 fields.2.2.1 q)
      | 1 => do
          let fields ← decodeClearPayload payload
          let q ← decodeLabelFuel fuel fields.2.2
          some (clear fields.1 fields.2.1 q)
      | 2 => do
          let q ← decodeLabelFuel fuel payload
          some (copy q)
      | 3 => do
          let fields ← decodePushPayload payload
          let q ← decodeLabelFuel fuel fields.2.2
          some (push fields.1 fields.2.1 q)
      | 4 =>
          let fields := decodeReadPayload payload
          match decodeLabelFuel fuel fields.1 with
          | none => none
          | some q₀ =>
            match decodeLabelFuel fuel fields.2.1 with
            | none => none
            | some q₁ =>
              match decodeLabelFuel fuel fields.2.2.1 with
              | none => none
              | some q₂ =>
                match decodeLabelFuel fuel fields.2.2.2.1 with
                | none => none
                | some q₃ =>
                  match decodeLabelFuel fuel fields.2.2.2.2 with
                  | none => none
                  | some q₄ =>
                      some (read fun
                        | none => q₀
                        | some Γ'.consₗ => q₁
                        | some Γ'.cons => q₂
                        | some Γ'.bit0 => q₃
                        | some Γ'.bit1 => q₄)
      | 5 => do
          let q ← decodeLabelFuel fuel payload
          some (succ q)
      | 6 => do
          let fields := decodePredPayload payload
          let q₁ ← decodeLabelFuel fuel fields.1
          let q₂ ← decodeLabelFuel fuel fields.2
          some (pred q₁ q₂)
      | _ => some (ret (Cont'.ofNatCont payload))

/-- Partial decoder for `PartrecToTM2` labels, using the code itself as fuel. -/
def decodeLabel (n : Nat) : Option Λ' :=
  decodeLabelFuel n n

/-- Division ignores a base-eight tag smaller than the base. -/
theorem div_eight_mul_add_of_lt (m t : Nat) (h : t < 8) : (8 * m + t) / 8 = m := by
  omega

/-- Modulo recovers a base-eight tag smaller than the base. -/
theorem mod_eight_mul_add_of_lt (m t : Nat) (h : t < 8) : (8 * m + t) % 8 = t := by
  omega

/-- The left component of a pairing is bounded by the pair code. -/
theorem left_le_pair (a b : Nat) : a ≤ Nat.pair a b := by
  simpa using (Nat.pair a b).unpair_left_le

/-- The right component of a pairing is bounded by the pair code. -/
theorem right_le_pair (a b : Nat) : b ≤ Nat.pair a b := by
  simpa using (Nat.pair a b).unpair_right_le

theorem movePayloadCode_target_le (p : Γ' → Bool) (k₁ k₂ : K') (qCode : Nat) :
    qCode ≤ movePayloadCode p k₁ k₂ qCode := by
  exact (right_le_pair (stackNameCode k₂) qCode).trans <|
    (right_le_pair (stackNameCode k₁) (Nat.pair (stackNameCode k₂) qCode)).trans <|
      right_le_pair (stackPredicateCode p)
        (Nat.pair (stackNameCode k₁) (Nat.pair (stackNameCode k₂) qCode))

theorem clearPayloadCode_target_le (p : Γ' → Bool) (k : K') (qCode : Nat) :
    qCode ≤ clearPayloadCode p k qCode := by
  exact (right_le_pair (stackNameCode k) qCode).trans <|
    right_le_pair (stackPredicateCode p) (Nat.pair (stackNameCode k) qCode)

theorem pushPayloadCode_target_le (k : K') (f : Option Γ' → Option Γ') (qCode : Nat) :
    qCode ≤ pushPayloadCode k f qCode := by
  exact (right_le_pair (localActionCode f) qCode).trans <|
    right_le_pair (stackNameCode k) (Nat.pair (localActionCode f) qCode)

theorem readPayloadCode_max_le (q₀ q₁ q₂ q₃ q₄ : Nat) :
    max q₀ (max q₁ (max q₂ (max q₃ q₄))) ≤ readPayloadCode q₀ q₁ q₂ q₃ q₄ := by
  have h₀ : q₀ ≤ readPayloadCode q₀ q₁ q₂ q₃ q₄ := by
    exact left_le_pair q₀ (Nat.pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄)))
  have h₁ : q₁ ≤ readPayloadCode q₀ q₁ q₂ q₃ q₄ := by
    exact (left_le_pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄))).trans <|
      right_le_pair q₀ (Nat.pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄)))
  have h₂ : q₂ ≤ readPayloadCode q₀ q₁ q₂ q₃ q₄ := by
    exact (left_le_pair q₂ (Nat.pair q₃ q₄)).trans <|
      (right_le_pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄))).trans <|
        right_le_pair q₀ (Nat.pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄)))
  have h₃ : q₃ ≤ readPayloadCode q₀ q₁ q₂ q₃ q₄ := by
    exact (left_le_pair q₃ q₄).trans <|
      (right_le_pair q₂ (Nat.pair q₃ q₄)).trans <|
        (right_le_pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄))).trans <|
          right_le_pair q₀ (Nat.pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄)))
  have h₄ : q₄ ≤ readPayloadCode q₀ q₁ q₂ q₃ q₄ := by
    exact (right_le_pair q₃ q₄).trans <|
      (right_le_pair q₂ (Nat.pair q₃ q₄)).trans <|
        (right_le_pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄))).trans <|
          right_le_pair q₀ (Nat.pair q₁ (Nat.pair q₂ (Nat.pair q₃ q₄)))
  omega

theorem predPayloadCode_max_le (q₁ q₂ : Nat) :
    max q₁ q₂ ≤ predPayloadCode q₁ q₂ := by
  have h₁ : q₁ ≤ predPayloadCode q₁ q₂ := left_le_pair q₁ q₂
  have h₂ : q₂ ≤ predPayloadCode q₁ q₂ := right_le_pair q₁ q₂
  omega

/-- Structural depth of a `PartrecToTM2` label, used as sufficient decoder fuel. -/
def labelDepth : Λ' → Nat
  | move _ _ _ q => labelDepth q + 1
  | clear _ _ q => labelDepth q + 1
  | copy q => labelDepth q + 1
  | push _ _ q => labelDepth q + 1
  | read f =>
      (max (labelDepth (f none)) <|
        max (labelDepth (f (some Γ'.consₗ))) <|
          max (labelDepth (f (some Γ'.cons))) <|
            max (labelDepth (f (some Γ'.bit0))) (labelDepth (f (some Γ'.bit1)))) + 1
  | succ q => labelDepth q + 1
  | pred q₁ q₂ => max (labelDepth q₁) (labelDepth q₂) + 1
  | ret _ => 1

set_option linter.flexible false in
theorem decodeLabelFuel_encodeLabel_of_depth :
    ∀ (q : Λ') (fuel : Nat), labelDepth q ≤ fuel →
      decodeLabelFuel fuel (encodeLabel q) = some q := by
  intro q
  induction q with
  | move p k₁ k₂ q ih =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have hq : labelDepth q ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_move, decodeLabelFuel, decodeMovePayload_movePayloadCode, ih fuel hq]
  | clear p k q ih =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have hq : labelDepth q ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_clear, decodeLabelFuel, div_eight_mul_add_of_lt,
            decodeClearPayload_clearPayloadCode, ih fuel hq]
  | copy q ih =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have hq : labelDepth q ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_copy, decodeLabelFuel, div_eight_mul_add_of_lt, ih fuel hq]
  | push k f q ih =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have hq : labelDepth q ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_push, decodeLabelFuel, div_eight_mul_add_of_lt,
            decodePushPayload_pushPayloadCode, ih fuel hq]
  | read f ih =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have h₀ : labelDepth (f none) ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          have h₁ : labelDepth (f (some Γ'.consₗ)) ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          have h₂ : labelDepth (f (some Γ'.cons)) ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          have h₃ : labelDepth (f (some Γ'.bit0)) ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          have h₄ : labelDepth (f (some Γ'.bit1)) ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_read, decodeLabelFuel, div_eight_mul_add_of_lt,
            decodeReadPayload_readPayloadCode, ih none fuel h₀,
            ih (some Γ'.consₗ) fuel h₁, ih (some Γ'.cons) fuel h₂,
            ih (some Γ'.bit0) fuel h₃, ih (some Γ'.bit1) fuel h₄]
          funext s
          cases s with
          | none => rfl
          | some a => cases a <;> rfl
  | succ q ih =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have hq : labelDepth q ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_succ, decodeLabelFuel, div_eight_mul_add_of_lt, ih fuel hq]
  | pred q₁ q₂ ih₁ ih₂ =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          have hq₁ : labelDepth q₁ ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          have hq₂ : labelDepth q₂ ≤ fuel := by
            simp [labelDepth] at hfuel
            omega
          simp [encodeLabel_pred, decodeLabelFuel, div_eight_mul_add_of_lt,
            decodePredPayload_predPayloadCode, ih₁ fuel hq₁, ih₂ fuel hq₂]
  | ret k =>
      intro fuel hfuel
      cases fuel with
      | zero =>
          simp [labelDepth] at hfuel
      | succ fuel =>
          simp [encodeLabel_ret, decodeLabelFuel, div_eight_mul_add_of_lt, ofNatCont_encodeCont]

theorem labelDepth_le_encodeLabel : ∀ q : Λ', labelDepth q ≤ encodeLabel q := by
  intro q
  induction q with
  | move p k₁ k₂ q ih =>
      have htarget := movePayloadCode_target_le p k₁ k₂ (encodeLabel q)
      rw [encodeLabel_move]
      simp [labelDepth]
      omega
  | clear p k q ih =>
      have htarget := clearPayloadCode_target_le p k (encodeLabel q)
      rw [encodeLabel_clear]
      simp [labelDepth]
      omega
  | copy q ih =>
      rw [encodeLabel_copy]
      simp [labelDepth]
      omega
  | push k f q ih =>
      have htarget := pushPayloadCode_target_le k f (encodeLabel q)
      rw [encodeLabel_push]
      simp [labelDepth]
      omega
  | read f ih =>
      have h₀ := ih none
      have h₁ := ih (some Γ'.consₗ)
      have h₂ := ih (some Γ'.cons)
      have h₃ := ih (some Γ'.bit0)
      have h₄ := ih (some Γ'.bit1)
      have hpayload := readPayloadCode_max_le
        (encodeLabel (f none)) (encodeLabel (f (some Γ'.consₗ)))
        (encodeLabel (f (some Γ'.cons))) (encodeLabel (f (some Γ'.bit0)))
        (encodeLabel (f (some Γ'.bit1)))
      rw [encodeLabel_read]
      simp [labelDepth]
      omega
  | succ q ih =>
      rw [encodeLabel_succ]
      simp [labelDepth]
      omega
  | pred q₁ q₂ ih₁ ih₂ =>
      have hpayload := predPayloadCode_max_le (encodeLabel q₁) (encodeLabel q₂)
      rw [encodeLabel_pred]
      simp [labelDepth]
      omega
  | ret k =>
      rw [encodeLabel_ret]
      simp [labelDepth]

theorem decodeLabel_encodeLabel (q : Λ') : decodeLabel (encodeLabel q) = some q := by
  exact decodeLabelFuel_encodeLabel_of_depth q (encodeLabel q) (labelDepth_le_encodeLabel q)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instEncodable : Encodable Λ' where
  encode := encodeLabel
  decode := decodeLabel
  encodek := decodeLabel_encodeLabel

theorem encodeLabel_eq : Encodable.encode = encodeLabel :=
  rfl

theorem decodeLabel_eq : Encodable.decode = decodeLabel :=
  rfl

end Λ'

end PartrecToTM2

end Turing
