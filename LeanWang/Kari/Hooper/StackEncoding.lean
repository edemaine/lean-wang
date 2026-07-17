/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SourceMachine
import Mathlib.Data.Nat.Digits.Defs

/-!
# Arithmetic encodings of finite one-sided tapes

Hooper's counter-machine simulation replaces each finite one-sided tape by a
natural number.  Digits are stored least-significant first, so the cell next
to the head is obtained by remainder and removing that cell is division.

The digit assignment is *pointed*: the distinguished blank symbol `default`
has digit zero.  This is essential for Mathlib's `Turing.ListBlank`, whose
representatives are identified after appending trailing blanks.  All other
symbols have positive digits.  We use base `Fintype.card Γ + 1`; the largest
base digit is deliberately unused, which keeps the base at least two even for
a one-symbol alphabet.  `Valid` records that this unused digit does not occur.

Besides the raw list encoding, this file defines mutually inverse maps between
`Turing.ListBlank Γ` and valid natural-number codes.  The final section packages
the two one-sided codes and scanned symbol of a Mathlib tape, proves the exact
arithmetic formulas for head moves, and identifies the registers of the fixed
source machine's canonical input tape.
-/

noncomputable section

namespace LeanWang
namespace Kari
namespace Hooper
namespace StackEncoding

open Turing

universe u

variable {Γ : Type u} [Fintype Γ] [Inhabited Γ]

/-- The radix for one-sided stack codes.  Digit `Fintype.card Γ` is unused. -/
def base (Γ : Type u) [Fintype Γ] : Nat :=
  Fintype.card Γ + 1

theorem card_pos (Γ : Type u) [Fintype Γ] [Inhabited Γ] :
    0 < Fintype.card Γ :=
  Fintype.card_pos

theorem one_lt_base (Γ : Type u) [Fintype Γ] [Inhabited Γ] :
    1 < base Γ := by
  simp only [base]
  exact Nat.add_lt_add_right (card_pos Γ) 1

theorem base_pos (Γ : Type u) [Fintype Γ] [Inhabited Γ] :
    0 < base Γ :=
  Nat.zero_lt_of_lt (one_lt_base Γ)

/-- Zero as an index into a nonempty finite alphabet. -/
def zeroIndex (Γ : Type u) [Fintype Γ] [Inhabited Γ] :
    Fin (Fintype.card Γ) :=
  ⟨0, card_pos Γ⟩

/-- A finite enumeration adjusted to send the distinguished blank to zero.

Keeping this as an equivalence makes injectivity of the digit assignment
explicit.  Downstream executable compilers only use its two finite functions.
-/
def symbolEquiv (Γ : Type u) [Fintype Γ] [Inhabited Γ] :
    Γ ≃ Fin (Fintype.card Γ) :=
  (Fintype.equivFin Γ).trans
    (Equiv.swap (Fintype.equivFin Γ default) (zeroIndex Γ))

@[simp]
theorem symbolEquiv_default (Γ : Type u) [Fintype Γ] [Inhabited Γ] :
    symbolEquiv Γ default = zeroIndex Γ := by
  simp [symbolEquiv]

/-- The base digit of a tape symbol.  Blank is zero; every nonblank is
positive. -/
def digit (a : Γ) : Nat :=
  (symbolEquiv Γ a).val

@[simp]
theorem digit_default : digit (default : Γ) = 0 := by
  simp [digit, zeroIndex]

theorem digit_lt_card (a : Γ) :
    digit a < Fintype.card Γ :=
  (symbolEquiv Γ a).isLt

theorem digit_lt_base (a : Γ) :
    digit a < base Γ := by
  exact Nat.lt_trans (digit_lt_card a) (Nat.lt_succ_self _)

theorem digit_injective :
    Function.Injective (digit : Γ → Nat) := by
  intro a b h
  apply (symbolEquiv Γ).injective
  apply Fin.ext
  exact h

@[simp]
theorem digit_eq_zero_iff (a : Γ) :
    digit a = 0 ↔ a = default := by
  constructor
  · intro h
    apply digit_injective
    simpa using h
  · rintro rfl
    exact digit_default

theorem digit_pos_iff (a : Γ) :
    0 < digit a ↔ a ≠ default := by
  rw [Nat.pos_iff_ne_zero, ne_eq, digit_eq_zero_iff]

/-- Interpret a base digit as a symbol.  The unused digit and all out-of-range
numbers decode to blank. -/
def decodeDigit (n : Nat) : Γ :=
  if h : n < Fintype.card Γ then
    (symbolEquiv Γ).symm ⟨n, h⟩
  else default

@[simp]
theorem decodeDigit_zero : decodeDigit (Γ := Γ) 0 = default := by
  rw [decodeDigit, dif_pos (card_pos Γ)]
  apply (symbolEquiv Γ).injective
  simp [zeroIndex]

@[simp]
theorem decodeDigit_digit (a : Γ) :
    decodeDigit (digit a) = a := by
  rw [decodeDigit, dif_pos (digit_lt_card a)]
  exact (symbolEquiv Γ).symm_apply_apply a

theorem digit_decodeDigit_of_lt {n : Nat}
    (h : n < Fintype.card Γ) :
    digit (decodeDigit (Γ := Γ) n) = n := by
  rw [decodeDigit, dif_pos h]
  change ((symbolEquiv Γ) ((symbolEquiv Γ).symm ⟨n, h⟩)).val = n
  simp

/-- Put a symbol on the near end of a numeric stack. -/
def push (a : Γ) (n : Nat) : Nat :=
  digit a + base Γ * n

/-- Remove the near digit of a numeric stack. -/
def pop (n : Nat) : Nat :=
  n / base Γ

/-- Read the near digit of a numeric stack, reading blank from the empty
stack. -/
def top (n : Nat) : Γ :=
  decodeDigit (Γ := Γ) (n % base Γ)

@[simp]
theorem push_mod (a : Γ) (n : Nat) :
    push a n % base Γ = digit a := by
  rw [push, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (digit_lt_base a)]

@[simp]
theorem push_div (a : Γ) (n : Nat) :
    push a n / base Γ = n := by
  rw [push, Nat.add_mul_div_left _ _ (base_pos Γ),
    Nat.div_eq_of_lt (digit_lt_base a), Nat.zero_add]

@[simp]
theorem top_push (a : Γ) (n : Nat) :
    top (push a n) = a := by
  simp [top]

@[simp]
theorem pop_push (a : Γ) (n : Nat) :
    pop (Γ := Γ) (push a n) = n := by
  simp [pop]

@[simp]
theorem top_zero : top (Γ := Γ) 0 = default := by
  simp [top]

omit [Inhabited Γ] in
@[simp]
theorem pop_zero : pop (Γ := Γ) 0 = 0 := by
  simp [pop]

omit [Inhabited Γ] in
/-- Quotient and remainder reconstruct every numeric stack. -/
theorem mod_add_base_mul_pop (n : Nat) :
    n % base Γ + base Γ * pop (Γ := Γ) n = n := by
  exact Nat.mod_add_div n (base Γ)

/-- A digit known not to be the unused top digit can be read and pushed back. -/
theorem push_top_pop_of_mod_lt_card (n : Nat)
    (h : n % base Γ < Fintype.card Γ) :
    push (top (Γ := Γ) n) (pop (Γ := Γ) n) = n := by
  rw [push, top, pop, digit_decodeDigit_of_lt h]
  exact mod_add_base_mul_pop n

/-- Encode a finite list with its head as the least-significant digit. -/
def encodeList : List Γ → Nat
  | [] => 0
  | a :: l => push a (encodeList l)

@[simp]
theorem encodeList_nil : encodeList ([] : List Γ) = 0 :=
  rfl

@[simp]
theorem encodeList_cons (a : Γ) (l : List Γ) :
    encodeList (a :: l) = push a (encodeList l) :=
  rfl

theorem encodeList_append (l r : List Γ) :
    encodeList (l ++ r) =
      encodeList l + (base Γ) ^ l.length * encodeList r := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.cons_append, encodeList_cons, List.length_cons, ih, push]
      rw [pow_succ]
      simp only [Nat.mul_add]
      ac_rfl

@[simp]
theorem encodeList_replicate_default (n : Nat) :
    encodeList (List.replicate n (default : Γ)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, encodeList_cons, ih]
      simp [push]

/-- Appending implicit blanks does not change a numeric stack code. -/
theorem encodeList_append_blanks (l : List Γ) (n : Nat) :
    encodeList (l ++ List.replicate n default) = encodeList l := by
  rw [encodeList_append, encodeList_replicate_default]
  simp

/-- Encode a Mathlib one-sided tape.  Pointed digits make this well-defined on
the quotient by trailing blanks. -/
def encode (L : Turing.ListBlank Γ) : Nat := by
  apply L.liftOn encodeList
  intro l _ h
  rcases h with ⟨n, rfl⟩
  exact (encodeList_append_blanks l n).symm

@[simp]
theorem encode_mk (l : List Γ) :
    encode (Turing.ListBlank.mk l) = encodeList l :=
  rfl

@[simp]
theorem encode_cons (a : Γ) (L : Turing.ListBlank Γ) :
    encode (L.cons a) = push a (encode L) := by
  refine L.induction_on ?_
  intro l
  rfl

@[simp]
theorem encode_mod (L : Turing.ListBlank Γ) :
    encode L % base Γ = digit L.head := by
  have hencode : encode L = push L.head (encode L.tail) := by
    calc
      encode L = encode (L.tail.cons L.head) :=
        congrArg encode (Turing.ListBlank.cons_head_tail L).symm
      _ = push L.head (encode L.tail) := encode_cons _ _
  rw [hencode, push_mod]

@[simp]
theorem encode_div (L : Turing.ListBlank Γ) :
    encode L / base Γ = encode L.tail := by
  have hencode : encode L = push L.head (encode L.tail) := by
    calc
      encode L = encode (L.tail.cons L.head) :=
        congrArg encode (Turing.ListBlank.cons_head_tail L).symm
      _ = push L.head (encode L.tail) := encode_cons _ _
  rw [hencode, push_div]

/-- Canonical finite-list decoding.  A zero quotient ends the list; internal
zero digits decode to explicit blanks. -/
def decodeList (n : Nat) : List Γ :=
  (Nat.digits (base Γ) n).map (decodeDigit (Γ := Γ))

@[simp]
theorem decodeList_zero : decodeList (Γ := Γ) 0 = [] := by
  simp [decodeList]

/-- Decode a natural number directly to a one-sided tape quotient. -/
def decode (n : Nat) : Turing.ListBlank Γ :=
  Turing.ListBlank.mk (decodeList (Γ := Γ) n)

@[simp]
theorem decode_zero : decode (Γ := Γ) 0 = Turing.ListBlank.mk [] := by
  simp [decode]

omit [Fintype Γ] in
private theorem cons_default_empty :
    (Turing.ListBlank.mk ([] : List Γ)).cons default =
      Turing.ListBlank.mk [] := by
  simpa using
    (Turing.ListBlank.cons_head_tail
      (Turing.ListBlank.mk ([] : List Γ)))

/-- Decoding an arithmetic push is exactly `ListBlank.cons`, including the
degenerate operation of pushing blank onto the empty stack. -/
@[simp]
theorem decode_push (a : Γ) (n : Nat) :
    decode (push a n) = (decode (Γ := Γ) n).cons a := by
  by_cases hp : push a n = 0
  · have hdigit : digit a = 0 := by
      change digit a + base Γ * n = 0 at hp
      exact (Nat.add_eq_zero_iff.mp hp).1
    have hn : n = 0 := by
      change digit a + base Γ * n = 0 at hp
      have hmul : base Γ * n = 0 := (Nat.add_eq_zero_iff.mp hp).2
      exact (Nat.mul_eq_zero.mp hmul).resolve_left (Nat.ne_of_gt (base_pos Γ))
    have ha : a = default := (digit_eq_zero_iff a).1 hdigit
    subst a
    subst n
    have hpush : push (default : Γ) 0 = 0 := by simp [push]
    rw [hpush, decode_zero]
    exact (cons_default_empty (Γ := Γ)).symm
  · rw [decode, decodeList]
    have hnonzero : digit a ≠ 0 ∨ n ≠ 0 := by
      by_cases hdigit : digit a = 0
      · right
        intro hn
        apply hp
        simp [push, hdigit, hn]
      · exact Or.inl hdigit
    rw [push, Nat.digits_add (base Γ) (one_lt_base Γ)
      (digit a) n (digit_lt_base a) hnonzero]
    simp [decode, decodeList]

/-- Decoding after encoding recovers the one-sided tape exactly. -/
@[simp]
theorem decode_encode (L : Turing.ListBlank Γ) :
    decode (Γ := Γ) (encode L) = L := by
  refine L.induction_on ?_
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      simpa using congrArg (Turing.ListBlank.cons a) ih

@[simp]
theorem decode_head (n : Nat) :
    (decode (Γ := Γ) n).head = top (Γ := Γ) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [decode, decodeList]
    rw [Nat.digits_def' (one_lt_base Γ) (Nat.pos_of_ne_zero hn)]
    simp [top]

@[simp]
theorem decode_tail (n : Nat) :
    (decode (Γ := Γ) n).tail = decode (Γ := Γ) (pop (Γ := Γ) n) := by
  by_cases hn : n = 0
  · subst n
    simp [decode]
  · rw [decode, decodeList]
    rw [Nat.digits_def' (one_lt_base Γ) (Nat.pos_of_ne_zero hn)]
    simp [pop, decode, decodeList]

/-- A numeric code is valid when canonical decoding and re-encoding preserves
it.  Equivalently, no base digit uses the deliberately unused value
`Fintype.card Γ`. -/
def Valid (n : Nat) : Prop :=
  encode (decode (Γ := Γ) n) = n

@[simp]
theorem valid_zero : Valid (Γ := Γ) 0 := by
  simp [Valid]

theorem valid_push {n : Nat} (hn : Valid (Γ := Γ) n) (a : Γ) :
    Valid (Γ := Γ) (push a n) := by
  simpa [Valid] using congrArg (push a) hn

theorem valid_encode (L : Turing.ListBlank Γ) :
    Valid (Γ := Γ) (encode L) := by
  simp [Valid]

/-- Valid numeric codes are recovered after decode-then-encode. -/
theorem encode_decode_of_valid (n : Nat) (hn : Valid (Γ := Γ) n) :
    encode (decode (Γ := Γ) n) = n := by
  exact hn

/-- The scanned symbol and two numeric one-sided tapes. -/
structure TapeRegisters (Γ : Type u) where
  head : Γ
  left : Nat
  right : Nat

namespace TapeRegisters

/-- Decode three registers to Mathlib's finite-support tape. -/
def decodeTape (r : TapeRegisters Γ) : Turing.Tape Γ :=
  ⟨r.head, decode (Γ := Γ) r.left, decode (Γ := Γ) r.right⟩

/-- Encode both one-sided components of a Mathlib tape. -/
def encodeTape (T : Turing.Tape Γ) : TapeRegisters Γ :=
  ⟨T.head, encode T.left, encode T.right⟩

@[simp]
theorem decodeTape_encodeTape (T : Turing.Tape Γ) :
    decodeTape (encodeTape T) = T := by
  cases T
  simp [decodeTape, encodeTape]

/-- Arithmetic implementation of a head move to the left. -/
def moveLeft (r : TapeRegisters Γ) : TapeRegisters Γ :=
  ⟨top (Γ := Γ) r.left, pop (Γ := Γ) r.left, push r.head r.right⟩

/-- Arithmetic implementation of a head move to the right. -/
def moveRight (r : TapeRegisters Γ) : TapeRegisters Γ :=
  ⟨top (Γ := Γ) r.right, push r.head r.left, pop (Γ := Γ) r.right⟩

/-- Arithmetic implementation of overwriting the scanned symbol. -/
def write (a : Γ) (r : TapeRegisters Γ) : TapeRegisters Γ :=
  { r with head := a }

@[simp]
theorem decodeTape_moveLeft (r : TapeRegisters Γ) :
    decodeTape (moveLeft r) = (decodeTape r).move .left := by
  cases r
  simp [decodeTape, moveLeft, Turing.Tape.move]

@[simp]
theorem decodeTape_moveRight (r : TapeRegisters Γ) :
    decodeTape (moveRight r) = (decodeTape r).move .right := by
  cases r
  simp [decodeTape, moveRight, Turing.Tape.move]

@[simp]
theorem decodeTape_write (a : Γ) (r : TapeRegisters Γ) :
    decodeTape (write a r) = (decodeTape r).write a := by
  cases r
  rfl

@[simp]
theorem encodeTape_moveLeft (T : Turing.Tape Γ) :
    encodeTape (T.move .left) = moveLeft (encodeTape T) := by
  cases T
  simp [encodeTape, moveLeft, Turing.Tape.move, top, pop]

@[simp]
theorem encodeTape_moveRight (T : Turing.Tape Γ) :
    encodeTape (T.move .right) = moveRight (encodeTape T) := by
  cases T
  simp [encodeTape, moveRight, Turing.Tape.move, top, pop]

@[simp]
theorem encodeTape_write (a : Γ) (T : Turing.Tape Γ) :
    encodeTape (T.write a) = write a (encodeTape T) := by
  cases T
  rfl

end TapeRegisters

/-! ## The fixed source machine's initial registers -/

/-- Left/head/right register data for the fixed universal source input. -/
def sourceInitialRegisters (c : Nat.Partrec.Code) :
    TapeRegisters SourceMachine.Alphabet :=
  TapeRegisters.encodeTape (SourceMachine.ambientInitial c).Tape

@[simp]
theorem sourceInitialRegisters_left (c : Nat.Partrec.Code) :
    (sourceInitialRegisters c).left = 0 := by
  rfl

@[simp]
theorem sourceInitialRegisters_head (c : Nat.Partrec.Code) :
    (sourceInitialRegisters c).head =
      (UniversalTM0Semantic.input c).headI := by
  rfl

@[simp]
theorem sourceInitialRegisters_right (c : Nat.Partrec.Code) :
    (sourceInitialRegisters c).right =
      encodeList (UniversalTM0Semantic.input c).tail := by
  rfl

/-- The source input registers decode to Mathlib's canonical initial tape. -/
@[simp]
theorem decodeTape_sourceInitialRegisters (c : Nat.Partrec.Code) :
    TapeRegisters.decodeTape (sourceInitialRegisters c) =
      (SourceMachine.ambientInitial c).Tape := by
  exact TapeRegisters.decodeTape_encodeTape _

/-- The same decoded tape is the tape component of the finite-control source
configuration used by the designated-run reduction. -/
theorem fullTape_sourceInitialRegisters (c : Nat.Partrec.Code) :
    FullTM0.Tape.ofMathlib
        (TapeRegisters.decodeTape (sourceInitialRegisters c)) =
      (SourceMachine.canonical c).tape := by
  rw [decodeTape_sourceInitialRegisters]
  rfl

end StackEncoding
end Hooper
end Kari
end LeanWang
