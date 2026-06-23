/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.ToPartrecEncoding

/-!
Executable list mirrors for Mathlib's `PartrecToTM2` support finsets.

`PartrecToTM2Support.labelList` currently uses `Finset.toList`, which is
noncomputable. This file mirrors Mathlib's recursive `trStmts₁`, `codeSupp'`,
`contSupp`, and `codeSupp` definitions with explicit lists. The current TM0
route has not yet been switched to these lists; keeping the mirror isolated
lets us prove the list/finset correspondence without rebuilding the folded
compiler on every intermediate edit.
-/

namespace LeanWang

namespace PartrecToTM2SupportList

open Turing
open Turing.PartrecToTM2

/-- All possible local store values read by `Λ'.read`. -/
def varList : List (Option Γ') :=
  none :: PartrecToTM2Support.stackAlphabetList.map some

theorem mem_varList (s : Option Γ') : s ∈ varList := by
  cases s with
  | none =>
      simp [varList]
  | some a =>
      simp [varList, PartrecToTM2Support.mem_stackAlphabetList a]

/-- List-valued mirror of Mathlib's `PartrecToTM2.trStmts₁`. -/
def trStmtsList : Λ' → List Λ'
  | Q@(Λ'.move _ _ _ q) => Q :: trStmtsList q
  | Q@(Λ'.push _ _ q) => Q :: trStmtsList q
  | Q@(Λ'.read q) => Q :: varList.flatMap fun s => trStmtsList (q s)
  | Q@(Λ'.clear _ _ q) => Q :: trStmtsList q
  | Q@(Λ'.copy q) => Q :: trStmtsList q
  | Q@(Λ'.succ q) => Q :: unrev q :: trStmtsList q
  | Q@(Λ'.pred q₁ q₂) => Q :: (trStmtsList q₁ ++ unrev q₂ :: trStmtsList q₂)
  | Q@(Λ'.ret _) => [Q]

/-- Numeric length mirror of `trStmtsList`, avoiding an encoding of evaluator labels. -/
def trStmtsLength : Λ' → Nat
  | Λ'.move _ _ _ q => 1 + trStmtsLength q
  | Λ'.push _ _ q => 1 + trStmtsLength q
  | Λ'.read q => 1 + (varList.map fun s => trStmtsLength (q s)).sum
  | Λ'.clear _ _ q => 1 + trStmtsLength q
  | Λ'.copy q => 1 + trStmtsLength q
  | Λ'.succ q => 1 + (1 + trStmtsLength q)
  | Λ'.pred q₁ q₂ => 1 + (1 + (trStmtsLength q₁ + trStmtsLength q₂))
  | Λ'.ret _ => 1

theorem trStmtsList_length (q : Λ') :
    (trStmtsList q).length = trStmtsLength q := by
  induction q with
  | move p k₁ k₂ q ih =>
      simp [trStmtsList, trStmtsLength, ih, Nat.add_comm]
  | clear p k q ih =>
      simp [trStmtsList, trStmtsLength, ih, Nat.add_comm]
  | copy q ih =>
      simp [trStmtsList, trStmtsLength, ih, Nat.add_comm]
  | push k f q ih =>
      simp [trStmtsList, trStmtsLength, ih, Nat.add_comm]
  | read q ih =>
      simp [trStmtsList, trStmtsLength, List.length_flatMap, ih, Nat.add_comm]
  | succ q ih =>
      simp [trStmtsList, trStmtsLength, ih, Nat.add_comm]
  | pred q₁ q₂ ih₁ ih₂ =>
      simp [trStmtsList, trStmtsLength, ih₁, ih₂, Nat.add_comm, Nat.add_left_comm]
  | ret k =>
      simp [trStmtsList, trStmtsLength]

theorem mem_trStmtsList_iff {q r : Λ'} :
    r ∈ trStmtsList q ↔ r ∈ trStmts₁ q := by
  induction q with
  | move p k₁ k₂ q ih =>
      simp [trStmtsList, trStmts₁, ih]
  | clear p k q ih =>
      simp [trStmtsList, trStmts₁, ih]
  | copy q ih =>
      simp [trStmtsList, trStmts₁, ih]
  | push k f q ih =>
      simp [trStmtsList, trStmts₁, ih]
  | read q ih =>
      simp [trStmtsList, trStmts₁, ih, mem_varList]
  | succ q ih =>
      simp [trStmtsList, trStmts₁, ih]
  | pred q₁ q₂ ih₁ ih₂ =>
      simp [trStmtsList, trStmts₁, ih₁, ih₂]
      tauto
  | ret k =>
      simp [trStmtsList, trStmts₁]

private theorem list_sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β)
    (w : β → Nat) :
    ((xs.flatMap f).map w).sum = (xs.map fun x => ((f x).map w).sum).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

/-- Weighted sum mirror of `trStmtsList`. -/
def trStmtsWeight (w : Λ' → Nat) : Λ' → Nat
  | Q@(Λ'.move _ _ _ q) => w Q + trStmtsWeight w q
  | Q@(Λ'.push _ _ q) => w Q + trStmtsWeight w q
  | Q@(Λ'.read q) => w Q + (varList.map fun s => trStmtsWeight w (q s)).sum
  | Q@(Λ'.clear _ _ q) => w Q + trStmtsWeight w q
  | Q@(Λ'.copy q) => w Q + trStmtsWeight w q
  | Q@(Λ'.succ q) => w Q + (w (unrev q) + trStmtsWeight w q)
  | Q@(Λ'.pred q₁ q₂) => w Q + (trStmtsWeight w q₁ + (w (unrev q₂) + trStmtsWeight w q₂))
  | Q@(Λ'.ret _) => w Q

theorem trStmtsList_weight (w : Λ' → Nat) (q : Λ') :
    ((trStmtsList q).map w).sum = trStmtsWeight w q := by
  induction q with
  | move p k₁ k₂ q ih =>
      simp [trStmtsList, trStmtsWeight, ih]
  | clear p k q ih =>
      simp [trStmtsList, trStmtsWeight, ih]
  | copy q ih =>
      simp [trStmtsList, trStmtsWeight, ih]
  | push k f q ih =>
      simp [trStmtsList, trStmtsWeight, ih]
  | read q ih =>
      change
        (List.map w (Λ'.read q :: varList.flatMap fun s => trStmtsList (q s))).sum =
          w (Λ'.read q) + (varList.map fun s => trStmtsWeight w (q s)).sum
      simp only [List.map_cons, List.sum_cons]
      rw [show (List.map w (List.flatMap (fun s => trStmtsList (q s)) varList)).sum =
          (varList.map fun s => ((trStmtsList (q s)).map w).sum).sum by
        exact list_sum_map_flatMap varList (fun s => trStmtsList (q s)) w]
      simp [ih]
  | succ q ih =>
      simp [trStmtsList, trStmtsWeight, ih]
  | pred q₁ q₂ ih₁ ih₂ =>
      simp [trStmtsList, trStmtsWeight, ih₁, ih₂]
  | ret k =>
      simp [trStmtsList, trStmtsWeight]

/-- Dense code for the auxiliary label `unrev q`, from the dense code for `q`. -/
def unrevCodeOf (qCode : Nat) : Nat :=
  8 * Turing.PartrecToTM2.Λ'.movePayloadCode (fun _ : Γ' => false) K'.rev K'.main qCode + 1

theorem unrevCodeOf_primrec : Primrec unrevCodeOf := by
  unfold unrevCodeOf
  have hpayload :
      Primrec fun qCode : Nat =>
        Turing.PartrecToTM2.Λ'.movePayloadCode
          (fun _ : Γ' => false) K'.rev K'.main qCode := by
    exact Turing.PartrecToTM2.Λ'.movePayloadCode_primrec.comp
      (Primrec.pair (Primrec.const (fun _ : Γ' => false))
        (Primrec.pair (Primrec.const K'.rev)
          (Primrec.pair (Primrec.const K'.main) Primrec.id)))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) hpayload) (Primrec.const 1)

theorem unrevCodeOf_encodeLabel (q : Λ') :
    unrevCodeOf (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (unrev q) := by
  simp [unrevCodeOf, Turing.PartrecToTM2.unrev,
    Turing.PartrecToTM2.Λ'.encodeLabel_move]

/--
One row step for computing `trStmtsWeight` by strong recursion over dense
label codes.

`prev` stores already-computed recursive values indexed by label code. The
function `wCode` gives the encoded weight of the current label and of the
extra `unrev` labels introduced by `trStmtsList`.
-/
def trStmtsWeightStepBody (wCode : Nat → Nat) (prev : List Nat) (n : Nat) : Nat :=
  let payload := n / 8
  let self := wCode n
  if n % 8 = 1 then
    match Turing.PartrecToTM2.Λ'.decodeMovePayload payload with
    | none => 0
    | some fields => self + Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.2.2
  else if n % 8 = 2 then
    match Turing.PartrecToTM2.Λ'.decodeClearPayload payload with
    | none => 0
    | some fields => self + Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.2
  else if n % 8 = 3 then
    self + Turing.PartrecToTM2.Λ'.normalizeLookup prev payload
  else if n % 8 = 4 then
    match Turing.PartrecToTM2.Λ'.decodePushPayload payload with
    | none => 0
    | some fields => self + Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.2
  else if n % 8 = 5 then
    let fields := Turing.PartrecToTM2.Λ'.decodeReadPayload payload
    self +
      (Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.1 +
        (Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.1 +
          (Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.2.1 +
            (Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.2.2.1 +
              Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2.2.2.2))))
  else if n % 8 = 6 then
    self + (wCode (unrevCodeOf payload) +
      Turing.PartrecToTM2.Λ'.normalizeLookup prev payload)
  else if n % 8 = 7 then
    let fields := Turing.PartrecToTM2.Λ'.decodePredPayload payload
    self +
      (Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.1 +
        (wCode (unrevCodeOf fields.2) +
          Turing.PartrecToTM2.Λ'.normalizeLookup prev fields.2))
  else
    self

theorem trStmtsWeightStepBody_primrec {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : List Nat × Nat => trStmtsWeightStepBody wCode p.1 p.2) := by
  unfold trStmtsWeightStepBody
  let hpayload : Primrec (fun p : List Nat × Nat => p.2 / 8) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  let htag : Primrec (fun p : List Nat × Nat => p.2 % 8) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  let hself : Primrec (fun p : List Nat × Nat => wCode p.2) :=
    hw.comp Primrec.snd
  let lookupOn
      {α : Type} [Primcodable α] (target : α → Nat) (htarget : Primrec target) :
      Primrec (fun p : (List Nat × Nat) × α =>
        Turing.PartrecToTM2.Λ'.normalizeLookup p.1.1 (target p.2)) :=
    Turing.PartrecToTM2.Λ'.normalizeLookup_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (htarget.comp Primrec.snd))
  let hmoveSome : Primrec₂ (fun p : List Nat × Nat =>
      fun fields : (Γ' → Bool) × K' × K' × Nat =>
        wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 fields.2.2.2) := by
    apply Primrec₂.mk
    exact Primrec.nat_add.comp (hself.comp Primrec.fst)
      (lookupOn (fun fields : (Γ' → Bool) × K' × K' × Nat => fields.2.2.2)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  let hmove : Primrec (fun p : List Nat × Nat =>
      match Turing.PartrecToTM2.Λ'.decodeMovePayload (p.2 / 8) with
      | none => 0
      | some fields =>
          wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 fields.2.2.2) :=
    (Primrec.option_casesOn
      (Turing.PartrecToTM2.Λ'.decodeMovePayload_primrec.comp hpayload)
      (Primrec.const 0) hmoveSome).of_eq fun p => by
        cases Turing.PartrecToTM2.Λ'.decodeMovePayload (p.2 / 8) <;> rfl
  let hclearSome : Primrec₂ (fun p : List Nat × Nat =>
      fun fields : (Γ' → Bool) × K' × Nat =>
        wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 fields.2.2) := by
    apply Primrec₂.mk
    exact Primrec.nat_add.comp (hself.comp Primrec.fst)
      (lookupOn (fun fields : (Γ' → Bool) × K' × Nat => fields.2.2)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
  let hclear : Primrec (fun p : List Nat × Nat =>
      match Turing.PartrecToTM2.Λ'.decodeClearPayload (p.2 / 8) with
      | none => 0
      | some fields =>
          wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 fields.2.2) :=
    (Primrec.option_casesOn
      (Turing.PartrecToTM2.Λ'.decodeClearPayload_primrec.comp hpayload)
      (Primrec.const 0) hclearSome).of_eq fun p => by
        cases Turing.PartrecToTM2.Λ'.decodeClearPayload (p.2 / 8) <;> rfl
  let hcopy : Primrec (fun p : List Nat × Nat =>
      wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 (p.2 / 8)) :=
    Primrec.nat_add.comp hself
      (Turing.PartrecToTM2.Λ'.normalizeLookup_primrec.comp
        (Primrec.pair Primrec.fst hpayload))
  let hpushSome : Primrec₂ (fun p : List Nat × Nat =>
      fun fields : K' × (Option Γ' → Option Γ') × Nat =>
        wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 fields.2.2) := by
    apply Primrec₂.mk
    exact Primrec.nat_add.comp (hself.comp Primrec.fst)
      (lookupOn (fun fields : K' × (Option Γ' → Option Γ') × Nat => fields.2.2)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
  let hpush : Primrec (fun p : List Nat × Nat =>
      match Turing.PartrecToTM2.Λ'.decodePushPayload (p.2 / 8) with
      | none => 0
      | some fields =>
          wCode p.2 + Turing.PartrecToTM2.Λ'.normalizeLookup p.1 fields.2.2) :=
    (Primrec.option_casesOn
      (Turing.PartrecToTM2.Λ'.decodePushPayload_primrec.comp hpayload)
      (Primrec.const 0) hpushSome).of_eq fun p => by
        cases Turing.PartrecToTM2.Λ'.decodePushPayload (p.2 / 8) <;> rfl
  let hreadFields :
      Primrec (fun p : List Nat × Nat =>
        Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)) :=
    Turing.PartrecToTM2.Λ'.decodeReadPayload_primrec.comp hpayload
  let hreadLookup (target :
      Nat × Nat × Nat × Nat × Nat → Nat) (htarget : Primrec target) :
      Primrec (fun p : List Nat × Nat =>
        Turing.PartrecToTM2.Λ'.normalizeLookup p.1
          (target (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)))) :=
    Turing.PartrecToTM2.Λ'.normalizeLookup_primrec.comp
      (Primrec.pair Primrec.fst (htarget.comp hreadFields))
  let hread₀ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).1) :=
    hreadLookup (fun fields : Nat × Nat × Nat × Nat × Nat => fields.1) Primrec.fst
  let hread₁ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.1) :=
    hreadLookup (fun fields : Nat × Nat × Nat × Nat × Nat => fields.2.1)
      (Primrec.fst.comp Primrec.snd)
  let hread₂ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.1) :=
    hreadLookup (fun fields : Nat × Nat × Nat × Nat × Nat => fields.2.2.1)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  let hread₃ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.2.1) :=
    hreadLookup (fun fields : Nat × Nat × Nat × Nat × Nat => fields.2.2.2.1)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  let hread₄ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.2.2) :=
    hreadLookup (fun fields : Nat × Nat × Nat × Nat × Nat => fields.2.2.2.2)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  let hreadTail : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
          (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).1 +
        (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
            (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.1 +
          (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
              (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.1 +
            (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
                (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.2.1 +
              Turing.PartrecToTM2.Λ'.normalizeLookup p.1
                (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.2.2)))) :=
    Primrec.nat_add.comp hread₀
      (Primrec.nat_add.comp hread₁
        (Primrec.nat_add.comp hread₂ (Primrec.nat_add.comp hread₃ hread₄)))
  let hread : Primrec (fun p : List Nat × Nat =>
      wCode p.2 +
        (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
            (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).1 +
          (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
              (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.1 +
            (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
                (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.1 +
              (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
                  (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.2.1 +
                Turing.PartrecToTM2.Λ'.normalizeLookup p.1
                  (Turing.PartrecToTM2.Λ'.decodeReadPayload (p.2 / 8)).2.2.2.2))))) :=
    Primrec.nat_add.comp hself hreadTail
  let hunrevPayload : Primrec (fun p : List Nat × Nat => wCode (unrevCodeOf (p.2 / 8))) :=
    hw.comp (unrevCodeOf_primrec.comp hpayload)
  let hsucc : Primrec (fun p : List Nat × Nat =>
      wCode p.2 + (wCode (unrevCodeOf (p.2 / 8)) +
        Turing.PartrecToTM2.Λ'.normalizeLookup p.1 (p.2 / 8))) :=
    Primrec.nat_add.comp hself (Primrec.nat_add.comp hunrevPayload
      (Turing.PartrecToTM2.Λ'.normalizeLookup_primrec.comp
        (Primrec.pair Primrec.fst hpayload)))
  let hpredFields :
      Primrec (fun p : List Nat × Nat =>
        Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)) :=
    Turing.PartrecToTM2.Λ'.decodePredPayload_primrec.comp hpayload
  let hpred₁ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).1) :=
    Turing.PartrecToTM2.Λ'.normalizeLookup_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp hpredFields))
  let hpred₂Target : Primrec (fun p : List Nat × Nat =>
      (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).2) :=
    Primrec.snd.comp hpredFields
  let hpredUnrev : Primrec (fun p : List Nat × Nat =>
      wCode (unrevCodeOf (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).2)) :=
    hw.comp (unrevCodeOf_primrec.comp hpred₂Target)
  let hpred₂ : Primrec (fun p : List Nat × Nat =>
      Turing.PartrecToTM2.Λ'.normalizeLookup p.1
        (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).2) :=
    Turing.PartrecToTM2.Λ'.normalizeLookup_primrec.comp
      (Primrec.pair Primrec.fst hpred₂Target)
  let hpred : Primrec (fun p : List Nat × Nat =>
      wCode p.2 +
        (Turing.PartrecToTM2.Λ'.normalizeLookup p.1
            (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).1 +
          (wCode (unrevCodeOf
              (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).2) +
            Turing.PartrecToTM2.Λ'.normalizeLookup p.1
              (Turing.PartrecToTM2.Λ'.decodePredPayload (p.2 / 8)).2))) :=
    Primrec.nat_add.comp hself
      (Primrec.nat_add.comp hpred₁ (Primrec.nat_add.comp hpredUnrev hpred₂))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hmove ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hclear ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hcopy ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) hpush ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) hread ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) hsucc ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) hpred ?_
  exact hself

set_option linter.flexible false in
theorem trStmtsWeightStepBody_encodeLabel
    (w : Λ' → Nat) (wCode : Nat → Nat)
    (hwCode : ∀ q : Λ', wCode (Turing.PartrecToTM2.Λ'.encodeLabel q) = w q)
    (prev : List Nat)
    (q : Λ')
    (hprev : ∀ r : Λ', Turing.PartrecToTM2.Λ'.encodeLabel r <
      Turing.PartrecToTM2.Λ'.encodeLabel q →
      Turing.PartrecToTM2.Λ'.normalizeLookup prev
        (Turing.PartrecToTM2.Λ'.encodeLabel r) = trStmtsWeight w r) :
    trStmtsWeightStepBody wCode prev (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      trStmtsWeight w q := by
  cases q with
  | move p k₁ k₂ q =>
      have hq : Turing.PartrecToTM2.Λ'.encodeLabel q <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.move p k₁ k₂ q) := by
        have htarget := Turing.PartrecToTM2.Λ'.movePayloadCode_target_le p k₁ k₂
          (Turing.PartrecToTM2.Λ'.encodeLabel q)
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_move]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_move,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        Turing.PartrecToTM2.Λ'.decodeMovePayload_movePayloadCode,
        hprev q hq]
      simpa [Turing.PartrecToTM2.Λ'.encodeLabel_move] using
        hwCode (Λ'.move p k₁ k₂ q)
  | clear p k q =>
      have hq : Turing.PartrecToTM2.Λ'.encodeLabel q <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.clear p k q) := by
        have htarget := Turing.PartrecToTM2.Λ'.clearPayloadCode_target_le p k
          (Turing.PartrecToTM2.Λ'.encodeLabel q)
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_clear]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_clear,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        Turing.PartrecToTM2.Λ'.decodeClearPayload_clearPayloadCode,
        hprev q hq]
      simpa [Turing.PartrecToTM2.Λ'.encodeLabel_clear] using
        hwCode (Λ'.clear p k q)
  | copy q =>
      have hq : Turing.PartrecToTM2.Λ'.encodeLabel q <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.copy q) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_copy]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_copy,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        hprev q hq]
      simpa [Turing.PartrecToTM2.Λ'.encodeLabel_copy] using hwCode (Λ'.copy q)
  | push k f q =>
      have hq : Turing.PartrecToTM2.Λ'.encodeLabel q <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.push k f q) := by
        have htarget := Turing.PartrecToTM2.Λ'.pushPayloadCode_target_le k f
          (Turing.PartrecToTM2.Λ'.encodeLabel q)
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_push]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_push,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        Turing.PartrecToTM2.Λ'.decodePushPayload_pushPayloadCode,
        hprev q hq]
      simpa [Turing.PartrecToTM2.Λ'.encodeLabel_push] using
        hwCode (Λ'.push k f q)
  | read f =>
      have hpayload := Turing.PartrecToTM2.Λ'.readPayloadCode_max_le
        (Turing.PartrecToTM2.Λ'.encodeLabel (f none))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.consₗ)))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.cons)))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit0)))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit1)))
      have h₀ : Turing.PartrecToTM2.Λ'.encodeLabel (f none) <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read f) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_read]
        omega
      have h₁ : Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.consₗ)) <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read f) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_read]
        omega
      have h₂ : Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.cons)) <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read f) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_read]
        omega
      have h₃ : Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit0)) <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read f) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_read]
        omega
      have h₄ : Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit1)) <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read f) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_read]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight, varList,
        Turing.PartrecToTM2.Λ'.encodeLabel_read,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        Turing.PartrecToTM2.Λ'.decodeReadPayload_readPayloadCode,
        hprev (f none) h₀, hprev (f (some Γ'.consₗ)) h₁,
        hprev (f (some Γ'.cons)) h₂, hprev (f (some Γ'.bit0)) h₃,
        hprev (f (some Γ'.bit1)) h₄]
      rw [show
        wCode
            (8 *
                Turing.PartrecToTM2.Λ'.readPayloadCode
                  (Turing.PartrecToTM2.Λ'.encodeLabel (f none))
                  (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.consₗ)))
                  (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.cons)))
                  (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit0)))
                  (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit1))) + 5) =
          w (Λ'.read f) by
        simpa [Turing.PartrecToTM2.Λ'.encodeLabel_read] using hwCode (Λ'.read f)]
      simp [PartrecToTM2Support.stackAlphabetList]
  | succ q =>
      have hq : Turing.PartrecToTM2.Λ'.encodeLabel q <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.succ q) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_succ]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_succ,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        unrevCodeOf_encodeLabel, hprev q hq]
      rw [show wCode (8 * Turing.PartrecToTM2.Λ'.encodeLabel q + 6) = w (Λ'.succ q) by
        simpa [Turing.PartrecToTM2.Λ'.encodeLabel_succ] using hwCode (Λ'.succ q)]
      rw [hwCode (unrev q)]
  | pred q₁ q₂ =>
      have hpayload := Turing.PartrecToTM2.Λ'.predPayloadCode_max_le
        (Turing.PartrecToTM2.Λ'.encodeLabel q₁) (Turing.PartrecToTM2.Λ'.encodeLabel q₂)
      have h₁ : Turing.PartrecToTM2.Λ'.encodeLabel q₁ <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.pred q₁ q₂) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_pred]
        omega
      have h₂ : Turing.PartrecToTM2.Λ'.encodeLabel q₂ <
          Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.pred q₁ q₂) := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_pred]
        omega
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_pred,
        Turing.PartrecToTM2.Λ'.div_eight_mul_add_of_lt,
        Turing.PartrecToTM2.Λ'.decodePredPayload_predPayloadCode,
        unrevCodeOf_encodeLabel, hprev q₁ h₁, hprev q₂ h₂]
      rw [show
        wCode (8 * Turing.PartrecToTM2.Λ'.predPayloadCode
          (Turing.PartrecToTM2.Λ'.encodeLabel q₁) (Turing.PartrecToTM2.Λ'.encodeLabel q₂) + 7) =
          w (Λ'.pred q₁ q₂) by
        simpa [Turing.PartrecToTM2.Λ'.encodeLabel_pred] using hwCode (Λ'.pred q₁ q₂)]
      rw [hwCode (unrev q₂)]
  | ret k =>
      simp [trStmtsWeightStepBody, trStmtsWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_ret]
      simpa [Turing.PartrecToTM2.Λ'.encodeLabel_ret] using hwCode (Λ'.ret k)

/-- Read a previous row of label weights, defaulting to `0` outside the row. -/
def trStmtsWeightLookup (prev : List Nat) (n : Nat) : Nat :=
  prev.getD n 0

theorem trStmtsWeightLookup_primrec :
    Primrec (fun p : List Nat × Nat => trStmtsWeightLookup p.1 p.2) := by
  unfold trStmtsWeightLookup
  exact Primrec.list_getD 0

/-- One bounded row update for the dense-code `trStmtsWeight` recursion. -/
def trStmtsWeightRowStep (wCode : Nat → Nat) (prev : List Nat) (bound : Nat) : List Nat :=
  (List.range (bound + 1)).map fun n => trStmtsWeightStepBody wCode prev n

theorem trStmtsWeightRowStep_primrec {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : List Nat × Nat => trStmtsWeightRowStep wCode p.1 p.2) := by
  unfold trStmtsWeightRowStep
  let hrow : Primrec (fun p : List Nat × Nat => List.range (p.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  let hentry : Primrec₂ (fun p : List Nat × Nat => fun n : Nat =>
      trStmtsWeightStepBody wCode p.1 n) :=
    (trStmtsWeightStepBody_primrec hw).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd) |>.to₂
  exact Primrec.list_map hrow hentry

/-- Bounded dynamic-programming rows for dense-code `trStmtsWeight`. -/
def trStmtsWeightRows (wCode : Nat → Nat) : Nat → Nat → List Nat
  | 0, bound => (List.range (bound + 1)).map fun _ => 0
  | fuel + 1, bound => trStmtsWeightRowStep wCode (trStmtsWeightRows wCode fuel bound) bound

theorem trStmtsWeightRows_primrec {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : Nat × Nat => trStmtsWeightRows wCode p.1 p.2) := by
  let hbase : Primrec (fun p : Nat × Nat => (List.range (p.2 + 1)).map fun _ => 0) := by
    let hrow : Primrec (fun p : Nat × Nat => List.range (p.2 + 1)) :=
      Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
    exact Primrec.list_map hrow (Primrec.const 0).to₂
  let hstep : Primrec₂ (fun p : Nat × Nat => fun s : Nat × List Nat =>
      trStmtsWeightRowStep wCode s.2 p.2) :=
    (trStmtsWeightRowStep_primrec hw).comp
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)) |>.to₂
  exact (Primrec.nat_rec' Primrec.fst hbase hstep).of_eq fun p => by
    induction p.1 with
    | zero =>
        rfl
    | succ fuel ih =>
        change trStmtsWeightRowStep wCode
          (Nat.rec ((List.range (p.2 + 1)).map fun _ => 0)
            (fun _ row => trStmtsWeightRowStep wCode row p.2) fuel) p.2 =
          trStmtsWeightRows wCode (fuel + 1) p.2
        rw [ih]
        rfl

theorem trStmtsWeightRowStep_getD
    (wCode : Nat → Nat) (prev : List Nat) {bound n : Nat} (hn : n ≤ bound) :
    (trStmtsWeightRowStep wCode prev bound).getD n 0 =
      trStmtsWeightStepBody wCode prev n := by
  unfold trStmtsWeightRowStep
  have hlt :
      n < ((List.range (bound + 1)).map fun n => trStmtsWeightStepBody wCode prev n).length := by
    simpa [List.length_map, List.length_range] using Nat.lt_succ_of_le hn
  rw [List.getD_eq_getElem
    (l := (List.range (bound + 1)).map fun n => trStmtsWeightStepBody wCode prev n)
    (d := 0) hlt]
  simp

/-- Numeric fuel approximation to `trStmtsWeight`, indexed by dense label code. -/
def trStmtsWeightFuel (wCode : Nat → Nat) (fuel n : Nat) : Nat :=
  trStmtsWeightLookup (trStmtsWeightRows wCode fuel n) n

/-- The diagonal row lookup is definitionally the direct fuel recursion. -/
theorem trStmtsWeightRows_diagonal_getD_eq_fuel
    (wCode : Nat → Nat) (fuel n : Nat) :
    (trStmtsWeightRows wCode fuel n).getD n 0 =
      trStmtsWeightFuel wCode fuel n := by
  rfl

theorem encodeLabel_pos (q : Λ') : 0 < Turing.PartrecToTM2.Λ'.encodeLabel q := by
  cases q <;> simp [Turing.PartrecToTM2.Λ'.encodeLabel_move,
    Turing.PartrecToTM2.Λ'.encodeLabel_clear,
    Turing.PartrecToTM2.Λ'.encodeLabel_copy,
    Turing.PartrecToTM2.Λ'.encodeLabel_push,
    Turing.PartrecToTM2.Λ'.encodeLabel_read,
    Turing.PartrecToTM2.Λ'.encodeLabel_succ,
    Turing.PartrecToTM2.Λ'.encodeLabel_pred,
    Turing.PartrecToTM2.Λ'.encodeLabel_ret]

theorem trStmtsWeightRows_getD_encodeLabel
    (w : Λ' → Nat) (wCode : Nat → Nat)
    (hwCode : ∀ q : Λ', wCode (Turing.PartrecToTM2.Λ'.encodeLabel q) = w q)
    {fuel bound : Nat} {q : Λ'}
    (hfuel : Turing.PartrecToTM2.Λ'.encodeLabel q ≤ fuel)
    (hbound : Turing.PartrecToTM2.Λ'.encodeLabel q ≤ bound) :
    (trStmtsWeightRows wCode fuel bound).getD
        (Turing.PartrecToTM2.Λ'.encodeLabel q) 0 = trStmtsWeight w q := by
  induction fuel generalizing bound q with
  | zero =>
      have hpos := encodeLabel_pos q
      omega
  | succ fuel ih =>
      unfold trStmtsWeightRows
      rw [trStmtsWeightRowStep_getD wCode (trStmtsWeightRows wCode fuel bound) hbound]
      refine trStmtsWeightStepBody_encodeLabel w wCode hwCode
        (trStmtsWeightRows wCode fuel bound) q ?_
      intro r hr
      exact ih (by omega) (by omega)

theorem trStmtsWeightFuel_primrec {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : Nat × Nat => trStmtsWeightFuel wCode p.1 p.2) := by
  unfold trStmtsWeightFuel
  exact trStmtsWeightLookup_primrec.comp
    (Primrec.pair (trStmtsWeightRows_primrec hw) Primrec.snd)

/-- Diagonal dense-code approximation to `trStmtsWeight`. -/
def trStmtsWeightCode (wCode : Nat → Nat) (n : Nat) : Nat :=
  trStmtsWeightFuel wCode n n

theorem trStmtsWeightCode_primrec {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (trStmtsWeightCode wCode) := by
  unfold trStmtsWeightCode
  exact trStmtsWeightFuel_primrec hw |>.comp (Primrec.pair Primrec.id Primrec.id)

theorem trStmtsWeightCode_encodeLabel
    (w : Λ' → Nat) (wCode : Nat → Nat)
    (hwCode : ∀ q : Λ', wCode (Turing.PartrecToTM2.Λ'.encodeLabel q) = w q)
    (q : Λ') :
    trStmtsWeightCode wCode (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      trStmtsWeight w q := by
  simpa [trStmtsWeightCode, trStmtsWeightFuel, trStmtsWeightLookup] using
    (trStmtsWeightRows_getD_encodeLabel (w := w) (wCode := wCode) hwCode
      (fuel := Turing.PartrecToTM2.Λ'.encodeLabel q)
      (bound := Turing.PartrecToTM2.Λ'.encodeLabel q)
      (q := q) le_rfl le_rfl)

/-- Encoded `Λ'.move` constructor from an already encoded target label. -/
def moveLabelCode (p : Γ' → Bool) (k₁ k₂ : K') (qCode : Nat) : Nat :=
  8 * Turing.PartrecToTM2.Λ'.movePayloadCode p k₁ k₂ qCode + 1

theorem moveLabelCode_primrec (p : Γ' → Bool) (k₁ k₂ : K') :
    Primrec (moveLabelCode p k₁ k₂) := by
  unfold moveLabelCode
  have hpayload : Primrec (fun qCode : Nat =>
      Turing.PartrecToTM2.Λ'.movePayloadCode p k₁ k₂ qCode) := by
    exact Turing.PartrecToTM2.Λ'.movePayloadCode_primrec.comp
      (Primrec.pair (Primrec.const p)
        (Primrec.pair (Primrec.const k₁) (Primrec.pair (Primrec.const k₂) Primrec.id)))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) hpayload) (Primrec.const 1)

theorem moveLabelCode_encodeLabel (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ') :
    moveLabelCode p k₁ k₂ (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.move p k₁ k₂ q) := by
  simp [moveLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_move]

/-- Encoded `Λ'.clear` constructor from an already encoded target label. -/
def clearLabelCode (p : Γ' → Bool) (k : K') (qCode : Nat) : Nat :=
  8 * Turing.PartrecToTM2.Λ'.clearPayloadCode p k qCode + 2

theorem clearLabelCode_primrec (p : Γ' → Bool) (k : K') :
    Primrec (clearLabelCode p k) := by
  unfold clearLabelCode
  have hpayload : Primrec (fun qCode : Nat =>
      Turing.PartrecToTM2.Λ'.clearPayloadCode p k qCode) := by
    exact Turing.PartrecToTM2.Λ'.clearPayloadCode_primrec.comp
      (Primrec.pair (Primrec.const p) (Primrec.pair (Primrec.const k) Primrec.id))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) hpayload) (Primrec.const 2)

theorem clearLabelCode_encodeLabel (p : Γ' → Bool) (k : K') (q : Λ') :
    clearLabelCode p k (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.clear p k q) := by
  simp [clearLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_clear]

/-- Encoded `Λ'.copy` constructor from an already encoded target label. -/
def copyLabelCode (qCode : Nat) : Nat :=
  8 * qCode + 3

theorem copyLabelCode_primrec : Primrec copyLabelCode := by
  unfold copyLabelCode
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) Primrec.id) (Primrec.const 3)

theorem copyLabelCode_encodeLabel (q : Λ') :
    copyLabelCode (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.copy q) := by
  simp [copyLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_copy]

/-- Encoded `Λ'.push` constructor from an already encoded target label. -/
def pushLabelCode (k : K') (f : Option Γ' → Option Γ') (qCode : Nat) : Nat :=
  8 * Turing.PartrecToTM2.Λ'.pushPayloadCode k f qCode + 4

theorem pushLabelCode_primrec (k : K') (f : Option Γ' → Option Γ') :
    Primrec (pushLabelCode k f) := by
  unfold pushLabelCode
  have hpayload : Primrec (fun qCode : Nat =>
      Turing.PartrecToTM2.Λ'.pushPayloadCode k f qCode) := by
    exact Turing.PartrecToTM2.Λ'.pushPayloadCode_primrec.comp
      (Primrec.pair (Primrec.const k) (Primrec.pair (Primrec.const f) Primrec.id))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) hpayload) (Primrec.const 4)

theorem pushLabelCode_encodeLabel (k : K') (f : Option Γ' → Option Γ') (q : Λ') :
    pushLabelCode k f (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.push k f q) := by
  simp [pushLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_push]

/-- Encoded `Λ'.read` constructor from the five already encoded branch labels. -/
def readLabelCode (q₀ q₁ q₂ q₃ q₄ : Nat) : Nat :=
  8 * Turing.PartrecToTM2.Λ'.readPayloadCode q₀ q₁ q₂ q₃ q₄ + 5

theorem readLabelCode_primrec :
    Primrec (fun p : Nat × Nat × Nat × Nat × Nat =>
      readLabelCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold readLabelCode
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) Turing.PartrecToTM2.Λ'.readPayloadCode_primrec)
    (Primrec.const 5)

theorem readLabelCode_encodeLabel (f : Option Γ' → Λ') :
    readLabelCode (Turing.PartrecToTM2.Λ'.encodeLabel (f none))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.consₗ)))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.cons)))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit0)))
        (Turing.PartrecToTM2.Λ'.encodeLabel (f (some Γ'.bit1))) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read f) := by
  simp [readLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_read]

/-- Encoded `Λ'.succ` constructor from an already encoded target label. -/
def succLabelCode (qCode : Nat) : Nat :=
  8 * qCode + 6

theorem succLabelCode_primrec : Primrec succLabelCode := by
  unfold succLabelCode
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) Primrec.id) (Primrec.const 6)

theorem succLabelCode_encodeLabel (q : Λ') :
    succLabelCode (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.succ q) := by
  simp [succLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_succ]

/-- Encoded `Λ'.pred` constructor from two already encoded target labels. -/
def predLabelCode (q₁Code q₂Code : Nat) : Nat :=
  8 * Turing.PartrecToTM2.Λ'.predPayloadCode q₁Code q₂Code + 7

theorem predLabelCode_primrec :
    Primrec (fun p : Nat × Nat => predLabelCode p.1 p.2) := by
  unfold predLabelCode
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) Turing.PartrecToTM2.Λ'.predPayloadCode_primrec)
    (Primrec.const 7)

theorem predLabelCode_encodeLabel (q₁ q₂ : Λ') :
    predLabelCode (Turing.PartrecToTM2.Λ'.encodeLabel q₁)
        (Turing.PartrecToTM2.Λ'.encodeLabel q₂) =
      Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.pred q₁ q₂) := by
  simp [predLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_pred]

/-- Encoded `Λ'.ret` constructor. -/
def retLabelCode (k : Cont') : Nat :=
  8 * Turing.PartrecToTM2.Cont'.encodeCont k + 8

theorem retLabelCode_primrec : Primrec retLabelCode := by
  unfold retLabelCode
  have henc : Primrec (fun k : Cont' => Turing.PartrecToTM2.Cont'.encodeCont k) :=
    (Primrec.encode).of_eq fun k => by
      rw [Turing.PartrecToTM2.Cont'.encodeCont_eq]
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) henc) (Primrec.const 8)

theorem retLabelCode_encodeLabel (k : Cont') :
    retLabelCode k = Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.ret k) := by
  simp [retLabelCode, Turing.PartrecToTM2.Λ'.encodeLabel_ret]

/-- Encoded `move₂` from Mathlib's `PartrecToTM2` evaluator. -/
def move₂LabelCode (p : Γ' → Bool) (k₁ k₂ : K') (qCode : Nat) : Nat :=
  moveLabelCode p k₁ K'.rev
    (pushLabelCode k₁ id
      (moveLabelCode (fun _ : Γ' => false) K'.rev k₂ qCode))

theorem move₂LabelCode_primrec (p : Γ' → Bool) (k₁ k₂ : K') :
    Primrec (move₂LabelCode p k₁ k₂) := by
  unfold move₂LabelCode
  exact (moveLabelCode_primrec p k₁ K'.rev).comp
    ((pushLabelCode_primrec k₁ id).comp
      ((moveLabelCode_primrec (fun _ : Γ' => false) K'.rev k₂)))

theorem move₂LabelCode_encodeLabel (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ') :
    move₂LabelCode p k₁ k₂ (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (move₂ p k₁ k₂ q) := by
  simp [move₂LabelCode, Turing.PartrecToTM2.move₂, Turing.PartrecToTM2.moveExcl,
    moveLabelCode_encodeLabel, pushLabelCode_encodeLabel]

/-- Encoded `head` helper from Mathlib's `PartrecToTM2` evaluator. -/
def headLabelCode (k : K') (qCode : Nat) : Nat :=
  let unrevCode := unrevCodeOf qCode
  let clearCode := clearLabelCode (fun x : Γ' => x = Γ'.consₗ) k unrevCode
  moveLabelCode natEnd k K'.rev <|
    pushLabelCode K'.rev (fun _ : Option Γ' => some Γ'.cons) <|
      readLabelCode clearCode unrevCode clearCode clearCode clearCode

set_option maxHeartbeats 800000 in
-- The explicit five-branch `read` expression makes the composed primrec proof large.
theorem headLabelCode_primrec (k : K') :
    Primrec (headLabelCode k) := by
  unfold headLabelCode
  let hunrev : Primrec (fun qCode : Nat => unrevCodeOf qCode) := unrevCodeOf_primrec
  let hclear : Primrec (fun qCode : Nat =>
      clearLabelCode (fun x : Γ' => x = Γ'.consₗ) k (unrevCodeOf qCode)) :=
    (clearLabelCode_primrec (fun x : Γ' => x = Γ'.consₗ) k).comp hunrev
  let hread : Primrec (fun qCode : Nat =>
      readLabelCode
        (clearLabelCode (fun x : Γ' => x = Γ'.consₗ) k (unrevCodeOf qCode))
        (unrevCodeOf qCode)
        (clearLabelCode (fun x : Γ' => x = Γ'.consₗ) k (unrevCodeOf qCode))
        (clearLabelCode (fun x : Γ' => x = Γ'.consₗ) k (unrevCodeOf qCode))
        (clearLabelCode (fun x : Γ' => x = Γ'.consₗ) k (unrevCodeOf qCode))) := by
    exact readLabelCode_primrec.comp
      (Primrec.pair hclear (Primrec.pair hunrev
        (Primrec.pair hclear (Primrec.pair hclear hclear))))
  exact (moveLabelCode_primrec natEnd k K'.rev).comp
    ((pushLabelCode_primrec K'.rev (fun _ : Option Γ' => some Γ'.cons)).comp hread)

set_option linter.flexible false in
theorem headLabelCode_encodeLabel (k : K') (q : Λ') :
    headLabelCode k (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      Turing.PartrecToTM2.Λ'.encodeLabel (head k q) := by
  let uq : Λ' := unrev q
  let cq : Λ' := Λ'.clear (fun x : Γ' => x = Γ'.consₗ) k uq
  let rf : Option Γ' → Λ'
    | none => cq
    | some Γ'.consₗ => uq
    | some Γ'.cons => cq
    | some Γ'.bit0 => cq
    | some Γ'.bit1 => cq
  have hread :
      readLabelCode (Turing.PartrecToTM2.Λ'.encodeLabel cq)
          (Turing.PartrecToTM2.Λ'.encodeLabel uq)
          (Turing.PartrecToTM2.Λ'.encodeLabel cq)
          (Turing.PartrecToTM2.Λ'.encodeLabel cq)
          (Turing.PartrecToTM2.Λ'.encodeLabel cq) =
        Turing.PartrecToTM2.Λ'.encodeLabel (Λ'.read rf) := by
    simpa [rf] using readLabelCode_encodeLabel rf
  unfold headLabelCode
  rw [unrevCodeOf_encodeLabel]
  change moveLabelCode natEnd k K'.rev
      (pushLabelCode K'.rev (fun _ : Option Γ' => some Γ'.cons)
        (readLabelCode (Turing.PartrecToTM2.Λ'.encodeLabel cq)
          (Turing.PartrecToTM2.Λ'.encodeLabel uq)
          (Turing.PartrecToTM2.Λ'.encodeLabel cq)
          (Turing.PartrecToTM2.Λ'.encodeLabel cq)
          (Turing.PartrecToTM2.Λ'.encodeLabel cq))) =
    Turing.PartrecToTM2.Λ'.encodeLabel (head k q)
  rw [hread, pushLabelCode_encodeLabel, moveLabelCode_encodeLabel]
  apply congrArg Turing.PartrecToTM2.Λ'.encodeLabel
  simp [Turing.PartrecToTM2.head, Turing.PartrecToTM2.unrev, uq, cq, rf]
  funext s
  cases s with
  | none => rfl
  | some a => cases a <;> rfl

/-- Encoded `trNormal` labels for Mathlib's `PartrecToTM2` evaluator. -/
def trNormalLabelCode : ToPartrec.Code → Cont' → Nat
  | ToPartrec.Code.zero', k =>
      pushLabelCode K'.main (fun _ : Option Γ' => some Γ'.cons) (retLabelCode k)
  | ToPartrec.Code.succ, k =>
      headLabelCode K'.main (succLabelCode (retLabelCode k))
  | ToPartrec.Code.tail, k =>
      clearLabelCode natEnd K'.main (retLabelCode k)
  | ToPartrec.Code.cons f fs, k =>
      pushLabelCode K'.stack (fun _ : Option Γ' => some Γ'.consₗ) <|
        moveLabelCode (fun _ : Γ' => false) K'.main K'.rev <|
          copyLabelCode <| trNormalLabelCode f (Cont'.cons₁ fs k)
  | ToPartrec.Code.comp f g, k =>
      trNormalLabelCode g (Cont'.comp f k)
  | ToPartrec.Code.case f g, k =>
      predLabelCode (trNormalLabelCode f k) (trNormalLabelCode g k)
  | ToPartrec.Code.fix f, k =>
      trNormalLabelCode f (Cont'.fix f k)

theorem trNormalLabelCode_encodeLabel (c : ToPartrec.Code) (k : Cont') :
    trNormalLabelCode c k =
      Turing.PartrecToTM2.Λ'.encodeLabel (trNormal c k) := by
  induction c generalizing k with
  | zero' =>
      simp [trNormalLabelCode, pushLabelCode_encodeLabel, retLabelCode_encodeLabel]
  | succ =>
      simp [trNormalLabelCode, headLabelCode_encodeLabel, succLabelCode_encodeLabel,
        retLabelCode_encodeLabel]
  | tail =>
      simp [trNormalLabelCode, clearLabelCode_encodeLabel, retLabelCode_encodeLabel]
  | cons f fs ihf ihfs =>
      simp [trNormalLabelCode, Turing.PartrecToTM2.trNormal, pushLabelCode_encodeLabel,
        moveLabelCode_encodeLabel, copyLabelCode_encodeLabel, ihf]
  | comp f g ihf ihg =>
      simp [trNormalLabelCode, Turing.PartrecToTM2.trNormal, ihg]
  | case f g ihf ihg =>
      simp [trNormalLabelCode, Turing.PartrecToTM2.trNormal, predLabelCode_encodeLabel,
        ihf, ihg]
  | fix f ih =>
      simp [trNormalLabelCode, Turing.PartrecToTM2.trNormal, ih]

/--
Fuelled encoded `trNormal` labels.

The fuel is a depth bound on the source code. Insufficient fuel returns `0`;
`trNormalLabelCodeFuel_eq` below shows that `ToPartrec.Code.depth` is enough.
-/
def trNormalLabelCodeFuel : Nat → ToPartrec.Code → Cont' → Nat
  | 0, _, _ => 0
  | _ + 1, ToPartrec.Code.zero', k =>
      pushLabelCode K'.main (fun _ : Option Γ' => some Γ'.cons) (retLabelCode k)
  | _ + 1, ToPartrec.Code.succ, k =>
      headLabelCode K'.main (succLabelCode (retLabelCode k))
  | _ + 1, ToPartrec.Code.tail, k =>
      clearLabelCode natEnd K'.main (retLabelCode k)
  | fuel + 1, ToPartrec.Code.cons f fs, k =>
      pushLabelCode K'.stack (fun _ : Option Γ' => some Γ'.consₗ) <|
        moveLabelCode (fun _ : Γ' => false) K'.main K'.rev <|
          copyLabelCode <| trNormalLabelCodeFuel fuel f (Cont'.cons₁ fs k)
  | fuel + 1, ToPartrec.Code.comp f g, k =>
      trNormalLabelCodeFuel fuel g (Cont'.comp f k)
  | fuel + 1, ToPartrec.Code.case f g, k =>
      predLabelCode (trNormalLabelCodeFuel fuel f k) (trNormalLabelCodeFuel fuel g k)
  | fuel + 1, ToPartrec.Code.fix f, k =>
      trNormalLabelCodeFuel fuel f (Cont'.fix f k)

theorem trNormalLabelCodeFuel_eq
    {fuel : Nat} (h : ToPartrec.Code.depth c ≤ fuel) :
    trNormalLabelCodeFuel fuel c k = trNormalLabelCode c k := by
  induction c generalizing fuel k with
  | zero' =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos ToPartrec.Code.zero'
          omega
      | succ fuel =>
          simp [trNormalLabelCodeFuel, trNormalLabelCode]
  | succ =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos ToPartrec.Code.succ
          omega
      | succ fuel =>
          simp [trNormalLabelCodeFuel, trNormalLabelCode]
  | tail =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos ToPartrec.Code.tail
          omega
      | succ fuel =>
          simp [trNormalLabelCodeFuel, trNormalLabelCode]
  | cons f fs ihf ihfs =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.cons f fs)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_left_lt_cons f fs
            omega
          simp [trNormalLabelCodeFuel, trNormalLabelCode, ihf hf]
  | comp f g ihf ihg =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.comp f g)
          omega
      | succ fuel =>
          have hg : ToPartrec.Code.depth g ≤ fuel := by
            have hlt := ToPartrec.Code.depth_right_lt_comp f g
            omega
          simp [trNormalLabelCodeFuel, trNormalLabelCode, ihg hg]
  | case f g ihf ihg =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.case f g)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_left_lt_case f g
            omega
          have hg : ToPartrec.Code.depth g ≤ fuel := by
            have hlt := ToPartrec.Code.depth_right_lt_case f g
            omega
          simp [trNormalLabelCodeFuel, trNormalLabelCode, ihf hf, ihg hg]
  | fix f ih =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.fix f)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_lt_fix f
            omega
          simp [trNormalLabelCodeFuel, trNormalLabelCode, ih hf]

theorem trNormalLabelCodeFuel_encodeCode_eq (c : ToPartrec.Code) (k : Cont') :
    trNormalLabelCodeFuel (ToPartrec.Code.encodeCode c + 1) c k =
      trNormalLabelCode c k :=
  trNormalLabelCodeFuel_eq (ToPartrec.Code.depth_le_encodeCode_succ c)

/-- Encoded state used by row computations over `(source code, continuation)` pairs. -/
def codeContStateCode (c : ToPartrec.Code) (k : Cont') : Nat :=
  Nat.pair (ToPartrec.Code.encodeCode c) (Turing.PartrecToTM2.Cont'.encodeCont k)

theorem codeContStateCode_primrec :
    Primrec (fun p : ToPartrec.Code × Cont' => codeContStateCode p.1 p.2) := by
  unfold codeContStateCode
  have hcode : Primrec (fun c : ToPartrec.Code => ToPartrec.Code.encodeCode c) :=
    (Primrec.encode).of_eq fun c => by rw [ToPartrec.Code.encodeCode_eq]
  have hcont : Primrec (fun k : Cont' => Turing.PartrecToTM2.Cont'.encodeCont k) :=
    (Primrec.encode).of_eq fun k => by rw [Turing.PartrecToTM2.Cont'.encodeCont_eq]
  exact Primrec₂.natPair.comp (hcode.comp Primrec.fst) (hcont.comp Primrec.snd)

/-- A square bound for every state code with bounded source-code and continuation codes. -/
def codeContStateBound (codeBound contBound : Nat) : Nat :=
  (max codeBound contBound + 1) ^ 2

theorem codeContStateBound_primrec :
    Primrec (fun p : Nat × Nat => codeContStateBound p.1 p.2) := by
  unfold codeContStateBound
  have hpow : Primrec₂ (fun a b : Nat => a ^ b) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact hpow.comp
    (Primrec.succ.comp (Primrec.nat_max.comp Primrec.fst Primrec.snd))
    (Primrec.const 2)

theorem codeContStateCode_lt_bound
    {c : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hcode : ToPartrec.Code.encodeCode c ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode c k < codeContStateBound codeBound contBound := by
  unfold codeContStateCode codeContStateBound
  exact lt_of_lt_of_le
    (Nat.pair_lt_max_add_one_sq
      (ToPartrec.Code.encodeCode c) (Turing.PartrecToTM2.Cont'.encodeCont k))
    (by
      have hle := Nat.succ_le_succ (max_le_max hcode hcont)
      simpa [Nat.pow_two] using Nat.mul_le_mul hle hle)

/-- One coarse growth step for continuations produced by recursive evaluator calls. -/
def contEncodeBoundStep (codeBound contBound : Nat) : Nat :=
  4 * codeContStateBound codeBound contBound + 4

theorem contBound_le_boundStep (codeBound contBound : Nat) :
    contBound ≤ contEncodeBoundStep codeBound contBound := by
  have hcont_bound : contBound ≤ codeContStateBound codeBound contBound := by
    unfold codeContStateBound
    rw [Nat.pow_two]
    exact (le_max_right codeBound contBound).trans
      ((Nat.le_succ (max codeBound contBound)).trans (Nat.le_mul_self _))
  unfold contEncodeBoundStep
  omega

theorem encodeCont_cons₁_le_boundStep
    {fs : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hcode : ToPartrec.Code.encodeCode fs ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    Turing.PartrecToTM2.Cont'.encodeCont (Cont'.cons₁ fs k) ≤
      contEncodeBoundStep codeBound contBound := by
  have hpair := codeContStateCode_lt_bound (c := fs) (k := k) hcode hcont
  unfold codeContStateCode at hpair
  unfold contEncodeBoundStep
  simp [Turing.PartrecToTM2.Cont'.encodeCont, Nat.bit_val]
  omega

theorem encodeCont_cons₂_le_boundStep
    {k : Cont'} {codeBound contBound : Nat}
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    Turing.PartrecToTM2.Cont'.encodeCont (Cont'.cons₂ k) ≤
      contEncodeBoundStep codeBound contBound := by
  have hcont_bound : contBound ≤ codeContStateBound codeBound contBound := by
    unfold codeContStateBound
    rw [Nat.pow_two]
    exact (le_max_right codeBound contBound).trans
      ((Nat.le_succ (max codeBound contBound)).trans (Nat.le_mul_self _))
  unfold contEncodeBoundStep
  simp [Turing.PartrecToTM2.Cont'.encodeCont, Nat.bit_val]
  omega

theorem encodeCont_comp_le_boundStep
    {f : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hcode : ToPartrec.Code.encodeCode f ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    Turing.PartrecToTM2.Cont'.encodeCont (Cont'.comp f k) ≤
      contEncodeBoundStep codeBound contBound := by
  have hpair := codeContStateCode_lt_bound (c := f) (k := k) hcode hcont
  unfold codeContStateCode at hpair
  unfold contEncodeBoundStep
  simp [Turing.PartrecToTM2.Cont'.encodeCont, Nat.bit_val]
  omega

theorem encodeCont_fix_le_boundStep
    {f : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hcode : ToPartrec.Code.encodeCode f ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    Turing.PartrecToTM2.Cont'.encodeCont (Cont'.fix f k) ≤
      contEncodeBoundStep codeBound contBound := by
  have hpair := codeContStateCode_lt_bound (c := f) (k := k) hcode hcont
  unfold codeContStateCode at hpair
  unfold contEncodeBoundStep
  simp [Turing.PartrecToTM2.Cont'.encodeCont, Nat.bit_val]
  omega

/-- Iterated coarse continuation bound for all continuations reachable within `fuel` calls. -/
def contEncodeFuelBound (fuel codeBound contBound : Nat) : Nat :=
  Nat.rec contBound (fun _ bound => contEncodeBoundStep codeBound bound) fuel

theorem contEncodeBoundStep_primrec :
    Primrec (fun p : Nat × Nat => contEncodeBoundStep p.1 p.2) := by
  unfold contEncodeBoundStep codeContStateBound
  have hpow : Primrec₂ (fun a b : Nat => a ^ b) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4)
      (hpow.comp
        (Primrec.succ.comp (Primrec.nat_max.comp Primrec.fst Primrec.snd))
        (Primrec.const 2)))
    (Primrec.const 4)

theorem contEncodeFuelBound_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => contEncodeFuelBound p.1.1 p.1.2 p.2) := by
  let hbase : Primrec (fun p : (Nat × Nat) × Nat => p.2) := Primrec.snd
  let hstep : Primrec₂ (fun p : (Nat × Nat) × Nat => fun s : Nat × Nat =>
      contEncodeBoundStep p.1.2 s.2) := by
    apply Primrec₂.mk
    exact contEncodeBoundStep_primrec.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
  exact Primrec.nat_rec' (Primrec.fst.comp Primrec.fst) hbase hstep

theorem childState_cons_left_lt_boundStep
    {f fs : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.cons f fs) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode f (Cont'.cons₁ fs k) <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_left_le_cons f fs).trans hparent
  · exact encodeCont_cons₁_le_boundStep
      ((ToPartrec.Code.encodeCode_right_le_cons f fs).trans hparent) hcont

theorem childState_cons_right_lt_boundStep
    {f fs : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.cons f fs) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode fs (Cont'.cons₂ k) <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_right_le_cons f fs).trans hparent
  · exact encodeCont_cons₂_le_boundStep hcont

theorem childState_comp_right_lt_boundStep
    {f g : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.comp f g) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode g (Cont'.comp f k) <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_right_le_comp f g).trans hparent
  · exact encodeCont_comp_le_boundStep
      ((ToPartrec.Code.encodeCode_left_le_comp f g).trans hparent) hcont

theorem childState_comp_left_lt_boundStep
    {f g : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.comp f g) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode f k <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_left_le_comp f g).trans hparent
  · exact hcont.trans (contBound_le_boundStep codeBound contBound)

theorem childState_case_left_lt_boundStep
    {f g : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.case f g) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode f k <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_left_le_case f g).trans hparent
  · exact hcont.trans (contBound_le_boundStep codeBound contBound)

theorem childState_case_right_lt_boundStep
    {f g : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.case f g) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode g k <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_right_le_case f g).trans hparent
  · exact hcont.trans (contBound_le_boundStep codeBound contBound)

theorem childState_fix_lt_boundStep
    {f : ToPartrec.Code} {k : Cont'} {codeBound contBound : Nat}
    (hparent : ToPartrec.Code.encodeCode (ToPartrec.Code.fix f) ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeContStateCode f (Cont'.fix f k) <
      codeContStateBound codeBound (contEncodeBoundStep codeBound contBound) := by
  refine codeContStateCode_lt_bound ?_ ?_
  · exact (ToPartrec.Code.encodeCode_le_fix f).trans hparent
  · exact encodeCont_fix_le_boundStep
      ((ToPartrec.Code.encodeCode_le_fix f).trans hparent) hcont

/-- Decode a numeric row index into the `(source code, continuation)` state it names. -/
def codeContStateOfCode (n : Nat) : ToPartrec.Code × Cont' :=
  (ToPartrec.Code.ofNatCode n.unpair.1, Turing.PartrecToTM2.Cont'.ofNatCont n.unpair.2)

theorem codeContStateOfCode_primrec :
    Primrec codeContStateOfCode := by
  unfold codeContStateOfCode
  exact Primrec.pair
    (Primrec.ofNat ToPartrec.Code |>.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.ofNat Cont' |>.comp (Primrec.snd.comp Primrec.unpair))

theorem codeContStateOfCode_codeContStateCode (c : ToPartrec.Code) (k : Cont') :
    codeContStateOfCode (codeContStateCode c k) = (c, k) := by
  simp [codeContStateOfCode, codeContStateCode, ToPartrec.Code.ofNatCode_encodeCode,
    Turing.PartrecToTM2.Λ'.ofNatCont_encodeCont]

/-- Lookup a previous fuel row by encoded `(source code, continuation)` state. -/
def codeContStateLookup (prev : List Nat) (c : ToPartrec.Code) (k : Cont') : Nat :=
  prev.getD (codeContStateCode c k) 0

theorem codeContStateLookup_primrec :
    Primrec (fun p : List Nat × (ToPartrec.Code × Cont') =>
      codeContStateLookup p.1 p.2.1 p.2.2) := by
  unfold codeContStateLookup
  exact Primrec.list_getD 0 |>.comp Primrec.fst
    (codeContStateCode_primrec.comp Primrec.snd)

/-- One semantic row step for fuelled encoded `trNormal` labels. -/
def trNormalLabelCodeFuelStep (prev : List Nat) : ToPartrec.Code → Cont' → Nat
  | ToPartrec.Code.zero', k =>
      pushLabelCode K'.main (fun _ : Option Γ' => some Γ'.cons) (retLabelCode k)
  | ToPartrec.Code.succ, k =>
      headLabelCode K'.main (succLabelCode (retLabelCode k))
  | ToPartrec.Code.tail, k =>
      clearLabelCode natEnd K'.main (retLabelCode k)
  | ToPartrec.Code.cons f fs, k =>
      pushLabelCode K'.stack (fun _ : Option Γ' => some Γ'.consₗ) <|
        moveLabelCode (fun _ : Γ' => false) K'.main K'.rev <|
          copyLabelCode <| codeContStateLookup prev f (Cont'.cons₁ fs k)
  | ToPartrec.Code.comp f g, k =>
      codeContStateLookup prev g (Cont'.comp f k)
  | ToPartrec.Code.case f g, k =>
      predLabelCode (codeContStateLookup prev f k) (codeContStateLookup prev g k)
  | ToPartrec.Code.fix f, k =>
      codeContStateLookup prev f (Cont'.fix f k)

theorem trNormalLabelCodeFuelStep_eq
    {prev : List Nat} {fuel : Nat}
    (hprev : ∀ c k, codeContStateLookup prev c k = trNormalLabelCodeFuel fuel c k)
    (c : ToPartrec.Code) (k : Cont') :
    trNormalLabelCodeFuelStep prev c k = trNormalLabelCodeFuel (fuel + 1) c k := by
  cases c with
  | zero' =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel]
  | succ =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel]
  | tail =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel]
  | cons f fs =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel, hprev]
  | comp f g =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel, hprev]
  | case f g =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel, hprev]
  | fix f =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel, hprev]

theorem trNormalLabelCodeFuelStep_eq_of_bound
    {prev : List Nat} {fuel codeBound contBound : Nat}
    (hprev : ∀ c k,
      ToPartrec.Code.encodeCode c ≤ codeBound →
      Turing.PartrecToTM2.Cont'.encodeCont k ≤ contEncodeBoundStep codeBound contBound →
      codeContStateLookup prev c k = trNormalLabelCodeFuel fuel c k)
    {c : ToPartrec.Code} {k : Cont'}
    (hcode : ToPartrec.Code.encodeCode c ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    trNormalLabelCodeFuelStep prev c k = trNormalLabelCodeFuel (fuel + 1) c k := by
  cases c with
  | zero' =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel]
  | succ =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel]
  | tail =>
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel]
  | cons f fs =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_left_le_cons f fs).trans hcode
      have hfsCode : ToPartrec.Code.encodeCode fs ≤ codeBound :=
        (ToPartrec.Code.encodeCode_right_le_cons f fs).trans hcode
      have hchildCont :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.cons₁ fs k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_cons₁_le_boundStep hfsCode hcont
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel,
        hprev f (Cont'.cons₁ fs k) hfCode hchildCont]
  | comp f g =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_left_le_comp f g).trans hcode
      have hgCode : ToPartrec.Code.encodeCode g ≤ codeBound :=
        (ToPartrec.Code.encodeCode_right_le_comp f g).trans hcode
      have hchildCont :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.comp f k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_comp_le_boundStep hfCode hcont
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel,
        hprev g (Cont'.comp f k) hgCode hchildCont]
  | case f g =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_left_le_case f g).trans hcode
      have hgCode : ToPartrec.Code.encodeCode g ≤ codeBound :=
        (ToPartrec.Code.encodeCode_right_le_case f g).trans hcode
      have hchildCont :
          Turing.PartrecToTM2.Cont'.encodeCont k ≤
            contEncodeBoundStep codeBound contBound :=
        hcont.trans (contBound_le_boundStep codeBound contBound)
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel,
        hprev f k hfCode hchildCont, hprev g k hgCode hchildCont]
  | fix f =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_le_fix f).trans hcode
      have hchildCont :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.fix f k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_fix_le_boundStep hfCode hcont
      simp [trNormalLabelCodeFuelStep, trNormalLabelCodeFuel,
        hprev f (Cont'.fix f k) hfCode hchildCont]

/-- One bounded row of fuelled encoded `trNormal` labels. -/
def trNormalLabelCodeFuelRowStep (prev : List Nat) (bound : Nat) : List Nat :=
  (List.range (bound + 1)).map fun n =>
    let s := codeContStateOfCode n
    trNormalLabelCodeFuelStep prev s.1 s.2

theorem trNormalLabelCodeFuelRowStep_getD_eq
    {prev : List Nat} {fuel bound n : Nat}
    (hprev : ∀ c k, codeContStateLookup prev c k = trNormalLabelCodeFuel fuel c k)
    (hn : n ≤ bound) :
    (trNormalLabelCodeFuelRowStep prev bound).getD n 0 =
      trNormalLabelCodeFuel (fuel + 1) (codeContStateOfCode n).1
        (codeContStateOfCode n).2 := by
  unfold trNormalLabelCodeFuelRowStep
  have hlt :
      n < ((List.range (bound + 1)).map fun n =>
        let s := codeContStateOfCode n
        trNormalLabelCodeFuelStep prev s.1 s.2).length := by
    simp
    omega
  rw [List.getD_eq_getElem
    (l := (List.range (bound + 1)).map fun n =>
      let s := codeContStateOfCode n
      trNormalLabelCodeFuelStep prev s.1 s.2) (d := 0) hlt]
  simp only [List.getElem_map, List.getElem_range]
  exact trNormalLabelCodeFuelStep_eq hprev _ _

/-- Numeric version of `trNormalLabelCodeFuelStep`, dispatching on dense source-code tags. -/
def trNormalLabelCodeFuelStepCode (prev : List Nat) (cCode : Nat) (k : Cont') : Nat :=
  if cCode = 0 then
    pushLabelCode K'.main (fun _ : Option Γ' => some Γ'.cons) (retLabelCode k)
  else if cCode = 1 then
    headLabelCode K'.main (succLabelCode (retLabelCode k))
  else if cCode = 2 then
    clearLabelCode natEnd K'.main (retLabelCode k)
  else
    let n := cCode - 3
    let m := n.div2.div2
    let f := ToPartrec.Code.ofNatCode m.unpair.1
    let g := ToPartrec.Code.ofNatCode m.unpair.2
    match n.bodd, n.div2.bodd with
    | false, false =>
        pushLabelCode K'.stack (fun _ : Option Γ' => some Γ'.consₗ) <|
          moveLabelCode (fun _ : Γ' => false) K'.main K'.rev <|
            copyLabelCode <| codeContStateLookup prev f (Cont'.cons₁ g k)
    | false, true =>
        codeContStateLookup prev g (Cont'.comp f k)
    | true, false =>
        predLabelCode (codeContStateLookup prev f k) (codeContStateLookup prev g k)
    | true, true =>
        let f := ToPartrec.Code.ofNatCode m
        codeContStateLookup prev f (Cont'.fix f k)

theorem trNormalLabelCodeFuelStepCode_primrec :
    Primrec (fun p : List Nat × Nat × Cont' =>
      trNormalLabelCodeFuelStepCode p.1 p.2.1 p.2.2) := by
  unfold trNormalLabelCodeFuelStepCode
  let hcode : Primrec (fun p : List Nat × Nat × Cont' => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  let hk : Primrec (fun p : List Nat × Nat × Cont' => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  let hn : Primrec (fun p : List Nat × Nat × Cont' => p.2.1 - 3) :=
    Primrec.nat_sub.comp hcode (Primrec.const 3)
  let hm : Primrec (fun p : List Nat × Nat × Cont' => (p.2.1 - 3).div2.div2) :=
    Primrec.nat_div2.comp (Primrec.nat_div2.comp hn)
  let hm₁ : Primrec (fun p : List Nat × Nat × Cont' => ((p.2.1 - 3).div2.div2).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  let hm₂ : Primrec (fun p : List Nat × Nat × Cont' => ((p.2.1 - 3).div2.div2).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  let hf : Primrec (fun p : List Nat × Nat × Cont' =>
      ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) :=
    Primrec.ofNat ToPartrec.Code |>.comp hm₁
  let hg : Primrec (fun p : List Nat × Nat × Cont' =>
      ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) :=
    Primrec.ofNat ToPartrec.Code |>.comp hm₂
  let hsingle : Primrec (fun p : List Nat × Nat × Cont' =>
      ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) :=
    Primrec.ofNat ToPartrec.Code |>.comp hm
  let hret : Primrec (fun p : List Nat × Nat × Cont' => retLabelCode p.2.2) :=
    retLabelCode_primrec.comp hk
  let hzero : Primrec (fun p : List Nat × Nat × Cont' =>
      pushLabelCode K'.main (fun _ : Option Γ' => some Γ'.cons) (retLabelCode p.2.2)) :=
    (pushLabelCode_primrec K'.main (fun _ : Option Γ' => some Γ'.cons)).comp hret
  let hsucc : Primrec (fun p : List Nat × Nat × Cont' =>
      headLabelCode K'.main (succLabelCode (retLabelCode p.2.2))) :=
    (headLabelCode_primrec K'.main).comp (succLabelCode_primrec.comp hret)
  let htail : Primrec (fun p : List Nat × Nat × Cont' =>
      clearLabelCode natEnd K'.main (retLabelCode p.2.2)) :=
    (clearLabelCode_primrec natEnd K'.main).comp hret
  let hlookupFCons₁ : Primrec (fun p : List Nat × Nat × Cont' =>
      codeContStateLookup p.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1)
        (Cont'.cons₁
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) := by
    let hstate : Primrec (fun p : List Nat × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1,
          Cont'.cons₁
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) := by
      exact Primrec.pair hf ((Turing.PartrecToTM2.Cont'.primrec₂_cons₁).comp hg hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair Primrec.fst hstate)
  let hcons : Primrec (fun p : List Nat × Nat × Cont' =>
      pushLabelCode K'.stack (fun _ : Option Γ' => some Γ'.consₗ) <|
        moveLabelCode (fun _ : Γ' => false) K'.main K'.rev <|
          copyLabelCode <| codeContStateLookup p.1
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1)
            (Cont'.cons₁
              (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) :=
    (pushLabelCode_primrec K'.stack (fun _ : Option Γ' => some Γ'.consₗ)).comp
      ((moveLabelCode_primrec (fun _ : Γ' => false) K'.main K'.rev).comp
        (copyLabelCode_primrec.comp hlookupFCons₁))
  let hlookupGComp : Primrec (fun p : List Nat × Nat × Cont' =>
      codeContStateLookup p.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
        (Cont'.comp
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2)) := by
    let hstate : Primrec (fun p : List Nat × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2,
          Cont'.comp
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2)) := by
      exact Primrec.pair hg ((Turing.PartrecToTM2.Cont'.primrec₂_comp).comp hf hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair Primrec.fst hstate)
  let hlookupF : Primrec (fun p : List Nat × Nat × Cont' =>
      codeContStateLookup p.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2) := by
    let hstate : Primrec (fun p : List Nat × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1, p.2.2)) :=
      Primrec.pair hf hk
    exact codeContStateLookup_primrec.comp (Primrec.pair Primrec.fst hstate)
  let hlookupG : Primrec (fun p : List Nat × Nat × Cont' =>
      codeContStateLookup p.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2) := by
    let hstate : Primrec (fun p : List Nat × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2, p.2.2)) :=
      Primrec.pair hg hk
    exact codeContStateLookup_primrec.comp (Primrec.pair Primrec.fst hstate)
  let hcase : Primrec (fun p : List Nat × Nat × Cont' =>
      predLabelCode
        (codeContStateLookup p.1
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2)
        (codeContStateLookup p.1
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) :=
    predLabelCode_primrec.comp (Primrec.pair hlookupF hlookupG)
  let hlookupFFix : Primrec (fun p : List Nat × Nat × Cont' =>
      codeContStateLookup p.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2))
        (Cont'.fix
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) := by
    let hstate : Primrec (fun p : List Nat × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2),
          Cont'.fix
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) := by
      exact Primrec.pair hsingle ((Turing.PartrecToTM2.Cont'.primrec₂_fix).comp hsingle hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair Primrec.fst hstate)
  let htag₀ : PrimrecPred (fun p : List Nat × Nat × Cont' => p.2.1 = 0) :=
    Primrec.eq.comp hcode (Primrec.const 0)
  let htag₁ : PrimrecPred (fun p : List Nat × Nat × Cont' => p.2.1 = 1) :=
    Primrec.eq.comp hcode (Primrec.const 1)
  let htag₂ : PrimrecPred (fun p : List Nat × Nat × Cont' => p.2.1 = 2) :=
    Primrec.eq.comp hcode (Primrec.const 2)
  let hbodd : Primrec (fun p : List Nat × Nat × Cont' => (p.2.1 - 3).bodd) :=
    Primrec.nat_bodd.comp hn
  let hdiv2bodd : Primrec (fun p : List Nat × Nat × Cont' => ((p.2.1 - 3).div2).bodd) :=
    Primrec.nat_bodd.comp (Primrec.nat_div2.comp hn)
  refine Primrec.ite htag₀ hzero ?_
  refine Primrec.ite htag₁ hsucc ?_
  refine Primrec.ite htag₂ htail ?_
  refine (Primrec.ite (Primrec.eq.comp hbodd (Primrec.const false))
    (Primrec.ite (Primrec.eq.comp hdiv2bodd (Primrec.const false)) hcons hlookupGComp)
    (Primrec.ite (Primrec.eq.comp hdiv2bodd (Primrec.const false)) hcase hlookupFFix)).of_eq ?_
  intro p
  dsimp only
  cases hb : (p.2.1 - 3).bodd <;>
    cases hd : ((p.2.1 - 3).div2).bodd <;>
    simp

theorem trNormalLabelCodeFuelStepCode_encodeCode
    (prev : List Nat) (c : ToPartrec.Code) (k : Cont') :
    trNormalLabelCodeFuelStepCode prev (ToPartrec.Code.encodeCode c) k =
      trNormalLabelCodeFuelStep prev c k := by
  cases c <;>
    simp [trNormalLabelCodeFuelStepCode, trNormalLabelCodeFuelStep,
      ToPartrec.Code.encodeCode, Nat.div2_val, ToPartrec.Code.ofNatCode_encodeCode]

theorem trNormalLabelCodeFuelStep_primrec :
    Primrec (fun p : List Nat × (ToPartrec.Code × Cont') =>
      trNormalLabelCodeFuelStep p.1 p.2.1 p.2.2) := by
  let hcode : Primrec ToPartrec.Code.encodeCode :=
    (Primrec.encode).of_eq fun c => by rw [ToPartrec.Code.encodeCode_eq]
  exact (trNormalLabelCodeFuelStepCode_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (hcode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))).of_eq fun p => by
      exact trNormalLabelCodeFuelStepCode_encodeCode p.1 p.2.1 p.2.2

theorem trNormalLabelCodeFuelRowStep_primrec :
    Primrec (fun p : List Nat × Nat => trNormalLabelCodeFuelRowStep p.1 p.2) := by
  unfold trNormalLabelCodeFuelRowStep
  let hrow : Primrec (fun p : List Nat × Nat => List.range (p.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  let hentry : Primrec₂ (fun p : List Nat × Nat => fun n : Nat =>
      let s := codeContStateOfCode n
      trNormalLabelCodeFuelStep p.1 s.1 s.2) := by
    apply Primrec₂.mk
    exact trNormalLabelCodeFuelStep_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (codeContStateOfCode_primrec.comp Primrec.snd))
  exact Primrec.list_map hrow hentry

/-- Numeric mirror of `codeSuppWeight'`, using encoded labels for every `trStmtsWeight`. -/
def codeSuppWeightCode' (wCode : Nat → Nat) : ToPartrec.Code → Cont' → Nat
  | c@ToPartrec.Code.zero', k => trStmtsWeightCode wCode (trNormalLabelCode c k)
  | c@ToPartrec.Code.succ, k => trStmtsWeightCode wCode (trNormalLabelCode c k)
  | c@ToPartrec.Code.tail, k => trStmtsWeightCode wCode (trNormalLabelCode c k)
  | c@(ToPartrec.Code.cons f fs), k =>
      trStmtsWeightCode wCode (trNormalLabelCode c k) +
        (codeSuppWeightCode' wCode f (Cont'.cons₁ fs k) +
          (trStmtsWeightCode wCode
              (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
                move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
                    trNormalLabelCode fs (Cont'.cons₂ k)) +
            (codeSuppWeightCode' wCode fs (Cont'.cons₂ k) +
              trStmtsWeightCode wCode (headLabelCode K'.stack <| retLabelCode k))))
  | c@(ToPartrec.Code.comp f g), k =>
      trStmtsWeightCode wCode (trNormalLabelCode c k) +
        (codeSuppWeightCode' wCode g (Cont'.comp f k) +
          (trStmtsWeightCode wCode (trNormalLabelCode f k) + codeSuppWeightCode' wCode f k))
  | c@(ToPartrec.Code.case f g), k =>
      trStmtsWeightCode wCode (trNormalLabelCode c k) +
        (codeSuppWeightCode' wCode f k + codeSuppWeightCode' wCode g k)
  | c@(ToPartrec.Code.fix f), k =>
      trStmtsWeightCode wCode (trNormalLabelCode c k) +
        (codeSuppWeightCode' wCode f (Cont'.fix f k) +
          (trStmtsWeightCode wCode
              (clearLabelCode natEnd K'.main <| trNormalLabelCode f (Cont'.fix f k)) +
            wCode (retLabelCode k)))

/--
Fuelled numeric mirror of `codeSuppWeightCode'`.

Recursive calls consume one unit of source-code depth fuel. The continuation may
grow, so this fuel is independent of the encoding size of the `(code,
continuation)` pair.
-/
def codeSuppWeightCodeFuel' (wCode : Nat → Nat) : Nat → ToPartrec.Code → Cont' → Nat
  | 0, _, _ => 0
  | fuel + 1, c@ToPartrec.Code.zero', k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k)
  | fuel + 1, c@ToPartrec.Code.succ, k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k)
  | fuel + 1, c@ToPartrec.Code.tail, k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k)
  | fuel + 1, c@(ToPartrec.Code.cons f fs), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k) +
        (codeSuppWeightCodeFuel' wCode fuel f (Cont'.cons₁ fs k) +
          (trStmtsWeightCode wCode
              (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
                move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
                    trNormalLabelCodeFuel fuel fs (Cont'.cons₂ k)) +
            (codeSuppWeightCodeFuel' wCode fuel fs (Cont'.cons₂ k) +
              trStmtsWeightCode wCode (headLabelCode K'.stack <| retLabelCode k))))
  | fuel + 1, c@(ToPartrec.Code.comp f g), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k) +
        (codeSuppWeightCodeFuel' wCode fuel g (Cont'.comp f k) +
          (trStmtsWeightCode wCode (trNormalLabelCodeFuel fuel f k) +
            codeSuppWeightCodeFuel' wCode fuel f k))
  | fuel + 1, c@(ToPartrec.Code.case f g), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k) +
        (codeSuppWeightCodeFuel' wCode fuel f k + codeSuppWeightCodeFuel' wCode fuel g k)
  | fuel + 1, c@(ToPartrec.Code.fix f), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuel (fuel + 1) c k) +
        (codeSuppWeightCodeFuel' wCode fuel f (Cont'.fix f k) +
          (trStmtsWeightCode wCode
              (clearLabelCode natEnd K'.main <|
                trNormalLabelCodeFuel fuel f (Cont'.fix f k)) +
            wCode (retLabelCode k)))

/-- One semantic row step for fuelled encoded support weights. -/
def codeSuppWeightCodeFuelStep'
    (wCode : Nat → Nat) (prevLabel prevWeight : List Nat) :
    ToPartrec.Code → Cont' → Nat
  | c@ToPartrec.Code.zero', k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k)
  | c@ToPartrec.Code.succ, k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k)
  | c@ToPartrec.Code.tail, k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k)
  | c@(ToPartrec.Code.cons f fs), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k) +
        (codeContStateLookup prevWeight f (Cont'.cons₁ fs k) +
          (trStmtsWeightCode wCode
              (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
                move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
                    codeContStateLookup prevLabel fs (Cont'.cons₂ k)) +
            (codeContStateLookup prevWeight fs (Cont'.cons₂ k) +
              trStmtsWeightCode wCode (headLabelCode K'.stack <| retLabelCode k))))
  | c@(ToPartrec.Code.comp f g), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k) +
        (codeContStateLookup prevWeight g (Cont'.comp f k) +
          (trStmtsWeightCode wCode (codeContStateLookup prevLabel f k) +
            codeContStateLookup prevWeight f k))
  | c@(ToPartrec.Code.case f g), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k) +
        (codeContStateLookup prevWeight f k + codeContStateLookup prevWeight g k)
  | c@(ToPartrec.Code.fix f), k =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStep prevLabel c k) +
        (codeContStateLookup prevWeight f (Cont'.fix f k) +
          (trStmtsWeightCode wCode
              (clearLabelCode natEnd K'.main <|
                codeContStateLookup prevLabel f (Cont'.fix f k)) +
            wCode (retLabelCode k)))

/--
Numeric version of `codeSuppWeightCodeFuelStep'`, dispatching on dense source-code tags.
-/
def codeSuppWeightCodeFuelStepCode'
    (wCode : Nat → Nat) (prevLabel prevWeight : List Nat) (cCode : Nat) (k : Cont') :
    Nat :=
  let normal := trStmtsWeightCode wCode (trNormalLabelCodeFuelStepCode prevLabel cCode k)
  if cCode = 0 then
    normal
  else if cCode = 1 then
    normal
  else if cCode = 2 then
    normal
  else
    let n := cCode - 3
    let m := n.div2.div2
    let f := ToPartrec.Code.ofNatCode m.unpair.1
    let g := ToPartrec.Code.ofNatCode m.unpair.2
    match n.bodd, n.div2.bodd with
    | false, false =>
        normal +
          (codeContStateLookup prevWeight f (Cont'.cons₁ g k) +
            (trStmtsWeightCode wCode
                (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
                  move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                    move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
                      codeContStateLookup prevLabel g (Cont'.cons₂ k)) +
              (codeContStateLookup prevWeight g (Cont'.cons₂ k) +
                trStmtsWeightCode wCode (headLabelCode K'.stack <| retLabelCode k))))
    | false, true =>
        normal +
          (codeContStateLookup prevWeight g (Cont'.comp f k) +
            (trStmtsWeightCode wCode (codeContStateLookup prevLabel f k) +
              codeContStateLookup prevWeight f k))
    | true, false =>
        normal + (codeContStateLookup prevWeight f k + codeContStateLookup prevWeight g k)
    | true, true =>
        let f := ToPartrec.Code.ofNatCode m
        normal +
          (codeContStateLookup prevWeight f (Cont'.fix f k) +
            (trStmtsWeightCode wCode
                (clearLabelCode natEnd K'.main <|
                  codeContStateLookup prevLabel f (Cont'.fix f k)) +
              wCode (retLabelCode k)))

theorem codeSuppWeightCodeFuelStepCode'_encodeCode
    (wCode : Nat → Nat) (prevLabel prevWeight : List Nat)
    (c : ToPartrec.Code) (k : Cont') :
    codeSuppWeightCodeFuelStepCode' wCode prevLabel prevWeight
        (ToPartrec.Code.encodeCode c) k =
      codeSuppWeightCodeFuelStep' wCode prevLabel prevWeight c k := by
  cases c <;>
    unfold codeSuppWeightCodeFuelStepCode' codeSuppWeightCodeFuelStep' <;>
    rw [trNormalLabelCodeFuelStepCode_encodeCode] <;>
    simp [ToPartrec.Code.encodeCode, Nat.div2_val, ToPartrec.Code.ofNatCode_encodeCode]

theorem codeSuppWeightCodeFuelStepCode'_primrec
    {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeSuppWeightCodeFuelStepCode' wCode p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold codeSuppWeightCodeFuelStepCode'
  let hprevLabel : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  let hprevWeight : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  let hcode : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  let hk : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  let hn : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => p.2.1 - 3) :=
    Primrec.nat_sub.comp hcode (Primrec.const 3)
  let hm : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      (p.2.1 - 3).div2.div2) :=
    Primrec.nat_div2.comp (Primrec.nat_div2.comp hn)
  let hm₁ : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      ((p.2.1 - 3).div2.div2).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  let hm₂ : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      ((p.2.1 - 3).div2.div2).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  let hf : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) :=
    Primrec.ofNat ToPartrec.Code |>.comp hm₁
  let hg : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) :=
    Primrec.ofNat ToPartrec.Code |>.comp hm₂
  let hsingle : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) :=
    Primrec.ofNat ToPartrec.Code |>.comp hm
  let hnormal : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStepCode p.1.1 p.2.1 p.2.2)) :=
    (trStmtsWeightCode_primrec hw).comp
      (trNormalLabelCodeFuelStepCode_primrec.comp
        (Primrec.pair hprevLabel (Primrec.pair hcode hk)))
  let hret : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => retLabelCode p.2.2) :=
    retLabelCode_primrec.comp hk
  let hhead : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode (headLabelCode K'.stack (retLabelCode p.2.2))) :=
    (trStmtsWeightCode_primrec hw).comp
      ((headLabelCode_primrec K'.stack).comp hret)
  let hlookupWeightFCons₁ : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.2
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1)
        (Cont'.cons₁
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1,
          Cont'.cons₁
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) := by
      exact Primrec.pair hf ((Turing.PartrecToTM2.Cont'.primrec₂_cons₁).comp hg hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevWeight hstate)
  let hlookupLabelGCons₂ : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
        (Cont'.cons₂ p.2.2)) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2,
          Cont'.cons₂ p.2.2)) := by
      exact Primrec.pair hg (Turing.PartrecToTM2.Cont'.primrec_cons₂.comp hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevLabel hstate)
  let hauxCons : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode
        (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
          move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
            move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
              codeContStateLookup p.1.1
                (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
                (Cont'.cons₂ p.2.2))) :=
    (trStmtsWeightCode_primrec hw).comp
      ((move₂LabelCode_primrec (fun _ : Γ' => false) K'.main K'.aux).comp
        ((move₂LabelCode_primrec (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main).comp
          ((move₂LabelCode_primrec (fun _ : Γ' => false) K'.aux K'.stack).comp
            hlookupLabelGCons₂)))
  let hlookupWeightGCons₂ : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.2
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
        (Cont'.cons₂ p.2.2)) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2,
          Cont'.cons₂ p.2.2)) := by
      exact Primrec.pair hg (Turing.PartrecToTM2.Cont'.primrec_cons₂.comp hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevWeight hstate)
  let hcons : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStepCode p.1.1 p.2.1 p.2.2) +
        (codeContStateLookup p.1.2
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1)
            (Cont'.cons₁
              (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2) +
          (trStmtsWeightCode wCode
              (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
                move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
                    codeContStateLookup p.1.1
                      (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
                      (Cont'.cons₂ p.2.2)) +
            (codeContStateLookup p.1.2
                (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
                (Cont'.cons₂ p.2.2) +
              trStmtsWeightCode wCode (headLabelCode K'.stack (retLabelCode p.2.2)))))) :=
    Primrec.nat_add.comp hnormal
      (Primrec.nat_add.comp hlookupWeightFCons₁
        (Primrec.nat_add.comp hauxCons
          (Primrec.nat_add.comp hlookupWeightGCons₂ hhead)))
  let hlookupWeightGComp : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.2
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
        (Cont'.comp
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2)) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2,
          Cont'.comp
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2)) := by
      exact Primrec.pair hg ((Turing.PartrecToTM2.Cont'.primrec₂_comp).comp hf hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevWeight hstate)
  let hlookupLabelF : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1, p.2.2)) :=
      Primrec.pair hf hk
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevLabel hstate)
  let htrLabelF : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode
        (codeContStateLookup p.1.1
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2)) :=
    (trStmtsWeightCode_primrec hw).comp hlookupLabelF
  let hlookupWeightF : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.2
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1, p.2.2)) :=
      Primrec.pair hf hk
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevWeight hstate)
  let hcomp : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStepCode p.1.1 p.2.1 p.2.2) +
        (codeContStateLookup p.1.2
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2)
            (Cont'.comp
              (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2) +
          (trStmtsWeightCode wCode
              (codeContStateLookup p.1.1
                (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2) +
            codeContStateLookup p.1.2
              (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2))) :=
    Primrec.nat_add.comp hnormal
      (Primrec.nat_add.comp hlookupWeightGComp
        (Primrec.nat_add.comp htrLabelF hlookupWeightF))
  let hlookupWeightG : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.2
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2, p.2.2)) :=
      Primrec.pair hg hk
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevWeight hstate)
  let hcase : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStepCode p.1.1 p.2.1 p.2.2) +
        (codeContStateLookup p.1.2
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.1) p.2.2 +
          codeContStateLookup p.1.2
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2).unpair.2) p.2.2)) :=
    Primrec.nat_add.comp hnormal (Primrec.nat_add.comp hlookupWeightF hlookupWeightG)
  let hlookupWeightFFix : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.2
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2))
        (Cont'.fix
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2),
          Cont'.fix
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) := by
      exact Primrec.pair hsingle ((Turing.PartrecToTM2.Cont'.primrec₂_fix).comp hsingle hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevWeight hstate)
  let hlookupLabelFFix : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      codeContStateLookup p.1.1
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2))
        (Cont'.fix
          (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) := by
    let hstate : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
        (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2),
          Cont'.fix
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) := by
      exact Primrec.pair hsingle ((Turing.PartrecToTM2.Cont'.primrec₂_fix).comp hsingle hk)
    exact codeContStateLookup_primrec.comp (Primrec.pair hprevLabel hstate)
  let hclearFix : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode
        (clearLabelCode natEnd K'.main <|
          codeContStateLookup p.1.1
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2))
            (Cont'.fix
              (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2))) :=
    (trStmtsWeightCode_primrec hw).comp
      ((clearLabelCode_primrec natEnd K'.main).comp hlookupLabelFFix)
  let hwret : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      wCode (retLabelCode p.2.2)) :=
    hw.comp hret
  let hfix : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' =>
      trStmtsWeightCode wCode (trNormalLabelCodeFuelStepCode p.1.1 p.2.1 p.2.2) +
        (codeContStateLookup p.1.2
            (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2))
            (Cont'.fix
              (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2) +
          (trStmtsWeightCode wCode
              (clearLabelCode natEnd K'.main <|
                codeContStateLookup p.1.1
                  (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2))
                  (Cont'.fix
                    (ToPartrec.Code.ofNatCode ((p.2.1 - 3).div2.div2)) p.2.2)) +
            wCode (retLabelCode p.2.2)))) :=
    Primrec.nat_add.comp hnormal
      (Primrec.nat_add.comp hlookupWeightFFix
        (Primrec.nat_add.comp hclearFix hwret))
  let htag₀ : PrimrecPred (fun p : (List Nat × List Nat) × Nat × Cont' => p.2.1 = 0) :=
    Primrec.eq.comp hcode (Primrec.const 0)
  let htag₁ : PrimrecPred (fun p : (List Nat × List Nat) × Nat × Cont' => p.2.1 = 1) :=
    Primrec.eq.comp hcode (Primrec.const 1)
  let htag₂ : PrimrecPred (fun p : (List Nat × List Nat) × Nat × Cont' => p.2.1 = 2) :=
    Primrec.eq.comp hcode (Primrec.const 2)
  let hbodd : Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => (p.2.1 - 3).bodd) :=
    Primrec.nat_bodd.comp hn
  let hdiv2bodd :
      Primrec (fun p : (List Nat × List Nat) × Nat × Cont' => ((p.2.1 - 3).div2).bodd) :=
    Primrec.nat_bodd.comp (Primrec.nat_div2.comp hn)
  refine Primrec.ite htag₀ hnormal ?_
  refine Primrec.ite htag₁ hnormal ?_
  refine Primrec.ite htag₂ hnormal ?_
  refine (Primrec.ite (Primrec.eq.comp hbodd (Primrec.const false))
    (Primrec.ite (Primrec.eq.comp hdiv2bodd (Primrec.const false)) hcons hcomp)
    (Primrec.ite (Primrec.eq.comp hdiv2bodd (Primrec.const false)) hcase hfix)).of_eq ?_
  intro p
  dsimp only
  cases hb : (p.2.1 - 3).bodd <;>
    cases hd : ((p.2.1 - 3).div2).bodd <;>
    simp

theorem codeSuppWeightCodeFuelStep'_primrec
    {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : (List Nat × List Nat) × (ToPartrec.Code × Cont') =>
      codeSuppWeightCodeFuelStep' wCode p.1.1 p.1.2 p.2.1 p.2.2) := by
  let hcode : Primrec ToPartrec.Code.encodeCode :=
    (Primrec.encode).of_eq fun c => by rw [ToPartrec.Code.encodeCode_eq]
  exact (codeSuppWeightCodeFuelStepCode'_primrec hw |>.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (hcode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))).of_eq fun p => by
      exact codeSuppWeightCodeFuelStepCode'_encodeCode wCode p.1.1 p.1.2 p.2.1 p.2.2

theorem codeSuppWeightCodeFuelStep'_eq
    (wCode : Nat → Nat) {prevLabel prevWeight : List Nat} {fuel : Nat}
    (hlabel : ∀ c k, codeContStateLookup prevLabel c k = trNormalLabelCodeFuel fuel c k)
    (hweight : ∀ c k,
      codeContStateLookup prevWeight c k = codeSuppWeightCodeFuel' wCode fuel c k)
    (c : ToPartrec.Code) (k : Cont') :
    codeSuppWeightCodeFuelStep' wCode prevLabel prevWeight c k =
      codeSuppWeightCodeFuel' wCode (fuel + 1) c k := by
  cases c with
  | zero' =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel]
  | succ =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel]
  | tail =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel]
  | cons f fs =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel, hlabel, hweight]
  | comp f g =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel, hlabel, hweight]
  | case f g =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel, hweight]
  | fix f =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel',
        trNormalLabelCodeFuelStep_eq hlabel, hlabel, hweight]

theorem codeSuppWeightCodeFuelStep'_eq_of_bound
    (wCode : Nat → Nat) {prevLabel prevWeight : List Nat} {fuel codeBound contBound : Nat}
    (hlabel : ∀ c k,
      ToPartrec.Code.encodeCode c ≤ codeBound →
      Turing.PartrecToTM2.Cont'.encodeCont k ≤ contEncodeBoundStep codeBound contBound →
      codeContStateLookup prevLabel c k = trNormalLabelCodeFuel fuel c k)
    (hweight : ∀ c k,
      ToPartrec.Code.encodeCode c ≤ codeBound →
      Turing.PartrecToTM2.Cont'.encodeCont k ≤ contEncodeBoundStep codeBound contBound →
      codeContStateLookup prevWeight c k = codeSuppWeightCodeFuel' wCode fuel c k)
    {c : ToPartrec.Code} {k : Cont'}
    (hcode : ToPartrec.Code.encodeCode c ≤ codeBound)
    (hcont : Turing.PartrecToTM2.Cont'.encodeCont k ≤ contBound) :
    codeSuppWeightCodeFuelStep' wCode prevLabel prevWeight c k =
      codeSuppWeightCodeFuel' wCode (fuel + 1) c k := by
  have hnormal :
      trNormalLabelCodeFuelStep prevLabel c k = trNormalLabelCodeFuel (fuel + 1) c k :=
    trNormalLabelCodeFuelStep_eq_of_bound hlabel hcode hcont
  cases c with
  | zero' =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal]
  | succ =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal]
  | tail =>
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal]
  | cons f fs =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_left_le_cons f fs).trans hcode
      have hfsCode : ToPartrec.Code.encodeCode fs ≤ codeBound :=
        (ToPartrec.Code.encodeCode_right_le_cons f fs).trans hcode
      have hcons₁ :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.cons₁ fs k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_cons₁_le_boundStep hfsCode hcont
      have hcons₂ :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.cons₂ k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_cons₂_le_boundStep hcont
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal,
        hlabel fs (Cont'.cons₂ k) hfsCode hcons₂,
        hweight f (Cont'.cons₁ fs k) hfCode hcons₁,
        hweight fs (Cont'.cons₂ k) hfsCode hcons₂]
  | comp f g =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_left_le_comp f g).trans hcode
      have hgCode : ToPartrec.Code.encodeCode g ≤ codeBound :=
        (ToPartrec.Code.encodeCode_right_le_comp f g).trans hcode
      have hcomp :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.comp f k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_comp_le_boundStep hfCode hcont
      have hsame :
          Turing.PartrecToTM2.Cont'.encodeCont k ≤
            contEncodeBoundStep codeBound contBound :=
        hcont.trans (contBound_le_boundStep codeBound contBound)
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal,
        hlabel f k hfCode hsame,
        hweight g (Cont'.comp f k) hgCode hcomp,
        hweight f k hfCode hsame]
  | case f g =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_left_le_case f g).trans hcode
      have hgCode : ToPartrec.Code.encodeCode g ≤ codeBound :=
        (ToPartrec.Code.encodeCode_right_le_case f g).trans hcode
      have hsame :
          Turing.PartrecToTM2.Cont'.encodeCont k ≤
            contEncodeBoundStep codeBound contBound :=
        hcont.trans (contBound_le_boundStep codeBound contBound)
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal,
        hweight f k hfCode hsame, hweight g k hgCode hsame]
  | fix f =>
      have hfCode : ToPartrec.Code.encodeCode f ≤ codeBound :=
        (ToPartrec.Code.encodeCode_le_fix f).trans hcode
      have hfix :
          Turing.PartrecToTM2.Cont'.encodeCont (Cont'.fix f k) ≤
            contEncodeBoundStep codeBound contBound :=
        encodeCont_fix_le_boundStep hfCode hcont
      simp [codeSuppWeightCodeFuelStep', codeSuppWeightCodeFuel', hnormal,
        hlabel f (Cont'.fix f k) hfCode hfix,
        hweight f (Cont'.fix f k) hfCode hfix]

/-- One bounded row of fuelled encoded support weights. -/
def codeSuppWeightCodeFuelRowStep'
    (wCode : Nat → Nat) (prevLabel prevWeight : List Nat) (bound : Nat) : List Nat :=
  (List.range (bound + 1)).map fun n =>
    let s := codeContStateOfCode n
    codeSuppWeightCodeFuelStep' wCode prevLabel prevWeight s.1 s.2

theorem codeSuppWeightCodeFuelRowStep'_primrec
    {wCode : Nat → Nat} (hw : Primrec wCode) :
    Primrec (fun p : (List Nat × List Nat) × Nat =>
      codeSuppWeightCodeFuelRowStep' wCode p.1.1 p.1.2 p.2) := by
  unfold codeSuppWeightCodeFuelRowStep'
  let hrow : Primrec (fun p : (List Nat × List Nat) × Nat => List.range (p.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  let hentry : Primrec₂ (fun p : (List Nat × List Nat) × Nat => fun n : Nat =>
      let s := codeContStateOfCode n
      codeSuppWeightCodeFuelStep' wCode p.1.1 p.1.2 s.1 s.2) := by
    apply Primrec₂.mk
    exact (codeSuppWeightCodeFuelStep'_primrec hw).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (codeContStateOfCode_primrec.comp Primrec.snd))
  exact Primrec.list_map hrow hentry

theorem codeSuppWeightCodeFuelRowStep'_getD_eq
    (wCode : Nat → Nat) {prevLabel prevWeight : List Nat} {fuel bound n : Nat}
    (hlabel : ∀ c k, codeContStateLookup prevLabel c k = trNormalLabelCodeFuel fuel c k)
    (hweight : ∀ c k,
      codeContStateLookup prevWeight c k = codeSuppWeightCodeFuel' wCode fuel c k)
    (hn : n ≤ bound) :
    (codeSuppWeightCodeFuelRowStep' wCode prevLabel prevWeight bound).getD n 0 =
      codeSuppWeightCodeFuel' wCode (fuel + 1) (codeContStateOfCode n).1
        (codeContStateOfCode n).2 := by
  unfold codeSuppWeightCodeFuelRowStep'
  have hlt :
      n < ((List.range (bound + 1)).map fun n =>
        let s := codeContStateOfCode n
        codeSuppWeightCodeFuelStep' wCode prevLabel prevWeight s.1 s.2).length := by
    simp
    omega
  rw [List.getD_eq_getElem
    (l := (List.range (bound + 1)).map fun n =>
      let s := codeContStateOfCode n
      codeSuppWeightCodeFuelStep' wCode prevLabel prevWeight s.1 s.2) (d := 0) hlt]
  simp only [List.getElem_map, List.getElem_range]
  exact codeSuppWeightCodeFuelStep'_eq wCode hlabel hweight _ _

def codeSuppWeightCodeFuelRowsBase (bound : Nat) : List Nat × List Nat :=
  let row := (List.range (bound + 1)).map fun _ => 0
  (row, row)

def codeSuppWeightCodeFuelRowsStep
    (wCode : Nat → Nat) (bound : Nat) (rows : List Nat × List Nat) :
    List Nat × List Nat :=
  (trNormalLabelCodeFuelRowStep rows.1 bound,
    codeSuppWeightCodeFuelRowStep' wCode rows.1 rows.2 bound)

/--
Paired bounded dynamic-programming rows for fuelled `trNormal` labels and
fuelled support weights.

The weight row for fuel `n + 1` is computed from the label and weight rows for
fuel `n`, matching `codeSuppWeightCodeFuelStep'`.
-/
@[irreducible] def codeSuppWeightCodeFuelRows' (wCode : Nat → Nat) (fuel bound : Nat) :
    List Nat × List Nat :=
  Nat.rec (codeSuppWeightCodeFuelRowsBase bound)
    (fun _ rows => codeSuppWeightCodeFuelRowsStep wCode bound rows) fuel

theorem codeSuppWeightCodeFuelRowsBase_primrec :
    Primrec codeSuppWeightCodeFuelRowsBase := by
  unfold codeSuppWeightCodeFuelRowsBase
  let hrow : Primrec (fun bound : Nat => (List.range (bound + 1)).map fun _ => 0) := by
    exact Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp Primrec.id)) (Primrec.const 0).to₂
  exact Primrec.pair hrow hrow

theorem codeSuppWeightCodeFuelRows'_zero (wCode : Nat → Nat) (bound : Nat) :
    codeSuppWeightCodeFuelRows' wCode 0 bound = codeSuppWeightCodeFuelRowsBase bound := by
  unfold codeSuppWeightCodeFuelRows'
  rfl

theorem codeSuppWeightCodeFuelRows'_succ
    (wCode : Nat → Nat) (fuel bound : Nat) :
    codeSuppWeightCodeFuelRows' wCode (fuel + 1) bound =
      codeSuppWeightCodeFuelRowsStep wCode bound
        (codeSuppWeightCodeFuelRows' wCode fuel bound) := by
  unfold codeSuppWeightCodeFuelRows'
  rfl

theorem codeSuppWeightCodeFuelRowsStep_fst
    (wCode : Nat → Nat) (bound : Nat) (rows : List Nat × List Nat) :
    (codeSuppWeightCodeFuelRowsStep wCode bound rows).1 =
      trNormalLabelCodeFuelRowStep rows.1 bound := rfl

theorem codeSuppWeightCodeFuelRowsStep_snd
    (wCode : Nat → Nat) (bound : Nat) (rows : List Nat × List Nat) :
    (codeSuppWeightCodeFuelRowsStep wCode bound rows).2 =
      codeSuppWeightCodeFuelRowStep' wCode rows.1 rows.2 bound := rfl

theorem codeSuppWeightCodeFuelRowsBase_label_correct
    (bound : Nat) (c : ToPartrec.Code) (k : Cont') :
    codeContStateLookup (codeSuppWeightCodeFuelRowsBase bound).1 c k =
      trNormalLabelCodeFuel 0 c k := by
  simp [codeSuppWeightCodeFuelRowsBase, codeContStateLookup, trNormalLabelCodeFuel]

theorem codeSuppWeightCodeFuelRowsBase_weight_correct
    (wCode : Nat → Nat) (bound : Nat) (c : ToPartrec.Code) (k : Cont') :
    codeContStateLookup (codeSuppWeightCodeFuelRowsBase bound).2 c k =
      codeSuppWeightCodeFuel' wCode 0 c k := by
  simp [codeSuppWeightCodeFuelRowsBase, codeContStateLookup, codeSuppWeightCodeFuel']

theorem codeSuppWeightCodeFuelRowsStep_fst_getD_eq
    (wCode : Nat → Nat) {rows : List Nat × List Nat} {fuel bound n : Nat}
    (hlabel : ∀ c k, codeContStateLookup rows.1 c k = trNormalLabelCodeFuel fuel c k)
    (hn : n ≤ bound) :
    (codeSuppWeightCodeFuelRowsStep wCode bound rows).1.getD n 0 =
      trNormalLabelCodeFuel (fuel + 1) (codeContStateOfCode n).1
        (codeContStateOfCode n).2 := by
  rw [codeSuppWeightCodeFuelRowsStep_fst]
  exact trNormalLabelCodeFuelRowStep_getD_eq hlabel hn

theorem codeSuppWeightCodeFuelRowsStep_snd_getD_eq
    (wCode : Nat → Nat) {rows : List Nat × List Nat} {fuel bound n : Nat}
    (hlabel : ∀ c k, codeContStateLookup rows.1 c k = trNormalLabelCodeFuel fuel c k)
    (hweight : ∀ c k,
      codeContStateLookup rows.2 c k = codeSuppWeightCodeFuel' wCode fuel c k)
    (hn : n ≤ bound) :
    (codeSuppWeightCodeFuelRowsStep wCode bound rows).2.getD n 0 =
      codeSuppWeightCodeFuel' wCode (fuel + 1) (codeContStateOfCode n).1
        (codeContStateOfCode n).2 := by
  rw [codeSuppWeightCodeFuelRowsStep_snd]
  exact codeSuppWeightCodeFuelRowStep'_getD_eq wCode hlabel hweight hn

theorem codeSuppWeightCodeFuel'_eq
    (wCode : Nat → Nat) {fuel : Nat} (h : ToPartrec.Code.depth c ≤ fuel) :
    codeSuppWeightCodeFuel' wCode fuel c k = codeSuppWeightCode' wCode c k := by
  induction c generalizing fuel k with
  | zero' =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos ToPartrec.Code.zero'
          omega
      | succ fuel =>
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h]
  | succ =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos ToPartrec.Code.succ
          omega
      | succ fuel =>
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h]
  | tail =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos ToPartrec.Code.tail
          omega
      | succ fuel =>
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h]
  | cons f fs ihf ihfs =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.cons f fs)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_left_lt_cons f fs
            omega
          have hfs : ToPartrec.Code.depth fs ≤ fuel := by
            have hlt := ToPartrec.Code.depth_right_lt_cons f fs
            omega
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h, trNormalLabelCodeFuel_eq hfs,
            ihf hf, ihfs hfs]
  | comp f g ihf ihg =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.comp f g)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_left_lt_comp f g
            omega
          have hg : ToPartrec.Code.depth g ≤ fuel := by
            have hlt := ToPartrec.Code.depth_right_lt_comp f g
            omega
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h, trNormalLabelCodeFuel_eq hf,
            ihf hf, ihg hg]
  | case f g ihf ihg =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.case f g)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_left_lt_case f g
            omega
          have hg : ToPartrec.Code.depth g ≤ fuel := by
            have hlt := ToPartrec.Code.depth_right_lt_case f g
            omega
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h, ihf hf, ihg hg]
  | fix f ih =>
      cases fuel with
      | zero =>
          have hpos := ToPartrec.Code.depth_pos (ToPartrec.Code.fix f)
          omega
      | succ fuel =>
          have hf : ToPartrec.Code.depth f ≤ fuel := by
            have hlt := ToPartrec.Code.depth_lt_fix f
            omega
          simp [codeSuppWeightCodeFuel', codeSuppWeightCode',
            trNormalLabelCodeFuel_eq h, trNormalLabelCodeFuel_eq hf, ih hf]

theorem codeSuppWeightCodeFuel'_encodeCode_eq
    (wCode : Nat → Nat) (c : ToPartrec.Code) (k : Cont') :
    codeSuppWeightCodeFuel' wCode (ToPartrec.Code.encodeCode c + 1) c k =
      codeSuppWeightCode' wCode c k :=
  codeSuppWeightCodeFuel'_eq wCode (ToPartrec.Code.depth_le_encodeCode_succ c)

/-- List-valued mirror of Mathlib's `PartrecToTM2.codeSupp'`. -/
def codeSuppList' : ToPartrec.Code → Cont' → List Λ'
  | c@ToPartrec.Code.zero', k => trStmtsList (trNormal c k)
  | c@ToPartrec.Code.succ, k => trStmtsList (trNormal c k)
  | c@ToPartrec.Code.tail, k => trStmtsList (trNormal c k)
  | c@(ToPartrec.Code.cons f fs), k =>
      trStmtsList (trNormal c k) ++
        (codeSuppList' f (Cont'.cons₁ fs k) ++
          (trStmtsList
              (move₂ (fun _ => false) K'.main K'.aux <|
                move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) ++
            (codeSuppList' fs (Cont'.cons₂ k) ++ trStmtsList (head K'.stack <| Λ'.ret k))))
  | c@(ToPartrec.Code.comp f g), k =>
      trStmtsList (trNormal c k) ++
        (codeSuppList' g (Cont'.comp f k) ++
          (trStmtsList (trNormal f k) ++ codeSuppList' f k))
  | c@(ToPartrec.Code.case f g), k =>
      trStmtsList (trNormal c k) ++ (codeSuppList' f k ++ codeSuppList' g k)
  | c@(ToPartrec.Code.fix f), k =>
      trStmtsList (trNormal c k) ++
        (codeSuppList' f (Cont'.fix f k) ++
          (trStmtsList (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)) ++
            [Λ'.ret k]))

/-- Numeric length mirror of `codeSuppList'`. -/
def codeSuppLength' : ToPartrec.Code → Cont' → Nat
  | c@ToPartrec.Code.zero', k => trStmtsLength (trNormal c k)
  | c@ToPartrec.Code.succ, k => trStmtsLength (trNormal c k)
  | c@ToPartrec.Code.tail, k => trStmtsLength (trNormal c k)
  | c@(ToPartrec.Code.cons f fs), k =>
      trStmtsLength (trNormal c k) +
        (codeSuppLength' f (Cont'.cons₁ fs k) +
          (trStmtsLength
              (move₂ (fun _ => false) K'.main K'.aux <|
                move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) +
            (codeSuppLength' fs (Cont'.cons₂ k) + trStmtsLength (head K'.stack <| Λ'.ret k))))
  | c@(ToPartrec.Code.comp f g), k =>
      trStmtsLength (trNormal c k) +
        (codeSuppLength' g (Cont'.comp f k) +
          (trStmtsLength (trNormal f k) + codeSuppLength' f k))
  | c@(ToPartrec.Code.case f g), k =>
      trStmtsLength (trNormal c k) + (codeSuppLength' f k + codeSuppLength' g k)
  | c@(ToPartrec.Code.fix f), k =>
      trStmtsLength (trNormal c k) +
        (codeSuppLength' f (Cont'.fix f k) +
          (trStmtsLength (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)) + 1))

/-- Weighted sum mirror of `codeSuppList'`. -/
def codeSuppWeight' (w : Λ' → Nat) : ToPartrec.Code → Cont' → Nat
  | c@ToPartrec.Code.zero', k => trStmtsWeight w (trNormal c k)
  | c@ToPartrec.Code.succ, k => trStmtsWeight w (trNormal c k)
  | c@ToPartrec.Code.tail, k => trStmtsWeight w (trNormal c k)
  | c@(ToPartrec.Code.cons f fs), k =>
      trStmtsWeight w (trNormal c k) +
        (codeSuppWeight' w f (Cont'.cons₁ fs k) +
          (trStmtsWeight w
              (move₂ (fun _ => false) K'.main K'.aux <|
                move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) +
            (codeSuppWeight' w fs (Cont'.cons₂ k) +
              trStmtsWeight w (head K'.stack <| Λ'.ret k))))
  | c@(ToPartrec.Code.comp f g), k =>
      trStmtsWeight w (trNormal c k) +
        (codeSuppWeight' w g (Cont'.comp f k) +
          (trStmtsWeight w (trNormal f k) + codeSuppWeight' w f k))
  | c@(ToPartrec.Code.case f g), k =>
      trStmtsWeight w (trNormal c k) + (codeSuppWeight' w f k + codeSuppWeight' w g k)
  | c@(ToPartrec.Code.fix f), k =>
      trStmtsWeight w (trNormal c k) +
        (codeSuppWeight' w f (Cont'.fix f k) +
          (trStmtsWeight w (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)) +
            w (Λ'.ret k)))

theorem codeSuppWeightCode'_eq
    (w : Λ' → Nat) (wCode : Nat → Nat)
    (hwCode : ∀ q : Λ', wCode (Turing.PartrecToTM2.Λ'.encodeLabel q) = w q)
    (c : ToPartrec.Code) (k : Cont') :
    codeSuppWeightCode' wCode c k = codeSuppWeight' w c k := by
  induction c generalizing k with
  | zero' =>
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, hwCode]
  | succ =>
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, hwCode]
  | tail =>
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, hwCode]
  | cons f fs ihf ihfs =>
      have haux :
          trStmtsWeightCode wCode
              (move₂LabelCode (fun _ : Γ' => false) K'.main K'.aux <|
                move₂LabelCode (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂LabelCode (fun _ : Γ' => false) K'.aux K'.stack <|
                    Turing.PartrecToTM2.Λ'.encodeLabel (trNormal fs (Cont'.cons₂ k))) =
            trStmtsWeight w
              (move₂ (fun _ : Γ' => false) K'.main K'.aux <|
                move₂ (fun s : Γ' => s = Γ'.consₗ) K'.stack K'.main <|
                  move₂ (fun _ : Γ' => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) := by
        rw [move₂LabelCode_encodeLabel]
        rw [move₂LabelCode_encodeLabel]
        rw [move₂LabelCode_encodeLabel]
        exact trStmtsWeightCode_encodeLabel w wCode hwCode _
      have hhead :
          trStmtsWeightCode wCode (headLabelCode K'.stack (retLabelCode k)) =
            trStmtsWeight w (head K'.stack (Λ'.ret k)) := by
        rw [retLabelCode_encodeLabel]
        rw [headLabelCode_encodeLabel]
        exact trStmtsWeightCode_encodeLabel w wCode hwCode _
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, ihf, ihfs, haux, hhead, hwCode]
  | comp f g ihf ihg =>
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, ihf, ihg, hwCode]
  | case f g ihf ihg =>
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, ihf, ihg, hwCode]
  | fix f ih =>
      have hclear :
          trStmtsWeightCode wCode
              (clearLabelCode natEnd K'.main <|
                Turing.PartrecToTM2.Λ'.encodeLabel (trNormal f (Cont'.fix f k))) =
            trStmtsWeight w (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)) := by
        rw [clearLabelCode_encodeLabel]
        exact trStmtsWeightCode_encodeLabel w wCode hwCode _
      have hret : wCode (retLabelCode k) = w (Λ'.ret k) := by
        rw [retLabelCode_encodeLabel]
        exact hwCode (Λ'.ret k)
      simp [codeSuppWeightCode', codeSuppWeight', trNormalLabelCode_encodeLabel,
        trStmtsWeightCode_encodeLabel, ih, hclear, hret, hwCode]

theorem codeSuppList'_length (c : ToPartrec.Code) (k : Cont') :
    (codeSuppList' c k).length = codeSuppLength' c k := by
  induction c generalizing k with
  | zero' =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length]
  | succ =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length]
  | tail =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length]
  | cons f fs ihf ihfs =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length, ihf, ihfs]
  | comp f g ihf ihg =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length, ihf, ihg]
  | case f g ihf ihg =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length, ihf, ihg]
  | fix f ih =>
      simp [codeSuppList', codeSuppLength', trStmtsList_length, ih]

theorem codeSuppList'_weight (w : Λ' → Nat) (c : ToPartrec.Code) (k : Cont') :
    ((codeSuppList' c k).map w).sum = codeSuppWeight' w c k := by
  induction c generalizing k with
  | zero' =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight]
  | succ =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight]
  | tail =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight]
  | cons f fs ihf ihfs =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight, ihf, ihfs]
  | comp f g ihf ihg =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight, ihf, ihg]
  | case f g ihf ihg =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight, ihf, ihg]
  | fix f ih =>
      simp [codeSuppList', codeSuppWeight', trStmtsList_weight, ih]

theorem mem_codeSuppList'_iff {c : ToPartrec.Code} {k : Cont'} {q : Λ'} :
    q ∈ codeSuppList' c k ↔ q ∈ codeSupp' c k := by
  induction c generalizing k with
  | zero' =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff]
  | succ =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff]
  | tail =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff]
  | cons f fs ihf ihfs =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff, ihf, ihfs]
  | comp f g ihf ihg =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff, ihf, ihg]
  | case f g ihf ihg =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff, ihf, ihg]
  | fix f ih =>
      simp [codeSuppList', codeSupp', mem_trStmtsList_iff, ih]
      tauto

/-- List-valued mirror of Mathlib's `PartrecToTM2.contSupp`. -/
def contSuppList : Cont' → List Λ'
  | Cont'.cons₁ fs k =>
      trStmtsList
          (move₂ (fun _ => false) K'.main K'.aux <|
            move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
              move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) ++
        (codeSuppList' fs (Cont'.cons₂ k) ++
          (trStmtsList (head K'.stack <| Λ'.ret k) ++ contSuppList k))
  | Cont'.cons₂ k => trStmtsList (head K'.stack <| Λ'.ret k) ++ contSuppList k
  | Cont'.comp f k => codeSuppList' f k ++ contSuppList k
  | Cont'.fix f k => codeSuppList' (ToPartrec.Code.fix f) k ++ contSuppList k
  | Cont'.halt => []

/-- Numeric length mirror of `contSuppList`. -/
def contSuppLength : Cont' → Nat
  | Cont'.cons₁ fs k =>
      trStmtsLength
          (move₂ (fun _ => false) K'.main K'.aux <|
            move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
              move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) +
        (codeSuppLength' fs (Cont'.cons₂ k) +
          (trStmtsLength (head K'.stack <| Λ'.ret k) + contSuppLength k))
  | Cont'.cons₂ k => trStmtsLength (head K'.stack <| Λ'.ret k) + contSuppLength k
  | Cont'.comp f k => codeSuppLength' f k + contSuppLength k
  | Cont'.fix f k => codeSuppLength' (ToPartrec.Code.fix f) k + contSuppLength k
  | Cont'.halt => 0

/-- Weighted sum mirror of `contSuppList`. -/
def contSuppWeight (w : Λ' → Nat) : Cont' → Nat
  | Cont'.cons₁ fs k =>
      trStmtsWeight w
          (move₂ (fun _ => false) K'.main K'.aux <|
            move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
              move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) +
        (codeSuppWeight' w fs (Cont'.cons₂ k) +
          (trStmtsWeight w (head K'.stack <| Λ'.ret k) + contSuppWeight w k))
  | Cont'.cons₂ k => trStmtsWeight w (head K'.stack <| Λ'.ret k) + contSuppWeight w k
  | Cont'.comp f k => codeSuppWeight' w f k + contSuppWeight w k
  | Cont'.fix f k => codeSuppWeight' w (ToPartrec.Code.fix f) k + contSuppWeight w k
  | Cont'.halt => 0

theorem contSuppList_length (k : Cont') :
    (contSuppList k).length = contSuppLength k := by
  induction k with
  | halt =>
      simp [contSuppList, contSuppLength]
  | cons₁ fs k ih =>
      simp [contSuppList, contSuppLength, trStmtsList_length,
        codeSuppList'_length, ih]
  | cons₂ k ih =>
      simp [contSuppList, contSuppLength, trStmtsList_length, ih]
  | comp f k ih =>
      simp [contSuppList, contSuppLength, codeSuppList'_length, ih]
  | fix f k ih =>
      simp [contSuppList, contSuppLength, codeSuppList'_length, ih]

theorem contSuppList_weight (w : Λ' → Nat) (k : Cont') :
    ((contSuppList k).map w).sum = contSuppWeight w k := by
  induction k with
  | halt =>
      simp [contSuppList, contSuppWeight]
  | cons₁ fs k ih =>
      simp [contSuppList, contSuppWeight, trStmtsList_weight,
        codeSuppList'_weight, ih]
  | cons₂ k ih =>
      simp [contSuppList, contSuppWeight, trStmtsList_weight, ih]
  | comp f k ih =>
      simp [contSuppList, contSuppWeight, codeSuppList'_weight, ih]
  | fix f k ih =>
      simp [contSuppList, contSuppWeight, codeSuppList'_weight, ih]

theorem mem_contSuppList_iff {k : Cont'} {q : Λ'} :
    q ∈ contSuppList k ↔ q ∈ contSupp k := by
  induction k with
  | halt =>
      simp [contSuppList, contSupp]
  | cons₁ fs k ih =>
      simp [contSuppList, contSupp, mem_trStmtsList_iff, mem_codeSuppList'_iff, ih]
  | cons₂ k ih =>
      simp [contSuppList, contSupp, mem_trStmtsList_iff, ih]
  | comp f k ih =>
      simp [contSuppList, contSupp, mem_codeSuppList'_iff, ih]
  | fix f k ih =>
      simp [contSuppList, contSupp, mem_codeSuppList'_iff, ih]

/-- List-valued mirror of Mathlib's `PartrecToTM2.codeSupp`. -/
def codeSuppList (c : ToPartrec.Code) (k : Cont') : List Λ' :=
  codeSuppList' c k ++ contSuppList k

theorem codeSuppList_primrec_of_parts
    (hcode : Primrec₂ codeSuppList') (hcont : Primrec contSuppList) :
    Primrec₂ codeSuppList := by
  apply Primrec₂.mk
  unfold codeSuppList
  exact Primrec.list_append.comp hcode (hcont.comp Primrec.snd)

/-- Numeric length mirror of `codeSuppList`. -/
def codeSuppLength (c : ToPartrec.Code) (k : Cont') : Nat :=
  codeSuppLength' c k + contSuppLength k

theorem codeSuppLength_primrec_of_parts
    (hcode : Primrec₂ codeSuppLength') (hcont : Primrec contSuppLength) :
    Primrec₂ codeSuppLength := by
  apply Primrec₂.mk
  unfold codeSuppLength
  exact Primrec.nat_add.comp hcode (hcont.comp Primrec.snd)

/-- Weighted sum mirror of `codeSuppList`. -/
def codeSuppWeight (w : Λ' → Nat) (c : ToPartrec.Code) (k : Cont') : Nat :=
  codeSuppWeight' w c k + contSuppWeight w k

theorem codeSuppWeight_primrec_of_parts
    {w : Λ' → Nat}
    (hcode : Primrec₂ (codeSuppWeight' w)) (hcont : Primrec (contSuppWeight w)) :
    Primrec₂ (codeSuppWeight w) := by
  apply Primrec₂.mk
  unfold codeSuppWeight
  exact Primrec.nat_add.comp hcode (hcont.comp Primrec.snd)

theorem codeSuppList_length (c : ToPartrec.Code) (k : Cont') :
    (codeSuppList c k).length = codeSuppLength c k := by
  simp [codeSuppList, codeSuppLength, codeSuppList'_length, contSuppList_length]

theorem codeSuppList_weight (w : Λ' → Nat) (c : ToPartrec.Code) (k : Cont') :
    ((codeSuppList c k).map w).sum = codeSuppWeight w c k := by
  simp [codeSuppList, codeSuppWeight, codeSuppList'_weight, contSuppList_weight]

theorem mem_codeSuppList_iff {c : ToPartrec.Code} {k : Cont'} {q : Λ'} :
    q ∈ codeSuppList c k ↔ q ∈ codeSupp c k := by
  simp [codeSuppList, codeSupp, mem_codeSuppList'_iff, mem_contSuppList_iff]

/-- Executable list form of the evaluator label support for code `tc`. -/
def labelList (tc : ToPartrec.Code) : List Λ' :=
  codeSuppList tc Cont'.halt

theorem labelList_primrec_of_codeSuppList
    (h : Primrec₂ codeSuppList) :
    Primrec labelList := by
  unfold labelList
  exact h.comp Primrec.id (Primrec.const Cont'.halt)

/-- Numeric length of the evaluator label support for code `tc`. -/
def labelCount (tc : ToPartrec.Code) : Nat :=
  codeSuppLength tc Cont'.halt

theorem labelCount_primrec_of_codeSuppLength
    (h : Primrec₂ codeSuppLength) :
    Primrec labelCount := by
  unfold labelCount
  exact h.comp Primrec.id (Primrec.const Cont'.halt)

/-- Weighted sum of the evaluator label support for code `tc`. -/
def labelWeight (w : Λ' → Nat) (tc : ToPartrec.Code) : Nat :=
  codeSuppWeight w tc Cont'.halt

theorem labelWeight_primrec_of_codeSuppWeight
    {w : Λ' → Nat} (h : Primrec₂ (codeSuppWeight w)) :
    Primrec (labelWeight w) := by
  unfold labelWeight
  exact h.comp Primrec.id (Primrec.const Cont'.halt)

theorem labelList_length (tc : ToPartrec.Code) :
    (labelList tc).length = labelCount tc := by
  simp [labelList, labelCount, codeSuppList_length]

theorem labelList_weight (w : Λ' → Nat) (tc : ToPartrec.Code) :
    ((labelList tc).map w).sum = labelWeight w tc := by
  simp [labelList, labelWeight, codeSuppList_weight]

theorem mem_labelList_iff {tc : ToPartrec.Code} {q : Λ'} :
    q ∈ labelList tc ↔ q ∈ PartrecToTM2Support.labels tc := by
  simp [labelList, PartrecToTM2Support.labels, mem_codeSuppList_iff]

theorem startLabel_mem_labelList (tc : ToPartrec.Code) :
    PartrecToTM2Support.startLabel tc ∈ labelList tc := by
  exact mem_labelList_iff.2 (PartrecToTM2Support.startLabel_mem_labels tc)

end PartrecToTM2SupportList

end LeanWang
