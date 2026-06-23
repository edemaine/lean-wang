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
