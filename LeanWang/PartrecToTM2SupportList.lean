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

theorem codeSuppList_length (c : ToPartrec.Code) (k : Cont') :
    (codeSuppList c k).length = codeSuppLength c k := by
  simp [codeSuppList, codeSuppLength, codeSuppList'_length, contSuppList_length]

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

theorem labelList_length (tc : ToPartrec.Code) :
    (labelList tc).length = labelCount tc := by
  simp [labelList, labelCount, codeSuppList_length]

theorem mem_labelList_iff {tc : ToPartrec.Code} {q : Λ'} :
    q ∈ labelList tc ↔ q ∈ PartrecToTM2Support.labels tc := by
  simp [labelList, PartrecToTM2Support.labels, mem_codeSuppList_iff]

theorem startLabel_mem_labelList (tc : ToPartrec.Code) :
    PartrecToTM2Support.startLabel tc ∈ labelList tc := by
  exact mem_labelList_iff.2 (PartrecToTM2Support.startLabel_mem_labels tc)

end PartrecToTM2SupportList

end LeanWang
