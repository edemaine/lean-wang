/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PartrecToTM2Support

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

theorem mem_codeSuppList_iff {c : ToPartrec.Code} {k : Cont'} {q : Λ'} :
    q ∈ codeSuppList c k ↔ q ∈ codeSupp c k := by
  simp [codeSuppList, codeSupp, mem_codeSuppList'_iff, mem_contSuppList_iff]

/-- Executable list form of the evaluator label support for code `tc`. -/
def labelList (tc : ToPartrec.Code) : List Λ' :=
  codeSuppList tc Cont'.halt

theorem mem_labelList_iff {tc : ToPartrec.Code} {q : Λ'} :
    q ∈ labelList tc ↔ q ∈ PartrecToTM2Support.labels tc := by
  simp [labelList, PartrecToTM2Support.labels, mem_codeSuppList_iff]

theorem startLabel_mem_labelList (tc : ToPartrec.Code) :
    PartrecToTM2Support.startLabel tc ∈ labelList tc := by
  exact mem_labelList_iff.2 (PartrecToTM2Support.startLabel_mem_labels tc)

end PartrecToTM2SupportList

end LeanWang
