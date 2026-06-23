/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0Route

/-!
State-code helpers for the Mathlib TM0 route.

The live finite-program construction is the folded simulation in
`TM0FoldedCompiler`. That proof still needs a numeric code for supported
Mathlib TM0 labels and the basic fact that one Mathlib TM0 step stays inside
the finite support. This file keeps only those shared helpers; it deliberately
does not build a direct table for the two-sided Mathlib TM0 machine.
-/

namespace LeanWang

namespace TM0FiniteCompiler

open TM0Route

/-- Numeric code for a supported translated TM0 state. -/
def stateCode (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) : Nat :=
  (TM0Route.partrecStartedTM0LabelSupportList tc).idxOf q

theorem stateCode_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (stateCode tc) := by
  unfold stateCode
  exact Primrec.list_idxOf₁ (TM0Route.partrecStartedTM0LabelSupportList tc)

/--
Bounded first-occurrence search for the numeric code of a translated TM0 label,
using the executable support-position decoder rather than materializing the
dependent support list directly.
-/
def stateCodeBySupportSearch (tc : Turing.ToPartrec.Code) (fuel : Nat)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) : Nat :=
  (List.range (TM0Route.partrecStartedTM0StateCount tc)).findIdx fun p =>
    decide (TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom? tc fuel p = some q)

theorem stateCodeBySupportSearch_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc) =>
      stateCodeBySupportSearch tc p.1 p.2) := by
  unfold stateCodeBySupportSearch
  have hlist : Primrec (fun _p : Nat ×
      Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc) =>
      List.range (TM0Route.partrecStartedTM0StateCount tc)) :=
    Primrec.const (List.range (TM0Route.partrecStartedTM0StateCount tc))
  have hpred : Primrec₂ (fun p : Nat ×
      Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc) => fun i : Nat =>
      decide (TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom? tc p.1 i =
        some p.2)) := by
    apply Primrec₂.mk
    have hdecode : Primrec (fun p : (Nat ×
        Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) × Nat =>
        TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom? tc p.1.1 p.2) :=
      (TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom?_primrec_fixed tc).comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    have htarget : Primrec (fun p : (Nat ×
        Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) × Nat =>
        (some p.1.2 : Option
          (Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)))) :=
      Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)
    exact Primrec.eq.decide.comp hdecode htarget
  exact Primrec.list_findIdx hlist hpred

private theorem range_findIdx_getElem?_eq_idxOf_of_mem {α : Type} [DecidableEq α]
    (xs : List α) {x : α} (hx : x ∈ xs) :
    (List.range xs.length).findIdx (fun i => decide (xs[i]? = some x)) = xs.idxOf x := by
  have hidx : xs.idxOf x < xs.length := List.idxOf_lt_length_of_mem hx
  apply (List.findIdx_eq (xs := List.range xs.length)
    (p := fun i => decide (xs[i]? = some x)) ?hrange).2
  · constructor
    · have hget := List.getElem?_idxOf hx
      rw [List.getElem_range]
      rw [hget]
      simp
    · intro j hj
      simp only [List.getElem_range]
      have hjlen : j < xs.length := lt_trans hj hidx
      simp only [decide_eq_false_iff_not]
      intro hget
      have hxTake : x ∈ xs.take (j + 1) := by
        rw [List.mem_iff_getElem?]
        exact ⟨j, by simpa [List.getElem?_take, hjlen, Nat.lt_succ_self] using hget⟩
      have hidxlt : xs.idxOf x < j + 1 :=
        (List.mem_take_iff_idxOf_lt (n := j + 1) hx).1 hxTake
      omega
  · simpa [List.length_range] using hidx

theorem stateCodeBySupportSearch_eq_stateCode (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0LabelSupportList tc) :
    stateCodeBySupportSearch tc (TM0Route.partrecStartedTM0StatementCount tc) q =
      stateCode tc q := by
  unfold stateCodeBySupportSearch stateCode
  rw [← TM0Route.partrecStartedTM0LabelSupportList_length_eq_stateCount tc]
  let support := TM0Route.partrecStartedTM0LabelSupportList tc
  change
    (List.range support.length).findIdx
        (fun p => decide
          (TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom? tc
              (TM0Route.partrecStartedTM0StatementCount tc) p =
            some q)) =
      support.idxOf q
  rw [show (fun p => decide
          (TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom? tc
              (TM0Route.partrecStartedTM0StatementCount tc) p =
            some q)) =
        (fun p => decide (support[p]? = some q)) by
      funext p
      rw [TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom?_start_eq_getElem?]]
  exact range_findIdx_getElem?_eq_idxOf_of_mem support hq

theorem stateCode_default (tc : Turing.ToPartrec.Code)
    : stateCode tc (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) =
      TM0Route.partrecStartedTM0Start := by
  simp [stateCode, TM0Route.partrecStartedTM0LabelSupportList,
    TM0Route.partrecStartedTM0Start]

theorem stateCode_mem_states (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc) :
    stateCode tc q ∈ TM0Route.partrecStartedTM0States tc := by
  unfold stateCode TM0Route.partrecStartedTM0States
  exact List.mem_range.2 (by
    rw [← TM0Route.partrecStartedTM0LabelSupportList_length_eq_stateCount]
    exact List.idxOf_lt_length_iff.2
      (TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq))

theorem labelSupportAtByStatementFrom?_stateCode
    (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0LabelSupportList tc) :
    TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom? tc
        (TM0Route.partrecStartedTM0StatementCount tc) (stateCode tc q) =
      some q := by
  rw [TM0Route.partrecStartedTM0LabelSupportAtByStatementFrom?_start_eq_getElem?]
  exact TM0Route.partrecStartedTM0StateCodeOfMem_get? tc q hq

theorem stateCode_ne_start_of_mem_labels_ne_default {tc : Turing.ToPartrec.Code}
    {q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hneq : q ≠ (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))) :
    stateCode tc q ≠ TM0Route.partrecStartedTM0Start := by
  let hqsupport := TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq
  have hcode :
      stateCode tc q = TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport := by
    rfl
  intro hstart
  have hindexStart :
      TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport =
        TM0Route.partrecStartedTM0Start := by
    simpa [hcode] using hstart
  have hget := TM0Route.partrecStartedTM0StateCodeOfMem_get? tc q hqsupport
  rw [hindexStart] at hget
  unfold TM0Route.partrecStartedTM0Start at hget
  rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero] at hget
  cases hget
  exact hneq rfl

theorem stateCode_injective_on_labels {tc : Turing.ToPartrec.Code}
    {q r : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hr : r ∈ TM0Route.partrecStartedTM0Labels tc)
    (hcode : stateCode tc q = stateCode tc r) :
    q = r := by
  by_cases hqdef :
      q = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
  · subst q
    by_cases hrdef :
        r = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    · exact hrdef.symm
    · have hrne := stateCode_ne_start_of_mem_labels_ne_default hr hrdef
      have hstart := stateCode_default tc
      rw [hstart] at hcode
      exact False.elim (hrne hcode.symm)
  · by_cases hrdef :
        r = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    · subst r
      have hqne := stateCode_ne_start_of_mem_labels_ne_default hq hqdef
      have hstart := stateCode_default tc
      rw [hstart] at hcode
      exact False.elim (hqne hcode)
    · let hqsupport := TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq
      let hrsupport := TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hr
      have hqcode :
          stateCode tc q = TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport := by
        rfl
      have hrcode :
          stateCode tc r = TM0Route.partrecStartedTM0StateCodeOfMem tc r hrsupport := by
        rfl
      have hindex :
          TM0Route.partrecStartedTM0StateCodeOfMem tc q hqsupport =
            TM0Route.partrecStartedTM0StateCodeOfMem tc r hrsupport := by
        simpa [hqcode, hrcode] using hcode
      have hgetq := TM0Route.partrecStartedTM0StateCodeOfMem_get? tc q hqsupport
      have hgetr := TM0Route.partrecStartedTM0StateCodeOfMem_get? tc r hrsupport
      rw [hindex, hgetr] at hgetq
      cases hgetq
      rfl

theorem next_label_mem_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    q' ∈ TM0Route.partrecStartedTM0Labels tc := by
  exact (TM0Route.partrecStartedTM0_supports tc).2
    (show (q', stmt) ∈ TM0Route.partrecStartedTM0Machine tc q a by
      rw [hstep]
      simp)
    hq

end TM0FiniteCompiler

end LeanWang
