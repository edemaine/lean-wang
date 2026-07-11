/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.NatPartrecToToPartrec
import LeanWang.TM0Route
import LeanWang.UniversalCode

/-!
# One fixed universal TM0 machine

This is the semantic core of the simplified machine reduction.  Instead of
compiling every source program into new finite control, translate the single
universal code once.  The varying source code is supplied as ordinary input to
that fixed machine.
-/

noncomputable section

namespace LeanWang

namespace UniversalTM0

open Encodable

private theorem trNum_eq (n : Num) :
    Turing.PartrecToTM2.trNum n =
      if (n : Nat) = 0 then []
      else
        (if (n : Nat).bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) ::
            Turing.PartrecToTM2.trNat (n : Nat).div2 := by
  cases n with
  | zero => rfl
  | pos n =>
      cases n with
      | one => rfl
      | bit0 a =>
          have hpos : (a : Nat) ≠ 0 := Nat.ne_of_gt (PosNum.cast_pos a)
          have hdiv : ((a : Nat) + (a : Nat)).div2 = (a : Nat) := by
            rw [Nat.div2_val, ← two_mul]
            simp
          have htr : Turing.PartrecToTM2.trNat (a : Nat) =
              Turing.PartrecToTM2.trPosNum a := by
            simp [Turing.PartrecToTM2.trNat, Turing.PartrecToTM2.trNum]
          simp [Turing.PartrecToTM2.trNum, Turing.PartrecToTM2.trPosNum,
            hpos, hdiv, htr]
      | bit1 a =>
          have hpos : (a : Nat) ≠ 0 := Nat.ne_of_gt (PosNum.cast_pos a)
          have hdiv0 : ((a : Nat) + (a : Nat)).div2 = (a : Nat) := by
            rw [Nat.div2_val, ← two_mul]
            simp
          have htr : Turing.PartrecToTM2.trNat (a : Nat) =
              Turing.PartrecToTM2.trPosNum a := by
            simp [Turing.PartrecToTM2.trNat, Turing.PartrecToTM2.trNum]
          simp [Turing.PartrecToTM2.trNum, Turing.PartrecToTM2.trPosNum,
            hpos, hdiv0, htr]

private theorem trNat_eq (n : Nat) :
    Turing.PartrecToTM2.trNat n =
      if n = 0 then []
      else
        (if n.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) ::
            Turing.PartrecToTM2.trNat n.div2 := by
  simpa [Turing.PartrecToTM2.trNat] using trNum_eq (n : Num)

private def trNatStep
    (prior : List (List Turing.PartrecToTM2.Γ')) :
    Option (List Turing.PartrecToTM2.Γ') :=
  let n := prior.length
  if n = 0 then some []
  else
    prior[n.div2]?.map fun tail =>
      (if n.bodd then Turing.PartrecToTM2.Γ'.bit1
        else Turing.PartrecToTM2.Γ'.bit0) :: tail

private theorem trNatStep_primrec : Primrec trNatStep := by
  unfold trNatStep
  have hn : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior.length) := Primrec.list_length
  have hzero : PrimrecPred (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior.length = 0) :=
    Primrec.eq.comp hn (Primrec.const 0)
  have hlookup : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior[prior.length.div2]?) :=
    Primrec.list_getElem?.comp
      Primrec.id (Primrec.nat_div2.comp hn)
  have hdigit : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      if prior.length.bodd then Turing.PartrecToTM2.Γ'.bit1
      else Turing.PartrecToTM2.Γ'.bit0) :=
    (Primrec.cond (Primrec.nat_bodd.comp hn)
      (Primrec.const Turing.PartrecToTM2.Γ'.bit1)
      (Primrec.const Turing.PartrecToTM2.Γ'.bit0)).of_eq fun prior => by
        cases prior.length.bodd <;> simp
  have hcons : Primrec₂ (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      fun tail : List Turing.PartrecToTM2.Γ' =>
        (if prior.length.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) :: tail) := by
    apply Primrec₂.mk
    exact Primrec.list_cons.comp
      (hdigit.comp Primrec.fst) Primrec.snd
  have hnext : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior[prior.length.div2]?.map fun tail =>
        (if prior.length.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) :: tail) :=
    Primrec.option_map hlookup hcons
  exact Primrec.ite hzero
    (Primrec.const (some ([] : List Turing.PartrecToTM2.Γ'))) hnext

private theorem trNat_primrec :
    Primrec Turing.PartrecToTM2.trNat := by
  have hrec : Primrec₂ (fun _ : Unit => Turing.PartrecToTM2.trNat) :=
    Primrec.nat_strong_rec
      (fun _ : Unit => Turing.PartrecToTM2.trNat)
      (show Primrec₂ (fun _ : Unit => fun prior => trNatStep prior) from
        Primrec₂.mk (trNatStep_primrec.comp
          (Primrec.snd : Primrec
            (fun p : Unit × List (List Turing.PartrecToTM2.Γ') => p.2))))
      (by
        intro _ n
        unfold trNatStep
        simp only [List.length_map, List.length_range]
        by_cases hn : n = 0
        · subst n
          simp [trNat_eq]
        · have hlt : n.div2 < n := Nat.binaryRec_decreasing hn
          rw [if_neg hn]
          rw [trNat_eq n, if_neg hn]
          simp [List.getElem?_map, List.getElem?_range hlt])
  exact hrec.comp (Primrec.const ()) Primrec.id

private theorem partrecStartedTM2InputFor_primrec :
    Primrec TM0Route.partrecStartedTM2InputFor := by
  unfold TM0Route.partrecStartedTM2InputFor Turing.PartrecToTM2.trList
  exact Primrec.list_append.comp trNat_primrec
    (Primrec.const [Turing.PartrecToTM2.Γ'.cons])

private def tm0InputCell (a : Turing.PartrecToTM2.Γ') :
    TM0Route.PartrecStartedTM0Symbol :=
  (false, Function.update (fun _ : TM0Route.PartrecStack => none)
    Turing.PartrecToTM2.K'.main (some a))

private theorem tm0InputCell_primrec : Primrec tm0InputCell := by
  classical
  exact Primrec.dom_finite tm0InputCell

private def markTM0InputHead (a : TM0Route.PartrecStartedTM0Symbol) :
    TM0Route.PartrecStartedTM0Symbol :=
  (true, a.2)

private theorem markTM0InputHead_primrec : Primrec markTM0InputHead := by
  classical
  exact Primrec.dom_finite markTM0InputHead

private theorem partrecStartedTM0InputFor_primrec :
    Primrec TM0Route.partrecStartedTM0InputFor := by
  have hreversed : Primrec (fun n : Nat =>
      (TM0Route.partrecStartedTM2InputFor n).reverse) :=
    Primrec.list_reverse.comp partrecStartedTM2InputFor_primrec
  have hmapped : Primrec (fun n : Nat =>
      (TM0Route.partrecStartedTM2InputFor n).reverse.map tm0InputCell) := by
    refine Primrec.list_map hreversed ?_
    apply Primrec₂.mk
    exact tm0InputCell_primrec.comp Primrec.snd
  have hhead : Primrec (fun n : Nat =>
      ((TM0Route.partrecStartedTM2InputFor n).reverse.map tm0InputCell).headI) :=
    Primrec.list_headI.comp hmapped
  have htail : Primrec (fun n : Nat =>
      ((TM0Route.partrecStartedTM2InputFor n).reverse.map tm0InputCell).tail) :=
    Primrec.list_tail.comp hmapped
  exact (Primrec.list_cons.comp
    (markTM0InputHead_primrec.comp hhead) htail).of_eq fun n => by
      rfl

/-- Input to the universal evaluator for running `c` on `0`. -/
def sourceInput (c : Nat.Partrec.Code) : Nat :=
  Nat.pair (encode c) 0

theorem sourceInput_primrec : Primrec sourceInput := by
  unfold sourceInput
  exact Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)

theorem sourceInput_computable : Computable sourceInput :=
  sourceInput_primrec.to_comp

/-- The fixed list-language code compiled by the machine reduction. -/
def code : Turing.ToPartrec.Code :=
  NatPartrecToToPartrec.translate UniversalCode.universalCode

/-- The fixed TM0 control used for every source program. -/
def machine :=
  TM0Route.partrecStartedTM0Machine code

/-- Only the initial tape depends on the source program. -/
def input (c : Nat.Partrec.Code) :=
  TM0Route.partrecStartedTM0InputFor (sourceInput c)

theorem input_ne_nil (c : Nat.Partrec.Code) : input c ≠ [] := by
  simp [input, TM0Route.partrecStartedTM0InputFor, Turing.TM2to1.trInit]

/--
The varying initial tape is computable from the source code.  This is now a
standalone binary-encoding lemma; it does not inspect or compile source syntax.
-/
theorem input_primrec : Primrec input := by
  exact partrecStartedTM0InputFor_primrec.comp sourceInput_primrec

theorem input_computable : Computable input := by
  exact input_primrec.to_comp

theorem eval_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM0.eval machine (input c)).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  rw [machine, input]
  rw [TM0Route.partrecStartedTM0_eval_dom_iff_tm2_for]
  rw [TM0Route.partrecStartedTM2_eval_dom_iff_partrec_for]
  change
    (StateTransition.eval
      (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init
        (NatPartrecToToPartrec.translate UniversalCode.universalCode)
        [sourceInput c])).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom
  rw [NatPartrecToToPartrec.translate_tm2_dom_at]
  rw [sourceInput, UniversalCode.universalCode_eval]

/-- Complemented form used by the Wang-tiling construction. -/
theorem not_eval_dom_iff (c : Nat.Partrec.Code) :
    ¬ (Turing.TM0.eval machine (input c)).Dom ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [eval_dom_iff]

end UniversalTM0

end LeanWang
