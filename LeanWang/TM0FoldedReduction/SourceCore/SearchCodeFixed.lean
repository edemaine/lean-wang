/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourceCore.SearchCode

/-!
Fixed-code primitive-recursion facts for bounded-search source decoders.

The final reduction needs the corresponding fact uniformly in
`Nat.Partrec.Code`.  This module records the already-available fixed-code
computability supplied by the folded compiler, keeping the remaining
uniformization target explicit.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of the support-search decoder's variable branch. -/
theorem sourceSearchCodeDecoderStepVar_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar c p.1 p.2.1 p.2.2) := by
  have hrows : Primrec (fun p : Nat × Nat × TM0Route.PartrecVar =>
      sourceSearchCodeOneRowsVar c p.1 p.2.2) :=
    (sourceSearchCodeOneRowsVar_primrec_fixed c).comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  exact (Primrec.pair Primrec.fst
    (Primrec.pair
      (Primrec.fst.comp Primrec.snd)
      (Primrec.option_some.comp hrows))).of_eq fun p => by
        exact (sourceSearchCodeDecoderStepVar_eq_oneRows c p.1 p.2.1 p.2.2).symm

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of the unresolved support-search decoder branch. -/
theorem sourceSearchCodeDecoderStepNone_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat =>
      sourceSearchCodeDecoderStepNone c p.1 p.2) := by
  have hlookup : Primrec (fun p : Nat × Nat =>
      TM0Route.partrecVarList[p.2]?) :=
    (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp Primrec.snd
  have hnone : Primrec (fun p : Nat × Nat =>
      (p.1 + 1, p.2 - TM0Route.partrecVarList.length,
        (none : Option (List TM0FoldedCompiler.SimStepData)))) := by
    exact Primrec.pair
      (Primrec.succ.comp Primrec.fst)
      (Primrec.pair
        (Primrec.nat_sub.comp Primrec.snd
          (Primrec.const TM0Route.partrecVarList.length))
        (Primrec.const (none : Option (List TM0FoldedCompiler.SimStepData))))
  have hvar := sourceSearchCodeDecoderStepVar_primrec_fixed c
  have hsome : Primrec₂ (fun p : Nat × Nat => fun v : TM0Route.PartrecVar =>
      sourceSearchCodeDecoderStepVar c p.1 p.2 v) := by
    apply Primrec₂.mk
    exact hvar.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    cases h : TM0Route.partrecVarList[p.2]? <;>
      simp [sourceSearchCodeDecoderStepNone, h]

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of one support-search decoder accumulator step. -/
theorem sourceSearchCodeDecoderStep_primrec_fixed (c : Code) :
    Primrec (sourceSearchCodeDecoderStep c) := by
  have hopt : Primrec (fun s : SourceSearchCodeDecoderState => s.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnoneStep := sourceSearchCodeDecoderStepNone_primrec_fixed c
  have hnoneCase : Primrec (fun s : SourceSearchCodeDecoderState =>
      sourceSearchCodeDecoderStepNone c s.1 s.2.1) :=
    hnoneStep.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hsome : Primrec₂
      (fun s : SourceSearchCodeDecoderState =>
        fun rows : List TM0FoldedCompiler.SimStepData =>
          (s.1, s.2.1, some rows)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp Primrec.snd))
  exact (Primrec.option_casesOn hopt hnoneCase hsome).of_eq fun s => by
    cases h : s.2.2 <;> simp [sourceSearchCodeDecoderStep, h]

set_option linter.style.longLine false in
/--
For each fixed source code, the bounded-search offset descriptor decoder is
primitive recursive in the fuel, statement offset, and variable-list offset.

The stronger source theorem must make the same construction primitive recursive
while the source code varies.
-/
theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode c p.1 p.2.1 p.2.2) := by
  exact (TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_primrec_fixed
    (NatPartrecToToPartrec.translate c)).of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexFromWithSearchCode
      rfl

set_option linter.style.longLine false in
/-- Fixed-source primitive-recursiveness of the iterated support-search decoder. -/
theorem sourceSearchCodeDecoder_primrec_fixed (c : Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      sourceSearchCodeDecoder c p.1 p.2.1 p.2.2) :=
  (sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_fixed c).of_eq fun p =>
    (sourceSearchCodeDecoder_eq_sourceSimStepDataForLabelIndexFromWithSearchCode
      c p.1 p.2.1 p.2.2).symm

end TM0FoldedReduction

end LeanWang
