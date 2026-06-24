/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.NatPartrecToToPartrec
import LeanWang.TM0FoldedProgram
import LeanWang.Theorems
import Mathlib.Computability.Reduce

/-!
Packaging the folded finite-TM0 construction as the machine-side reduction.

`TM0FoldedProgram` provides the executable finite program data. This file
isolates the exact obligations needed to instantiate the main theorem surface:
computability of that program map and its semantic correctness against Mathlib's
translated TM0 evaluator.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/-- The remaining obligations for the folded finite-TM0 route. -/
structure Obligations where
  program_computable :
    Computable (fun tc : Turing.ToPartrec.Code => TM0FoldedCompiler.program tc)
  correct : ∀ tc : Turing.ToPartrec.Code,
    (TM0FoldedCompiler.program tc).HaltsEmpty ↔
      (Turing.TM0.eval
        (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom

/--
The exact obligations needed for the final reduction from `Nat.Partrec.Code`.

This avoids asking for computability of the folded compiler on every
`Turing.ToPartrec.Code`; the undecidability proof only uses codes reached by the
computable translation `NatPartrecToToPartrec.translate`.
-/
structure SourceObligations where
  program_computable :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))
  correct : ∀ c : Code,
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)).HaltsEmpty ↔
      (Nat.Partrec.Code.eval c 0).Dom

/-- Broad folded-route obligations imply the source-code obligations actually used. -/
def Obligations.toSource (h : Obligations) : SourceObligations where
  program_computable := by
    exact (h.program_computable.comp NatPartrecToToPartrec.translate_computable).of_eq
      fun c => (TM0FoldedCompiler.programData_eq_program
        (NatPartrecToToPartrec.translate c)).symm
  correct := by
    intro c
    rw [TM0FoldedCompiler.programData_eq_program]
    exact (h.correct (NatPartrecToToPartrec.translate c)).trans
      ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2
          (NatPartrecToToPartrec.translate c)).trans
        ((TM0Route.partrecStartedTM2_eval_dom_iff_partrec
            (NatPartrecToToPartrec.translate c)).trans
          (NatPartrecToToPartrec.translate_tm2_dom c)))

/-- Source-code descriptor list for the folded finite-TM0 reduction. -/
def sourceSimStepData (c : Code) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepData (NatPartrecToToPartrec.translate c)

/-- Source-code normalized folded program data. -/
def sourceProgramData (c : Code) : FiniteTM0Program :=
  TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)

theorem sourceProgramData_eq (c : Code) :
    sourceProgramData c =
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c) :=
  rfl

theorem sourceSimStepData_eq (c : Code) :
    sourceSimStepData c =
      TM0FoldedCompiler.simStepData (NatPartrecToToPartrec.translate c) :=
  rfl

/--
Source-code version of the fully offset descriptor decoder.

This is the computability target that the final reduction actually needs:
before decoding finite TM0 labels, compose the source `Nat.Partrec.Code` with
the fixed translation to Mathlib `ToPartrec.Code`.
-/
def sourceSimStepDataForLabelIndexFrom
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFrom
    (NatPartrecToToPartrec.translate c) fuel k i

/--
Source-code version of the fully offset descriptor decoder factored through
numeric folded state codes.
-/
def sourceSimStepDataForLabelIndexFromWithCode
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
    (NatPartrecToToPartrec.translate c) fuel k i

/--
Source-code version of the fully offset descriptor decoder whose current-state
code is computed by bounded support search.
-/
def sourceSimStepDataForLabelIndexFromWithSearchCode
    (c : Code) (fuel k i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
    (NatPartrecToToPartrec.translate c) fuel k i

/-- Source-code version of the canonical offset-start descriptor decoder. -/
def sourceSimStepDataForLabelIndexStart
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStart
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the canonical numeric-state offset-start decoder. -/
def sourceSimStepDataForLabelIndexStartWithCode
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
    (NatPartrecToToPartrec.translate c) i

/-- Source-code version of the semantic label-index descriptor decoder. -/
def sourceSimStepDataForLabelIndex
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndex
    (NatPartrecToToPartrec.translate c) i

/-- Source-code indexed descriptor list for the folded finite-TM0 reduction. -/
def sourceSimStepDataByLabelIndex (c : Code) : List TM0FoldedCompiler.SimStepData :=
  (List.range
      (TM0Route.partrecStartedTM0LabelCount
        (NatPartrecToToPartrec.translate c))).flatMap
    (sourceSimStepDataForLabelIndex c)

/-- Source-code indexed descriptor list through the numeric-state decoder path. -/
def sourceSimStepDataByLabelIndexWithCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range
      (TM0Route.partrecStartedTM0LabelCount
        (NatPartrecToToPartrec.translate c))).flatMap
    (sourceSimStepDataForLabelIndexStartWithCode c)

theorem sourceSimStepDataForLabelIndexStart_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStart c i =
      sourceSimStepDataForLabelIndex c i := by
  unfold sourceSimStepDataForLabelIndexStart sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataForLabelIndexStart_eq
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexStartWithCode_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithCode c i =
      sourceSimStepDataForLabelIndex c i := by
  unfold sourceSimStepDataForLabelIndexStartWithCode sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode_eq
    (NatPartrecToToPartrec.translate c) i

theorem sourceSimStepDataForLabelIndexFrom_eq_withCode
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFrom c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFrom sourceSimStepDataForLabelIndexFromWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexFrom_eq_withCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (c : Code) (fuel k i : Nat) :
    sourceSimStepDataForLabelIndexFromWithSearchCode c fuel k i =
      sourceSimStepDataForLabelIndexFromWithCode c fuel k i := by
  unfold sourceSimStepDataForLabelIndexFromWithSearchCode
    sourceSimStepDataForLabelIndexFromWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (NatPartrecToToPartrec.translate c) fuel k i

theorem sourceSimStepDataByLabelIndex_eq (c : Code) :
    sourceSimStepDataByLabelIndex c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndex sourceSimStepData sourceSimStepDataForLabelIndex
  exact TM0FoldedCompiler.simStepDataByLabelIndex_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithCode c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndexWithCode sourceSimStepData
  exact TM0FoldedCompiler.simStepDataByLabelIndexWithCode_eq
    (NatPartrecToToPartrec.translate c)

/--
Primitive recursiveness of the translated source-level offset decoder is enough
for the source-level indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndex_primrec_of_source_labelIndexFrom
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndex := by
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStart p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFrom p.1
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate p.1)) 0 p.2) :=
      hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          ((TM0Route.partrecStartedTM0StatementCount_primrec.comp
              NatPartrecToToPartrec.translate_primrec).comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStart sourceSimStepDataForLabelIndexFrom
        TM0FoldedCompiler.simStepDataForLabelIndexStart
      rfl
  have hlabel : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndex p.1 p.2) :=
    hstart.of_eq fun p => sourceSimStepDataForLabelIndexStart_eq p.1 p.2
  unfold sourceSimStepDataByLabelIndex
  refine Primrec.list_flatMap
    (Primrec.list_range.comp
      ((TM0Route.partrecStartedTM0LabelCount_primrec.comp
          NatPartrecToToPartrec.translate_primrec))) ?_
  apply Primrec₂.mk
  exact hlabel

/--
Primitive recursiveness of the source-level canonical numeric-state decoder is
enough for the source-level numeric-state indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithCode := by
  unfold sourceSimStepDataByLabelIndexWithCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp
      ((TM0Route.partrecStartedTM0LabelCount_primrec.comp
          NatPartrecToToPartrec.translate_primrec))) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level numeric-state offset decoder is
enough for primitive recursiveness of the source-level numeric-state indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexFromWithCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithCode := by
  apply sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithCode p.1
          (TM0Route.partrecStartedTM0StatementCount
            (NatPartrecToToPartrec.translate p.1)) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            ((TM0Route.partrecStartedTM0StatementCount_primrec.comp
                NatPartrecToToPartrec.translate_primrec).comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithCode
        sourceSimStepDataForLabelIndexFromWithCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
      rfl
  exact hstart

/--
The older global offset-decoder target implies the source-specific decoder
target by precomposing with the `Nat.Partrec.Code` translation.
-/
theorem sourceSimStepDataForLabelIndexFrom_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFrom
        rfl

/--
The source-level numeric-state offset decoder implies the source-level semantic
offset decoder by the data-level `WithCode` factoring theorem.
-/
theorem sourceSimStepDataForLabelIndexFrom_primrec_of_source_withCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hindex.of_eq fun p =>
    (sourceSimStepDataForLabelIndexFrom_eq_withCode p.1 p.2.1 p.2.2.1 p.2.2.2).symm

/--
The older global numeric-state offset-decoder target implies the source-specific
numeric-state decoder target by precomposing with the source translation.
-/
theorem sourceSimStepDataForLabelIndexFromWithCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithCode
        rfl

/--
The older global bounded-search offset-decoder target implies the
source-specific bounded-search decoder target by precomposing with the source
translation.
-/
theorem sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithSearchCode
        rfl

theorem sourceSimStepDataForLabelIndexFromWithCode_primrec_of_source_searchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  hindex.of_eq fun p =>
    sourceSimStepDataForLabelIndexFromWithSearchCode_eq_withCode
      p.1 p.2.1 p.2.2.1 p.2.2.2

/--
Global primitive recursiveness of the canonical numeric-state decoder implies
the source-specific canonical numeric-state decoder target by precomposing with
the source-code translation.
-/
theorem sourceSimStepDataForLabelIndexStartWithCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexStartWithCode
        rfl

/--
Global primitive recursiveness of the folded descriptor list is enough for the
source-level normalized folded program-data map used by the final reduction.
-/
theorem sourceProgramData_computable_of_global_simStepData
    (hsteps : Primrec TM0FoldedCompiler.simStepData) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepData hsteps).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_simStepData'
    (hsteps : Primrec TM0FoldedCompiler.simStepData) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_simStepData hsteps).of_eq fun _ => rfl

-- The source-level indexed descriptor list is enough for computability of the
-- normalized folded finite-TM0 program data used by the final reduction.
set_option maxHeartbeats 800000 in
-- The final equality unfolds normalized program data and the descriptor-row compiler.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndex
    (hsteps : Primrec sourceSimStepDataByLabelIndex) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (TM0Route.partrecStartedTM0StateCount
          (NatPartrecToToPartrec.translate c))
        (sourceSimStepDataByLabelIndex c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        (TM0Route.partrecStartedTM0StateCount_primrec.comp
          NatPartrecToToPartrec.translate_primrec)
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndex_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

set_option maxHeartbeats 800000 in
-- The final equality unfolds normalized program data and the descriptor-row compiler.
theorem sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (hsteps : Primrec sourceSimStepDataByLabelIndexWithCode) :
    Computable sourceProgramData := by
  have hdata : Primrec (fun c : Code =>
      TM0FoldedCompiler.programDataOfStepData
        (TM0Route.partrecStartedTM0StateCount
          (NatPartrecToToPartrec.translate c))
        (sourceSimStepDataByLabelIndexWithCode c)) := by
    exact TM0FoldedCompiler.programDataOfStepData_primrec.comp
      (Primrec.pair
        (TM0Route.partrecStartedTM0StateCount_primrec.comp
          NatPartrecToToPartrec.translate_primrec)
        hsteps)
  exact (hdata.of_eq fun c => by
    unfold sourceProgramData TM0FoldedCompiler.programData
      TM0FoldedCompiler.programDataOfStepData
    rw [sourceSimStepDataByLabelIndexWithCode_eq c]
    rw [sourceSimStepData_eq c]
    rw [← TM0FoldedCompiler.simRows_eq_stepData
      (NatPartrecToToPartrec.translate c)]).to_comp

/--
Primitive recursiveness of the source-level canonical numeric-state decoder is
enough for computability of the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexStartWithCode
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexStartWithCode hindex)

/--
The remaining source-level folded computability target: primitive recursiveness
of the translated fully offset decoder implies computability of the normalized
folded finite-TM0 program data used by the final reduction.
-/
theorem sourceProgramData_computable_of_source_labelIndexFrom
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndex
    (sourceSimStepDataByLabelIndex_primrec_of_source_labelIndexFrom hindex)

/--
The numeric-state source-level folded computability target. This is equivalent
to the semantic source decoder target, but exposes the state code fed to the
finite program.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_simStepDataByLabelIndexWithCode
    (sourceSimStepDataByLabelIndexWithCode_primrec_of_source_labelIndexFromWithCode hindex)

/--
The source-level bounded-search decoder target is enough for computability of
the normalized folded finite-TM0 program data.
-/
theorem sourceProgramData_computable_of_source_labelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  sourceProgramData_computable_of_source_labelIndexFromWithCode
    (sourceSimStepDataForLabelIndexFromWithCode_primrec_of_source_searchCode hindex)

/--
The current lowest-level folded computability target, phrased at source-code
level: primitive recursiveness of the fully offset label-index descriptor
decoder implies computability of the normalized folded finite-TM0 program data
used by the final reduction.
-/
theorem sourceProgramData_computable_of_global_labelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFrom hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFrom'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFrom hindex).of_eq fun _ => rfl

/--
Global canonical numeric-state decoder bridge for the source reduction.
This is the non-source-specialized version of
`sourceProgramData_computable_of_source_labelIndexStartWithCode`.
-/
theorem sourceProgramData_computable_of_global_labelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexStartWithCode
      hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexStartWithCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexStartWithCode hindex).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_global_labelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFromWithCode hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFromWithCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFromWithCode hindex).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_global_labelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFromWithSearchCode
    hindex).comp NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFromWithSearchCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFromWithSearchCode hindex).of_eq fun _ => rfl

/-- Fixed-domino instance produced directly from a source partial-recursive code. -/
def sourceFixedDominoReduction (_h : SourceObligations) (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData
    (PostProgram.toTableProgram
      (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)))

theorem sourceFixedDominoReduction_computable (h : SourceObligations) :
    Computable (sourceFixedDominoReduction h) := by
  exact tableProgramFixedDominoData_computable.comp
    (PostProgram.toTableProgram_computable.comp h.program_computable)

theorem sourceFixedDominoReduction_correct (h : SourceObligations) (c : Code) :
    TilesQuarterWithSeed (sourceFixedDominoReduction h c).1
        (sourceFixedDominoReduction h c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold sourceFixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff
      (PostProgram.toTableProgram
        (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))))]
  rw [tableProgramFixedDomino_correct]
  rw [PostProgram.toTableProgram_toMachine_haltsEmpty_iff]
  rw [h.correct c]

/-- Final scaffolded tileset produced directly from a source partial-recursive code. -/
def sourceDominoReduction (S : Scaffold) (h : SourceObligations) (c : Code) : TileSet :=
  combineWithScaffold S (sourceFixedDominoReduction h c).1
    (sourceFixedDominoReduction h c).2

theorem sourceDominoReduction_computable (S : Scaffold) (h : SourceObligations) :
    Computable (sourceDominoReduction S h) := by
  exact (combineWithScaffold_computable S).comp (sourceFixedDominoReduction_computable h)

theorem sourceDominoReduction_correct
    {S : Scaffold} (hS : IsScaffold S) (h : SourceObligations) (c : Code) :
    TilesPlane (sourceDominoReduction S h c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourceDominoReduction]
  exact (scaffold_reduction_correct hS
    (sourceFixedDominoReduction h c).1 (sourceFixedDominoReduction h c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (sourceFixedDominoReduction h c).1
        (sourceFixedDominoReduction h c).2).symm.trans
          (sourceFixedDominoReduction_correct h c))

/-- Encoded version of the source-code folded reduction. -/
def sourceDominoReductionCode
    (S : Scaffold) (h : SourceObligations) (c : Code) : Nat :=
  encodeTileSet (sourceDominoReduction S h c)

theorem sourceDominoReductionCode_computable
    (S : Scaffold) (h : SourceObligations) :
    Computable (sourceDominoReductionCode S h) := by
  exact encodeTileSet_computable.comp (sourceDominoReduction_computable S h)

theorem sourceDominoReductionCode_correct
    {S : Scaffold} (hS : IsScaffold S) (h : SourceObligations) (c : Code) :
    TilesPlane (decodeTileSet (sourceDominoReductionCode S h c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourceDominoReductionCode, decodeTileSet_encodeTileSet]
  exact sourceDominoReduction_correct hS h c

/--
Encoded domino undecidability from the exact source-code folded-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_source
    (S : Scaffold) (hS : IsScaffold S) (h : SourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro hdec
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (sourceDominoReductionCode S h c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (sourceDominoReductionCode_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hencoded.of_eq fun c => sourceDominoReductionCode_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Unencoded domino undecidability from the exact source-code folded-route
obligations.
-/
theorem domino_problem_undecidable_of_scaffold_source
    (S : Scaffold) (hS : IsScaffold S) (h : SourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro hdec
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (sourceDominoReduction S h c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (sourceDominoReduction_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hdomino.of_eq fun c => sourceDominoReduction_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Encoded domino undecidability from a scaffold and the folded finite-TM0 route,
assuming the broader folded-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (h : Obligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_source S hS h.toSource

/--
Unencoded domino undecidability from a scaffold and the folded finite-TM0 route,
assuming the broader folded-route obligations.
-/
theorem domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (h : Obligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_source S hS h.toSource

end TM0FoldedReduction

end LeanWang

end
