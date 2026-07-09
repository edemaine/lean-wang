/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.OffsetStart.Core

/-!
Indexed descriptor-list definitions, start-decoder equivalences, and
primitive-recursion target bridges.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

def sourceSimStepDataForLabelIndex
    (c : Code) (i : Nat) : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataForLabelIndex
    (NatPartrecToToPartrec.translate c) i

/-- Source-code indexed descriptor list for the folded finite-TM0 reduction. -/
def sourceSimStepDataByLabelIndex (c : Code) : List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndex c)

/-- Source-code indexed descriptor list through the numeric-state decoder path. -/
def sourceSimStepDataByLabelIndexWithCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithCode c)

/-- Source-code indexed descriptor list through the bounded-search decoder path. -/
def sourceSimStepDataByLabelIndexWithSearchCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithSearchCode c)

/-- Source-code indexed descriptor list through the position-coded decoder path. -/
def sourceSimStepDataByLabelIndexWithPositionCode (c : Code) :
    List TM0FoldedCompiler.SimStepData :=
  (List.range (sourceLabelCount c)).flatMap
    (sourceSimStepDataForLabelIndexStartWithPositionCode c)

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_tail_after_firstBlock
    (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      (List.Ico TM0Route.partrecVarList.length (sourceLabelCount c)).flatMap
        (sourceSimStepDataForLabelIndexStartWithPositionCode c) := by
  unfold sourceSimStepDataByLabelIndexWithPositionCode
  rw [flatMap_range_dropPrefix
    (sourceSimStepDataForLabelIndexStartWithPositionCode c)
    (sourcePartrecVarList_length_le_sourceLabelCount c)]
  simp [sourceSimStepDataForLabelIndexStartWithPositionCode_firstBlock_eq_nil c]

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_interiorRowsByTailIndex
    (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      sourcePositionCodeInteriorRowsByTailIndex c := by
  rw [sourceSimStepDataByLabelIndexWithPositionCode_eq_tail_after_firstBlock]
  unfold sourcePositionCodeInteriorRowsByTailIndex
  apply flatMap_congr_of_mem
  intro n hn
  have hbounds :
      TM0Route.partrecVarList.length ≤ n ∧ n < sourceLabelCount c := by
    simpa using (List.Ico.mem (n := TM0Route.partrecVarList.length)
      (m := sourceLabelCount c) (l := n)).1 hn
  exact sourceSimStepDataForLabelIndexStartWithPositionCode_tail_index_eq
    (c := c) (n := n) hbounds.1 hbounds.2

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

theorem sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithSearchCode c i =
      sourceSimStepDataForLabelIndexStartWithCode c i := by
  unfold sourceSimStepDataForLabelIndexStartWithSearchCode
    sourceSimStepDataForLabelIndexStartWithCode
  exact TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (NatPartrecToToPartrec.translate c) i

set_option linter.style.longLine false in
/-- The numeric-state start decoder gives the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_codeLabelIndexStart
    (hindex : SourceCodeLabelIndexStartPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  hindex.of_eq fun p =>
    (sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode p.1 p.2).symm

set_option linter.style.longLine false in
/-- The bounded-search start decoder recovers the numeric-state start-decoder target. -/
theorem sourceCodeLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
    (hindex : SourceSearchCodeLabelIndexStartPrimrec) :
    SourceCodeLabelIndexStartPrimrec :=
  hindex.of_eq fun p =>
    sourceSimStepDataForLabelIndexStartWithSearchCode_eq_withCode p.1 p.2

theorem sourceSimStepDataForLabelIndexStartWithPositionCode_eq (c : Code) (i : Nat) :
    sourceSimStepDataForLabelIndexStartWithPositionCode c i =
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
        (NatPartrecToToPartrec.translate c) i :=
  rfl

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

theorem sourceSimStepDataByLabelIndexWithSearchCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithSearchCode c = sourceSimStepData c := by
  unfold sourceSimStepDataByLabelIndexWithSearchCode sourceSimStepData
  exact TM0FoldedCompiler.simStepDataByLabelIndexWithSearchCode_eq
    (NatPartrecToToPartrec.translate c)

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq (c : Code) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode
        (NatPartrecToToPartrec.translate c) := by
  rfl

theorem sourceSimStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
    (c : Code)
    (hmin : ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    sourceSimStepDataByLabelIndexWithPositionCode c =
      sourceSimStepDataByLabelIndexWithCode c := by
  change TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode
      (NatPartrecToToPartrec.translate c) =
    TM0FoldedCompiler.simStepDataByLabelIndexWithCode
      (NatPartrecToToPartrec.translate c)
  exact
    TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
      (NatPartrecToToPartrec.translate c) hmin

theorem sourceSimRowsOfStepDataByLabelIndexWithPositionCode_eq_of_minimal
    (c : Code)
    (hmin : ∀ i, i < sourceLabelCount c →
      ∀ q : TM0FoldedCompiler.SourceLabel (NatPartrecToToPartrec.translate c) × Nat,
        TM0FoldedCompiler.labelAtByStatementFromWithPositionCode?
            (NatPartrecToToPartrec.translate c) (sourceStatementCount c) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList
              (NatPartrecToToPartrec.translate c))[m]? ≠ some q.1) :
    TM0FoldedCompiler.simRowsOfStepData
        (sourceSimStepDataByLabelIndexWithPositionCode c) =
      TM0FoldedCompiler.simRows (NatPartrecToToPartrec.translate c) := by
  rw [sourceSimStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal c hmin]
  rw [sourceSimStepDataByLabelIndexWithCode_eq c]
  rw [sourceSimStepData_eq c]
  exact (TM0FoldedCompiler.simRows_eq_stepData
    (NatPartrecToToPartrec.translate c)).symm

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
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (sourceStatementCount_primrec.comp Primrec.fst)
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
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
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
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level bounded-search start decoder is
enough for the source-level bounded-search indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithSearchCode := by
  unfold sourceSimStepDataByLabelIndexWithSearchCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

/--
Primitive recursiveness of the source-level position-coded start decoder is
enough for the source-level position-coded indexed descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start
    (hindex : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode := by
  unfold sourceSimStepDataByLabelIndexWithPositionCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp sourceLabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

set_option linter.style.longLine false in
/--
The full source-specialized position-code offset decoder gives the start
decoder target by fixing the fuel to `sourceStatementCount c` and the offset to
zero.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_of_labelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeLabelIndexStartPrimrec := by
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1
        (sourceStatementCount p.1) 0 p.2) :=
    hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (sourceStatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))
  exact hstart.of_eq fun p => by
    unfold sourceSimStepDataForLabelIndexStartWithPositionCode
      sourceSimStepDataForLabelIndexFromWithPositionCode
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
    rfl

set_option linter.style.longLine false in
/--
For the source-specialized position-code route, the fixed-start decoder target
and the full offset decoder target are equivalent.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_iff_labelIndexFromPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  ⟨sourcePositionCodeLabelIndexFromPrimrec_of_labelIndexStart,
    sourcePositionCodeLabelIndexStartPrimrec_of_labelIndexFrom⟩

set_option linter.style.longLine false in
/--
For the source-specialized position-code route, the fixed-start decoder target
is equivalent to primitive recursiveness of the generated accumulator step.

This is the narrowest remaining machine-side target: proving the local
accumulator-step decoder uniformly in the source code closes the fixed-start
and full offset decoder targets used by the final reduction.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_iff_decoderStepPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeLabelIndexStartPrimrec_iff_labelIndexFromPrimrec.trans
    sourcePositionCodeDecoderStepPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec.symm

set_option linter.style.longLine false in
/--
The source-specialized position-code start decoder gives the exact
one-row-at-index target used by the generated accumulator.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_of_labelIndexStart
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  sourcePositionCodeOneRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec.2
    (sourcePositionCodeLabelIndexFromPrimrec_of_labelIndexStart hstart)

set_option linter.style.longLine false in
/--
The exact generated one-row-at-index target recovers the source-specialized
position-code start decoder.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_of_oneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexStartPrimrec :=
  sourcePositionCodeLabelIndexStartPrimrec_of_labelIndexFrom
    (sourcePositionCodeOneRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec.1 hrows)

set_option linter.style.longLine false in
/--
For the generated position-code route, the final start-decoder target is
equivalent to primitive recursiveness of the exact one-row-at-index decoder
used by the accumulator.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_iff_oneRowsAtIndexPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeOneRowsAtIndexPrimrec :=
  ⟨sourcePositionCodeOneRowsAtIndexPrimrec_of_labelIndexStart,
    sourcePositionCodeLabelIndexStartPrimrec_of_oneRowsAtIndex⟩

set_option linter.style.longLine false in
/--
For the exact generated row slots used by the accumulator, primitive
recursiveness of the fixed-start position-code decoder is equivalent to
primitive recursiveness of bounded interior at-index decoding.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_iff_boundedInteriorRowsAtIndexPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeLabelIndexStartPrimrec_iff_oneRowsAtIndexPrimrec.trans
    sourcePositionCodeOneRowsAtIndexPrimrec_iff_boundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
For the exact generated row slots used by the accumulator, primitive
recursiveness of the fixed-start position-code decoder is equivalent to
primitive recursiveness of interior at-index decoding.

This names the current narrow source frontier directly: closing either the
fixed-start decoder or the nondependent interior-row decoder closes the other.
-/
theorem sourcePositionCodeLabelIndexStartPrimrec_iff_interiorRowsAtIndexPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  ⟨sourcePositionCodeInteriorRowsAtIndexPrimrec_of_labelIndexStart,
    fun hinterior =>
      sourcePositionCodeLabelIndexStartPrimrec_of_labelIndexFrom
        (sourcePositionCodeLabelIndexFromPrimrec_of_interiorAtIndex hinterior)⟩

theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_interiorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode :=
  (sourcePositionCodeInteriorRowsByTailIndex_primrec_of_interior hinterior).of_eq
    fun c => (sourceSimStepDataByLabelIndexWithPositionCode_eq_interiorRowsByTailIndex c).symm

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
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithCode
        sourceSimStepDataForLabelIndexFromWithCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode
      rfl
  exact hstart

/--
Primitive recursiveness of the source-level bounded-search offset decoder is
enough for primitive recursiveness of the source-level bounded-search indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_from
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithSearchCode := by
  apply sourceSimStepDataByLabelIndexWithSearchCode_primrec_of_start
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithSearchCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithSearchCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithSearchCode
        sourceSimStepDataForLabelIndexFromWithSearchCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
      rfl
  exact hstart

set_option linter.style.longLine false in
/-- The full bounded-search label-index decoder gives the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_labelIndexFrom
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec := by
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexFromWithSearchCode p.1
        (sourceStatementCount p.1) 0 p.2) :=
    hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (sourceStatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))
  exact hstart.of_eq fun p => by
    unfold sourceSimStepDataForLabelIndexStartWithSearchCode
      sourceSimStepDataForLabelIndexFromWithSearchCode
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithSearchCode
    rfl

set_option linter.style.longLine false in
/-- The bounded-search accumulator step gives the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_decoderStep
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  sourceSearchCodeLabelIndexStartPrimrec_of_labelIndexFrom
    (sourceSearchCodeLabelIndexFromPrimrec_of_decoderStep hstep)

set_option linter.style.longLine false in
/-- One-fuel bounded-search rows give the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_oneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  sourceSearchCodeLabelIndexStartPrimrec_of_labelIndexFrom
    (sourceSearchCodeLabelIndexFromPrimrec_of_oneRows hrows)

set_option linter.style.longLine false in
/-- Variable-branch bounded-search one-row proofs give the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  sourceSearchCodeLabelIndexStartPrimrec_of_labelIndexFrom
    (sourceSearchCodeLabelIndexFromPrimrec_of_oneVarRows hrows)

set_option linter.style.longLine false in
/-- Bounded-interior bounded-search rows give the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_boundedInteriorRows
    (hbounded : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  sourceSearchCodeLabelIndexStartPrimrec_of_oneVarRows
    (sourceSearchCodeOneVarRowsPrimrec_of_boundedInteriorRows hbounded)

set_option linter.style.longLine false in
/-- Interior bounded-search rows give the bounded-search start-decoder target. -/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  sourceSearchCodeLabelIndexStartPrimrec_of_boundedInteriorRows
    (sourceSearchCodeBoundedInteriorRowsPrimrec_of_interiorRows hinterior)

/--
Primitive recursiveness of the source-level position-coded offset decoder is
enough for primitive recursiveness of the source-level position-coded indexed
descriptor list.
-/
theorem sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_from
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec sourceSimStepDataByLabelIndexWithPositionCode := by
  apply sourceSimStepDataByLabelIndexWithPositionCode_primrec_of_start
  have hstart : Primrec (fun p : Code × Nat =>
      sourceSimStepDataForLabelIndexStartWithPositionCode p.1 p.2) := by
    have hfrom : Primrec (fun p : Code × Nat =>
        sourceSimStepDataForLabelIndexFromWithPositionCode p.1
          (sourceStatementCount p.1) 0 p.2) :=
      hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (sourceStatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd)))
    exact hfrom.of_eq fun p => by
      unfold sourceSimStepDataForLabelIndexStartWithPositionCode
        sourceSimStepDataForLabelIndexFromWithPositionCode
        TM0FoldedCompiler.simStepDataForLabelIndexStartWithPositionCode
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

set_option linter.style.longLine false in
/--
The global numeric-state start-decoder target implies the source-specialized
start-decoder target by precomposing with the source-code translation.
-/
theorem sourceCodeLabelIndexStartPrimrec_of_globalCodeLabelIndexStartPrimrec
    (hindex : GlobalCodeLabelIndexStartPrimrec) :
    SourceCodeLabelIndexStartPrimrec := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexStartWithCode
        rfl

set_option linter.style.longLine false in
/--
The global numeric-state start-decoder target also gives the equivalent
bounded-search start-decoder target for ordinary `programData`.
-/
theorem sourceSearchCodeLabelIndexStartPrimrec_of_globalCodeLabelIndexStartPrimrec
    (hindex : GlobalCodeLabelIndexStartPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  sourceSearchCodeLabelIndexStartPrimrec_of_codeLabelIndexStart
    (sourceCodeLabelIndexStartPrimrec_of_globalCodeLabelIndexStartPrimrec
      hindex)

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

theorem sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (hindex.comp
    (Primrec.pair
      (NatPartrecToToPartrec.translate_primrec.comp Primrec.fst)
      Primrec.snd)).of_eq fun p => by
        unfold sourceSimStepDataForLabelIndexFromWithPositionCode
        rfl

set_option linter.style.longLine false in
/--
The global position-code label-index decoder target implies the source-specific
target by precomposing with `NatPartrecToToPartrec.translate`.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex

set_option linter.style.longLine false in
/--
The global position-code label-index decoder target implies the generated
source-code accumulator-step target used by the preferred final route.
-/
theorem sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2) :=
  sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode
    (sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_global hindex)

set_option linter.style.longLine false in
/-- Named version of `sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode`. -/
theorem sourcePositionCodeDecoderStepPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_global_labelIndexFromWithPositionCode hindex

set_option linter.style.longLine false in
/--
The source-specific position-code label-index decoder target implies the
generated source-code accumulator-step target used by the final route.
-/
theorem sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFromPrimrec
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode hindex


end TM0FoldedReduction

end LeanWang
