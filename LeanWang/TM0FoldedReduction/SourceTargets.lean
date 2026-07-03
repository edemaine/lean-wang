/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourcePositionCode

/-!
Public primitive-recursion targets and equivalences for the source-level folded
reduction.

The decoder constructions live in `SourceCore` and `SourcePositionCode`; this
module keeps the theorem surface cheap to edit and rebuild.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
The source-uniform primitive-recursion target for one bounded-support-search
row on a concrete translated Partrec-variable branch.
-/
abbrev SourceSearchCodeOneVarRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
    sourceSearchCodeOneRowsVar p.1 p.2.1 p.2.2)

/-- Primitive-recursion target for interior bounded-support-search rows. -/
abbrev SourceSearchCodeInteriorRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
    sourceSearchCodeInteriorRowsVar p.1 p.2.1 p.2.2)

/-- Primitive-recursion target for bounded interior bounded-support-search rows. -/
abbrev SourceSearchCodeBoundedInteriorRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × TM0Route.PartrecVar =>
    sourceSearchCodeBoundedInteriorRowsVar p.1 p.2.1 p.2.2)

/--
The source-uniform primitive-recursion target for the one-fuel bounded-search
label-index decoder.
-/
abbrev SourceSearchCodeOneRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat =>
    sourceSimStepDataForLabelIndexFromWithSearchCode p.1 1 p.2.1 p.2.2)

/-- Primitive-recursion target for the bounded-support-search accumulator step. -/
abbrev SourceSearchCodeDecoderStepPrimrec : Prop :=
  Primrec (fun p : Code × SourceSearchCodeDecoderState =>
    sourceSearchCodeDecoderStep p.1 p.2)

set_option linter.style.longLine false in
/-- Primitive-recursion target for the source-specialized bounded-search label-index decoder. -/
abbrev SourceSearchCodeLabelIndexFromPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × Nat =>
    sourceSimStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- One-row bounded-search rows generate the interior-row bounded-search target. -/
theorem sourceSearchCodeInteriorRowsPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeInteriorRowsPrimrec :=
  sourceSearchCodeInteriorRowsVar_primrec_of_oneRows hrows

/-- Interior bounded-search rows generate the bounded-interior target. -/
theorem sourceSearchCodeBoundedInteriorRowsPrimrec_of_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceSearchCodeBoundedInteriorRowsPrimrec :=
  sourceSearchCodeBoundedInteriorRowsVar_primrec_of_interior hinterior

/-- Bounded-interior bounded-search rows generate the one-row target. -/
theorem sourceSearchCodeOneVarRowsPrimrec_of_boundedInteriorRows
    (hbounded : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    SourceSearchCodeOneVarRowsPrimrec :=
  sourceSearchCodeOneRowsVar_primrec_of_boundedInterior hbounded

/-- Variable-branch one-row bounded-search rows generate one-fuel label-index rows. -/
theorem sourceSearchCodeOneRowsPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeOneRowsPrimrec :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_one_primrec_of_varRows hrows

/-- Variable-branch one-row bounded-search rows generate the decoder-step target. -/
theorem sourceSearchCodeDecoderStepPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeDecoderStepPrimrec :=
  sourceSearchCodeDecoderStep_primrec_of_oneVarRows hrows

/-- One-fuel bounded-search label-index rows generate the decoder-step target. -/
theorem sourceSearchCodeDecoderStepPrimrec_of_oneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceSearchCodeDecoderStepPrimrec :=
  sourceSearchCodeDecoderStep_primrec_of_oneRows hrows

/-- The bounded-search decoder step generates the full label-index decoder target. -/
theorem sourceSearchCodeLabelIndexFromPrimrec_of_decoderStep
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_decoder_step hstep

/-- One-fuel bounded-search rows generate the full label-index decoder target. -/
theorem sourceSearchCodeLabelIndexFromPrimrec_of_oneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneRows hrows

/--
The full bounded-search label-index decoder target specializes back to the
one-fuel row target.
-/
theorem sourceSearchCodeOneRowsPrimrec_of_labelIndexFrom
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceSearchCodeOneRowsPrimrec :=
  hindex.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.const 1) Primrec.snd))

/-- Variable-branch one-row bounded-search rows generate the full label-index decoder target. -/
theorem sourceSearchCodeLabelIndexFromPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithSearchCode_primrec_of_oneVarRows hrows

/-- The full bounded-search label-index decoder target generates the decoder step. -/
theorem sourceSearchCodeDecoderStepPrimrec_of_labelIndexFrom
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceSearchCodeDecoderStepPrimrec :=
  sourceSearchCodeDecoderStepPrimrec_of_oneRows
    (sourceSearchCodeOneRowsPrimrec_of_labelIndexFrom hindex)

/--
For the bounded-search source route, primitive recursiveness of the full
label-index decoder and of the accumulator step are equivalent.
-/
theorem sourceSearchCodeDecoderStepPrimrec_iff_labelIndexFromPrimrec :
    SourceSearchCodeDecoderStepPrimrec ↔ SourceSearchCodeLabelIndexFromPrimrec :=
  ⟨sourceSearchCodeLabelIndexFromPrimrec_of_decoderStep,
    sourceSearchCodeDecoderStepPrimrec_of_labelIndexFrom⟩

/--
For the bounded-search source route, primitive recursiveness of the one-fuel
label-index rows and of the full label-index decoder are equivalent.
-/
theorem sourceSearchCodeOneRowsPrimrec_iff_labelIndexFromPrimrec :
    SourceSearchCodeOneRowsPrimrec ↔ SourceSearchCodeLabelIndexFromPrimrec :=
  ⟨sourceSearchCodeLabelIndexFromPrimrec_of_oneRows,
    sourceSearchCodeOneRowsPrimrec_of_labelIndexFrom⟩

/--
The one-row and interior bounded-search row targets are equivalent through the
existing bounded-interior bridge.
-/
theorem sourceSearchCodeOneVarRowsPrimrec_iff_interiorRowsPrimrec :
    SourceSearchCodeOneVarRowsPrimrec ↔ SourceSearchCodeInteriorRowsPrimrec :=
  ⟨sourceSearchCodeInteriorRowsPrimrec_of_oneVarRows,
    fun hinterior =>
      sourceSearchCodeOneVarRowsPrimrec_of_boundedInteriorRows
        (sourceSearchCodeBoundedInteriorRowsPrimrec_of_interiorRows hinterior)⟩

/--
The source-uniform primitive-recursion target for one generated position-code
row.  This is the nondependent boundary where the translated source statement
lookup has already been turned into concrete folded TM0 descriptor rows.
-/
abbrev SourcePositionCodeOneRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

/--
The source-uniform primitive-recursion target for the generated position-code
row at a concrete numeric label slot.

This is weaker than `SourcePositionCodeOneRowsPrimrec`: the variable is first
decoded from the fixed `partrecVarList`, matching the branch actually used by
the generated position-code accumulator.
-/
abbrev SourcePositionCodeOneRowsAtIndexPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat =>
    sourcePositionCodeOneRowsAtIndex p.1 p.2.1 p.2.2)

/--
Primitive-recursion target for the vacuous tail of generated position-code rows
at numeric label slots.  Rows at `sourceStatementCount c + offset` are past the
translated source program's finite statement support, so they decode to `[]`.
-/
abbrev SourcePositionCodePostStatementRowsAtIndexPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat =>
    sourcePositionCodeOneRowsAtIndex p.1
      (sourceStatementCount p.1 + p.2.1) p.2.2)

/--
Primitive-recursion target for generated position-code interior rows at a
concrete numeric label slot.  This is the natural source-side target for the
descriptor payload: it excludes the known empty row zero and the known empty
post-statement tail while still avoiding the stronger arbitrary-variable row
target.
-/
abbrev SourcePositionCodeInteriorRowsAtIndexPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat =>
    sourcePositionCodeInteriorRowsAtIndex p.1 p.2.1 p.2.2)

/--
Primitive-recursion target for bounded interior generated position-code rows
at a concrete numeric label slot.
-/
abbrev SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat =>
    sourcePositionCodeBoundedInteriorRowsAtIndex p.1 p.2.1 p.2.2)

/-- Primitive-recursion target for the generated position-code accumulator step. -/
abbrev SourcePositionCodeDecoderStepPrimrec : Prop :=
  Primrec (fun p : Code × SourceSearchCodeDecoderState =>
    sourcePositionCodeDecoderStep p.1 p.2)

set_option linter.style.longLine false in
/-- Primitive-recursion target for the global position-code label-index decoder. -/
abbrev GlobalPositionCodeLabelIndexFromPrimrec : Prop :=
  Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
    TM0FoldedCompiler.simStepDataForLabelIndexFromWithPositionCode
      p.1 p.2.1 p.2.2.1 p.2.2.2)

set_option linter.style.longLine false in
/--
Primitive-recursion target for the source-specialized position-code label-index
decoder.  This is weaker than `GlobalPositionCodeLabelIndexFromPrimrec`: the
final reduction only needs the decoder after translating `Nat.Partrec.Code`
into Mathlib's `Turing.ToPartrec.Code`.
-/
abbrev SourcePositionCodeLabelIndexFromPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × Nat =>
    sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the generated position-code accumulator step implies
the source-specialized position-code label-index decoder target.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_decoder_step
    hstep

set_option linter.style.longLine false in
/--
The source-specialized position-code label-index decoder also gives the
generated position-code accumulator step.
-/
theorem sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_labelIndexFromWithPositionCode hindex

set_option linter.style.longLine false in
/--
The source-specialized position-code label-index decoder gives the exact
one-row-at-index target by fixing the fuel to `1`.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_of_sourcePositionCodeLabelIndexFrom
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  sourcePositionCodeOneRowsAtIndex_primrec_of_labelIndexFrom hindex

/--
Generated position-code rows past the translated source program's finite
statement support are primitive recursive at numeric label slots.
-/
theorem sourcePositionCodePostStatementRowsAtIndexPrimrec :
    SourcePositionCodePostStatementRowsAtIndexPrimrec :=
  sourcePositionCodeOneRowsAtIndex_statementCount_add_primrec

set_option linter.style.longLine false in
/--
The exact one-row-at-index target gives interior rows by shifting the row index
by one.
-/
theorem sourcePositionCodeInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeInteriorRowsAtIndex_primrec_of_oneRowsAtIndex hrows

set_option linter.style.longLine false in
/--
Interior numeric-slot rows give bounded-interior numeric-slot rows by cutting
off the known empty post-statement tail.
-/
theorem sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeBoundedInteriorRowsAtIndex_primrec_of_interiorAtIndex hinterior

set_option linter.style.longLine false in
/--
The generated one-row-at-index target gives the accumulator-step target.
-/
theorem sourcePositionCodeDecoderStepPrimrec_of_oneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStep_primrec_of_oneRowsAtIndex hrows

set_option linter.style.longLine false in
/--
Bounded-interior at-index rows recover one-row-at-index rows by handling the
zero row and post-support rows as empty rows.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_of_boundedInteriorAtIndex
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  sourcePositionCodeOneRowsAtIndex_primrec_of_boundedInteriorAtIndex hbounded

set_option linter.style.longLine false in
/--
The exact one-row-at-index target also gives bounded-interior at-index rows,
because bounded row `j` is the one-row decoder at row `j + 1`.
-/
theorem sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
    (sourcePositionCodeInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Bounded-interior at-index rows imply the generated accumulator-step target.
-/
theorem sourcePositionCodeDecoderStepPrimrec_of_boundedInteriorAtIndex
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourcePositionCodeDecoderStepPrimrec_of_oneRowsAtIndex
    (sourcePositionCodeOneRowsAtIndexPrimrec_of_boundedInteriorAtIndex hbounded)

set_option linter.style.longLine false in
/--
Bounded-interior at-index rows imply the source-specialized position-code
label-index decoder target.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_boundedInteriorAtIndex
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep
    (sourcePositionCodeDecoderStepPrimrec_of_boundedInteriorAtIndex hbounded)

set_option linter.style.longLine false in
/--
The generated one-row-at-index target implies the source-specialized
position-code label-index decoder target.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_oneRowsAtIndex
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep
    (sourcePositionCodeDecoderStepPrimrec_of_oneRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Interior numeric-slot rows imply the source-specialized position-code
label-index decoder target through the bounded-interior accumulator route.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_interiorAtIndex
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeLabelIndexFromPrimrec_of_boundedInteriorAtIndex
    (sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
      hinterior)

set_option linter.style.longLine false in
/--
The generated accumulator-step target gives the one-row-at-index target.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_of_decoderStep
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  sourcePositionCodeOneRowsAtIndexPrimrec_of_sourcePositionCodeLabelIndexFrom
    (sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep hstep)

set_option linter.style.longLine false in
/--
For the source-specialized generated position-code route, primitive
recursiveness of one-row-at-index decoding and of the accumulator step are
equivalent.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_iff_decoderStepPrimrec :
    SourcePositionCodeOneRowsAtIndexPrimrec ↔ SourcePositionCodeDecoderStepPrimrec :=
  ⟨sourcePositionCodeDecoderStepPrimrec_of_oneRowsAtIndex,
    sourcePositionCodeOneRowsAtIndexPrimrec_of_decoderStep⟩

set_option linter.style.longLine false in
/--
For the exact generated row slots used by the accumulator, one-row and
bounded-interior decoding are equivalent.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_iff_boundedInteriorRowsAtIndexPrimrec :
    SourcePositionCodeOneRowsAtIndexPrimrec ↔
      SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  ⟨sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex,
    sourcePositionCodeOneRowsAtIndexPrimrec_of_boundedInteriorAtIndex⟩

set_option linter.style.longLine false in
/--
For the source-specialized generated position-code route, primitive
recursiveness of the label-index decoder and of the accumulator step are
equivalent.
-/
theorem sourcePositionCodeDecoderStepPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec :
    SourcePositionCodeDecoderStepPrimrec ↔ SourcePositionCodeLabelIndexFromPrimrec :=
  ⟨sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep,
    sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFrom⟩

set_option linter.style.longLine false in
/--
For the exact generated row slots used by the accumulator, primitive
recursiveness of one-row-at-index decoding and of the source-specialized
label-index decoder are equivalent.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec :
    SourcePositionCodeOneRowsAtIndexPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeOneRowsAtIndexPrimrec_iff_decoderStepPrimrec.trans
    sourcePositionCodeDecoderStepPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
For the exact generated row slots used by the accumulator, primitive
recursiveness of bounded-interior at-index decoding and of the
source-specialized label-index decoder are equivalent.
-/
theorem sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeOneRowsAtIndexPrimrec_iff_boundedInteriorRowsAtIndexPrimrec.symm.trans
    sourcePositionCodeOneRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec

/-- Primitive-recursion target for interior generated position-code rows. -/
abbrev SourcePositionCodeInteriorRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Primitive-recursion target for bounded interior generated position-code rows. -/
abbrev SourcePositionCodeBoundedInteriorRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

/--
Primitive recursiveness of the generated one-row position-code decoder implies
the source-specialized position-code label-index decoder target.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeOneRows
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourceSimStepDataForLabelIndexFromWithPositionCode_primrec_of_indexVarRows
    hrows

set_option linter.style.longLine false in
/--
The arbitrary-variable one-row target implies the exact one-row-at-index target
used by the accumulator.
-/
theorem sourcePositionCodeOneRowsAtIndexPrimrec_of_positionCodeOneRows
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  sourcePositionCodeOneRowsAtIndex_primrec_of_indexVarRows hrows

set_option linter.style.longLine false in
/--
The arbitrary-variable bounded-interior target implies the exact
bounded-interior at-index target.
-/
theorem sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_positionCodeBoundedInteriorRows
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeBoundedInteriorRowsAtIndex_primrec_of_boundedInterior hbounded

set_option linter.style.longLine false in
/--
The arbitrary-variable interior target implies the exact interior-at-index
target used by the generated position-code route.
-/
theorem sourcePositionCodeInteriorRowsAtIndexPrimrec_of_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  sourcePositionCodeInteriorRowsAtIndex_primrec_of_interior hinterior

set_option linter.style.longLine false in
/--
Primitive recursiveness of the generated bounded-interior position-code rows
implies the source-specialized position-code label-index decoder target.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeBoundedInteriorRows
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeOneRows
    (sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hbounded)

set_option linter.style.longLine false in
/--
Primitive recursiveness of the generated interior position-code rows implies
the source-specialized position-code label-index decoder target.
-/
theorem sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourcePositionCodeLabelIndexFromPrimrec_of_boundedInteriorAtIndex
    (sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
      (sourcePositionCodeInteriorRowsAtIndexPrimrec_of_positionCodeInteriorRows
        hinterior))

/--
The statement-list uniqueness fact needed to identify support-search state
codes with position-coded state codes for the translated source TM0 machines.
-/
abbrev SourceStatementListNodup : Prop :=
  ∀ c : Code,
    (TM0Route.partrecStartedTM0StatementList
      (NatPartrecToToPartrec.translate c)).Nodup

/--
Source-uniform local statement-support uniqueness for each started TM1 label
appearing in the translated source machines.
-/
abbrev SourceStartedTM1StatementSupportNodup : Prop :=
  ∀ c : Code, ∀ q ∈
      TM0Route.partrecStartedTM1LabelList (NatPartrecToToPartrec.translate c),
    (TM0Route.tm1StmtSupportList
      (TM0Route.partrecStartedTM1Machine (NatPartrecToToPartrec.translate c) q)).Nodup

/--
Source-uniform disjointness between local statement-support lists for distinct
started TM1 labels.
-/
abbrev SourceStartedTM1StatementSupportPairwiseDisjoint : Prop :=
  ∀ c : Code,
    (TM0Route.partrecStartedTM1LabelList
      (NatPartrecToToPartrec.translate c)).Pairwise fun q₁ q₂ =>
        List.Disjoint
          (TM0Route.tm1StmtSupportList
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c) q₁))
          (TM0Route.tm1StmtSupportList
            (TM0Route.partrecStartedTM1Machine
              (NatPartrecToToPartrec.translate c) q₂))

/--
The opaque source statement-list uniqueness obligation follows from
duplicate-free local TM1 statement supports and pairwise disjointness between
the supports for different started TM1 labels.
-/
theorem sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    SourceStatementListNodup := by
  intro c
  exact TM0Route.partrecStartedTM0StatementList_nodup_of_pairwise_disjoint
    (NatPartrecToToPartrec.translate c) (hstmt c) (hdisj c)

/-- Source-uniform one-row position-code decoder plus statement uniqueness. -/
structure SourcePositionCodeOneRowsWithStatementNodup : Prop where
  rows : SourcePositionCodeOneRowsPrimrec
  statementList_nodup : SourceStatementListNodup

/-- Source-uniform bounded-interior position-code decoder plus statement uniqueness. -/
structure SourcePositionCodeBoundedInteriorRowsWithStatementNodup : Prop where
  rows : SourcePositionCodeBoundedInteriorRowsPrimrec
  statementList_nodup : SourceStatementListNodup

/-- Source-uniform interior position-code decoder plus statement uniqueness. -/
structure SourcePositionCodeInteriorRowsWithStatementNodup : Prop where
  rows : SourcePositionCodeInteriorRowsPrimrec
  statementList_nodup : SourceStatementListNodup

/-- One-row generated position-code rows give the interior-row target. -/
theorem sourcePositionCodeInteriorRowsPrimrec_of_oneRows
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    SourcePositionCodeInteriorRowsPrimrec :=
  sourcePositionCodeInteriorRowsIndexVar_primrec_of_oneRows hrows

/-- Interior generated position-code rows give the bounded-interior target. -/
theorem sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeBoundedInteriorRowsPrimrec :=
  sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior hinterior

/-- Bounded interior generated position-code rows give the one-row target. -/
theorem sourcePositionCodeOneRowsPrimrec_of_boundedInterior
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeOneRowsPrimrec :=
  sourcePositionCodeOneRowsIndexVar_primrec_of_boundedInterior hbounded

/-- Interior generated position-code rows give the one-row target. -/
theorem sourcePositionCodeOneRowsPrimrec_of_interior
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeOneRowsPrimrec :=
  sourcePositionCodeOneRowsPrimrec_of_boundedInterior
    (sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior)

set_option linter.style.longLine false in
/--
The one-row and interior-row source primitive-recursion targets are equivalent.

The final reduction can therefore target whichever spelling is more convenient:
one-row primitive recursiveness gives all interior rows by shifting the row
index, while interior rows include the bounded rows and hence recover the
zero/padding cases of the one-row decoder.
-/
theorem sourcePositionCodeOneRowsPrimrec_iff_interiorRowsPrimrec :
    SourcePositionCodeOneRowsPrimrec ↔ SourcePositionCodeInteriorRowsPrimrec :=
  ⟨sourcePositionCodeInteriorRowsPrimrec_of_oneRows,
    sourcePositionCodeOneRowsPrimrec_of_interior⟩

set_option linter.style.longLine false in
/--
The one-row and bounded-interior source primitive-recursion targets are
equivalent.
-/
theorem sourcePositionCodeOneRowsPrimrec_iff_boundedInteriorRowsPrimrec :
    SourcePositionCodeOneRowsPrimrec ↔ SourcePositionCodeBoundedInteriorRowsPrimrec :=
  ⟨fun hrows =>
      sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior
        (sourcePositionCodeInteriorRowsPrimrec_of_oneRows hrows),
    sourcePositionCodeOneRowsPrimrec_of_boundedInterior⟩

set_option linter.style.longLine false in
/--
The interior-row and bounded-interior source primitive-recursion targets are
equivalent.
-/
theorem sourcePositionCodeInteriorRowsPrimrec_iff_boundedInteriorRowsPrimrec :
    SourcePositionCodeInteriorRowsPrimrec ↔ SourcePositionCodeBoundedInteriorRowsPrimrec :=
  sourcePositionCodeOneRowsPrimrec_iff_interiorRowsPrimrec.symm.trans
    sourcePositionCodeOneRowsPrimrec_iff_boundedInteriorRowsPrimrec

/-- A one-row package also supplies the interior package. -/
def sourcePositionCodeInteriorRowsWithStatementNodup_of_oneRows
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    SourcePositionCodeInteriorRowsWithStatementNodup where
  rows := sourcePositionCodeInteriorRowsPrimrec_of_oneRows hrows.rows
  statementList_nodup := hrows.statementList_nodup

/-- An interior package also supplies the bounded-interior package. -/
def sourcePositionCodeBoundedInteriorRowsWithStatementNodup_of_interior
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    SourcePositionCodeBoundedInteriorRowsWithStatementNodup where
  rows := sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior.rows
  statementList_nodup := hinterior.statementList_nodup

/-- A bounded-interior package also supplies the one-row package. -/
def sourcePositionCodeOneRowsWithStatementNodup_of_boundedInterior
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    SourcePositionCodeOneRowsWithStatementNodup where
  rows := sourcePositionCodeOneRowsPrimrec_of_boundedInterior hbounded.rows
  statementList_nodup := hbounded.statementList_nodup

/-- An interior package also supplies the one-row package. -/
def sourcePositionCodeOneRowsWithStatementNodup_of_interior
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    SourcePositionCodeOneRowsWithStatementNodup :=
  sourcePositionCodeOneRowsWithStatementNodup_of_boundedInterior
    (sourcePositionCodeBoundedInteriorRowsWithStatementNodup_of_interior
      hinterior)

set_option linter.style.longLine false in
/--
The one-row and interior-row packaged source targets are equivalent when they
also carry statement-list uniqueness.
-/
theorem sourcePositionCodeOneRowsWithStatementNodup_iff_interiorRowsWithStatementNodup :
    SourcePositionCodeOneRowsWithStatementNodup ↔
      SourcePositionCodeInteriorRowsWithStatementNodup :=
  ⟨sourcePositionCodeInteriorRowsWithStatementNodup_of_oneRows,
    sourcePositionCodeOneRowsWithStatementNodup_of_interior⟩

set_option linter.style.longLine false in
/--
The one-row and bounded-interior packaged source targets are equivalent when
they also carry statement-list uniqueness.
-/
theorem sourcePositionCodeOneRowsWithStatementNodup_iff_boundedInteriorRowsWithStatementNodup :
    SourcePositionCodeOneRowsWithStatementNodup ↔
      SourcePositionCodeBoundedInteriorRowsWithStatementNodup :=
  ⟨fun hrows =>
      sourcePositionCodeBoundedInteriorRowsWithStatementNodup_of_interior
        (sourcePositionCodeInteriorRowsWithStatementNodup_of_oneRows hrows),
    sourcePositionCodeOneRowsWithStatementNodup_of_boundedInterior⟩

set_option linter.style.longLine false in
/--
The interior-row and bounded-interior packaged source targets are equivalent
when they also carry statement-list uniqueness.
-/
theorem sourcePositionCodeInteriorRowsWithStatementNodup_iff_boundedInteriorRowsWithStatementNodup :
    SourcePositionCodeInteriorRowsWithStatementNodup ↔
      SourcePositionCodeBoundedInteriorRowsWithStatementNodup :=
  sourcePositionCodeOneRowsWithStatementNodup_iff_interiorRowsWithStatementNodup.symm.trans
    sourcePositionCodeOneRowsWithStatementNodup_iff_boundedInteriorRowsWithStatementNodup

end TM0FoldedReduction

end LeanWang
