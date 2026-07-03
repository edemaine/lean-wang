/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.SourcePositionCode

/-!
Public primitive-recursion targets and equivalences for the source-level
position-coded folded reduction.

The decoder construction lives in `SourcePositionCode`; this module keeps the
theorem surface cheap to edit and rebuild.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
The source-uniform primitive-recursion target for one generated position-code
row.  This is the nondependent boundary where the translated source statement
lookup has already been turned into concrete folded TM0 descriptor rows.
-/
abbrev SourcePositionCodeOneRowsPrimrec : Prop :=
  Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
    sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)

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
For the source-specialized generated position-code route, primitive
recursiveness of the label-index decoder and of the accumulator step are
equivalent.
-/
theorem sourcePositionCodeDecoderStepPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec :
    SourcePositionCodeDecoderStepPrimrec ↔ SourcePositionCodeLabelIndexFromPrimrec :=
  ⟨sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep,
    sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFrom⟩

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
  sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeBoundedInteriorRows
    (sourcePositionCodeBoundedInteriorRowsIndexVar_primrec_of_interior hinterior)

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
