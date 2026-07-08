/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Final.SourceTargets

/-!
Implications between source-side target names for the final Wang-tile
undecidability theorem.

This module is intentionally independent of the finite Robinson scaffold
plumbing in `LeanWang.Final`.  It gives source-frontier edits a smaller cached
boundary and keeps the public final module focused on construction interfaces.
-/

namespace LeanWang

/-- The global position-code label-index target implies the decoder-step target. -/
theorem sourceDecoderStepPrimrec_of_globalLabelIndex
    (h : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourcePositionCodeDecoderStepPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    h

set_option linter.style.longLine false in
/-- The global position-code label-index target implies the source-specialized target. -/
theorem sourceLabelIndexPrimrec_of_globalLabelIndex
    (h : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    h

set_option linter.style.longLine false in
/-- The bounded-search decoder-step target gives the bounded-search label-index target. -/
theorem searchCodeLabelIndexPrimrec_of_decoderStep
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexFromPrimrec_of_decoderStep hstep

set_option linter.style.longLine false in
/-- The bounded-search label-index target recovers the bounded-search decoder-step target. -/
theorem searchCodeDecoderStepPrimrec_of_labelIndex
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceSearchCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourceSearchCodeDecoderStepPrimrec_of_labelIndexFrom hindex

/-- One-fuel bounded-search rows give the bounded-search decoder-step target. -/
theorem searchCodeDecoderStepPrimrec_of_oneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceSearchCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourceSearchCodeDecoderStepPrimrec_of_oneRows hrows

/-- One-fuel bounded-search rows give the bounded-search label-index target. -/
theorem searchCodeLabelIndexPrimrec_of_oneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexFromPrimrec_of_oneRows hrows

/-- The bounded-search label-index target recovers one-fuel rows. -/
theorem searchCodeOneRowsPrimrec_of_labelIndex
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceSearchCodeOneRowsPrimrec :=
  TM0FoldedReduction.sourceSearchCodeOneRowsPrimrec_of_labelIndexFrom hindex

set_option linter.style.longLine false in
/-- The bounded-search label-index target gives the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_labelIndex
    (hindex : SourceSearchCodeLabelIndexFromPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_labelIndexFrom
    hindex

set_option linter.style.longLine false in
/-- The numeric-state start decoder gives the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_codeLabelIndexStart
    (hindex : SourceCodeLabelIndexStartPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_codeLabelIndexStart
    hindex

set_option linter.style.longLine false in
/-- The global numeric-state start decoder gives the source-specialized target. -/
theorem codeLabelIndexStartPrimrec_of_globalCodeLabelIndexStart
    (hindex : GlobalCodeLabelIndexStartPrimrec) :
    SourceCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceCodeLabelIndexStartPrimrec_of_globalCodeLabelIndexStartPrimrec
    hindex

set_option linter.style.longLine false in
/-- The global numeric-state start decoder gives the bounded-search start target. -/
theorem searchCodeLabelIndexStartPrimrec_of_globalCodeLabelIndexStart
    (hindex : GlobalCodeLabelIndexStartPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_globalCodeLabelIndexStartPrimrec
    hindex

set_option linter.style.longLine false in
/-- The bounded-search start decoder recovers the numeric-state start-decoder target. -/
theorem codeLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
    (hindex : SourceSearchCodeLabelIndexStartPrimrec) :
    SourceCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceCodeLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
    hindex

set_option linter.style.longLine false in
/-- The bounded-search decoder-step target gives the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_decoderStep
    (hstep : SourceSearchCodeDecoderStepPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_decoderStep
    hstep

set_option linter.style.longLine false in
/-- One-fuel bounded-search rows give the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_oneRows
    (hrows : SourceSearchCodeOneRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_oneRows hrows

set_option linter.style.longLine false in
/-- Variable-branch bounded-search one-row proofs give the one-fuel row target. -/
theorem searchCodeOneRowsPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeOneRowsPrimrec :=
  TM0FoldedReduction.sourceSearchCodeOneRowsPrimrec_of_oneVarRows hrows

set_option linter.style.longLine false in
/-- Variable-branch bounded-search one-row proofs give the bounded-search label-index target. -/
theorem searchCodeLabelIndexPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexFromPrimrec_of_oneVarRows hrows

set_option linter.style.longLine false in
/-- Variable-branch bounded-search one-row proofs give the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_oneVarRows
    (hrows : SourceSearchCodeOneVarRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_oneVarRows
    hrows

set_option linter.style.longLine false in
/-- Interior bounded-search rows give bounded-interior bounded-search rows. -/
theorem searchCodeBoundedInteriorRowsPrimrec_of_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceSearchCodeBoundedInteriorRowsPrimrec :=
  TM0FoldedReduction.sourceSearchCodeBoundedInteriorRowsPrimrec_of_interiorRows
    hinterior

set_option linter.style.longLine false in
/-- Bounded-interior bounded-search rows give variable-branch one-row proofs. -/
theorem searchCodeOneVarRowsPrimrec_of_boundedInteriorRows
    (hbounded : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    SourceSearchCodeOneVarRowsPrimrec :=
  TM0FoldedReduction.sourceSearchCodeOneVarRowsPrimrec_of_boundedInteriorRows
    hbounded

set_option linter.style.longLine false in
/-- Interior bounded-search rows give variable-branch one-row proofs. -/
theorem searchCodeOneVarRowsPrimrec_of_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceSearchCodeOneVarRowsPrimrec :=
  searchCodeOneVarRowsPrimrec_of_boundedInteriorRows
    (searchCodeBoundedInteriorRowsPrimrec_of_interiorRows hinterior)

set_option linter.style.longLine false in
/-- Interior bounded-search rows give the bounded-search label-index target. -/
theorem searchCodeLabelIndexPrimrec_of_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  searchCodeLabelIndexPrimrec_of_oneVarRows
    (searchCodeOneVarRowsPrimrec_of_interiorRows hinterior)

set_option linter.style.longLine false in
/-- Interior bounded-search rows give the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_interiorRows
    (hinterior : SourceSearchCodeInteriorRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_interiorRows
    hinterior

set_option linter.style.longLine false in
/-- Bounded-interior bounded-search rows give the bounded-search label-index target. -/
theorem searchCodeLabelIndexPrimrec_of_boundedInteriorRows
    (hbounded : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    SourceSearchCodeLabelIndexFromPrimrec :=
  searchCodeLabelIndexPrimrec_of_oneVarRows
    (searchCodeOneVarRowsPrimrec_of_boundedInteriorRows hbounded)

set_option linter.style.longLine false in
/-- Bounded-interior bounded-search rows give the bounded-search start-decoder target. -/
theorem searchCodeLabelIndexStartPrimrec_of_boundedInteriorRows
    (hbounded : SourceSearchCodeBoundedInteriorRowsPrimrec) :
    SourceSearchCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourceSearchCodeLabelIndexStartPrimrec_of_boundedInteriorRows
    hbounded

set_option linter.style.longLine false in
/-- The bounded-search decoder-step and label-index targets are equivalent. -/
theorem searchCodeDecoderStepPrimrec_iff_labelIndexPrimrec :
    SourceSearchCodeDecoderStepPrimrec ↔ SourceSearchCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourceSearchCodeDecoderStepPrimrec_iff_labelIndexFromPrimrec

set_option linter.style.longLine false in
/-- The one-fuel row and label-index bounded-search targets are equivalent. -/
theorem searchCodeOneRowsPrimrec_iff_labelIndexPrimrec :
    SourceSearchCodeOneRowsPrimrec ↔ SourceSearchCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourceSearchCodeOneRowsPrimrec_iff_labelIndexFromPrimrec

set_option linter.style.longLine false in
/-- The variable-branch one-row and interior bounded-search row targets are equivalent. -/
theorem searchCodeOneVarRowsPrimrec_iff_interiorRowsPrimrec :
    SourceSearchCodeOneVarRowsPrimrec ↔ SourceSearchCodeInteriorRowsPrimrec :=
  TM0FoldedReduction.sourceSearchCodeOneVarRowsPrimrec_iff_interiorRowsPrimrec

/-- The source-specialized label-index target implies the decoder-step target. -/
theorem sourceDecoderStepPrimrec_of_sourceLabelIndex
    (h : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFromPrimrec
    h

/-- The decoder-step target implies the source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_decoderStep
    (h : SourcePositionCodeDecoderStepPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_decoderStep h

set_option linter.style.longLine false in
/-- The source-specialized full offset decoder gives the position-coded start decoder target. -/
theorem sourceLabelIndexStartPrimrec_of_sourceLabelIndex
    (h : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexStartPrimrec_of_labelIndexFrom h

set_option linter.style.longLine false in
/-- The position-coded start decoder recovers the full source-specialized offset decoder target. -/
theorem sourceLabelIndexPrimrec_of_labelIndexStart
    (h : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_labelIndexStart h

set_option linter.style.longLine false in
/-- The position-coded start decoder implies the generated position-code decoder step. -/
theorem sourceDecoderStepPrimrec_of_labelIndexStart
    (h : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  sourceDecoderStepPrimrec_of_sourceLabelIndex
    (sourceLabelIndexPrimrec_of_labelIndexStart h)

set_option linter.style.longLine false in
/-- The position-coded start decoder recovers the interior-at-index row target. -/
theorem sourceInteriorRowsAtIndexPrimrec_of_labelIndexStart
    (h : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeInteriorRowsAtIndexPrimrec_of_labelIndexStart h

set_option linter.style.longLine false in
/-- The position-coded start decoder recovers bounded interior rows at index. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_of_labelIndexStart
    (h : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_labelIndexStart h

set_option linter.style.longLine false in
/-- The position-coded start decoder recovers the exact one-row-at-index target. -/
theorem sourceOneRowsAtIndexPrimrec_of_labelIndexStart
    (h : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsAtIndexPrimrec_of_labelIndexStart h

set_option linter.style.longLine false in
/-- The position-coded start decoder gives the first interior row target. -/
theorem sourceFirstInteriorRowsAtIndexPrimrec_of_labelIndexStart
    (h : SourcePositionCodeLabelIndexStartPrimrec) :
    SourcePositionCodeFirstInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeFirstInteriorRowsAtIndexPrimrec_of_labelIndexStart h

set_option linter.style.longLine false in
/-- The exact one-row-at-index target gives the first interior row target. -/
theorem sourceFirstInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    (h : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeFirstInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeFirstInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex h

set_option linter.style.longLine false in
/-- The interior-at-index target gives the first interior row target. -/
theorem sourceFirstInteriorRowsAtIndexPrimrec_of_interiorAtIndex
    (h : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeFirstInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeFirstInteriorRowsAtIndexPrimrec_of_interiorAtIndex h

set_option linter.style.longLine false in
/-- The exact one-row-at-index target recovers the final position-coded start decoder target. -/
theorem sourceLabelIndexStartPrimrec_of_oneRowsAtIndex
    (h : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexStartPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexStartPrimrec_of_oneRowsAtIndex h

set_option linter.style.longLine false in
/-- The final source-specialized start decoder and full offset decoder targets are equivalent. -/
theorem sourceLabelIndexStartPrimrec_iff_sourceLabelIndexPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexStartPrimrec_iff_labelIndexFromPrimrec

set_option linter.style.longLine false in
/-- The final source-specialized start decoder target is equivalent to one-row at-index rows. -/
theorem sourceLabelIndexStartPrimrec_iff_oneRowsAtIndexPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeOneRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexStartPrimrec_iff_oneRowsAtIndexPrimrec

set_option linter.style.longLine false in
/-- The final source-specialized start decoder target is equivalent to interior rows at index. -/
theorem sourceLabelIndexStartPrimrec_iff_interiorRowsAtIndexPrimrec :
    SourcePositionCodeLabelIndexStartPrimrec ↔
      SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexStartPrimrec_iff_interiorRowsAtIndexPrimrec

/-- The final source-side decoder-step and source-specialized label-index targets are equivalent. -/
theorem sourceDecoderStepPrimrec_iff_sourceLabelIndexPrimrec :
    SourcePositionCodeDecoderStepPrimrec ↔ SourcePositionCodeLabelIndexFromPrimrec :=
  ⟨sourceLabelIndexPrimrec_of_decoderStep,
    sourceDecoderStepPrimrec_of_sourceLabelIndex⟩

/-- One-row generated position-code rows give the interior-row target. -/
theorem sourceInteriorRowsPrimrec_of_oneRows
    (h : SourcePositionCodeOneRowsPrimrec) :
    SourcePositionCodeInteriorRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeInteriorRowsPrimrec_of_oneRows h

/-- Interior generated position-code rows give the bounded-interior target. -/
theorem sourceBoundedInteriorRowsPrimrec_of_interiorRows
    (h : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeBoundedInteriorRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior h

/-- Bounded-interior generated position-code rows give the one-row target. -/
theorem sourceOneRowsPrimrec_of_boundedInteriorRows
    (h : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeOneRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsPrimrec_of_boundedInterior h

/-- Interior generated position-code rows give the one-row target. -/
theorem sourceOneRowsPrimrec_of_interiorRows
    (h : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeOneRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsPrimrec_of_interior h

set_option linter.style.longLine false in
/-- Bounded-interior generated position-code rows imply the at-index target. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_of_boundedInteriorRows
    (h : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_positionCodeBoundedInteriorRows
    h

set_option linter.style.longLine false in
/-- Interior generated position-code rows imply the at-index target. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_of_interiorRows
    (h : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourceBoundedInteriorRowsAtIndexPrimrec_of_boundedInteriorRows
    (sourceBoundedInteriorRowsPrimrec_of_interiorRows h)

set_option linter.style.longLine false in
/-- Interior generated position-code rows imply the interior-at-index target. -/
theorem sourceInteriorRowsAtIndexPrimrec_of_interiorRows
    (h : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeInteriorRowsAtIndexPrimrec_of_positionCodeInteriorRows
    h

set_option linter.style.longLine false in
/-- One-row at-index generated position-code rows imply the bounded-interior at-index target. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    (h : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    h

set_option linter.style.longLine false in
/-- One-row at-index generated position-code rows imply interior at-index rows. -/
theorem sourceInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    (h : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    h

set_option linter.style.longLine false in
/-- Interior at-index generated position-code rows imply bounded-interior at-index rows. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_of_interiorRowsAtIndex
    (h : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_of_interiorAtIndex
    h

set_option linter.style.longLine false in
/-- Bounded-interior at-index generated position-code rows recover one-row at-index rows. -/
theorem sourceOneRowsAtIndexPrimrec_of_boundedInteriorRowsAtIndex
    (h : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsAtIndexPrimrec_of_boundedInteriorAtIndex
    h

set_option linter.style.longLine false in
/-- The at-index bounded-interior target implies the final generated decoder-step target. -/
theorem sourceDecoderStepPrimrec_of_boundedInteriorRowsAtIndex
    (h : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourcePositionCodeDecoderStepPrimrec_of_boundedInteriorAtIndex
    h

set_option linter.style.longLine false in
/-- The at-index one-row target implies the final generated decoder-step target. -/
theorem sourceDecoderStepPrimrec_of_oneRowsAtIndex
    (h : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourcePositionCodeDecoderStepPrimrec_of_oneRowsAtIndex h

set_option linter.style.longLine false in
/-- The at-index bounded-interior target implies the final source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_boundedInteriorRowsAtIndex
    (h : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourceLabelIndexPrimrec_of_decoderStep
    (sourceDecoderStepPrimrec_of_boundedInteriorRowsAtIndex h)

set_option linter.style.longLine false in
/-- The at-index one-row target implies the final source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_oneRowsAtIndex
    (h : SourcePositionCodeOneRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  sourceLabelIndexPrimrec_of_decoderStep
    (sourceDecoderStepPrimrec_of_oneRowsAtIndex h)

set_option linter.style.longLine false in
/-- The at-index interior-row target implies the final source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_interiorRowsAtIndex
    (h : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_interiorAtIndex
    h

set_option linter.style.longLine false in
/-- The source-specialized label-index target recovers the exact one-row at-index target. -/
theorem sourceOneRowsAtIndexPrimrec_of_sourceLabelIndex
    (h : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeOneRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsAtIndexPrimrec_of_sourcePositionCodeLabelIndexFrom
    h

set_option linter.style.longLine false in
/-- The source-specialized label-index target recovers bounded-interior rows at index. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_of_sourceLabelIndex
    (h : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  sourceBoundedInteriorRowsAtIndexPrimrec_of_oneRowsAtIndex
    (sourceOneRowsAtIndexPrimrec_of_sourceLabelIndex h)

set_option linter.style.longLine false in
/-- The final one-row and interior source-row targets are equivalent. -/
theorem sourceOneRowsPrimrec_iff_interiorRowsPrimrec :
    SourcePositionCodeOneRowsPrimrec ↔ SourcePositionCodeInteriorRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsPrimrec_iff_interiorRowsPrimrec

set_option linter.style.longLine false in
/-- The final one-row and bounded-interior source-row targets are equivalent. -/
theorem sourceOneRowsPrimrec_iff_boundedInteriorRowsPrimrec :
    SourcePositionCodeOneRowsPrimrec ↔
      SourcePositionCodeBoundedInteriorRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsPrimrec_iff_boundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/-- The final interior and bounded-interior source-row targets are equivalent. -/
theorem sourceInteriorRowsPrimrec_iff_boundedInteriorRowsPrimrec :
    SourcePositionCodeInteriorRowsPrimrec ↔
      SourcePositionCodeBoundedInteriorRowsPrimrec :=
  TM0FoldedReduction.sourcePositionCodeInteriorRowsPrimrec_iff_boundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/-- The final one-row-at-index and bounded-interior-at-index targets are equivalent. -/
theorem sourceOneRowsAtIndexPrimrec_iff_boundedInteriorRowsAtIndexPrimrec :
    SourcePositionCodeOneRowsAtIndexPrimrec ↔
      SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsAtIndexPrimrec_iff_boundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/-- The final one-row-at-index and source-specialized label-index targets are equivalent. -/
theorem sourceOneRowsAtIndexPrimrec_iff_sourceLabelIndexPrimrec :
    SourcePositionCodeOneRowsAtIndexPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeOneRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/-- The final bounded-interior-at-index and source-specialized label-index targets are equivalent. -/
theorem sourceBoundedInteriorRowsAtIndexPrimrec_iff_sourceLabelIndexPrimrec :
    SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeBoundedInteriorRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/-- The final interior-at-index and source-specialized label-index targets are equivalent. -/
theorem sourceInteriorRowsAtIndexPrimrec_iff_sourceLabelIndexPrimrec :
    SourcePositionCodeInteriorRowsAtIndexPrimrec ↔
      SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeInteriorRowsAtIndexPrimrec_iff_sourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/-- One-row generated position-code rows imply the source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_oneRows
    (h : SourcePositionCodeOneRowsPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeOneRows h

set_option linter.style.longLine false in
/-- Bounded-interior generated position-code rows imply the source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_boundedInteriorRows
    (h : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeBoundedInteriorRows h

set_option linter.style.longLine false in
/-- Interior generated position-code rows imply the source-specialized label-index target. -/
theorem sourceLabelIndexPrimrec_of_interiorRows
    (h : SourcePositionCodeInteriorRowsPrimrec) :
    SourcePositionCodeLabelIndexFromPrimrec :=
  TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows h

end LeanWang
