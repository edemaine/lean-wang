/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction

/-!
Source-side target names for the final Wang-tile undecidability theorem.

These are thin aliases for the generated position-coded folded-TM0 source
obligations.  Keeping them in a small submodule gives the final theorem surface
a cached boundary for source-frontier edits.
-/

namespace LeanWang

set_option linter.style.longLine false in
/--
Source-side primitive-recursion target for the generated position-coded folded
program.  This is the narrower target preferred by the final route: prove the
global accumulator step primitive recursive, then derive the program-data source
obligations through `PositionSourceObligations`.
-/
abbrev SourcePositionCodeDecoderStepPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeDecoderStepPrimrec

/--
Source-side primitive-recursion target for one generated position-code row.
This is equivalent to the interior and bounded-interior row targets below, but
is often the smallest local target to prove by inspecting one generated row.
-/
abbrev SourcePositionCodeOneRowsPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeOneRowsPrimrec

/--
Source-side primitive-recursion target for generated interior position-code
rows.
-/
abbrev SourcePositionCodeInteriorRowsPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Source-side primitive-recursion target for generated bounded-interior
position-code rows.
-/
abbrev SourcePositionCodeBoundedInteriorRowsPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeBoundedInteriorRowsPrimrec

/--
Source-side primitive-recursion target for one generated position-code row at
the concrete numeric label slots decoded by the final position-code
accumulator.
-/
abbrev SourcePositionCodeOneRowsAtIndexPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeOneRowsAtIndexPrimrec

/--
Source-side primitive-recursion target for the first nonempty generated
position-code row at concrete numeric label slots.
-/
abbrev SourcePositionCodeFirstInteriorRowsAtIndexPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeFirstInteriorRowsAtIndexPrimrec

/--
Source-side primitive-recursion target for generated interior position-code
rows at the concrete numeric label slots decoded by the final position-code
accumulator.
-/
abbrev SourcePositionCodeInteriorRowsAtIndexPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeInteriorRowsAtIndexPrimrec

/--
Source-side primitive-recursion target for generated bounded-interior
position-code rows at the concrete numeric label slots decoded by the final
position-code accumulator.
-/
abbrev SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

/--
Source-side primitive-recursion target for the global position-code label-index
decoder.  This is the current cleanest source-facing target: it implies the
generated position-code accumulator step by specializing to `fuel = 1`.
-/
abbrev GlobalPositionCodeLabelIndexFromPrimrec : Prop :=
  TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec

/--
Source-specialized primitive-recursion target for the generated position-code
label-index decoder.  This is weaker than
`GlobalPositionCodeLabelIndexFromPrimrec`, because the final reduction only
needs codes of the form `NatPartrecToToPartrec.translate c`.
-/
abbrev SourcePositionCodeLabelIndexFromPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec

/--
Source-side primitive-recursion target for the position-coded start decoder
used directly by `positionProgramData`.
-/
abbrev SourcePositionCodeLabelIndexStartPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Source-side primitive-recursion target for the bounded-search label-index
decoder used by the ordinary `programData` source route.
-/
abbrev SourceSearchCodeLabelIndexFromPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeLabelIndexFromPrimrec

/--
Source-side primitive-recursion target for the numeric-state start decoder
used directly by ordinary `programData`.
-/
abbrev SourceCodeLabelIndexStartPrimrec : Prop :=
  TM0FoldedReduction.SourceCodeLabelIndexStartPrimrec

/--
Global primitive-recursion target for the numeric-state start decoder used
directly by ordinary `programData`.  This is the non-source-specialized version
of `SourceCodeLabelIndexStartPrimrec`; the final reduction uses it after
precomposing with `NatPartrecToToPartrec.translate`.
-/
abbrev GlobalCodeLabelIndexStartPrimrec : Prop :=
  TM0FoldedReduction.GlobalCodeLabelIndexStartPrimrec

/--
Source-side primitive-recursion target for the bounded-search start decoder
used directly by ordinary `programData`.
-/
abbrev SourceSearchCodeLabelIndexStartPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeLabelIndexStartPrimrec

/--
Source-side primitive-recursion target for the bounded-search accumulator step.
This is equivalent to `SourceSearchCodeLabelIndexFromPrimrec` but often closer
to the recursive decoder implementation.
-/
abbrev SourceSearchCodeDecoderStepPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeDecoderStepPrimrec

/--
Source-side primitive-recursion target for the one-fuel bounded-search
label-index rows.
-/
abbrev SourceSearchCodeOneRowsPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeOneRowsPrimrec

/--
Source-side primitive-recursion target for one bounded-search row on a concrete
translated Partrec-variable branch.
-/
abbrev SourceSearchCodeOneVarRowsPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeOneVarRowsPrimrec

/-- Source-side primitive-recursion target for interior bounded-search rows. -/
abbrev SourceSearchCodeInteriorRowsPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeInteriorRowsPrimrec

/--
Source-side primitive-recursion target for bounded-interior bounded-search
rows.
-/
abbrev SourceSearchCodeBoundedInteriorRowsPrimrec : Prop :=
  TM0FoldedReduction.SourceSearchCodeBoundedInteriorRowsPrimrec

end LeanWang
