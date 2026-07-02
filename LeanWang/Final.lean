/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction

/-!
Final theorem surface for the Wang-tile undecidability proof.

This module keeps the public endpoint small.  The remaining work is isolated in
`FinalReductionInputs`: the finite-transcription-facing Robinson Section 7
board/free-line layer-patch scaffold package and the generated-position source
obligations for the folded TM0 reduction.  Constructors below also expose the
source-row route and the origin-zero-window route, which derives the checked
stacks from the geometric origin-zero scaffold invariant and the audited finite
Figure 13 / Figure 16 pair-compatibility table.

The cleanest paper-facing scaffold surface is
`FinalSection7PositiveBoxConstructionObligations`: Robinson Section 7
board/free-line active-corner recognition plus centered positive active-corner
boxes.  The lower-level layer-patch and checked-Figure-16 surfaces are retained
as finite-transcription routes.
-/

noncomputable section

namespace LeanWang

open Nat.Partrec (Code)
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

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
Source-side primitive-recursion target for the global position-code label-index
decoder.  This is the current cleanest source-facing target: it implies the
generated position-code accumulator step by specializing to `fuel = 1`.
-/
abbrev GlobalPositionCodeLabelIndexFromPrimrec : Prop :=
  TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec

/--
Scaffold-side target for the first audited L2-blank candidate: Section 7
board/free-line active-corner recognition.
-/
abbrev L2C1Section7BoardFreeLineActiveCorner : Prop :=
  TM0FoldedReduction.Section7BoardFreeLineActiveCornerInvariant
    l2Component1Figure18ScaffoldData

/--
Narrower scaffold-side target for the first audited L2-blank candidate:
active/corner recognition at Robinson's canonical free crossings.  This is
equivalent to `L2C1Section7BoardFreeLineActiveCorner`, but usually closer to
the local recognizability proof.
-/
abbrev L2C1Section7CanonicalActiveCorner : Prop :=
  TM0FoldedReduction.Section7CanonicalFreeSiteRectActiveCornerInvariant
    l2Component1Figure18ScaffoldData

/--
Raw Figure 13 board-level square-tiling target at the positive Robinson board
sizes used by the Section 7 construction.
-/
abbrev Figure13PositiveBoardLevelTileableSquares : Prop :=
  TM0FoldedReduction.Figure13PositiveBoardLevelTileableSquares

/-- The global position-code label-index target implies the decoder-step target. -/
theorem sourceDecoderStepPrimrec_of_globalLabelIndex
    (h : GlobalPositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourcePositionCodeDecoderStepPrimrec_of_globalPositionCodeLabelIndexFromPrimrec
    h

/--
The two remaining construction interfaces for the current preferred route to
the domino problem.

`scaffold` packages the Section 7 board/free-line active-corner recognition and
the finite active-corner layer patches for the audited first L2 candidate.
`source` packages the generated-position source reduction obligations.  The
final `positionProgramData` route does not need the stronger statement-list
uniqueness package used by the older canonical-row-equality route.
-/
structure FinalReductionInputs : Prop where
  scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData
  source : TM0FoldedReduction.PositionSourceObligations

/--
Preferred remaining proof obligations for the current construction route.

These are the three proof-facing facts still to be supplied by the scaffold
and source-code construction:
* the Section 7 origin-zero active/corner window invariant for the first
  audited L2 blank candidate;
* row-major checked compatible Figure 16 level data, which supplies the finite
  active-corner layer patches;
* the source-uniform generated-position interior row decoder.
-/
structure FinalConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Preferred source-facing variant of the remaining proof obligations.

Compared with `FinalConstructionObligations`, this asks for primitive
recursiveness of the generated position-code decoder step directly, instead of
the stronger interior-row generator package.
-/
structure FinalDecoderStepConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Preferred source-facing variant using the global position-code label-index
decoder.  This is slightly closer to the generated folded-program construction
than `FinalDecoderStepConstructionObligations`; the decoder step is derived
uniformly from this label-index decoder.
-/
structure FinalGlobalPositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Proof-facing variant of the preferred remaining proof obligations.

This asks for compatible Figure 16 level checks directly, avoiding the
row-major checked-data packaging when the scaffold construction naturally
produces source and target site rectangles with Boolean checks.
-/
structure FinalLevelChecksConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Proof-facing variant with the narrower decoder-step source target.
-/
structure FinalLevelChecksDecoderStepConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Proof-facing variant with the global position-code label-index source target.
-/
structure FinalLevelChecksGlobalPositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Finite-check-facing variant of the preferred remaining proof obligations.

The checked stack field is a finite transcription target for the audited first
L2 blank candidate.  It implies the origin-zero active/corner window invariant
used by the scaffold package, so this is the cleaner theorem surface for the
next scaffold-instantiation step.
-/
structure FinalCheckedConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Finite-check-facing variant with the narrower decoder-step source target.

The scaffold fields are the concrete checked origin-zero stacks plus audited
Figure 16 level data; the source field is only the generated position-code
accumulator-step primitive-recursion proof.
-/
structure FinalCheckedDecoderStepConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Finite-check-facing variant with the global position-code label-index source
target.  The checked scaffold fields remain concrete finite targets; the
source field is the uniform generated label-index decoder.
-/
structure FinalCheckedGlobalPositionCodeConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Paper-facing Section 7 board/free-line final obligations.

This is the currently preferred scaffold surface: the Robinson board/free-line
geometry supplies active/corner recognition, and centered positive active-corner
boxes supply the finite layer patches needed by the backward construction.  It
avoids the false raw Figure 13 macro-square diagnostic route and the over-strong
source-stack raw-boundary diagnostic interfaces below.
-/
structure FinalSection7PositiveBoxConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Paper-facing Section 7 board/free-line obligations with the narrower
decoder-step source target.
-/
structure FinalSection7PositiveBoxDecoderStepConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Paper-facing Section 7 board/free-line obligations with the global
position-code label-index source target.
-/
structure FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Paper-facing Section 7 final obligations split into the two geometric facts
that Robinson's construction naturally proves: board/free-line active-corner
recognition and positive board-level raw Figure 13 squares.
-/
structure FinalSection7BoardLevelConstructionObligations : Prop where
  boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner
  positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Board-level Section 7 obligations with the narrower decoder-step source target.
-/
structure FinalSection7BoardLevelDecoderStepConstructionObligations : Prop where
  boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner
  positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Board-level Section 7 obligations with the global position-code label-index
source target.
-/
structure FinalSection7BoardLevelGlobalPositionCodeConstructionObligations : Prop where
  boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner
  positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Most local scaffold-facing Section 7 final obligations: active/corner
recognition only at canonical free crossings plus positive board-level raw
Figure 13 squares.
-/
structure FinalSection7ActiveCornerBoardLevelConstructionObligations : Prop where
  activeCorner : L2C1Section7CanonicalActiveCorner
  positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Canonical-active-corner board-level obligations with the narrower decoder-step
source target.
-/
structure FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations :
    Prop where
  activeCorner : L2C1Section7CanonicalActiveCorner
  positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Canonical-active-corner board-level obligations with the global position-code
label-index source target.
-/
structure FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations :
    Prop where
  activeCorner : L2C1Section7CanonicalActiveCorner
  positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Raw-boundary diagnostic variant of the remaining proof obligations.

This route is useful for testing finite Figure 13/Figure 16 data plumbing, but
it is stronger than Robinson Section 7 because it asks the source Figure 16
layer stack itself to be compatible along raw Figure 13 boundaries.  The
paper-shaped proof should use `FinalSection7PositiveBoxConstructionObligations`
instead.
-/
structure FinalRawBoundaryConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryCheckedLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Raw-boundary level-check variant of the diagnostic obligations.

This exposes the finite-check statement directly: for each Figure 16 level,
produce a source/free-grid rectangle whose ordinary compatibility and
raw-boundary compatibility Boolean checks pass.  The checked-data packaging is
derived from these level checks.
-/
structure FinalRawBoundaryLevelChecksConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelChecks
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Raw-boundary level-certificate variant of the diagnostic obligations.

This is the proof-facing form of the same scaffold target: for each level,
provide the actual source/free-grid rectangle together with compatibility and
raw-boundary proofs.  It is equivalent to the level-check form, but usually
more convenient when the construction is not just a finite Boolean audit.
-/
structure FinalRawBoundaryLevelCertificatesConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelCertificates
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

namespace FinalReductionInputs

/-- Build the final inputs directly from the scaffold package and source obligations. -/
def ofScaffoldAndSource
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs where
  scaffold := scaffold
  source := source

/--
Build the final inputs directly from the scaffold package and generated
interior position-code rows.
-/
def ofScaffoldAndSourceRows
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs directly from the scaffold package and the primitive
recursive generated position-code accumulator step.  This is a lower-level
source route than `ofScaffoldAndSourceRows`: it asks only for the global
decoder step, then uses the semantic folded-position proof to package the
source obligations.
-/
def ofScaffoldAndSourceDecoderStep
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      hstep)

set_option linter.style.longLine false in
/--
Build the final inputs directly from the scaffold package and the global
position-code label-index decoder target.  This is a slightly higher-level
source route than `ofScaffoldAndSourceDecoderStep`: it derives the generated
position-code accumulator step by specializing the label-index decoder to
`fuel = 1` on valid variable slots.
-/
def ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- This constructor unfolds the Section 7 board-level bridge into finite
-- layer-patch data, which is large but still a one-time endpoint conversion.
/--
Build the final inputs from Section 7 board/free-line active-corner recognition,
positive board-level raw Figure 13 square tilings, and source obligations.
-/
def ofSection7BoardLevelSource
    (boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofScaffoldAndSource
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfBoardFreeLineData
      (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineDataOfPositiveBoardLevelTileableSquares
        boardFreeLineActiveCorner positiveBoardLevels))
    source

/--
Build the final inputs from Section 7 board/free-line active-corner recognition,
positive board-level raw Figure 13 square tilings, and generated interior
position-code rows.
-/
def ofSection7BoardLevel
    (boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofSection7BoardLevelSource
    boardFreeLineActiveCorner positiveBoardLevels
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from Section 7 board/free-line active-corner recognition,
positive board-level raw Figure 13 square tilings, and the primitive recursive
generated position-code accumulator step.
-/
def ofSection7BoardLevelDecoderStep
    (boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofSection7BoardLevelSource
    boardFreeLineActiveCorner positiveBoardLevels
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      hstep)

set_option linter.style.longLine false in
/--
Build the final inputs from Section 7 board/free-line active-corner recognition,
positive board-level raw Figure 13 square tilings, and the global primitive
recursive position-code label-index decoder.
-/
def ofSection7BoardLevelGlobalPositionCodeLabelIndexFrom
    (boardFreeLineActiveCorner : L2C1Section7BoardFreeLineActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofSection7BoardLevelSource
    boardFreeLineActiveCorner positiveBoardLevels
    (TM0FoldedReduction.positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Build the final inputs from canonical free-crossing active/corner recognition,
positive board-level raw Figure 13 square tilings, and source obligations.
-/
def ofSection7ActiveCornerBoardLevelSource
    (activeCorner : L2C1Section7CanonicalActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofSection7BoardLevelSource
    (TM0FoldedReduction.section7BoardFreeLineActiveCorner_of_activeCorner
      activeCorner)
    positiveBoardLevels source

/--
Build the final inputs from canonical free-crossing active/corner recognition,
positive board-level raw Figure 13 square tilings, and generated interior
position-code rows.
-/
def ofSection7ActiveCornerBoardLevel
    (activeCorner : L2C1Section7CanonicalActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofSection7ActiveCornerBoardLevelSource
    activeCorner positiveBoardLevels
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from canonical free-crossing active/corner recognition,
positive board-level raw Figure 13 square tilings, and the primitive recursive
generated position-code accumulator step.
-/
def ofSection7ActiveCornerBoardLevelDecoderStep
    (activeCorner : L2C1Section7CanonicalActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofSection7ActiveCornerBoardLevelSource
    activeCorner positiveBoardLevels
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      hstep)

set_option linter.style.longLine false in
/--
Build the final inputs from canonical free-crossing active/corner recognition,
positive board-level raw Figure 13 square tilings, and the global primitive
recursive position-code label-index decoder.
-/
def ofSection7ActiveCornerBoardLevelGlobalPositionCodeLabelIndexFrom
    (activeCorner : L2C1Section7CanonicalActiveCorner)
    (positiveBoardLevels : Figure13PositiveBoardLevelTileableSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofSection7ActiveCornerBoardLevelSource
    activeCorner positiveBoardLevels
    (TM0FoldedReduction.positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Build the final inputs directly from the scaffold package and the packaged
generated interior position-code decoder.

This is the proof-facing source route: the package carries the row generator
and translated statement-list uniqueness, while
`positionProgramData_haltsEmpty_iff_tm0_eval_dom` discharges semantic
correctness against the Mathlib TM0 evaluator.
-/
def ofScaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
      sourceRows
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom)

/--
Build the final inputs from the two split finite scaffold obligations for the
first audited L2 candidate: checked origin-zero stacks and finite active-corner
layer patches.
-/
def ofCheckedStacksAndLayerPatchesSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs where
  scaffold :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches
  source := source

/--
Build the final inputs from the two split finite scaffold obligations and
generated interior position-code rows.
-/
def ofCheckedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches)
    sourceRows

/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate.  This is the current finite transcription target for the scaffold
side: checked origin-zero stacks imply the Section 7 board/free-line
active-corner recognition field, while the supplied patches give the backward
active-corner box realization.
-/
def ofCheckedStackLayerPatchDataSource
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs where
  scaffold :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold
  source := source

/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate and generated interior position-code rows.
-/
def ofCheckedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold)
    sourceRows

/--
Build the final inputs from checked origin-zero stacks plus compatible Figure
16 macro-squares.  The Figure 16 certificate supplies the active-corner layer
patches for the first audited L2 candidate.
-/
def ofCheckedStacksAndCompatibleFig16Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      checkedStacks fig16)
    source

/--
Build the final inputs from checked origin-zero stacks, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
def ofCheckedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16Source
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus compatible
Figure 16 macro-squares.  The checked-stack part is derived from the
origin-zero windows using the audited finite Figure 13/Figure 16
pair-compatibility table.
-/
def ofOriginZeroWindowsAndCompatibleFig16Source
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
      originZeroWindows fig16)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and generated interior position-code rows.
-/
def ofOriginZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16Source
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, proof-facing
compatible Figure 16 level checks, and source obligations.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelChecksSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16Source
    originZeroWindows fig16 source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus proof-facing
compatible Figure 16 level checks.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelChecksSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, proof-facing
compatible Figure 16 level checks, and the primitive recursive generated
position-code accumulator step.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelChecksDecoderStep
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelChecksSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      hstep)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, proof-facing
compatible Figure 16 level checks, and the global primitive recursive
position-code label-index decoder.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelChecksSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus row-major checked
compatible Figure 16 level data.
-/
def ofCheckedStacksAndCompatibleFig16LevelDataSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16LevelData
      checkedStacks fig16)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and generated interior position-code rows.
-/
def ofCheckedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16LevelDataSource
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
def ofCheckedStacksAndCompatibleFig16LevelDataPackage
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16LevelDataSource
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
      sourceRows
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom)

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the primitive recursive generated
position-code accumulator step.
-/
def ofCheckedStacksAndCompatibleFig16LevelDataDecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16LevelDataSource
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      hstep)

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the global primitive recursive
position-code label-index decoder.
-/
def ofCheckedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16LevelDataSource
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus row-major
checked compatible Figure 16 level data.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16LevelData
      originZeroWindows fig16)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and generated interior position-code
rows.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the primitive recursive generated
position-code accumulator step.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataDecoderStep
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      hstep)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the global primitive recursive
position-code label-index decoder.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus row-major
checked raw-boundary Figure 16 level data.
-/
def ofOriginZeroWindowsAndRawBoundaryCheckedLevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryCheckedLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows
    (TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelData_of_rawBoundaryCheckedLevelData
      rawBoundary)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked raw-boundary Figure 16 level data, and generated interior position-code
rows.
-/
def ofOriginZeroWindowsAndRawBoundaryCheckedLevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryCheckedLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndRawBoundaryCheckedLevelDataSource
    originZeroWindows rawBoundary
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus raw-boundary
Figure 16 level checks.
-/
def ofOriginZeroWindowsAndRawBoundaryLevelChecksSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelChecks)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndRawBoundaryCheckedLevelDataSource
    originZeroWindows
    (TM0FoldedReduction.canonicalRawBoundaryCheckedLevelData_of_levelChecks
      rawBoundary)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, raw-boundary
Figure 16 level checks, and generated interior position-code rows.
-/
def ofOriginZeroWindowsAndRawBoundaryLevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndRawBoundaryLevelChecksSource
    originZeroWindows rawBoundary
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus
raw-boundary Figure 16 level certificates.
-/
def ofOriginZeroWindowsAndRawBoundaryLevelCertificatesSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelCertificates)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndRawBoundaryLevelChecksSource
    originZeroWindows
    (TM0FoldedReduction.canonicalRawBoundaryLevelChecks_of_levelCertificates
      rawBoundary)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, raw-boundary
Figure 16 level certificates, and generated interior position-code rows.
-/
def ofOriginZeroWindowsAndRawBoundaryLevelCertificates
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelCertificates)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndRawBoundaryLevelCertificatesSource
    originZeroWindows rawBoundary
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
      sourceRows
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom)

end FinalReductionInputs

namespace FinalDecoderStepConstructionObligations

/-- Convert the decoder-step final obligation package into the low-level endpoint. -/
def toFinalReductionInputs
    (h : FinalDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataDecoderStep
    h.originZeroWindows h.fig16 h.decoderStep

end FinalDecoderStepConstructionObligations

namespace FinalGlobalPositionCodeConstructionObligations

/--
Convert the global-label-index final obligation package into the decoder-step
obligation package.
-/
def toDecoderStepConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    FinalDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 := h.fig16
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label-index final obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    h.originZeroWindows h.fig16 h.labelIndex

end FinalGlobalPositionCodeConstructionObligations

namespace FinalConstructionObligations

/-- Convert the preferred final obligation package into the low-level endpoint. -/
def toFinalReductionInputs
    (h : FinalConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelData
    h.originZeroWindows h.fig16 h.sourceRows

end FinalConstructionObligations

namespace FinalLevelChecksDecoderStepConstructionObligations

set_option linter.style.longLine false in
/-- Convert the level-check decoder-step obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelChecksDecoderStep
    h.originZeroWindows h.fig16 h.decoderStep

end FinalLevelChecksDecoderStepConstructionObligations

namespace FinalLevelChecksGlobalPositionCodeConstructionObligations

/--
Convert the level-check global-label-index package into the level-check
decoder-step package.
-/
def toDecoderStepConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalLevelChecksDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 := h.fig16
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the level-check global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    h.originZeroWindows h.fig16 h.labelIndex

end FinalLevelChecksGlobalPositionCodeConstructionObligations

namespace FinalLevelChecksConstructionObligations

set_option linter.style.longLine false in
/-- Convert the level-check final obligation package into the low-level endpoint. -/
def toFinalReductionInputs
    (h : FinalLevelChecksConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelChecks
    h.originZeroWindows h.fig16 h.sourceRows

end FinalLevelChecksConstructionObligations

namespace FinalCheckedDecoderStepConstructionObligations

/--
Convert the finite-check-facing decoder-step package into the window-based
decoder-step obligation package.
-/
def toDecoderStepConstructionObligations
    (h : FinalCheckedDecoderStepConstructionObligations) :
    FinalDecoderStepConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  fig16 := h.fig16
  decoderStep := h.decoderStep

/-- Convert the finite-check-facing decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataDecoderStep
    h.checkedStacks h.fig16 h.decoderStep

end FinalCheckedDecoderStepConstructionObligations

namespace FinalCheckedGlobalPositionCodeConstructionObligations

/--
Convert the finite-check-facing global-label-index package into the
window-based global-label-index obligation package.
-/
def toGlobalPositionCodeConstructionObligations
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    FinalGlobalPositionCodeConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  fig16 := h.fig16
  labelIndex := h.labelIndex

/--
Convert the finite-check-facing global-label-index package into the
decoder-step package.
-/
def toCheckedDecoderStepConstructionObligations
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    FinalCheckedDecoderStepConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 := h.fig16
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the finite-check-facing global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    h.checkedStacks h.fig16 h.labelIndex

end FinalCheckedGlobalPositionCodeConstructionObligations

namespace FinalCheckedConstructionObligations

/--
Convert the finite-check-facing obligation package into the window-based
preferred final obligation package.
-/
def toConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    FinalConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  fig16 := h.fig16
  sourceRows := h.sourceRows

/-- Convert the finite-check-facing obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelData
    h.checkedStacks h.fig16 h.sourceRows

end FinalCheckedConstructionObligations

namespace FinalRawBoundaryConstructionObligations

/--
The raw-boundary final obligation package is inconsistent for the current
Figure 13/Figure 16 transcription: its raw-boundary field would imply the
refuted positive-board raw Figure 13 square tilings.
-/
theorem impossible : ¬ FinalRawBoundaryConstructionObligations := by
  intro h
  exact ConcreteData.not_hasCanonicalFigure16SourceRawBoundaryCheckedLevelData
    h.rawBoundary

/--
Convert the raw-boundary final obligation package into the compatible-level
obligation package.
-/
def toConstructionObligations
    (h : FinalRawBoundaryConstructionObligations) :
    FinalConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 :=
    TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelData_of_rawBoundaryCheckedLevelData
      h.rawBoundary
  sourceRows := h.sourceRows

/-- Convert the raw-boundary final obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalRawBoundaryConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryCheckedLevelData
    h.originZeroWindows h.rawBoundary h.sourceRows

end FinalRawBoundaryConstructionObligations

namespace FinalRawBoundaryLevelChecksConstructionObligations

/--
The raw-boundary level-check final obligation package is inconsistent for the
current Figure 13/Figure 16 transcription.
-/
theorem impossible : ¬ FinalRawBoundaryLevelChecksConstructionObligations := by
  intro h
  exact ConcreteData.not_hasCanonicalFigure16SourceRawBoundaryLevelChecks
    h.rawBoundary

/--
Convert the raw-boundary level-check final obligation package into the
checked-data raw-boundary package.
-/
def toRawBoundaryConstructionObligations
    (h : FinalRawBoundaryLevelChecksConstructionObligations) :
    FinalRawBoundaryConstructionObligations where
  originZeroWindows := h.originZeroWindows
  rawBoundary :=
    TM0FoldedReduction.canonicalRawBoundaryCheckedLevelData_of_levelChecks
      h.rawBoundary
  sourceRows := h.sourceRows

/-- Convert the raw-boundary level-check package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalRawBoundaryLevelChecksConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryLevelChecks
    h.originZeroWindows h.rawBoundary h.sourceRows

end FinalRawBoundaryLevelChecksConstructionObligations

namespace FinalRawBoundaryLevelCertificatesConstructionObligations

/--
The raw-boundary level-certificate final obligation package is inconsistent
for the current Figure 13/Figure 16 transcription.
-/
theorem impossible :
    ¬ FinalRawBoundaryLevelCertificatesConstructionObligations := by
  intro h
  exact ConcreteData.not_hasCanonicalFigure16SourceRawBoundaryLevelCertificates
    h.rawBoundary

/--
Convert the raw-boundary level-certificate final obligation package into the
level-check package.
-/
def toRawBoundaryLevelChecksConstructionObligations
    (h : FinalRawBoundaryLevelCertificatesConstructionObligations) :
    FinalRawBoundaryLevelChecksConstructionObligations where
  originZeroWindows := h.originZeroWindows
  rawBoundary :=
    TM0FoldedReduction.canonicalRawBoundaryLevelChecks_of_levelCertificates
      h.rawBoundary
  sourceRows := h.sourceRows

/--
Convert the raw-boundary level-certificate final obligation package into the
checked-data raw-boundary package.
-/
def toRawBoundaryConstructionObligations
    (h : FinalRawBoundaryLevelCertificatesConstructionObligations) :
    FinalRawBoundaryConstructionObligations :=
  h.toRawBoundaryLevelChecksConstructionObligations.toRawBoundaryConstructionObligations

/-- Convert the raw-boundary level-certificate package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalRawBoundaryLevelCertificatesConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryLevelCertificates
    h.originZeroWindows h.rawBoundary h.sourceRows

end FinalRawBoundaryLevelCertificatesConstructionObligations

namespace FinalSection7PositiveBoxDecoderStepConstructionObligations

/-- Convert the paper-facing Section 7 decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7PositiveBoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
      h.section7)
    h.decoderStep

end FinalSection7PositiveBoxDecoderStepConstructionObligations

namespace FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations

/--
Convert the paper-facing Section 7 global-label-index package into the
decoder-step package.
-/
def toDecoderStepConstructionObligations
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 := h.section7
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the paper-facing Section 7 global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
      h.section7)
    h.labelIndex

end FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations

namespace FinalSection7PositiveBoxConstructionObligations

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 board/free-line obligations. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7PositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    h.section7 h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 board/free-line obligations. -/
theorem domino_problem_undecidable
    (h : FinalSection7PositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    h.section7 h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalSection7PositiveBoxConstructionObligations

namespace FinalSection7BoardLevelDecoderStepConstructionObligations

set_option linter.style.longLine false in
/-- Convert the board-level Section 7 decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7BoardLevelDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofSection7BoardLevelDecoderStep
    h.boardFreeLineActiveCorner h.positiveBoardLevels h.decoderStep

end FinalSection7BoardLevelDecoderStepConstructionObligations

namespace FinalSection7BoardLevelGlobalPositionCodeConstructionObligations

/--
Convert the board-level Section 7 global-label-index package into the
decoder-step package.
-/
def toDecoderStepConstructionObligations
    (h : FinalSection7BoardLevelGlobalPositionCodeConstructionObligations) :
    FinalSection7BoardLevelDecoderStepConstructionObligations where
  boardFreeLineActiveCorner := h.boardFreeLineActiveCorner
  positiveBoardLevels := h.positiveBoardLevels
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the board-level Section 7 global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7BoardLevelGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofSection7BoardLevelGlobalPositionCodeLabelIndexFrom
    h.boardFreeLineActiveCorner h.positiveBoardLevels h.labelIndex

end FinalSection7BoardLevelGlobalPositionCodeConstructionObligations

namespace FinalSection7BoardLevelConstructionObligations

set_option linter.style.longLine false in
/-- Convert the board-level Section 7 package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7BoardLevelConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofSection7BoardLevel
    h.boardFreeLineActiveCorner h.positiveBoardLevels h.sourceRows

end FinalSection7BoardLevelConstructionObligations

namespace FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations

set_option linter.style.longLine false in
/-- Convert the canonical-active-corner board-level decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofSection7ActiveCornerBoardLevelDecoderStep
    h.activeCorner h.positiveBoardLevels h.decoderStep

end FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations

namespace FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations

/--
Convert the canonical-active-corner board-level global-label-index package into
the decoder-step package.
-/
def toDecoderStepConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations) :
    FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations where
  activeCorner := h.activeCorner
  positiveBoardLevels := h.positiveBoardLevels
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Convert the canonical-active-corner board-level global-label-index package into
the endpoint.
-/
def toFinalReductionInputs
    (h : FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofSection7ActiveCornerBoardLevelGlobalPositionCodeLabelIndexFrom
    h.activeCorner h.positiveBoardLevels h.labelIndex

end FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations

namespace FinalSection7ActiveCornerBoardLevelConstructionObligations

set_option linter.style.longLine false in
/-- Convert the canonical-active-corner board-level package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7ActiveCornerBoardLevelConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofSection7ActiveCornerBoardLevel
    h.activeCorner h.positiveBoardLevels h.sourceRows

end FinalSection7ActiveCornerBoardLevelConstructionObligations

set_option linter.style.longLine false in
/-- Encoded Wang domino undecidability from the final construction inputs. -/
theorem encoded_domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      h.scaffold h.source

set_option linter.style.longLine false in
/-- Wang domino undecidability from the final construction inputs. -/
theorem domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      h.scaffold h.source

/--
Encoded Wang domino undecidability from the preferred decoder-step final
obligations.
-/
theorem encoded_domino_problem_undecidable_of_decoderStepConstructionObligations
    (h : FinalDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/--
Wang domino undecidability from the preferred decoder-step final obligations.
-/
theorem domino_problem_undecidable_of_decoderStepConstructionObligations
    (h : FinalDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

/--
Encoded Wang domino undecidability from the preferred global-label-index final
obligations.
-/
theorem encoded_domino_problem_undecidable_of_globalPositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/--
Wang domino undecidability from the preferred global-label-index final
obligations.
-/
theorem domino_problem_undecidable_of_globalPositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

/-- Encoded Wang domino undecidability from the preferred final obligations. -/
theorem encoded_domino_problem_undecidable_of_constructionObligations
    (h : FinalConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/-- Wang domino undecidability from the preferred final obligations. -/
theorem domino_problem_undecidable_of_constructionObligations
    (h : FinalConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksConstructionObligations
    (h : FinalLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksConstructionObligations
    (h : FinalLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check decoder-step final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksDecoderStepConstructionObligations
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
decoder-step final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksDecoderStepConstructionObligations
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check global-label-index final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksGlobalPositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
global-label-index final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksGlobalPositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

/--
Encoded Wang domino undecidability from the finite-check-facing preferred
final obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/--
Wang domino undecidability from the finite-check-facing preferred final
obligations.
-/
theorem domino_problem_undecidable_of_checkedConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

/--
Encoded Wang domino undecidability from the finite-check-facing decoder-step
final obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedDecoderStepConstructionObligations
    (h : FinalCheckedDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/--
Wang domino undecidability from the finite-check-facing decoder-step final
obligations.
-/
theorem domino_problem_undecidable_of_checkedDecoderStepConstructionObligations
    (h : FinalCheckedDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

/--
Encoded Wang domino undecidability from the finite-check-facing
global-label-index final obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedGlobalPositionCodeConstructionObligations
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/--
Wang domino undecidability from the finite-check-facing global-label-index
final obligations.
-/
theorem domino_problem_undecidable_of_checkedGlobalPositionCodeConstructionObligations
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line construction obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7PositiveBoxConstructionObligations
    (h : FinalSection7PositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
construction obligations.
-/
theorem domino_problem_undecidable_of_section7PositiveBoxConstructionObligations
    (h : FinalSection7PositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line decoder-step construction obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7PositiveBoxDecoderStepConstructionObligations
    (h : FinalSection7PositiveBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
decoder-step construction obligations.
-/
theorem domino_problem_undecidable_of_section7PositiveBoxDecoderStepConstructionObligations
    (h : FinalSection7PositiveBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line global-label-index construction obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7PositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
global-label-index construction obligations.
-/
theorem domino_problem_undecidable_of_section7PositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from Section 7 board/free-line active-corner
recognition plus positive board-level raw Figure 13 squares.
-/
theorem encoded_domino_problem_undecidable_of_section7BoardLevelConstructionObligations
    (h : FinalSection7BoardLevelConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from Section 7 board/free-line active-corner
recognition plus positive board-level raw Figure 13 squares.
-/
theorem domino_problem_undecidable_of_section7BoardLevelConstructionObligations
    (h : FinalSection7BoardLevelConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from Section 7 board-level decoder-step
obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7BoardLevelDecoderStepConstructionObligations
    (h : FinalSection7BoardLevelDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from Section 7 board-level decoder-step obligations.
-/
theorem domino_problem_undecidable_of_section7BoardLevelDecoderStepConstructionObligations
    (h : FinalSection7BoardLevelDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from Section 7 board-level global-label-index
obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7BoardLevelGlobalPositionCodeConstructionObligations
    (h : FinalSection7BoardLevelGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from Section 7 board-level global-label-index
obligations.
-/
theorem domino_problem_undecidable_of_section7BoardLevelGlobalPositionCodeConstructionObligations
    (h : FinalSection7BoardLevelGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-crossing active/corner
recognition plus positive board-level raw Figure 13 squares.
-/
theorem encoded_domino_problem_undecidable_of_section7ActiveCornerBoardLevelConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-crossing active/corner
recognition plus positive board-level raw Figure 13 squares.
-/
theorem domino_problem_undecidable_of_section7ActiveCornerBoardLevelConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical-active-corner board-level
decoder-step obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7ActiveCornerBoardLevelDecoderStepConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical-active-corner board-level decoder-step
obligations.
-/
theorem domino_problem_undecidable_of_section7ActiveCornerBoardLevelDecoderStepConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical-active-corner board-level
global-label-index obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical-active-corner board-level
global-label-index obligations.
-/
theorem domino_problem_undecidable_of_section7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations
    (h : FinalSection7ActiveCornerBoardLevelGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the raw-boundary construction
obligations.
-/
theorem encoded_domino_problem_undecidable_of_rawBoundaryConstructionObligations
    (h : FinalRawBoundaryConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the raw-boundary construction obligations.
-/
theorem domino_problem_undecidable_of_rawBoundaryConstructionObligations
    (h : FinalRawBoundaryConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the raw-boundary level-check
construction obligations.
-/
theorem encoded_domino_problem_undecidable_of_rawBoundaryLevelChecksConstructionObligations
    (h : FinalRawBoundaryLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the raw-boundary level-check construction
obligations.
-/
theorem domino_problem_undecidable_of_rawBoundaryLevelChecksConstructionObligations
    (h : FinalRawBoundaryLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the raw-boundary level-certificate
construction obligations.
-/
theorem encoded_domino_problem_undecidable_of_rawBoundaryLevelCertificatesConstructionObligations
    (h : FinalRawBoundaryLevelCertificatesConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the raw-boundary level-certificate construction
obligations.
-/
theorem domino_problem_undecidable_of_rawBoundaryLevelCertificatesConstructionObligations
    (h : FinalRawBoundaryLevelCertificatesConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and packaged source decoder.
-/
theorem encoded_domino_problem_undecidable_of_scaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourcePackage scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and packaged source decoder.
-/
theorem domino_problem_undecidable_of_scaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourcePackage scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and the primitive recursive generated
position-code accumulator step.
-/
theorem encoded_domino_problem_undecidable_of_scaffoldAndSourceDecoderStep
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourceDecoderStep scaffold hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and the primitive recursive generated
position-code accumulator step.
-/
theorem domino_problem_undecidable_of_scaffoldAndSourceDecoderStep
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourceDecoderStep scaffold hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and the global primitive recursive
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_scaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and the global primitive recursive
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_scaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchDataSource
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataSource scaffold source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchDataSource
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataSource scaffold source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatches
      checkedStacks patches sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatches
      checkedStacks patches sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks and
compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks and compatible
Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16Source
      checkedStacks fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure 16
macro-squares, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16Source
      checkedStacks fig16 source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and
compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
proof-facing compatible Figure 16 level checks.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16
    originZeroWindows fig16 sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and
proof-facing compatible Figure 16 level checks.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16
    originZeroWindows fig16 sourceRows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
compatible Figure 16 macro-squares, and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16Source
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16Source
      originZeroWindows fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16Source
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16Source
      originZeroWindows fig16 source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks and row-major
checked compatible Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelData
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks and row-major checked
compatible Figure 16 level data.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelData
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, row-major
checked compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataPackage
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataPackage
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataPackage
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataPackage
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, row-major
checked compatible Figure 16 level data, and the primitive recursive generated
position-code accumulator step.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataDecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataDecoderStep
      checkedStacks fig16 hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the primitive recursive generated
position-code accumulator step.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataDecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataDecoderStep
      checkedStacks fig16 hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, row-major
checked compatible Figure 16 level data, and the global primitive recursive
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the global primitive recursive
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, row-major
checked compatible Figure 16 level data, and generated-position source
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSource
      checkedStacks fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSource
      checkedStacks fig16 source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
row-major checked compatible Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelData
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and row-major
checked compatible Figure 16 level data.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelData
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
row-major checked raw-boundary Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndRawBoundaryCheckedLevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryCheckedLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryCheckedLevelData
      originZeroWindows rawBoundary sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and row-major
checked raw-boundary Figure 16 level data.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndRawBoundaryCheckedLevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryCheckedLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryCheckedLevelData
      originZeroWindows rawBoundary sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
raw-boundary Figure 16 level checks.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndRawBoundaryLevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryLevelChecks
      originZeroWindows rawBoundary sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and
raw-boundary Figure 16 level checks.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndRawBoundaryLevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryLevelChecks
      originZeroWindows rawBoundary sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
raw-boundary Figure 16 level certificates.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndRawBoundaryLevelCertificates
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelCertificates)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryLevelCertificates
      originZeroWindows rawBoundary sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and
raw-boundary Figure 16 level certificates.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndRawBoundaryLevelCertificates
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (rawBoundary : TM0FoldedReduction.Figure18CanonicalRawBoundaryLevelCertificates)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndRawBoundaryLevelCertificates
      originZeroWindows rawBoundary sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
row-major checked compatible Figure 16 level data, and the packaged generated
interior position-code decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataPackage
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataPackage
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
row-major checked compatible Figure 16 level data, and the primitive recursive
generated position-code accumulator step.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataDecoderStep
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataDecoderStep
      originZeroWindows fig16 hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the primitive recursive generated
position-code accumulator step.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataDecoderStep
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hstep : Primrec (fun p : Code × TM0FoldedReduction.SourceSearchCodeDecoderState =>
      TM0FoldedReduction.sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataDecoderStep
      originZeroWindows fig16 hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
row-major checked compatible Figure 16 level data, and the global primitive
recursive position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
      originZeroWindows fig16 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the global primitive recursive
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
      originZeroWindows fig16 hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
row-major checked compatible Figure 16 level data, and generated-position
source obligations.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
      originZeroWindows fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and generated-position source
obligations.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
      originZeroWindows fig16 source)

end LeanWang

end
