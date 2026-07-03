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
open OllingerRobinson
open OllingerRobinson.Figure18ScaffoldData
open OllingerRobinson.Figure13Layers
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
Source-specialized primitive-recursion target for the generated position-code
label-index decoder.  This is weaker than
`GlobalPositionCodeLabelIndexFromPrimrec`, because the final reduction only
needs codes of the form `NatPartrecToToPartrec.translate c`.
-/
abbrev SourcePositionCodeLabelIndexFromPrimrec : Prop :=
  TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec

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

/-- The source-specialized label-index target implies the decoder-step target. -/
theorem sourceDecoderStepPrimrec_of_sourceLabelIndex
    (h : SourcePositionCodeLabelIndexFromPrimrec) :
    SourcePositionCodeDecoderStepPrimrec :=
  TM0FoldedReduction.sourcePositionCodeDecoderStepPrimrec_of_sourcePositionCodeLabelIndexFromPrimrec
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
Preferred source-facing variant using the source-specialized position-code
label-index decoder.

Compared with `FinalGlobalPositionCodeConstructionObligations`, this is weaker
on the source side: the decoder only has to be primitive recursive after
specializing to translated `Nat.Partrec.Code` inputs.
-/
structure FinalSourcePositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Proof-facing variant with the weakest source-specialized position-code
label-index source target.
-/
structure FinalLevelChecksSourcePositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Finite-check-facing variant with the weakest source-specialized position-code
label-index source target.
-/
structure FinalCheckedSourcePositionCodeConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Lowest finite-scaffold-facing variant of the current proof frontier.

The scaffold field is the concrete checked-stack/layer-patch package for the
first audited L2 candidate.  Thus the remaining assumptions are exactly the
finite Section 7 scaffold certificate and the source-uniform global
position-code label-index decoder.
-/
structure FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Weakest source-facing variant of the current finite-scaffold proof frontier.

Compared with
`FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations`, this
asks only for the position-code label-index decoder on translated
`Nat.Partrec.Code` inputs.
-/
structure FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Paper-facing Section 7 board/free-line final obligations.

This is the currently preferred scaffold surface: the Robinson board/free-line
geometry supplies active/corner recognition, and centered positive active-corner
boxes supply the finite layer patches needed by the backward construction.  It
avoids the false raw Figure 13 macro-square diagnostic route and the over-strong
source-stack raw-boundary diagnostic route.
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
Paper-facing Section 7 board/free-line obligations with the source-specialized
position-code label-index source target.

Compared with the global-label-index variant, this asks only for primitive
recursiveness after specializing to translated `Nat.Partrec.Code` inputs.
-/
structure FinalSection7PositiveBoxSourcePositionCodeConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Free-site-rectangle Section 7 obligations with the row-source target.

This exposes Robinson's canonical free-site routing as the scaffold-facing
frontier while keeping the older row-source assumption available.
-/
structure FinalFreeSiteRectConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Free-site-rectangle Section 7 obligations with the decoder-step source target.
-/
structure FinalFreeSiteRectDecoderStepConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Free-site-rectangle Section 7 obligations with the global position-code
label-index source target.
-/
structure FinalFreeSiteRectGlobalPositionCodeConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Free-site-rectangle Section 7 obligations with proof-facing compatible
Figure 16 level checks and the row-source target.
-/
structure FinalFreeSiteRectLevelChecksConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Free-site-rectangle Section 7 obligations with proof-facing compatible
Figure 16 level checks and the decoder-step source target.
-/
structure FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Free-site-rectangle Section 7 obligations with proof-facing compatible
Figure 16 level checks and the global position-code label-index source target.
-/
structure FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Free-site-rectangle Section 7 obligations with proof-facing compatible
Figure 16 level checks and the source-specialized position-code label-index
source target.
-/
structure FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Free-site-rectangle Section 7 obligations with the source-specialized
position-code label-index source target.

This is the scaffold-facing target closest to the current Robinson route:
Section 7 supplies canonical free-site-rectangle routing, the checked Figure 16
level data supplies positive translated active boxes, and the source field is
the weakest current source-code assumption.
-/
structure FinalFreeSiteRectSourcePositionCodeConstructionObligations : Prop where
  routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Origin-zero active/corner windows plus checked compatible Figure 16 level data
produce the paper-facing Section 7 positive-box scaffold package.

The origin-zero windows supply the board/free-line active-corner invariant.
The checked Figure 16 level data supplies positive translated active-corner
boxes, which are centered to match the positive-box surface.
-/
def section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16LevelData
    originZeroWindows fig16

set_option linter.style.longLine false in
/--
Origin-zero active/corner windows plus proof-facing compatible Figure 16
level checks produce the paper-facing Section 7 positive-box scaffold package.
-/
def section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelChecks
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16LevelChecks
    originZeroWindows fig16

set_option linter.style.longLine false in
/--
Canonical free-site-rectangle routing plus checked compatible Figure 16 level
data produce the paper-facing Section 7 positive-box scaffold package.
-/
def section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
    (routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfFreeSiteRectObligations
    (TM0FoldedReduction.l2c1FreeSiteRectCanonicalCheckedCompatibleFig16LevelDataBundledObligations
      routing fig16)

set_option linter.style.longLine false in
/--
Canonical free-site-rectangle routing plus proof-facing compatible Figure 16
level checks produce the paper-facing Section 7 positive-box scaffold package.
-/
def section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelChecks
    (routing : TM0FoldedReduction.L2C1CanonicalFreeSiteRectRouting)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLinePositiveBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfFreeSiteRectRoutingCanonicalCheckedCompatibleFig16LevelChecks
    routing fig16

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
/--
Build the final inputs directly from the scaffold package and the
source-specialized position-code label-index decoder target.
-/
def ofScaffoldAndSourcePositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Build the final inputs directly from the scaffold package and the packaged
generated interior position-code decoder.

This is the proof-facing source route: the package carries the row generator,
translated statement-list uniqueness, and semantic correctness against the
Mathlib TM0 evaluator.
-/
def ofScaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
      sourceRows)

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

set_option linter.style.longLine false in
/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate and the primitive recursive generated position-code accumulator
step.
-/
def ofCheckedStackLayerPatchDataDecoderStep
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate and the global primitive recursive position-code label-index
decoder.
-/
def ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate and the source-specialized primitive recursive position-code
label-index decoder.
-/
def ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourcePositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold)
    hindex

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
Build the final inputs from origin-zero active/corner windows, proof-facing
compatible Figure 16 level checks, and the source-specialized primitive
recursive position-code label-index decoder.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelChecksSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
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
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
      sourceRows)

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
Build the final inputs from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the source-specialized primitive recursive
position-code label-index decoder.
-/
def ofCheckedStacksAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16LevelDataSource
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
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
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the source-specialized primitive
recursive position-code label-index decoder.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      hindex)

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
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
      sourceRows)

end FinalReductionInputs

namespace FinalDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 decoder-step package into the
paper-facing Section 7 positive-box decoder-step package.
-/
def toSection7PositiveBoxDecoderStepConstructionObligations
    (h : FinalDecoderStepConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelData
      h.originZeroWindows h.fig16
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 decoder-step package into the
free-site-rectangle decoder-step package.
-/
def toFreeSiteRectDecoderStepConstructionObligations
    (h : FinalDecoderStepConstructionObligations) :
    FinalFreeSiteRectDecoderStepConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  decoderStep := h.decoderStep

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
/--
Forget the global decoder target to the source-specialized decoder target used
by the narrowed source-facing final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    FinalSourcePositionCodeConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 := h.fig16
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 global-label-index package into the
paper-facing Section 7 positive-box global-label-index package.
-/
def toSection7PositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelData
      h.originZeroWindows h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 global-label-index package into the
free-site-rectangle global-label-index package.
-/
def toFreeSiteRectGlobalPositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    FinalFreeSiteRectGlobalPositionCodeConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label-index final obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    h.originZeroWindows h.fig16 h.labelIndex

end FinalGlobalPositionCodeConstructionObligations

namespace FinalSourcePositionCodeConstructionObligations

/--
Convert the source-specialized label-index final obligation package into the
decoder-step obligation package.
-/
def toDecoderStepConstructionObligations
    (h : FinalSourcePositionCodeConstructionObligations) :
    FinalDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 := h.fig16
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 source-specialized package into the
paper-facing Section 7 positive-box package.

The origin-zero windows supply the board/free-line active-corner invariant,
while the checked Figure 16 level data supplies positive translated boxes,
which are centered to match the Section 7 positive-box surface.
-/
def toSection7PositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalSourcePositionCodeConstructionObligations) :
    FinalSection7PositiveBoxSourcePositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelData
      h.originZeroWindows h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 source-specialized package into the
free-site-rectangle source-specialized package.
-/
def toFreeSiteRectSourcePositionCodeConstructionObligations
    (h : FinalSourcePositionCodeConstructionObligations) :
    FinalFreeSiteRectSourcePositionCodeConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the source-specialized label-index final obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    h.originZeroWindows h.fig16 h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from origin-zero windows, checked Figure 16 level data, and source-specialized label-index data. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  let hfree := h.toFreeSiteRectSourcePositionCodeConstructionObligations
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
      (section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
        hfree.routing hfree.fig16)
      hfree.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from origin-zero windows, checked Figure 16 level data, and source-specialized label-index data. -/
theorem domino_problem_undecidable
    (h : FinalSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  let hfree := h.toFreeSiteRectSourcePositionCodeConstructionObligations
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
      (section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
        hfree.routing hfree.fig16)
      hfree.labelIndex

end FinalSourcePositionCodeConstructionObligations

namespace FinalConstructionObligations

/--
Convert the older interior-row final obligation package into the
source-specialized label-index package.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalConstructionObligations) :
    FinalSourcePositionCodeConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 := h.fig16
  labelIndex :=
    TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
      h.sourceRows

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 row-source package into the
paper-facing Section 7 positive-box row-source package.
-/
def toSection7PositiveBoxConstructionObligations
    (h : FinalConstructionObligations) :
    FinalSection7PositiveBoxConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelData
      h.originZeroWindows h.fig16
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Convert the origin-zero/checked-Figure-16 row-source package into the
free-site-rectangle row-source package.
-/
def toFreeSiteRectConstructionObligations
    (h : FinalConstructionObligations) :
    FinalFreeSiteRectConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  sourceRows := h.sourceRows

/-- Convert the preferred final obligation package into the low-level endpoint. -/
def toFinalReductionInputs
    (h : FinalConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelData
    h.originZeroWindows h.fig16 h.sourceRows

end FinalConstructionObligations

namespace FinalLevelChecksDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check decoder-step package
into the free-site-rectangle level-check decoder-step package.
-/
def toFreeSiteRectLevelChecksDecoderStepConstructionObligations
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check decoder-step package
into the paper-facing Section 7 positive-box decoder-step package.
-/
def toSection7PositiveBoxDecoderStepConstructionObligations
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelChecks
      h.originZeroWindows h.fig16
  decoderStep := h.decoderStep

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
/--
Forget the global decoder target to the source-specialized level-check package.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalLevelChecksSourcePositionCodeConstructionObligations where
  originZeroWindows := h.originZeroWindows
  fig16 := h.fig16
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check global-label-index
package into the free-site-rectangle level-check global-label-index package.
-/
def toFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check global-label-index
package into the paper-facing Section 7 positive-box global-label-index package.
-/
def toSection7PositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelChecks
      h.originZeroWindows h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the level-check global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    h.originZeroWindows h.fig16 h.labelIndex

end FinalLevelChecksGlobalPositionCodeConstructionObligations

namespace FinalLevelChecksSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check source-specialized
package into the free-site-rectangle level-check source-specialized package.
-/
def toFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations
    (h : FinalLevelChecksSourcePositionCodeConstructionObligations) :
    FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check source-specialized
package into the paper-facing Section 7 positive-box source-specialized package.
-/
def toSection7PositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalLevelChecksSourcePositionCodeConstructionObligations) :
    FinalSection7PositiveBoxSourcePositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelChecks
      h.originZeroWindows h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the level-check source-specialized package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalLevelChecksSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    h.originZeroWindows h.fig16 h.labelIndex

end FinalLevelChecksSourcePositionCodeConstructionObligations

namespace FinalLevelChecksConstructionObligations

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check row-source package
into the free-site-rectangle level-check row-source package.
-/
def toFreeSiteRectLevelChecksConstructionObligations
    (h : FinalLevelChecksConstructionObligations) :
    FinalFreeSiteRectLevelChecksConstructionObligations where
  routing :=
    TM0FoldedReduction.l2c1CanonicalFreeSiteRectRoutingOfOriginZeroWindows
      h.originZeroWindows
  fig16 := h.fig16
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Convert the origin-zero/compatible-Figure-16 level-check row-source package
into the paper-facing Section 7 positive-box row-source package.
-/
def toSection7PositiveBoxConstructionObligations
    (h : FinalLevelChecksConstructionObligations) :
    FinalSection7PositiveBoxConstructionObligations where
  section7 :=
    section7PositiveBoxOfOriginZeroWindowsAndCompatibleFig16LevelChecks
      h.originZeroWindows h.fig16
  sourceRows := h.sourceRows

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
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    FinalCheckedSourcePositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 := h.fig16
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the finite-check-facing global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataGlobalPositionCodeLabelIndexFrom
    h.checkedStacks h.fig16 h.labelIndex

end FinalCheckedGlobalPositionCodeConstructionObligations

namespace FinalCheckedSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the finite-check-facing source-label-index package into the
window-based source-label-index obligation package.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedSourcePositionCodeConstructionObligations) :
    FinalSourcePositionCodeConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  fig16 := h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the finite-check-facing source-label-index package into the concrete
checked-stack/layer-patch source-label-index package.
-/
def toCheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalCheckedSourcePositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16LevelData
      h.checkedStacks h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the finite-check-facing source-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    h.checkedStacks h.fig16 h.labelIndex

end FinalCheckedSourcePositionCodeConstructionObligations

namespace FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Convert the concrete checked-stack/layer-patch global-label-index package into
the endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations

namespace FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the concrete checked-stack/layer-patch source-label-index package into
the endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations

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

set_option linter.style.longLine false in
/--
Convert the finite-check-facing row-source package into the source-specialized
label-index package.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    FinalSourcePositionCodeConstructionObligations :=
  h.toConstructionObligations.toSourcePositionCodeConstructionObligations

/-- Convert the finite-check-facing obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelData
    h.checkedStacks h.fig16 h.sourceRows

end FinalCheckedConstructionObligations

namespace FinalSection7PositiveBoxDecoderStepConstructionObligations

/-- Convert the paper-facing Section 7 decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7PositiveBoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
      h.section7)
    h.decoderStep

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 decoder-step package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7PositiveBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    h.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 decoder-step package. -/
theorem domino_problem_undecidable
    (h : FinalSection7PositiveBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    h.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

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

/--
Forget the global decoder target to the source-specialized decoder target used
by the narrowed source-facing Section 7 route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxSourcePositionCodeConstructionObligations where
  section7 := h.section7
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the paper-facing Section 7 global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
      h.section7)
    h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 global-label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 global-label-index package. -/
theorem domino_problem_undecidable
    (h : FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

end FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations

namespace FinalSection7PositiveBoxSourcePositionCodeConstructionObligations

/--
Convert the paper-facing Section 7 source-specialized label-index package into
the decoder-step package.
-/
def toDecoderStepConstructionObligations
    (h : FinalSection7PositiveBoxSourcePositionCodeConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 := h.section7
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the paper-facing Section 7 source-specialized label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7PositiveBoxSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourcePositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
      h.section7)
    h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 source-specialized label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7PositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
      h.section7 h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 source-specialized label-index package. -/
theorem domino_problem_undecidable
    (h : FinalSection7PositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
      h.section7 h.labelIndex

end FinalSection7PositiveBoxSourcePositionCodeConstructionObligations

namespace FinalFreeSiteRectConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle row-source package into the paper-facing
Section 7 positive-box row-source package.
-/
def toSection7PositiveBoxConstructionObligations
    (h : FinalFreeSiteRectConstructionObligations) :
    FinalSection7PositiveBoxConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
      h.routing h.fig16
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle row-source package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    h.toSection7PositiveBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle row-source package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    h.toSection7PositiveBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFreeSiteRectConstructionObligations

namespace FinalFreeSiteRectDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle decoder-step package into the paper-facing
Section 7 positive-box decoder-step package.
-/
def toSection7PositiveBoxDecoderStepConstructionObligations
    (h : FinalFreeSiteRectDecoderStepConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
      h.routing h.fig16
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle decoder-step package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    h.toSection7PositiveBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle decoder-step package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    h.toSection7PositiveBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFreeSiteRectDecoderStepConstructionObligations

namespace FinalFreeSiteRectGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle global-label-index package into the
paper-facing Section 7 positive-box global-label-index package.
-/
def toSection7PositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalFreeSiteRectGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
      h.routing h.fig16
  labelIndex := h.labelIndex

/--
Forget the global decoder target to the free-site source-specialized target.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectGlobalPositionCodeConstructionObligations) :
    FinalFreeSiteRectSourcePositionCodeConstructionObligations where
  routing := h.routing
  fig16 := h.fig16
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle global-label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.toSection7PositiveBoxGlobalPositionCodeConstructionObligations.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle global-label-index package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.toSection7PositiveBoxGlobalPositionCodeConstructionObligations.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

end FinalFreeSiteRectGlobalPositionCodeConstructionObligations

namespace FinalFreeSiteRectLevelChecksConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle level-check row-source package into the
paper-facing Section 7 positive-box row-source package.
-/
def toSection7PositiveBoxConstructionObligations
    (h : FinalFreeSiteRectLevelChecksConstructionObligations) :
    FinalSection7PositiveBoxConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelChecks
      h.routing h.fig16
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle level-check row-source package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    h.toSection7PositiveBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle level-check row-source package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
    h.toSection7PositiveBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFreeSiteRectLevelChecksConstructionObligations

namespace FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle level-check decoder-step package into the
paper-facing Section 7 positive-box decoder-step package.
-/
def toSection7PositiveBoxDecoderStepConstructionObligations
    (h : FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelChecks
      h.routing h.fig16
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle level-check decoder-step package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    h.toSection7PositiveBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle level-check decoder-step package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
    h.toSection7PositiveBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations

namespace FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle level-check global-label-index package into
the paper-facing Section 7 positive-box global-label-index package.
-/
def toSection7PositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelChecks
      h.routing h.fig16
  labelIndex := h.labelIndex

/--
Forget the global decoder target to the free-site level-check
source-specialized target.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations where
  routing := h.routing
  fig16 := h.fig16
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle level-check global-label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.toSection7PositiveBoxGlobalPositionCodeConstructionObligations.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle level-check global-label-index package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.toSection7PositiveBoxGlobalPositionCodeConstructionObligations.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

end FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations

namespace FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle level-check source-specialized package into
the paper-facing Section 7 positive-box source-specialized package.
-/
def toSection7PositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations) :
    FinalSection7PositiveBoxSourcePositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelChecks
      h.routing h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle level-check source-specialized package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.toSection7PositiveBoxSourcePositionCodeConstructionObligations.section7
    h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle level-check source-specialized package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    h.toSection7PositiveBoxSourcePositionCodeConstructionObligations.section7
    h.labelIndex

end FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations

namespace FinalFreeSiteRectSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the free-site-rectangle source-specialized package into the
paper-facing Section 7 positive-box package.
-/
def toSection7PositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectSourcePositionCodeConstructionObligations) :
    FinalSection7PositiveBoxSourcePositionCodeConstructionObligations where
  section7 :=
    section7PositiveBoxOfFreeSiteRectRoutingAndCompatibleFig16LevelData
      h.routing h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Encoded endpoint from the free-site-rectangle source-specialized package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFreeSiteRectSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toSection7PositiveBoxSourcePositionCodeConstructionObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the free-site-rectangle source-specialized package. -/
theorem domino_problem_undecidable
    (h : FinalFreeSiteRectSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toSection7PositiveBoxSourcePositionCodeConstructionObligations
    |>.domino_problem_undecidable

end FinalFreeSiteRectSourcePositionCodeConstructionObligations

namespace FinalSection7PositiveBoxConstructionObligations

set_option linter.style.longLine false in
/-- Convert the paper-facing Section 7 source-row package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7PositiveBoxConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfPositiveBoxData
      h.section7)
    h.sourceRows

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
  h.toFreeSiteRectDecoderStepConstructionObligations.encoded_domino_problem_undecidable

/--
Wang domino undecidability from the preferred decoder-step final obligations.
-/
theorem domino_problem_undecidable_of_decoderStepConstructionObligations
    (h : FinalDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toFreeSiteRectDecoderStepConstructionObligations.domino_problem_undecidable

/--
Encoded Wang domino undecidability from the preferred global-label-index final
obligations.
-/
theorem encoded_domino_problem_undecidable_of_globalPositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toFreeSiteRectGlobalPositionCodeConstructionObligations.encoded_domino_problem_undecidable

/--
Wang domino undecidability from the preferred global-label-index final
obligations.
-/
theorem domino_problem_undecidable_of_globalPositionCodeConstructionObligations
    (h : FinalGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toFreeSiteRectGlobalPositionCodeConstructionObligations.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, checked Figure 16
level data, and row-source obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectConstructionObligations
    (h : FinalFreeSiteRectConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, checked Figure 16 level
data, and row-source obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectConstructionObligations
    (h : FinalFreeSiteRectConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, checked Figure 16
level data, and decoder-step obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectDecoderStepConstructionObligations
    (h : FinalFreeSiteRectDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, checked Figure 16 level
data, and decoder-step obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectDecoderStepConstructionObligations
    (h : FinalFreeSiteRectDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, checked Figure 16
level data, and global position-code label-index obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectGlobalPositionCodeConstructionObligations
    (h : FinalFreeSiteRectGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, checked Figure 16 level
data, and global position-code label-index obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectGlobalPositionCodeConstructionObligations
    (h : FinalFreeSiteRectGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, proof-facing
compatible Figure 16 level checks, and row-source obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectLevelChecksConstructionObligations
    (h : FinalFreeSiteRectLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, proof-facing compatible
Figure 16 level checks, and row-source obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectLevelChecksConstructionObligations
    (h : FinalFreeSiteRectLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, proof-facing
compatible Figure 16 level checks, and decoder-step obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectLevelChecksDecoderStepConstructionObligations
    (h : FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, proof-facing compatible
Figure 16 level checks, and decoder-step obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectLevelChecksDecoderStepConstructionObligations
    (h : FinalFreeSiteRectLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, proof-facing
compatible Figure 16 level checks, and global-label-index obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectLevelChecksGlobalPositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, proof-facing compatible
Figure 16 level checks, and global-label-index obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectLevelChecksGlobalPositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site rectangles, proof-facing
compatible Figure 16 level checks, and source-specialized label-index
obligations.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectLevelChecksSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site rectangles, proof-facing compatible
Figure 16 level checks, and source-specialized label-index obligations.
-/
theorem domino_problem_undecidable_of_freeSiteRectLevelChecksSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero windows, checked Figure 16
level data, and the source-specialized position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_sourcePositionCodeConstructionObligations
    (h : FinalSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero windows, checked Figure 16 level
data, and the source-specialized position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_sourcePositionCodeConstructionObligations
    (h : FinalSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

/-- Encoded Wang domino undecidability from the preferred final obligations. -/
theorem encoded_domino_problem_undecidable_of_constructionObligations
    (h : FinalConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toFreeSiteRectConstructionObligations.encoded_domino_problem_undecidable

/-- Wang domino undecidability from the preferred final obligations. -/
theorem domino_problem_undecidable_of_constructionObligations
    (h : FinalConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toFreeSiteRectConstructionObligations.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksConstructionObligations
    (h : FinalLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toSection7PositiveBoxConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksConstructionObligations
    (h : FinalLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toSection7PositiveBoxConstructionObligations.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check decoder-step final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksDecoderStepConstructionObligations
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toSection7PositiveBoxDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
decoder-step final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksDecoderStepConstructionObligations
    (h : FinalLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toSection7PositiveBoxDecoderStepConstructionObligations.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check global-label-index final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksGlobalPositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toSection7PositiveBoxGlobalPositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
global-label-index final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksGlobalPositionCodeConstructionObligations
    (h : FinalLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toSection7PositiveBoxGlobalPositionCodeConstructionObligations.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from proof-facing compatible Figure 16
level-check source-specialized final obligations.
-/
theorem encoded_domino_problem_undecidable_of_levelChecksSourcePositionCodeConstructionObligations
    (h : FinalLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toSection7PositiveBoxSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from proof-facing compatible Figure 16 level-check
source-specialized final obligations.
-/
theorem domino_problem_undecidable_of_levelChecksSourcePositionCodeConstructionObligations
    (h : FinalLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toSection7PositiveBoxSourcePositionCodeConstructionObligations.domino_problem_undecidable

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
Encoded Wang domino undecidability from the finite-check-facing
source-label-index final obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedSourcePositionCodeConstructionObligations
    (h : FinalCheckedSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the finite-check-facing source-label-index
final obligations.
-/
theorem domino_problem_undecidable_of_checkedSourcePositionCodeConstructionObligations
    (h : FinalCheckedSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete checked-stack/layer-patch
scaffold package and the global primitive recursive position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete checked-stack/layer-patch scaffold
package and the global primitive recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete checked-stack/layer-patch
scaffold package and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete checked-stack/layer-patch scaffold
package and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
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
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
construction obligations.
-/
theorem domino_problem_undecidable_of_section7PositiveBoxConstructionObligations
    (h : FinalSection7PositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

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
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line source-specialized label-index construction obligations.
-/
theorem encoded_domino_problem_undecidable_of_section7PositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalSection7PositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
source-specialized label-index construction obligations.
-/
theorem domino_problem_undecidable_of_section7PositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalSection7PositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from free-site-rectangle routing, checked
Figure 16 level data, and the source-specialized label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_freeSiteRectSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from free-site-rectangle routing, checked Figure 16
level data, and the source-specialized label-index decoder.
-/
theorem domino_problem_undecidable_of_freeSiteRectSourcePositionCodeConstructionObligations
    (h : FinalFreeSiteRectSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

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
Encoded Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and the source-specialized primitive
recursive position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_scaffoldAndSourcePositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and the source-specialized primitive
recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_scaffoldAndSourcePositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourcePositionCodeLabelIndexFrom
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
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate and the generated position-code decoder-step target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchDataDecoderStep
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataDecoderStep
      scaffold hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate and the generated position-code decoder-step target.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchDataDecoderStep
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataDecoderStep
      scaffold hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate and the global position-code label-index target.
-/
theorem
    encoded_domino_problem_undecidable_of_checkedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate and the global position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate and the source-specialized position-code label-index
target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate and the source-specialized position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
      scaffold hindex)

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
proof-facing compatible Figure 16 level checks, and the source-specialized
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_levelChecksSourcePositionCodeConstructionObligations
    {
      originZeroWindows := originZeroWindows
      fig16 := fig16
      labelIndex := hindex
    }

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, proof-facing
compatible Figure 16 level checks, and the source-specialized position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_levelChecksSourcePositionCodeConstructionObligations
    {
      originZeroWindows := originZeroWindows
      fig16 := fig16
      labelIndex := hindex
    }

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
checked compatible Figure 16 level data, and the source-specialized primitive
recursive position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and the source-specialized primitive
recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
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
row-major checked compatible Figure 16 level data, and the source-specialized
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_sourceCodeCorrect
      originZeroWindows fig16 hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the source-specialized
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataSourcePositionCodeLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : TM0FoldedReduction.SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_origin_zero_compatible_fig16_level_data_sourceCodeCorrect
      originZeroWindows fig16 hindex

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
