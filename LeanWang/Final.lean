/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction
import LeanWang.OllingerRobinsonFigure13Obstructions

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
Finite-scaffold-facing checked-stack/layer-patch construction route.

The scaffold field is the concrete checked-stack/layer-patch package for the
first audited L2 candidate; the source field is the generated interior-row
primitive-recursion proof.  This route bypasses the refuted checked Figure 16
level-data interface.
-/
structure FinalCheckedStackLayerPatchConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Finite-scaffold-facing checked-stack/layer-patch route with the narrower
decoder-step source target.

This is the source-facing version closest to the current generated decoder-step
work while still avoiding the checked Figure 16 level-data interface.
-/
structure FinalCheckedStackLayerPatchDecoderStepConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Finite-scaffold-facing checked-stack/layer-patch route with the global
position-code label-index source target.

The scaffold field is the concrete checked-stack/layer-patch package for the
first audited L2 candidate.  Thus the remaining assumptions are the finite
Section 7 scaffold certificate and the source-uniform global position-code
label-index decoder.
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

set_option linter.style.longLine false in
/--
Concrete origin-zero translated-box finite scaffold target for the first
audited L2 candidate.

This is the current most direct Section 7 finite-check surface: it contains the
origin-zero recognizability, pair compatibility, and translated positive
active-corner boxes needed to build the checked-stack/layer-patch package used
by the final reduction.
-/
abbrev FinalOriginZeroTranslatedBoxData : Prop :=
  NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid

/--
Diagnostic origin-zero Figure 13 finite-box scaffold target for the first
audited L2 candidate.

This is one step closer to the human transcription data than
`FinalOriginZeroTranslatedBoxData`, but the finite raw Figure 13 box field is
now known to be impossible for the current macro-tile transcription.  The live
proof-facing target is `FinalCheckedStackLayerPatchData`.
-/
abbrev FinalOriginZeroFig13BoxData : Prop :=
  TM0FoldedReduction.L2C1OriginZeroFig13BoxData

/--
Diagnostic checked-stack Figure 13 finite-box scaffold target for the first
audited L2 candidate.

Compared with `FinalOriginZeroFig13BoxData`, this asks for the finite checked
origin-zero stack certificate rather than the semantic origin-zero window
invariant directly, but it still includes the impossible raw Figure 13 finite
box field.
-/
abbrev FinalCheckedSignalTowerFig13BoxData : Prop :=
  TM0FoldedReduction.L2C1CheckedSignalTowerFig13BoxData

/--
The origin-zero Figure 13 finite-box final package is diagnostic only: its raw
Figure 13 box field is refuted by the finite Figure 13 obstruction.
-/
theorem not_finalOriginZeroFig13BoxData : ¬ FinalOriginZeroFig13BoxData := by
  intro data
  exact TM0FoldedReduction.not_tileableBoxes_fig13Tiles data.fig13Boxes

/--
The checked-stack Figure 13 finite-box final package is also diagnostic only:
it contains the same impossible raw Figure 13 box field.
-/
theorem not_finalCheckedSignalTowerFig13BoxData :
    ¬ FinalCheckedSignalTowerFig13BoxData := by
  intro data
  exact TM0FoldedReduction.not_tileableBoxes_fig13Tiles data.fig13Boxes

set_option linter.style.longLine false in
/--
Diagnostic bridge: origin-zero recognizability plus finite Figure 13 boxes
would instantiate the origin-zero translated-box scaffold target, but the
premise is refuted by `not_finalOriginZeroFig13BoxData`.
-/
def finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData
    (data : FinalOriginZeroFig13BoxData) :
    FinalOriginZeroTranslatedBoxData :=
  NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations.ofL2C1Figure18ScaffoldDataPositiveFig13TileableBoxes
    data.originZeroWindows data.fig13Boxes

set_option linter.style.longLine false in
/--
Diagnostic bridge: origin-zero recognizability plus finite Figure 13 boxes
would instantiate the checked-stack/layer-patch finite scaffold target, but the
premise is refuted by `not_finalOriginZeroFig13BoxData`.
-/
def finalCheckedStackLayerPatchDataOfOriginZeroFig13BoxData
    (data : FinalOriginZeroFig13BoxData) :
    TM0FoldedReduction.L2C1CheckedStackLayerPatchData :=
  TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroFig13BoxData
    data

set_option linter.style.longLine false in
/--
Diagnostic bridge: checked origin-zero stacks plus finite Figure 13 boxes would
instantiate the origin-zero Figure 13 finite-box scaffold target, but the
premise is refuted by `not_finalCheckedSignalTowerFig13BoxData`.
-/
def finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData
    (data : FinalCheckedSignalTowerFig13BoxData) :
    FinalOriginZeroFig13BoxData :=
  TM0FoldedReduction.l2c1OriginZeroFig13BoxDataOfCheckedStacks
    data.checkedStacks data.fig13Boxes

set_option linter.style.longLine false in
/--
Checked origin-zero stacks plus canonical checked Figure 13 macro-square
recognition instantiate the checked-stack Figure 13 finite-box scaffold target.

This is the direct paper-facing route from the checked Figure 16-recognized
Robinson-board macro-square invariant to the finite Figure 13 boxes used by
the final reduction.
-/
def finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares) :
    FinalCheckedSignalTowerFig13BoxData where
  checkedStacks := checkedStacks
  fig13Boxes :=
    TM0FoldedReduction.tileableBoxes_fig13Tiles_of_canonicalCheckedRecognizedMacroSquares
      fig13

/--
Origin-zero translated-box construction route with the generated interior-row
source target.
-/
structure FinalOriginZeroTranslatedBoxConstructionObligations : Prop where
  scaffold : FinalOriginZeroTranslatedBoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Origin-zero translated-box construction route with the generated decoder-step
source target.
-/
structure FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations : Prop where
  scaffold : FinalOriginZeroTranslatedBoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Origin-zero translated-box construction route with the global position-code
label-index source target.
-/
structure FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations : Prop where
  scaffold : FinalOriginZeroTranslatedBoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Origin-zero translated-box construction route with the source-specialized
position-code label-index source target.
-/
structure FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations : Prop where
  scaffold : FinalOriginZeroTranslatedBoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Origin-zero Figure 13 finite-box construction route with the generated
interior-row source target.
-/
structure FinalOriginZeroFig13BoxConstructionObligations : Prop where
  scaffold : FinalOriginZeroFig13BoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Origin-zero Figure 13 finite-box construction route with the generated
decoder-step source target.
-/
structure FinalOriginZeroFig13BoxDecoderStepConstructionObligations : Prop where
  scaffold : FinalOriginZeroFig13BoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Origin-zero Figure 13 finite-box construction route with the global
position-code label-index source target.
-/
structure FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations : Prop where
  scaffold : FinalOriginZeroFig13BoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Origin-zero Figure 13 finite-box construction route with the source-specialized
position-code label-index source target.
-/
structure FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations : Prop where
  scaffold : FinalOriginZeroFig13BoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Checked-stack Figure 13 finite-box construction route with the generated
interior-row source target.
-/
structure FinalCheckedSignalTowerFig13BoxConstructionObligations : Prop where
  scaffold : FinalCheckedSignalTowerFig13BoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Checked-stack Figure 13 finite-box construction route with the generated
decoder-step source target.
-/
structure FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations : Prop where
  scaffold : FinalCheckedSignalTowerFig13BoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Checked-stack Figure 13 finite-box construction route with the global
position-code label-index source target.
-/
structure FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations : Prop where
  scaffold : FinalCheckedSignalTowerFig13BoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Checked-stack Figure 13 finite-box construction route with the
source-specialized position-code label-index source target.
-/
structure FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations : Prop where
  scaffold : FinalCheckedSignalTowerFig13BoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

/--
Checked-stack Figure 13 recognized macro-square construction route with the
generated interior-row source target.
-/
structure FinalCheckedSignalTowerRecognizedFig13ConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Checked-stack Figure 13 recognized macro-square construction route with the
generated decoder-step source target.
-/
structure FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Checked-stack Figure 13 recognized macro-square construction route with the
global position-code label-index source target.
-/
structure FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Checked-stack Figure 13 recognized macro-square construction route with the
source-specialized position-code label-index source target.
-/
structure FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares
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
The row-major checked Figure 16 level-data surface is inconsistent.  Keep this
fact close to the final theorem surfaces so the live route is clearly the
level-check interface.
-/
theorem not_figure18CanonicalCheckedRecognizedCompatibleLevelData :
    ¬ TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData := by
  simpa [TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData] using
    not_hasCanonicalCheckedFigure16RecognizedCompatibleLevelData

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

set_option linter.style.longLine false in
/--
Build the final inputs from the two split finite scaffold obligations and the
packaged generated interior position-code decoder.
-/
def ofCheckedStacksAndLayerPatchesPackage
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofScaffoldAndSourcePackage
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from the two split finite scaffold obligations and the
primitive recursive generated position-code accumulator step.
-/
def ofCheckedStacksAndLayerPatchesDecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from the two split finite scaffold obligations and the
global primitive recursive position-code label-index decoder.
-/
def ofCheckedStacksAndLayerPatchesGlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from the two split finite scaffold obligations and the
source-specialized primitive recursive position-code label-index decoder.
-/
def ofCheckedStacksAndLayerPatchesSourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourcePositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches)
    hindex

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

set_option linter.style.longLine false in
/--
Build the final inputs from the origin-zero translated-box finite scaffold
certificate and generated-position source obligations.
-/
def ofOriginZeroTranslatedBoxSource
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      scaffold)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from the origin-zero translated-box finite scaffold
certificate and generated interior position-code rows.
-/
def ofOriginZeroTranslatedBox
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchData
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      scaffold)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from the origin-zero translated-box finite scaffold
certificate and the primitive recursive generated position-code accumulator
step.
-/
def ofOriginZeroTranslatedBoxDecoderStep
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataDecoderStep
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      scaffold)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from the origin-zero translated-box finite scaffold
certificate and the global primitive recursive position-code label-index
decoder.
-/
def ofOriginZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from the origin-zero translated-box finite scaffold
certificate and the source-specialized primitive recursive position-code
label-index decoder.
-/
def ofOriginZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero recognizability plus finite Figure 13
boxes and generated-position source obligations.
-/
def ofOriginZeroFig13BoxDataSource
    (scaffold : FinalOriginZeroFig13BoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (finalCheckedStackLayerPatchDataOfOriginZeroFig13BoxData scaffold)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero recognizability plus finite Figure 13
boxes and generated interior position-code rows.
-/
def ofOriginZeroFig13BoxData
    (scaffold : FinalOriginZeroFig13BoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchData
    (finalCheckedStackLayerPatchDataOfOriginZeroFig13BoxData scaffold)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero recognizability plus finite Figure 13
boxes and the primitive recursive generated position-code accumulator step.
-/
def ofOriginZeroFig13BoxDataDecoderStep
    (scaffold : FinalOriginZeroFig13BoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataDecoderStep
    (finalCheckedStackLayerPatchDataOfOriginZeroFig13BoxData scaffold)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero recognizability plus finite Figure 13
boxes and the global primitive recursive position-code label-index decoder.
-/
def ofOriginZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroFig13BoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    (finalCheckedStackLayerPatchDataOfOriginZeroFig13BoxData scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero recognizability plus finite Figure 13
boxes and the source-specialized primitive recursive position-code label-index
decoder.
-/
def ofOriginZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroFig13BoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (finalCheckedStackLayerPatchDataOfOriginZeroFig13BoxData scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus finite Figure 13
boxes and generated-position source obligations.
-/
def ofCheckedSignalTowerFig13BoxDataSource
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofOriginZeroFig13BoxDataSource
    (finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData scaffold)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus finite Figure 13
boxes and generated interior position-code rows.
-/
def ofCheckedSignalTowerFig13BoxData
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroFig13BoxData
    (finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData scaffold)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus finite Figure 13
boxes and the primitive recursive generated position-code accumulator step.
-/
def ofCheckedSignalTowerFig13BoxDataDecoderStep
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroFig13BoxDataDecoderStep
    (finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData scaffold)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus finite Figure 13
boxes and the global primitive recursive position-code label-index decoder.
-/
def ofCheckedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus finite Figure 13
boxes and the source-specialized primitive recursive position-code label-index
decoder.
-/
def ofCheckedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
    (finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData scaffold)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and generated-position source obligations.
-/
def ofCheckedStacksAndRecognizedFig13Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedSignalTowerFig13BoxDataSource
    (finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      checkedStacks fig13)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and generated interior position-code rows.
-/
def ofCheckedStacksAndRecognizedFig13
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndRecognizedFig13Source
    checkedStacks fig13
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the primitive recursive generated
position-code accumulator step.
-/
def ofCheckedStacksAndRecognizedFig13DecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofCheckedSignalTowerFig13BoxDataDecoderStep
    (finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      checkedStacks fig13)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the global primitive recursive
position-code label-index decoder.
-/
def ofCheckedStacksAndRecognizedFig13GlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      checkedStacks fig13)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the source-specialized primitive
recursive position-code label-index decoder.
-/
def ofCheckedStacksAndRecognizedFig13SourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
    (finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      checkedStacks fig13)
    hindex


end FinalReductionInputs

namespace FinalCheckedStackLayerPatchConstructionObligations

set_option linter.style.longLine false in
/--
Convert the concrete checked-stack/layer-patch interior-row package into the
endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedStackLayerPatchConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStackLayerPatchData
    h.scaffold h.sourceRows

end FinalCheckedStackLayerPatchConstructionObligations

namespace FinalCheckedStackLayerPatchDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the concrete checked-stack/layer-patch decoder-step package into the
endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedStackLayerPatchDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStackLayerPatchDataDecoderStep
    h.scaffold h.decoderStep

end FinalCheckedStackLayerPatchDecoderStepConstructionObligations

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

namespace FinalOriginZeroTranslatedBoxConstructionObligations

set_option linter.style.longLine false in
/--
Project the origin-zero translated-box package to the checked-stack/layer-patch
package used by the older final route.
-/
def toCheckedStackLayerPatchConstructionObligations
    (h : FinalOriginZeroTranslatedBoxConstructionObligations) :
    FinalCheckedStackLayerPatchConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      h.scaffold
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the origin-zero translated-box row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroTranslatedBoxConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBox
    h.scaffold h.sourceRows

end FinalOriginZeroTranslatedBoxConstructionObligations

namespace FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the origin-zero translated-box package to the checked-stack/layer-patch
decoder-step package used by the older final route.
-/
def toCheckedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations) :
    FinalCheckedStackLayerPatchDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      h.scaffold
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Convert the origin-zero translated-box decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBoxDecoderStep
    h.scaffold h.decoderStep

end FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations

namespace FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the origin-zero translated-box package to the checked-stack/layer-patch
global-label-index package used by the older final route.
-/
def toCheckedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the origin-zero translated-box global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations

namespace FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project the origin-zero translated-box package to the checked-stack/layer-patch
source-label-index package used by the older final route.
-/
def toCheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroObligations
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the origin-zero translated-box source-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations

namespace FinalOriginZeroFig13BoxConstructionObligations

set_option linter.style.longLine false in
/--
Project origin-zero Figure 13 finite-box data to the translated-box package
used by the current final route.
-/
def toOriginZeroTranslatedBoxConstructionObligations
    (h : FinalOriginZeroFig13BoxConstructionObligations) :
    FinalOriginZeroTranslatedBoxConstructionObligations where
  scaffold := finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData h.scaffold
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the origin-zero Figure 13 finite-box row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroFig13BoxConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroFig13BoxData
    h.scaffold h.sourceRows

end FinalOriginZeroFig13BoxConstructionObligations

namespace FinalOriginZeroFig13BoxDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project origin-zero Figure 13 finite-box data to the translated-box
decoder-step package used by the current final route.
-/
def toOriginZeroTranslatedBoxDecoderStepConstructionObligations
    (h : FinalOriginZeroFig13BoxDecoderStepConstructionObligations) :
    FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations where
  scaffold := finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData h.scaffold
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Convert the origin-zero Figure 13 finite-box decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroFig13BoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroFig13BoxDataDecoderStep
    h.scaffold h.decoderStep

end FinalOriginZeroFig13BoxDecoderStepConstructionObligations

namespace FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project origin-zero Figure 13 finite-box data to the translated-box
global-label-index package used by the current final route.
-/
def toOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations where
  scaffold := finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the origin-zero Figure 13 finite-box global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations

namespace FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project origin-zero Figure 13 finite-box data to the translated-box
source-label-index package used by the current final route.
-/
def toOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold := finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the origin-zero Figure 13 finite-box source-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations

namespace FinalCheckedSignalTowerFig13BoxConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 finite-box data to the origin-zero Figure 13
finite-box package used by the current final route.
-/
def toOriginZeroFig13BoxConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxConstructionObligations) :
    FinalOriginZeroFig13BoxConstructionObligations where
  scaffold := finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData h.scaffold
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the checked-stack Figure 13 finite-box row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerFig13BoxConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedSignalTowerFig13BoxData
    h.scaffold h.sourceRows

end FinalCheckedSignalTowerFig13BoxConstructionObligations

namespace FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 finite-box data to the origin-zero Figure 13
decoder-step package used by the current final route.
-/
def toOriginZeroFig13BoxDecoderStepConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations) :
    FinalOriginZeroFig13BoxDecoderStepConstructionObligations where
  scaffold := finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData h.scaffold
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Convert the checked-stack Figure 13 finite-box decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataDecoderStep
    h.scaffold h.decoderStep

end FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations

namespace FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations) :
    FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 finite-box data to the origin-zero Figure 13
global-label-index package used by the current final route.
-/
def toOriginZeroFig13BoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations where
  scaffold := finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the checked-stack Figure 13 finite-box global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations

namespace FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 finite-box data to the origin-zero Figure 13
source-label-index package used by the current final route.
-/
def toOriginZeroFig13BoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations) :
    FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations where
  scaffold := finalOriginZeroFig13BoxDataOfCheckedSignalTowerFig13BoxData h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the checked-stack Figure 13 finite-box source-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
    h.scaffold h.labelIndex

end FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations

namespace FinalCheckedSignalTowerRecognizedFig13ConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 macro-square recognition to the finite-box
package used by the current final route.
-/
def toCheckedSignalTowerFig13BoxConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13ConstructionObligations) :
    FinalCheckedSignalTowerFig13BoxConstructionObligations where
  scaffold :=
    finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      h.checkedStacks h.fig13
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Convert the checked-stack Figure 13 macro-square row-source package into the
endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerRecognizedFig13ConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndRecognizedFig13
    h.checkedStacks h.fig13 h.sourceRows

end FinalCheckedSignalTowerRecognizedFig13ConstructionObligations

namespace FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 macro-square recognition to the finite-box
decoder-step package used by the current final route.
-/
def toCheckedSignalTowerFig13BoxDecoderStepConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations) :
    FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations where
  scaffold :=
    finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      h.checkedStacks h.fig13
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Convert the checked-stack Figure 13 macro-square decoder-step package into the
endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndRecognizedFig13DecoderStep
    h.checkedStacks h.fig13 h.decoderStep

end FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations

namespace FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations) :
    FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  fig13 := h.fig13
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 macro-square recognition to the finite-box
global-label-index package used by the current final route.
-/
def toCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations) :
    FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations where
  scaffold :=
    finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      h.checkedStacks h.fig13
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the checked-stack Figure 13 macro-square global-label-index package
into the endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndRecognizedFig13GlobalPositionCodeLabelIndexFrom
    h.checkedStacks h.fig13 h.labelIndex

end FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations

namespace FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack Figure 13 macro-square recognition to the finite-box
source-label-index package used by the current final route.
-/
def toCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations) :
    FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations where
  scaffold :=
    finalCheckedSignalTowerFig13BoxDataOfCheckedStacksRecognizedFig13
      h.checkedStacks h.fig13
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Convert the checked-stack Figure 13 macro-square source-label-index package
into the endpoint.
-/
def toFinalReductionInputs
    (h : FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndRecognizedFig13SourcePositionCodeLabelIndexFrom
    h.checkedStacks h.fig13 h.labelIndex

end FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations

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

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete checked-stack/layer-patch
scaffold package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchConstructionObligations
    (h : FinalCheckedStackLayerPatchConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete checked-stack/layer-patch scaffold
package and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchConstructionObligations
    (h : FinalCheckedStackLayerPatchConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete checked-stack/layer-patch
scaffold package and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalCheckedStackLayerPatchDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete checked-stack/layer-patch scaffold
package and the primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalCheckedStackLayerPatchDecoderStepConstructionObligations) :
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
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxConstructionObligations
    (h : FinalOriginZeroTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
package and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxConstructionObligations
    (h : FinalOriginZeroTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold package and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxDecoderStepConstructionObligations
    (h : FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
package and the primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxDecoderStepConstructionObligations
    (h : FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold package and the global primitive recursive position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
package and the global primitive recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold package and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
package and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxConstructionObligations
    (h : FinalOriginZeroFig13BoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxConstructionObligations
    (h : FinalOriginZeroFig13BoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxDecoderStepConstructionObligations
    (h : FinalOriginZeroFig13BoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and the primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxDecoderStepConstructionObligations
    (h : FinalOriginZeroFig13BoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and the global primitive recursive position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and the global primitive recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroFig13BoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxDecoderStepConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and the primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxDecoderStepConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and the global primitive recursive position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and the global primitive recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerFig13BoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13ConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13ConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13ConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13ConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and the primitive recursive
generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13DecoderStepConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the primitive recursive generated
position-code decoder step.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13DecoderStepConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13DecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and the global primitive recursive
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the global primitive recursive
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13GlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and the source-specialized
primitive recursive position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the source-specialized primitive
recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations
    (h : FinalCheckedSignalTowerRecognizedFig13SourcePositionCodeConstructionObligations) :
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
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold certificate and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxSource
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxSource scaffold source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
certificate and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxSource
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxSource scaffold source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold certificate.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBox
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBox scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
certificate.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBox
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBox scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold certificate and the generated position-code decoder-step target.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxDecoderStep
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxDecoderStep scaffold hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
certificate and the generated position-code decoder-step target.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxDecoderStep
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxDecoderStep scaffold hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold certificate and the global position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
certificate and the global position-code label-index target.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero translated-box finite
scaffold certificate and the source-specialized position-code label-index
target.
-/
theorem encoded_domino_problem_undecidable_of_originZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero translated-box finite scaffold
certificate and the source-specialized position-code label-index target.
-/
theorem domino_problem_undecidable_of_originZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability and finite
Figure 13 boxes with generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxDataSource
    (scaffold : FinalOriginZeroFig13BoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataSource scaffold source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability and finite Figure
13 boxes with generated-position source obligations.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxDataSource
    (scaffold : FinalOriginZeroFig13BoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataSource scaffold source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxData
    (scaffold : FinalOriginZeroFig13BoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxData
    (scaffold : FinalOriginZeroFig13BoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and the generated position-code decoder-step target.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxDataDecoderStep
    (scaffold : FinalOriginZeroFig13BoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataDecoderStep scaffold hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and the generated position-code decoder-step target.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxDataDecoderStep
    (scaffold : FinalOriginZeroFig13BoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataDecoderStep scaffold hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and the global position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroFig13BoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and the global position-code label-index target.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroFig13BoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognizability, finite
Figure 13 boxes, and the source-specialized position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_originZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroFig13BoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognizability, finite Figure 13
boxes, and the source-specialized position-code label-index target.
-/
theorem domino_problem_undecidable_of_originZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
    (scaffold : FinalOriginZeroFig13BoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroFig13BoxDataSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks and finite
Figure 13 boxes with generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataSource
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataSource scaffold source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks and finite Figure 13
boxes with generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataSource
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataSource scaffold source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxData
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxData
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and the generated position-code decoder-step target.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataDecoderStep
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataDecoderStep
      scaffold hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and the generated position-code decoder-step target.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataDecoderStep
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataDecoderStep
      scaffold hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and the global position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and the global position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataGlobalPositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, finite
Figure 13 boxes, and the source-specialized position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, finite Figure 13
boxes, and the source-specialized position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
    (scaffold : FinalCheckedSignalTowerFig13BoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedSignalTowerFig13BoxDataSourcePositionCodeLabelIndexFrom
      scaffold hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and generated-position source
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndRecognizedFig13Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13Source
      checkedStacks fig13 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndRecognizedFig13Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13Source
      checkedStacks fig13 source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndRecognizedFig13
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13
      checkedStacks fig13 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checkedStacksAndRecognizedFig13
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13
      checkedStacks fig13 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and the generated position-code
decoder-step target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndRecognizedFig13DecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13DecoderStep
      checkedStacks fig13 hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the generated position-code
decoder-step target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndRecognizedFig13DecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13DecoderStep
      checkedStacks fig13 hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and the global position-code
label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndRecognizedFig13GlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13GlobalPositionCodeLabelIndexFrom
      checkedStacks fig13 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the global position-code label-index
target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndRecognizedFig13GlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13GlobalPositionCodeLabelIndexFrom
      checkedStacks fig13 hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, canonical
checked Figure 13 macro-square recognition, and the source-specialized
position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndRecognizedFig13SourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13SourcePositionCodeLabelIndexFrom
      checkedStacks fig13 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, canonical checked
Figure 13 macro-square recognition, and the source-specialized position-code
label-index target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndRecognizedFig13SourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig13 : TM0FoldedReduction.Figure13CanonicalCheckedRecognizedMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndRecognizedFig13SourcePositionCodeLabelIndexFrom
      checkedStacks fig13 hindex)

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
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatchesSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesSource
      checkedStacks patches source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatchesSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesSource
      checkedStacks patches source)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations and the packaged generated interior position-code
decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatchesPackage
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesPackage
      checkedStacks patches sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations and the packaged generated interior position-code decoder.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatchesPackage
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesPackage
      checkedStacks patches sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations and the generated position-code decoder-step
target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatchesDecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesDecoderStep
      checkedStacks patches hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations and the generated position-code decoder-step target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatchesDecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesDecoderStep
      checkedStacks patches hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations and the global position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatchesGlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesGlobalPositionCodeLabelIndexFrom
      checkedStacks patches hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations and the global position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatchesGlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesGlobalPositionCodeLabelIndexFrom
      checkedStacks patches hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations and the source-specialized position-code
label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatchesSourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesSourcePositionCodeLabelIndexFrom
      checkedStacks patches hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations and the source-specialized position-code label-index
target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatchesSourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatchesSourcePositionCodeLabelIndexFrom
      checkedStacks patches hindex)


end LeanWang

end
