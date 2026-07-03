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
Legacy over-strong proof obligations for the checked Figure 16 level-data route.

These were previously used as the preferred construction route:
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
Legacy source-facing variant of the checked Figure 16 level-data route.

Compared with `FinalConstructionObligations`, this asks for primitive
recursiveness of the generated position-code decoder step directly, instead of
the stronger interior-row generator package.
-/
structure FinalDecoderStepConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Legacy source-facing checked Figure 16 level-data variant using the global
position-code label-index decoder.  The decoder step is derived uniformly from
this label-index decoder.
-/
structure FinalGlobalPositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Legacy source-facing checked Figure 16 level-data variant using the
source-specialized position-code label-index decoder.

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
Finite-check-facing checked-stack route with proof-facing compatible Figure 16
level checks.

This is the structured version of the live checked-stack compatible-Figure-16
route.  Unlike `FinalCheckedConstructionObligations`, it uses the macro-square
level-check predicate instead of the refuted row-major level-data predicate.
-/
structure FinalCheckedLevelChecksConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Finite-check-facing checked-stack level-check route with the narrower
decoder-step source target.
-/
structure FinalCheckedLevelChecksDecoderStepConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Finite-check-facing checked-stack level-check route with the global
position-code label-index source target.
-/
structure FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Finite-check-facing checked-stack level-check route with the source-specialized
position-code label-index source target.
-/
structure FinalCheckedLevelChecksSourcePositionCodeConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Concrete origin-zero Figure 13 finite-box scaffold target for the first audited
L2 candidate.

This is one step closer to the human transcription data than
`FinalOriginZeroTranslatedBoxData`: origin-zero recognizability plus finite raw
Figure 13 boxes build the translated active-corner boxes by the existing
Robinson compactness/positive-box route.
-/
abbrev FinalOriginZeroFig13BoxData : Prop :=
  TM0FoldedReduction.L2C1OriginZeroFig13BoxData

/--
Concrete checked-stack Figure 13 finite-box scaffold target for the first
audited L2 candidate.

Compared with `FinalOriginZeroFig13BoxData`, this asks for the finite checked
origin-zero stack certificate rather than the semantic origin-zero window
invariant directly.
-/
abbrev FinalCheckedSignalTowerFig13BoxData : Prop :=
  TM0FoldedReduction.L2C1CheckedSignalTowerFig13BoxData

set_option linter.style.longLine false in
/--
Origin-zero recognizability plus finite Figure 13 boxes instantiate the
origin-zero translated-box scaffold target.
-/
def finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData
    (data : FinalOriginZeroFig13BoxData) :
    FinalOriginZeroTranslatedBoxData :=
  NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations.ofL2C1Figure18ScaffoldDataPositiveFig13TileableBoxes
    data.originZeroWindows data.fig13Boxes

set_option linter.style.longLine false in
/--
Checked origin-zero stacks plus finite Figure 13 boxes instantiate the
origin-zero Figure 13 finite-box scaffold target.
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

/--
The row-major checked Figure 16 level-data surface is inconsistent.  Keep this
fact close to the final theorem surfaces so the legacy obligation packages
below remain visibly diagnostic rather than proof targets.
-/
theorem not_figure18CanonicalCheckedRecognizedCompatibleLevelData :
    ¬ TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData := by
  simpa [TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData] using
    not_hasCanonicalCheckedFigure16RecognizedCompatibleLevelData

/-- The legacy row-source construction package is diagnostic only. -/
theorem not_finalConstructionObligations :
    ¬ FinalConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy decoder-step construction package is diagnostic only. -/
theorem not_finalDecoderStepConstructionObligations :
    ¬ FinalDecoderStepConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy global-label-index construction package is diagnostic only. -/
theorem not_finalGlobalPositionCodeConstructionObligations :
    ¬ FinalGlobalPositionCodeConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy source-label-index construction package is diagnostic only. -/
theorem not_finalSourcePositionCodeConstructionObligations :
    ¬ FinalSourcePositionCodeConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy checked row-source construction package is diagnostic only. -/
theorem not_finalCheckedConstructionObligations :
    ¬ FinalCheckedConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy checked decoder-step construction package is diagnostic only. -/
theorem not_finalCheckedDecoderStepConstructionObligations :
    ¬ FinalCheckedDecoderStepConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy checked global-label-index construction package is diagnostic only. -/
theorem not_finalCheckedGlobalPositionCodeConstructionObligations :
    ¬ FinalCheckedGlobalPositionCodeConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy checked source-label-index construction package is diagnostic only. -/
theorem not_finalCheckedSourcePositionCodeConstructionObligations :
    ¬ FinalCheckedSourcePositionCodeConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy free-site row-source construction package is diagnostic only. -/
theorem not_finalFreeSiteRectConstructionObligations :
    ¬ FinalFreeSiteRectConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy free-site decoder-step construction package is diagnostic only. -/
theorem not_finalFreeSiteRectDecoderStepConstructionObligations :
    ¬ FinalFreeSiteRectDecoderStepConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy free-site global-label-index construction package is diagnostic only. -/
theorem not_finalFreeSiteRectGlobalPositionCodeConstructionObligations :
    ¬ FinalFreeSiteRectGlobalPositionCodeConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

/-- The legacy free-site source-label-index construction package is diagnostic only. -/
theorem not_finalFreeSiteRectSourcePositionCodeConstructionObligations :
    ¬ FinalFreeSiteRectSourcePositionCodeConstructionObligations := by
  intro h
  exact not_figure18CanonicalCheckedRecognizedCompatibleLevelData h.fig16

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
  ofOriginZeroTranslatedBoxSource
    (finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData scaffold)
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
  ofOriginZeroTranslatedBox
    (finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData scaffold)
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
  ofOriginZeroTranslatedBoxDecoderStep
    (finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData scaffold)
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
  ofOriginZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
    (finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData scaffold)
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
  ofOriginZeroTranslatedBoxSourcePositionCodeLabelIndexFrom
    (finalOriginZeroTranslatedBoxDataOfOriginZeroFig13BoxData scaffold)
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
Build the final inputs from checked origin-zero stacks, compatible Figure 16
macro-squares, and the primitive recursive generated position-code accumulator
step.
-/
def ofCheckedStacksAndCompatibleFig16DecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataDecoderStep
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      checkedStacks fig16)
    hstep

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, compatible Figure 16
macro-squares, and the global primitive recursive position-code label-index
decoder.
-/
def ofCheckedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      checkedStacks fig16)
    hindex

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, compatible Figure 16
macro-squares, and the source-specialized primitive recursive position-code
label-index decoder.
-/
def ofCheckedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      checkedStacks fig16)
    hindex

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

set_option linter.style.longLine false in
/--
Project the legacy row-major checked Figure 16 level-data package to the live
checked-stack level-check decoder-step package.
-/
def toCheckedLevelChecksDecoderStepConstructionObligations
    (h : FinalCheckedDecoderStepConstructionObligations) :
    FinalCheckedLevelChecksDecoderStepConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 :=
    TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16
  decoderStep := h.decoderStep

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
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16DecoderStep
    h.checkedStacks
    (TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16)
    h.decoderStep

end FinalCheckedDecoderStepConstructionObligations

namespace FinalCheckedGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project the legacy row-major checked Figure 16 level-data package to the live
checked-stack level-check global-label-index package.
-/
def toCheckedLevelChecksGlobalPositionCodeConstructionObligations
    (h : FinalCheckedGlobalPositionCodeConstructionObligations) :
    FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 :=
    TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16
  labelIndex := h.labelIndex

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
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
    h.checkedStacks
    (TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16)
    h.labelIndex

end FinalCheckedGlobalPositionCodeConstructionObligations

namespace FinalCheckedSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project the legacy row-major checked Figure 16 level-data package to the live
checked-stack level-check source-label-index package.
-/
def toCheckedLevelChecksSourcePositionCodeConstructionObligations
    (h : FinalCheckedSourcePositionCodeConstructionObligations) :
    FinalCheckedLevelChecksSourcePositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 :=
    TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16
  labelIndex := h.labelIndex

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
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
    h.checkedStacks
    (TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16)
    h.labelIndex

end FinalCheckedSourcePositionCodeConstructionObligations

namespace FinalCheckedLevelChecksConstructionObligations

set_option linter.style.longLine false in
/--
Convert the checked-stack level-check row-source package into the concrete
checked-stack/layer-patch row-source package.
-/
def toCheckedStackLayerPatchConstructionObligations
    (h : FinalCheckedLevelChecksConstructionObligations) :
    FinalCheckedStackLayerPatchConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.fig16
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the checked-stack level-check row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedLevelChecksConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16
    h.checkedStacks h.fig16 h.sourceRows

end FinalCheckedLevelChecksConstructionObligations

namespace FinalCheckedLevelChecksDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the checked-stack level-check decoder-step package into the concrete
checked-stack/layer-patch decoder-step package.
-/
def toCheckedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalCheckedLevelChecksDecoderStepConstructionObligations) :
    FinalCheckedStackLayerPatchDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.fig16
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Convert the checked-stack level-check decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedLevelChecksDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16DecoderStep
    h.checkedStacks h.fig16 h.decoderStep

end FinalCheckedLevelChecksDecoderStepConstructionObligations

namespace FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the checked-stack level-check global-label-index package into the
concrete checked-stack/layer-patch global-label-index package.
-/
def toCheckedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Forget the global decoder target to the source-specialized decoder target used
by the current final route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalCheckedLevelChecksSourcePositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 := h.fig16
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the checked-stack level-check global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
    h.checkedStacks h.fig16 h.labelIndex

end FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations

namespace FinalCheckedLevelChecksSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the checked-stack level-check source-label-index package into the
concrete checked-stack/layer-patch source-label-index package.
-/
def toCheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksSourcePositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.fig16
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the checked-stack level-check source-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedLevelChecksSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
    h.checkedStacks h.fig16 h.labelIndex

end FinalCheckedLevelChecksSourcePositionCodeConstructionObligations

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

namespace FinalCheckedConstructionObligations

set_option linter.style.longLine false in
/--
Project the legacy row-major checked Figure 16 level-data package to the live
checked-stack level-check row-source package.
-/
def toCheckedLevelChecksConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    FinalCheckedLevelChecksConstructionObligations where
  checkedStacks := h.checkedStacks
  fig16 :=
    TM0FoldedReduction.canonicalCheckedRecognizedCompatibleLevelChecks_of_checkedLevelData
      h.fig16
  sourceRows := h.sourceRows

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
  h.toCheckedLevelChecksConstructionObligations.toFinalReductionInputs

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

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite checked stacks, proof-facing
compatible Figure 16 level checks, and row-source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedLevelChecksConstructionObligations
    (h : FinalCheckedLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite checked stacks, proof-facing compatible
Figure 16 level checks, and row-source obligations.
-/
theorem domino_problem_undecidable_of_checkedLevelChecksConstructionObligations
    (h : FinalCheckedLevelChecksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite checked stacks, proof-facing
compatible Figure 16 level checks, and decoder-step obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedLevelChecksDecoderStepConstructionObligations
    (h : FinalCheckedLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite checked stacks, proof-facing compatible
Figure 16 level checks, and decoder-step obligations.
-/
theorem domino_problem_undecidable_of_checkedLevelChecksDecoderStepConstructionObligations
    (h : FinalCheckedLevelChecksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite checked stacks, proof-facing
compatible Figure 16 level checks, and global-label-index obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedLevelChecksGlobalPositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite checked stacks, proof-facing compatible
Figure 16 level checks, and global-label-index obligations.
-/
theorem domino_problem_undecidable_of_checkedLevelChecksGlobalPositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite checked stacks, proof-facing
compatible Figure 16 level checks, and source-specialized label-index
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedLevelChecksSourcePositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite checked stacks, proof-facing compatible
Figure 16 level checks, and source-specialized label-index obligations.
-/
theorem domino_problem_undecidable_of_checkedLevelChecksSourcePositionCodeConstructionObligations
    (h : FinalCheckedLevelChecksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

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
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and the generated position-code decoder-step target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16DecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16DecoderStep
      checkedStacks fig16 hstep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and the generated position-code decoder-step target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16DecoderStep
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16DecoderStep
      checkedStacks fig16 hstep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and the global position-code label-index target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and the global position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16GlobalPositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and the source-specialized position-code label-index
target.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and the source-specialized position-code label-index target.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16SourcePositionCodeLabelIndexFrom
      checkedStacks fig16 hindex)

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

end LeanWang

end
