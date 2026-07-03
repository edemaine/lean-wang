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

set_option linter.style.longLine false in
/--
Finite-scaffold construction route one step below layer patches.

The scaffold field asks for checked origin-zero stacks plus valid translated
Figure 18 scaffold boxes.  The Section 7 layer-patch package follows from the
finite no-neighbor active-site checks already proved for the audited first L2
candidate.
-/
structure FinalCheckedStackValidTranslatedBoxConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackValidTranslatedBoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Second-candidate version of the finite checked-stack/layer-patch construction
route.

The default final theorem surface uses the first audited L2 candidate, but the
same generated-source route is available for the second candidate as an
independent scaffold audit.
-/
structure FinalL2C2CheckedStackLayerPatchConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Second-candidate finite-scaffold construction route one step below layer
patches.
-/
structure FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete nat-site indexed-window scaffold route.

This is the public final surface closest to the human-audited Figure 13 layer
transcription: it supplies raw checked active Figure 18 site specs, a checked
corner site, indexed active/corner windows, and a realization certificate for
the resulting concrete scaffold instance.
-/
structure FinalFigure13NatSitesIndexedWindowConstructionObligations where
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true
  indexedActiveWindows :
    OllingerRobinson.HasFigure18IndexedActiveCornerWindows
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable
  realizes :
    (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
      cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete Robinson indexed-box scaffold route.

This packages the current Figure 13/Figure 16 scaffold target directly: the
finite Nat-site certificate carries the checked Robinson routed free-grid stacks
and active-corner indexed boxes, while `sourceRows` carries the generated
interior position-code source reduction.
-/
structure FinalFigure13RobinsonIndexedBoxConstructionObligations where
  scaffold : NatSiteRobinsonIndexedBoxScaffoldCertificate
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete Robinson tower/indexed-box scaffold route.

This is one step below `FinalFigure13RobinsonIndexedBoxConstructionObligations`:
the scaffold side supplies the Section 7 local signal tower, generated pair
compatibility, and active-corner indexed boxes.  The existing constructor then
packages those fields as a `NatSiteRobinsonIndexedBoxScaffoldCertificate`.
-/
structure FinalFigure13RobinsonTowerIndexedBoxConstructionObligations where
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true
  scaffold :
    NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete Robinson signal-tower/translated-positive-box scaffold route.

This is the current Section 7 proof-facing surface: a coherent obstruction
signal tower plus arbitrarily large translated active-corner boxes.  It converts
through tower/indexed-box obligations before reaching the final theorem.
-/
structure FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations where
  activeSiteSpecs : List (Nat × Quadrant)
  activeSiteSpecs_valid :
    OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true
  cornerIndex : Nat
  cornerQuadrant : Quadrant
  cornerIndex_valid : decide (cornerIndex < 92) = true
  scaffold :
    NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid
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

set_option linter.style.longLine false in
/--
Concrete signal-tower/translated-positive-box scaffold target for the first
audited L2 candidate.

This is the L2-specialized version of the current Section 7 proof-facing
surface: origin-zero or checked-stack data can feed it, and it in turn packages
into the Robinson indexed-box final route.
-/
abbrev FinalL2C1SignalTowerTranslatedPositiveBoxData : Prop :=
  NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations
    l2Component1BlankCandidateActiveSiteSpecs
    l2Component1BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.southwest
    l2Component1BlankCandidateSanity.cornerIndex_valid

set_option linter.style.longLine false in
/--
Origin-zero translated-box data instantiates the L2-specialized
signal-tower/translated-positive-box target.
-/
def finalL2C1SignalTowerTranslatedPositiveBoxDataOfOriginZeroTranslatedBoxData
    (data : FinalOriginZeroTranslatedBoxData) :
    FinalL2C1SignalTowerTranslatedPositiveBoxData :=
  data.toL2C1SignalTowerTranslatedPositiveBoxObligations

set_option linter.style.longLine false in
/--
The proof-facing Section 7 translated-box package instantiates the
L2-specialized signal-tower/translated-positive-box target.
-/
def finalL2C1SignalTowerTranslatedPositiveBoxDataOfSignalTowerTranslatedBoxData
    (data : TM0FoldedReduction.L2C1SignalTowerTranslatedBoxData) :
    FinalL2C1SignalTowerTranslatedPositiveBoxData :=
  NatSiteRobinsonSignalTowerTranslatedPositiveBoxObligations.ofL2C1Figure18ScaffoldDataPositiveTranslatedBoxes
    data.signalLocalTower data.translatedBoxes

/--
Diagnostic origin-zero Figure 13 finite-box scaffold target for the first
audited L2 candidate.

This is one step closer to the human transcription data than
`FinalOriginZeroTranslatedBoxData`, but the finite raw Figure 13 box field is
now known to be impossible for the current macro-tile transcription.  The live
proof-facing target is `FinalCheckedStackLayerPatchConstructionObligations`.
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
  exact TM0FoldedReduction.not_l2c1OriginZeroFig13BoxData

/--
The checked-stack Figure 13 finite-box final package is also diagnostic only:
it contains the same impossible raw Figure 13 box field.
-/
theorem not_finalCheckedSignalTowerFig13BoxData :
    ¬ FinalCheckedSignalTowerFig13BoxData := by
  exact TM0FoldedReduction.not_l2c1CheckedSignalTowerFig13BoxData

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
L2-specialized signal-tower/translated-positive-box construction route with
generated interior-row source target.
-/
structure FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations : Prop where
  scaffold : FinalL2C1SignalTowerTranslatedPositiveBoxData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

/--
Section 7 translated-box construction route with generated interior-row source
target.
-/
structure FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations : Prop where
  scaffold : TM0FoldedReduction.L2C1SignalTowerTranslatedBoxData
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
Paper-facing Section 7 board/free-line translated-box final obligations.

This is one step below the centered positive-box route: the scaffold side gives
board/free-line active/corner recognition and translated active-corner boxes,
which the Section 7 layer converts to centered positive boxes.
-/
structure FinalSection7TranslatedBoxConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData
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

namespace FinalCheckedStackValidTranslatedBoxConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the checked-stack/layer-patch
package used by the current final route.
-/
def toCheckedStackLayerPatchConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    FinalCheckedStackLayerPatchConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  sourceRows := h.sourceRows

/-- Convert the checked-stack/valid-translated-box row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackLayerPatchConstructionObligations.toFinalReductionInputs

end FinalCheckedStackValidTranslatedBoxConstructionObligations

namespace FinalL2C2CheckedStackLayerPatchConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the second checked-stack/layer-patch finite scaffold
package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRows
    h.scaffold h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from the second checked-stack/layer-patch finite scaffold
package and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRows
    h.scaffold h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalL2C2CheckedStackLayerPatchConstructionObligations

namespace FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations

set_option linter.style.longLine false in
/--
Project second-candidate checked-stack/valid-translated-box data to the
checked-stack/layer-patch package.
-/
def toCheckedStackLayerPatchConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCheckedStackLayerPatchConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCheckedStackLayerPatchConstructionObligations.domino_problem_undecidable

end FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations

namespace FinalFigure13NatSitesIndexedWindowConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete nat-site indexed-window scaffold package and
generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure13NatSitesIndexedWindowConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_interiorRows
    h.activeSiteSpecs h.activeSiteSpecs_valid h.cornerIndex h.cornerQuadrant
    h.cornerIndex_valid h.indexedActiveWindows h.realizes h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete nat-site indexed-window scaffold package
and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure13NatSitesIndexedWindowConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_interiorRows
    h.activeSiteSpecs h.activeSiteSpecs_valid h.cornerIndex h.cornerQuadrant
    h.cornerIndex_valid h.indexedActiveWindows h.realizes h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure13NatSitesIndexedWindowConstructionObligations

namespace FinalFigure13RobinsonIndexedBoxConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete Robinson indexed-box scaffold certificate
and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure13RobinsonIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_figure18_flexible_position_source_interiorRows
    h.scaffold.flexibleInstance h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete Robinson indexed-box scaffold certificate
and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure13RobinsonIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_figure18_flexible_position_source_interiorRows
    h.scaffold.flexibleInstance h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure13RobinsonIndexedBoxConstructionObligations

namespace FinalFigure13RobinsonTowerIndexedBoxConstructionObligations

set_option linter.style.longLine false in
/--
Package tower/indexed-box obligations into the Robinson indexed-box final route.
-/
def toRobinsonIndexedBoxConstructionObligations
    (h : FinalFigure13RobinsonTowerIndexedBoxConstructionObligations) :
    FinalFigure13RobinsonIndexedBoxConstructionObligations where
  scaffold := h.scaffold.toIndexedBoxScaffoldCertificate
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from the Robinson tower/indexed-box scaffold package and
generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure13RobinsonTowerIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toRobinsonIndexedBoxConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the Robinson tower/indexed-box scaffold package and
generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure13RobinsonTowerIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toRobinsonIndexedBoxConstructionObligations.domino_problem_undecidable

end FinalFigure13RobinsonTowerIndexedBoxConstructionObligations

namespace FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations

set_option linter.style.longLine false in
/--
Package signal-tower/translated-positive-box obligations into the
tower/indexed-box final route.
-/
def toRobinsonTowerIndexedBoxConstructionObligations
    (h : FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations) :
    FinalFigure13RobinsonTowerIndexedBoxConstructionObligations where
  activeSiteSpecs := h.activeSiteSpecs
  activeSiteSpecs_valid := h.activeSiteSpecs_valid
  cornerIndex := h.cornerIndex
  cornerQuadrant := h.cornerQuadrant
  cornerIndex_valid := h.cornerIndex_valid
  scaffold := h.scaffold.toTowerIndexedBoxObligations
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from Robinson signal towers, translated positive boxes, and
generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toRobinsonTowerIndexedBoxConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from Robinson signal towers, translated positive boxes, and
generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toRobinsonTowerIndexedBoxConstructionObligations.domino_problem_undecidable

end FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations

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
Project the origin-zero translated-box package to the L2-specialized
signal-tower/translated-positive-box package.
-/
def toL2C1SignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalOriginZeroTranslatedBoxConstructionObligations) :
    FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations where
  scaffold :=
    finalL2C1SignalTowerTranslatedPositiveBoxDataOfOriginZeroTranslatedBoxData
      h.scaffold
  sourceRows := h.sourceRows

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

namespace FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations

set_option linter.style.longLine false in
/--
Project the L2-specialized signal-tower/translated-positive-box package to the
generic signal-tower final route.
-/
def toFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations) :
    FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations where
  activeSiteSpecs := l2Component1BlankCandidateActiveSiteSpecs
  activeSiteSpecs_valid := l2Component1BlankCandidateSanity.activeSiteSpecs_valid
  cornerIndex := 0
  cornerQuadrant := Quadrant.southwest
  cornerIndex_valid := l2Component1BlankCandidateSanity.cornerIndex_valid
  scaffold := h.scaffold
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from the first L2 candidate's signal-tower/translated-box
scaffold package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the first L2 candidate's signal-tower/translated-box
scaffold package and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations
    |>.domino_problem_undecidable

end FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations

namespace FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations

set_option linter.style.longLine false in
/--
Project the Section 7 translated-box data package to the L2-specialized final
signal-tower route.
-/
def toL2C1SignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations) :
    FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations where
  scaffold :=
    finalL2C1SignalTowerTranslatedPositiveBoxDataOfSignalTowerTranslatedBoxData
      h.scaffold
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from the proof-facing Section 7 translated-box package and
generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toL2C1SignalTowerTranslatedPositiveBoxConstructionObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the proof-facing Section 7 translated-box package and
generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toL2C1SignalTowerTranslatedPositiveBoxConstructionObligations
    |>.domino_problem_undecidable

end FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations

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

namespace FinalSection7TranslatedBoxConstructionObligations

set_option linter.style.longLine false in
/--
Convert the board/free-line translated-box package to the centered positive-box
package.
-/
def toPositiveBoxConstructionObligations
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    FinalSection7PositiveBoxConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfTranslatedBoxData
      h.section7
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the board/free-line translated-box row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    FinalReductionInputs :=
  h.toPositiveBoxConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from the paper-facing Section 7 board/free-line translated-box
package.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toPositiveBoxConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the paper-facing Section 7 board/free-line
translated-box package.
-/
theorem domino_problem_undecidable
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toPositiveBoxConstructionObligations.domino_problem_undecidable

end FinalSection7TranslatedBoxConstructionObligations

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
Encoded Wang domino undecidability from checked origin-zero stacks, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackValidTranslatedBoxConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, valid translated
scaffold boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checkedStackValidTranslatedBoxConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second checked-stack/layer-patch
scaffold package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackLayerPatchConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second checked-stack/layer-patch scaffold
package and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackLayerPatchConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate checked origin-zero
stacks, valid translated scaffold boxes, and generated interior position-code
rows.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate checked origin-zero stacks,
valid translated scaffold boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete human-audited Figure 13
layer table, indexed active/corner windows, realization, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13NatSitesIndexedWindowConstructionObligations
    (h : FinalFigure13NatSitesIndexedWindowConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete human-audited Figure 13 layer
table, indexed active/corner windows, realization, and generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure13NatSitesIndexedWindowConstructionObligations
    (h : FinalFigure13NatSitesIndexedWindowConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete Robinson indexed-box
scaffold certificate and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonIndexedBoxConstructionObligations
    (h : FinalFigure13RobinsonIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete Robinson indexed-box scaffold
certificate and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure13RobinsonIndexedBoxConstructionObligations
    (h : FinalFigure13RobinsonIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from Robinson tower/indexed-box scaffold
obligations and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxConstructionObligations
    (h : FinalFigure13RobinsonTowerIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from Robinson tower/indexed-box scaffold obligations
and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxConstructionObligations
    (h : FinalFigure13RobinsonTowerIndexedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from Robinson signal towers, translated
positive boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from Robinson signal towers, translated positive
boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalFigure13RobinsonSignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line translated-box package and generated interior position-code
rows.
-/
theorem encoded_domino_problem_undecidable_of_section7TranslatedBoxConstructionObligations
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
translated-box package and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_section7TranslatedBoxConstructionObligations
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the first L2 candidate's
signal-tower/translated-box scaffold package and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_l2c1SignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the first L2 candidate's
signal-tower/translated-box scaffold package and generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_l2c1SignalTowerTranslatedPositiveBoxConstructionObligations
    (h : FinalL2C1SignalTowerTranslatedPositiveBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the proof-facing Section 7
translated-box package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_l2c1SignalTowerTranslatedBoxDataConstructionObligations
    (h : FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the proof-facing Section 7 translated-box
package and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_l2c1SignalTowerTranslatedBoxDataConstructionObligations
    (h : FinalL2C1SignalTowerTranslatedBoxDataConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

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
