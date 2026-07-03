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

set_option linter.style.longLine false in
/--
Finite checked-stack/valid-translated-box route with the narrower generated
decoder-step source target.
-/
structure FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackValidTranslatedBoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Finite checked-stack/valid-translated-box route with the global position-code
label-index source target.
-/
structure FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackValidTranslatedBoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Finite checked-stack/valid-translated-box route with the source-specialized
position-code label-index source target.
-/
structure FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C1CheckedStackValidTranslatedBoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Finite Figure 16 compatible macro-square route for the first audited L2
candidate.

This keeps the final scaffold obligation close to the human-audited finite
data: checked origin-zero stacks supply the Section 7 board/free-line
recognition, while compatible Figure 16 macro-squares supply the valid
translated boxes.
-/
structure FinalFigure16CompatibleConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Finite Figure 16 compatible macro-square route with the narrower generated
decoder-step source target.
-/
structure FinalFigure16CompatibleDecoderStepConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Finite Figure 16 compatible macro-square route with the global position-code
label-index source target.
-/
structure FinalFigure16CompatibleGlobalPositionCodeConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Finite Figure 16 compatible macro-square route with the source-specialized
position-code label-index source target.
-/
structure FinalFigure16CompatibleSourcePositionCodeConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Finite Figure 16 compatible macro-square route from origin-zero active/corner
windows for the first audited L2 candidate.

This is one step closer to the concrete scaffold transcription than
`FinalFigure16CompatibleConstructionObligations`: the checked origin-zero
stacks are derived from the origin-zero window certificate.
-/
structure FinalFigure16CompatibleOriginZeroConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Origin-zero Figure 16 compatible route with the narrower generated
decoder-step source target.
-/
structure FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Origin-zero Figure 16 compatible route with the global position-code
label-index source target.
-/
structure FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Origin-zero Figure 16 compatible route with the source-specialized
position-code label-index source target.
-/
structure FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Finite Figure 16 compatible macro-square route from canonical free-site
recognition for the first audited L2 candidate.

This is the clean scaffold-facing surface: Section 7 derives the checked
origin-zero stacks and valid translated boxes from canonical free-site
active-corner recognition.
-/
structure FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Canonical-free-site Figure 16 compatible route with the narrower generated
decoder-step source target.
-/
structure FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Canonical-free-site Figure 16 compatible route with the global position-code
label-index source target.
-/
structure FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Canonical-free-site Figure 16 compatible route with the source-specialized
position-code label-index source target.
-/
structure FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  compatibleMacroSquares :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from direct Section 7 board/free-line
active-corner recognition.

This separates the geometric recognition needed by Section 7 from the stronger
origin-zero window certificate that currently supplies it.
-/
structure FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations : Prop where
  boardFreeLineActiveCorner :
    TM0FoldedReduction.Section7BoardFreeLineActiveCornerInvariant
      l2Component1Figure18ScaffoldData
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from direct Section 7 board/free-line
active-corner recognition, using the primitive recursive generated
position-code decoder step.
-/
structure FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations :
    Prop where
  boardFreeLineActiveCorner :
    TM0FoldedReduction.Section7BoardFreeLineActiveCornerInvariant
      l2Component1Figure18ScaffoldData
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from direct Section 7 board/free-line
active-corner recognition, using the global position-code label-index source
target.
-/
structure FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations :
    Prop where
  boardFreeLineActiveCorner :
    TM0FoldedReduction.Section7BoardFreeLineActiveCornerInvariant
      l2Component1Figure18ScaffoldData
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from direct Section 7 board/free-line
active-corner recognition, using the source-specialized position-code
label-index source target.
-/
structure FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations :
    Prop where
  boardFreeLineActiveCorner :
    TM0FoldedReduction.Section7BoardFreeLineActiveCornerInvariant
      l2Component1Figure18ScaffoldData
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from origin-zero active/corner windows.

This exposes the core scaffold target directly: a plane tiling of the compatible
Figure 18 scaffold tiles supplies the translated active-corner boxes, while the
origin-zero window certificate supplies board/free-line recognition.
-/
structure FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from origin-zero active/corner windows, using
the primitive recursive generated position-code decoder step.
-/
structure FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from origin-zero active/corner windows, using
the global position-code label-index source target.
-/
structure FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from origin-zero active/corner windows, using
the source-specialized position-code label-index source target.
-/
structure FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from finite origin-zero checked layer stacks.

The checked stacks already imply canonical Robinson free-site active/corner
recognition for the first audited L2 candidate, so this package exposes the
current finite scaffold target without requiring callers to restate the
canonical recognition field separately.
-/
structure FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from finite origin-zero checked layer stacks,
using the primitive recursive generated position-code decoder step.
-/
structure FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from finite origin-zero checked layer stacks,
using the global position-code label-index source target.
-/
structure FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from finite origin-zero checked layer stacks,
using the source-specialized position-code label-index source target.
-/
structure FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from canonical Robinson free-site
active/corner recognition.

This is the current clean scaffold-facing surface: the Robinson geometry proof
only has to identify active/corner sites on canonical free crossings, while
the generic bridge derives the origin-zero window certificate used by the
Section 7 reduction route.
-/
structure FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations :
    Prop where
  canonicalActiveCorner :
    TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from canonical Robinson free-site
active/corner recognition, using the primitive recursive generated
position-code decoder step.
-/
structure FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations :
    Prop where
  canonicalActiveCorner :
    TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from canonical Robinson free-site
active/corner recognition, using the global position-code label-index source
target.
-/
structure FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner :
    TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Figure 18 scaffold-tiling route from canonical Robinson free-site
active/corner recognition, using the source-specialized position-code
label-index source target.
-/
structure FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner :
    TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Second-candidate checked-stack/layer-patch route with the narrower generated
decoder-step source target.
-/
structure FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Second-candidate checked-stack/layer-patch route with the global position-code
label-index source target.
-/
structure FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Second-candidate checked-stack/layer-patch route with the source-specialized
position-code label-index source target.
-/
structure FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Second-candidate valid-translated-box route with the narrower generated
decoder-step source target.
-/
structure FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Second-candidate valid-translated-box route with the global position-code
label-index source target.
-/
structure FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Second-candidate valid-translated-box route with the source-specialized
position-code label-index source target.
-/
structure FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Second-candidate canonical-free-site Figure 16 route with generated interior
position-code rows.

This is the row-source analogue of
`FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations`:
the existing source-side bridge turns `sourceRows` into the source-specialized
label-index decoder used by the current endpoint.
-/
structure FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  compatibleLevelChecks :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Second-candidate canonical-free-site Figure 16 route with the
source-specialized position-code label-index source target.

This mirrors the preferred first-candidate canonical-free-site/Figure16 final
surface, but uses the second audited L2 blank candidate.
-/
structure FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  compatibleLevelChecks :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Second-candidate canonical-free-site scaffold-plane route with generated
interior position-code rows.

This is the L2C2 analogue of
`FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations`,
using a direct tiling of the compatible Figure 18 scaffold tiles instead of the
Figure 16 macro-square certificate.
-/
structure FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Second-candidate canonical-free-site scaffold-plane route with the generated
position-code decoder step.
-/
structure FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Second-candidate canonical-free-site scaffold-plane route with the global
position-code label-index target.
-/
structure FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Second-candidate canonical-free-site scaffold-plane route with the
source-specialized position-code label-index source target.
-/
structure FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  scaffoldPlane : TilesPlane figure18ScaffoldTiles
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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

set_option linter.style.longLine false in
/--
The concrete Figure 13 scaffold data for the second audited L2-blank
candidate.

This abbreviation keeps the final compatible-level surface focused on the two
remaining Robinson scaffold facts: compatible routed free grids and realization.
-/
abbrev FinalFigure13L2C2CompatibleLevelScaffoldData :=
  scaffoldDataOfNatSites
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 compatible-level scaffold route.

This is a lower-level scaffold-facing surface than the canonical-free-site
Figure 16 wrappers: it asks directly for compatible routed Robinson free grids
and a realization certificate for the concrete human-audited L2C2 Figure 13
scaffold, plus the source-specialized generated position-code decoder.
-/
structure FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations :
    Prop where
  compatibleRoutedFreeGrids :
    OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
      FinalFigure13L2C2CompatibleLevelScaffoldData.table
  realizes :
    RealizesActiveCornerSquares
      FinalFigure13L2C2CompatibleLevelScaffoldData.table.presentation.toScaffold
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 compatible-level/layer-patch scaffold
route.

This is the finite-patch version of
`FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations`:
instead of a full realization certificate, it asks for the active-corner layer
box patches used by the Section 7 realization bridge.
-/
structure FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations :
    Prop where
  compatibleRoutedFreeGrids :
    OllingerRobinson.HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
      FinalFigure13L2C2CompatibleLevelScaffoldData.table
  layerPatches :
    HasActiveCornerLayerBoxPatches
      FinalFigure13L2C2CompatibleLevelScaffoldData.table.presentation.toScaffold
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 canonical-product-routing/layer-patch
scaffold route.

This is one routing step below the compatible-level/layer-patch surface:
Robinson's canonical product-witness routing implies the compatible routed
free-grid obligation, while the finite layer patches supply the realization
side of the Section 7 compatible-level package.
-/
structure FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations :
    Prop where
  canonicalProductRouting :
    OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
      FinalFigure13L2C2CompatibleLevelScaffoldData.table
  layerPatches :
    HasActiveCornerLayerBoxPatches
      FinalFigure13L2C2CompatibleLevelScaffoldData.table.presentation.toScaffold
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 canonical-product-routing/positive-box
scaffold route.

This is the positive-radius indexed-box version of
`FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations`:
the radius-zero layer patch is supplied by the scaffold corner, so the finite
backward scaffold work only has to construct active-corner indexed boxes for
positive radii.
-/
structure FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations :
    Prop where
  canonicalProductRouting :
    OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
      FinalFigure13L2C2CompatibleLevelScaffoldData.table
  positiveIndexedBoxes :
    ∀ r : Nat, 0 < r →
      Nonempty (ActiveCornerIndexedBox
        FinalFigure13L2C2CompatibleLevelScaffoldData.scaffold r)
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 canonical-product-routing/translated
positive-box scaffold route.

This is the translated-origin version of
`FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations`:
the finite scaffold target can construct active-corner indexed boxes around any
origin convenient for the local Section 7 geometry, and the existing layer-patch
bridge recenters them.
-/
structure FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations :
    Prop where
  canonicalProductRouting :
    OllingerRobinson.HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
      FinalFigure13L2C2CompatibleLevelScaffoldData.table
  positiveTranslatedIndexedBoxes :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        Nonempty (TranslatedActiveCornerIndexedBox
          FinalFigure13L2C2CompatibleLevelScaffoldData.scaffold r origin)
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 canonical-routing/translated-positive-box
scaffold route.

This is the preferred ordinary-canonical version of the L2C2 translated-box
surface.  It reuses the existing Nat-site interface, so the scaffold side only
has to prove canonical Robinson-board routing and translated positive-radius
active-corner indexed boxes for the concrete human-audited L2C2 Figure 13 data.
-/
structure FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations :
    Prop where
  scaffold :
    NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 free-site-rectangle/translated-positive-box
scaffold route.

This is the Section 7 shaped version of the L2C2 translated-box surface: the
scaffold side supplies the selected free/free site-rectangle routing plus
translated positive-radius active-corner indexed boxes for the concrete
human-audited L2C2 Figure 13 data.
-/
structure FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations :
    Prop where
  scaffold :
    NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete second-candidate Figure 13 origin-zero/translated-positive-box
scaffold route.

This is the L2C2 analogue of `FinalOriginZeroTranslatedBoxData`, but kept under
the Figure 13/L2C2 final surface.  Origin-zero active/corner windows imply the
free-site-rectangle routing, and the translated positive boxes provide the
backward scaffold realization.
-/
structure FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations :
    Prop where
  scaffold :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Paper-facing Section 7 board/free-line translated-box obligations with the
narrower decoder-step source target.
-/
structure FinalSection7TranslatedBoxDecoderStepConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

/--
Paper-facing Section 7 board/free-line translated-box obligations with the
global position-code label-index source target.
-/
structure FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

/--
Paper-facing Section 7 board/free-line translated-box obligations with the
source-specialized position-code label-index source target.
-/
structure FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations : Prop where
  section7 : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData
  labelIndex : SourcePositionCodeLabelIndexFromPrimrec

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
Project checked-stack/valid-translated-box data to the proof-facing Section 7
translated-box package.
-/
def toSection7TranslatedBoxConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    FinalSection7TranslatedBoxConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  sourceRows := h.sourceRows

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

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the origin-zero
translated-box row-source package.
-/
def toOriginZeroTranslatedBoxConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    FinalOriginZeroTranslatedBoxConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  sourceRows := h.sourceRows

/-- Convert the checked-stack/valid-translated-box row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedStackValidTranslatedBoxConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBox
    (TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    h.sourceRows

end FinalCheckedStackValidTranslatedBoxConstructionObligations

namespace FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the proof-facing Section 7
translated-box decoder-step package.
-/
def toSection7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    FinalSection7TranslatedBoxDecoderStepConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the checked-stack/layer-patch
decoder-step package.
-/
def toCheckedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    FinalCheckedStackLayerPatchDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the origin-zero
translated-box decoder-step package.
-/
def toOriginZeroTranslatedBoxDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  decoderStep := h.decoderStep

/-- Convert the checked-stack/valid-translated-box decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBoxDecoderStep
    (TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    h.decoderStep

end FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations

namespace FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label package to the valid-translated-box decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations where
  scaffold := h.scaffold
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the checked-stack/layer-patch
global-label package.
-/
def toCheckedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the origin-zero
translated-box global-label package.
-/
def toOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

/-- Convert the checked-stack/valid-translated-box global-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroTranslatedBoxGlobalPositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    h.labelIndex

end FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations

namespace FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the valid-translated-box decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations where
  scaffold := h.scaffold
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the checked-stack/layer-patch
source-label package.
-/
def toCheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box data to the origin-zero
translated-positive-box final surface.
-/
def toOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

/-- Convert the checked-stack/valid-translated-box source-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofCheckedStackLayerPatchDataSourcePositionCodeLabelIndexFrom
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, valid translated scaffold
boxes, and the source-specialized position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, valid translated scaffold
boxes, and the source-specialized position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations

namespace FinalFigure16CompatibleConstructionObligations

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
proof-facing Section 7 translated-box package.
-/
def toSection7TranslatedBoxConstructionObligations
    (h : FinalFigure16CompatibleConstructionObligations) :
    FinalSection7TranslatedBoxConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.compatibleMacroSquares
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
checked-stack/valid-translated-box package.
-/
def toCheckedStackValidTranslatedBoxConstructionObligations
    (h : FinalFigure16CompatibleConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.compatibleMacroSquares
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
origin-zero translated-box row-source package.
-/
def toOriginZeroTranslatedBoxConstructionObligations
    (h : FinalFigure16CompatibleConstructionObligations) :
    FinalOriginZeroTranslatedBoxConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations
    |>.toOriginZeroTranslatedBoxConstructionObligations

/-- Convert the finite Figure 16 compatible macro-square package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure16CompatibleConstructionObligations

namespace FinalFigure16CompatibleDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
checked-stack/valid-translated-box decoder-step package.
-/
def toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.compatibleMacroSquares
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
origin-zero translated-box decoder-step package.
-/
def toOriginZeroTranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations
    |>.toOriginZeroTranslatedBoxDecoderStepConstructionObligations

/-- Convert the finite Figure 16 compatible decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and the generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and the generated position-code decoder step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFigure16CompatibleDecoderStepConstructionObligations

namespace FinalFigure16CompatibleGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    FinalFigure16CompatibleSourcePositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  compatibleMacroSquares := h.compatibleMacroSquares
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    FinalFigure16CompatibleDecoderStepConstructionObligations where
  checkedStacks := h.checkedStacks
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
checked-stack/valid-translated-box global-label package.
-/
def toCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.compatibleMacroSquares
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
origin-zero translated-box global-label package.
-/
def toOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    |>.toOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations

/-- Convert the finite Figure 16 compatible global-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and the global position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and the global position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure16CompatibleGlobalPositionCodeConstructionObligations

namespace FinalFigure16CompatibleSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    FinalFigure16CompatibleDecoderStepConstructionObligations where
  checkedStacks := h.checkedStacks
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
checked-stack/valid-translated-box source-label package.
-/
def toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      h.checkedStacks h.compatibleMacroSquares
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project the finite Figure 16 compatible macro-square package to the
origin-zero translated-box source-label package.
-/
def toOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    |>.toOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations

/-- Convert the finite Figure 16 compatible source-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and the source-specialized position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, compatible Figure 16
macro-squares, and the source-specialized position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalFigure16CompatibleSourcePositionCodeConstructionObligations

namespace FinalFigure16CompatibleOriginZeroConstructionObligations

set_option linter.style.longLine false in
/--
Project the origin-zero-window Figure 16 package to the checked-stack Figure 16
final route.
-/
def toFigure16CompatibleConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    FinalFigure16CompatibleConstructionObligations where
  checkedStacks :=
    TM0FoldedReduction.l2c1OriginZeroCheckedStacksOfOriginZeroWindows
      h.originZeroWindows
  compatibleMacroSquares := h.compatibleMacroSquares
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Project the origin-zero-window Figure 16 package to the proof-facing Section 7
translated-box package.
-/
def toSection7TranslatedBoxConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    FinalSection7TranslatedBoxConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
      h.originZeroWindows h.compatibleMacroSquares
  sourceRows := h.sourceRows

/-- Convert the origin-zero-window Figure 16 package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    FinalReductionInputs :=
  h.toFigure16CompatibleConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from origin-zero active/corner windows, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from origin-zero active/corner windows, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure16CompatibleOriginZeroConstructionObligations

namespace FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the origin-zero-window Figure 16 decoder-step package to the
proof-facing Section 7 translated-box decoder-step package.
-/
def toSection7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations) :
    FinalSection7TranslatedBoxDecoderStepConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
      h.originZeroWindows h.compatibleMacroSquares
  decoderStep := h.decoderStep

/-- Convert the origin-zero-window Figure 16 decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      h.toSection7TranslatedBoxDecoderStepConstructionObligations.section7)
    h.decoderStep

set_option linter.style.longLine false in
/--
Encoded endpoint from origin-zero active/corner windows, compatible Figure 16
macro-squares, and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Unencoded endpoint from origin-zero active/corner windows, compatible Figure 16
macro-squares, and the primitive recursive generated position-code decoder
step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations

namespace FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the global-label-index package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations where
  originZeroWindows := h.originZeroWindows
  compatibleMacroSquares := h.compatibleMacroSquares
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the origin-zero Figure 16 global-label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the origin-zero Figure 16 global-label-index package. -/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations

namespace FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-specialized label-index package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations) :
    FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

/-- Convert the source-specialized label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the origin-zero Figure 16 source-label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.toDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the origin-zero Figure 16 source-label-index package. -/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.toDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    h.labelIndex

end FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations

namespace FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 package to the checked-stack Figure
16 final route.
-/
def toFigure16CompatibleConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalFigure16CompatibleConstructionObligations where
  checkedStacks :=
    TM0FoldedReduction.l2c1OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner
      h.canonicalActiveCorner
  compatibleMacroSquares := h.compatibleMacroSquares
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 package to checked-stack valid
translated boxes.
-/
def toCheckedStackValidTranslatedBoxConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      h.canonicalActiveCorner h.compatibleMacroSquares
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 row-source package to the
origin-zero translated-box row-source package.
-/
def toOriginZeroTranslatedBoxConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalOriginZeroTranslatedBoxConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations
    |>.toOriginZeroTranslatedBoxConstructionObligations

/-- Convert the canonical-free-site Figure 16 package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from canonical free-site recognition, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toCheckedStackValidTranslatedBoxConstructionObligations.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from canonical free-site recognition, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toCheckedStackValidTranslatedBoxConstructionObligations.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations

namespace FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 decoder-step package to the checked
stack Figure 16 decoder-step route.
-/
def toFigure16CompatibleDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    FinalFigure16CompatibleDecoderStepConstructionObligations where
  checkedStacks :=
    TM0FoldedReduction.l2c1OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner
      h.canonicalActiveCorner
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 decoder-step package to
checked-stack valid translated boxes.
-/
def toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      h.canonicalActiveCorner h.compatibleMacroSquares
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 decoder-step package to the
origin-zero translated-box decoder-step package.
-/
def toOriginZeroTranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations
    |>.toOriginZeroTranslatedBoxDecoderStepConstructionObligations

/-- Convert the canonical-free-site Figure 16 decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from canonical free-site recognition, compatible Figure 16
macro-squares, and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Unencoded endpoint from canonical free-site recognition, compatible Figure 16
macro-squares, and the primitive recursive generated position-code decoder
step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toCheckedStackValidTranslatedBoxDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations

namespace FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the global-label-index package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  compatibleMacroSquares := h.compatibleMacroSquares
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 global-label package to
checked-stack valid translated boxes.
-/
def toCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      h.canonicalActiveCorner h.compatibleMacroSquares
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 global-label package to the
origin-zero translated-box global-label package.
-/
def toOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    |>.toOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations

/-- Convert the canonical-free-site Figure 16 global-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the canonical-free-site Figure 16 global-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the canonical-free-site Figure 16 global-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations

namespace FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-specialized label-index package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  compatibleMacroSquares := h.compatibleMacroSquares
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 source-label package to
checked-stack valid translated boxes.
-/
def toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      h.canonicalActiveCorner h.compatibleMacroSquares
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project the canonical-free-site Figure 16 source-label package to the
origin-zero translated-box source-label package.
-/
def toOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    |>.toOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations

/-- Convert the canonical-free-site Figure 16 source-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the canonical-free-site Figure 16 source-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the canonical-free-site Figure 16 source-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations

set_option linter.style.longLine false in
/-- The Section 7 translated-box package supplied by the direct board/free-line surface. -/
def section7
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfFigure18ScaffoldTilesPlane
    h.boardFreeLineActiveCorner h.scaffoldPlane

set_option linter.style.longLine false in
/--
Project the direct board/free-line scaffold-tiling package to the proof-facing
Section 7 translated-box row-source package.
-/
def toSection7TranslatedBoxConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    FinalSection7TranslatedBoxConstructionObligations where
  section7 := section7 h
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the direct board/free-line scaffold-tiling row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      (section7 h))
    h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from direct board/free-line active-corner recognition, a plane
tiling of the compatible Figure 18 scaffold tiles, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    (section7 h)
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from direct board/free-line active-corner recognition, a
plane tiling of the compatible Figure 18 scaffold tiles, and generated interior
position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    (section7 h)
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations

set_option linter.style.longLine false in
/-- The Section 7 translated-box package supplied by the direct board/free-line surface. -/
def section7
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfFigure18ScaffoldTilesPlane
    h.boardFreeLineActiveCorner h.scaffoldPlane

set_option linter.style.longLine false in
/--
Project the direct board/free-line scaffold-tiling decoder-step package to the
proof-facing Section 7 translated-box decoder-step package.
-/
def toSection7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    FinalSection7TranslatedBoxDecoderStepConstructionObligations where
  section7 := section7 h
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Convert the direct board/free-line scaffold-tiling decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      (section7 h))
    h.decoderStep

set_option linter.style.longLine false in
/--
Encoded endpoint from direct board/free-line active-corner recognition, a plane
tiling of the compatible Figure 18 scaffold tiles, and the generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    (section7 h)
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Unencoded endpoint from direct board/free-line active-corner recognition, a
plane tiling of the compatible Figure 18 scaffold tiles, and the generated
position-code decoder step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    (section7 h)
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the global-label package to the direct board/free-line decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations where
  boardFreeLineActiveCorner := h.boardFreeLineActiveCorner
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations where
  boardFreeLineActiveCorner := h.boardFreeLineActiveCorner
  scaffoldPlane := h.scaffoldPlane
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations.toFinalReductionInputs
    (toDecoderStepConstructionObligations h)

set_option linter.style.longLine false in
/-- Encoded endpoint from the direct board/free-line scaffold-tiling global-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations.section7
      (toDecoderStepConstructionObligations h))
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the direct board/free-line scaffold-tiling global-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations.section7
      (toDecoderStepConstructionObligations h))
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

end FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- The Section 7 translated-box package supplied by the direct board/free-line surface. -/
def section7
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineTranslatedBoxData :=
  TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfFigure18ScaffoldTilesPlane
    h.boardFreeLineActiveCorner h.scaffoldPlane

set_option linter.style.longLine false in
/-- Convert the source-label package to the direct board/free-line decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations where
  boardFreeLineActiveCorner := h.boardFreeLineActiveCorner
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the direct board/free-line scaffold-tiling source-label package to the
proof-facing Section 7 translated-box source-label package.
-/
def toSection7TranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations where
  section7 := section7 h
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/-- Convert the source-specialized label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations.toFinalReductionInputs
    (toDecoderStepConstructionObligations h)

set_option linter.style.longLine false in
/-- Encoded endpoint from the direct board/free-line scaffold-tiling source-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (section7 h)
    h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the direct board/free-line scaffold-tiling source-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (section7 h)
    h.labelIndex

end FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations

set_option linter.style.longLine false in
/--
Project the Figure 18 scaffold-tiling package to the proof-facing Section 7
translated-box row-source package.
-/
def toSection7TranslatedBoxConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations) :
    FinalSection7TranslatedBoxConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroWindowsFigure18ScaffoldTilesPlane
      h.originZeroWindows h.scaffoldPlane
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/-- Convert the Figure 18 scaffold-tiling row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      h.toSection7TranslatedBoxConstructionObligations.section7)
    h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from origin-zero active/corner windows, a plane tiling of the
compatible Figure 18 scaffold tiles, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from origin-zero active/corner windows, a plane tiling of the
compatible Figure 18 scaffold tiles, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.toSection7TranslatedBoxConstructionObligations.section7
    h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

end FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the Figure 18 scaffold-tiling decoder-step package to the proof-facing
Section 7 translated-box decoder-step package.
-/
def toSection7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations) :
    FinalSection7TranslatedBoxDecoderStepConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroWindowsFigure18ScaffoldTilesPlane
      h.originZeroWindows h.scaffoldPlane
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/-- Convert the Figure 18 scaffold-tiling decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofScaffoldAndSourceDecoderStep
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      h.toSection7TranslatedBoxDecoderStepConstructionObligations.section7)
    h.decoderStep

set_option linter.style.longLine false in
/--
Encoded endpoint from origin-zero active/corner windows, a plane tiling of the
compatible Figure 18 scaffold tiles, and the generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Unencoded endpoint from origin-zero active/corner windows, a plane tiling of the
compatible Figure 18 scaffold tiles, and the generated position-code decoder
step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the global-label package to the Figure 18 scaffold-tiling decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations where
  originZeroWindows := h.originZeroWindows
  scaffoldPlane := h.scaffoldPlane
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the global-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the Figure 18 scaffold-tiling global-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.toDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the Figure 18 scaffold-tiling global-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.toDecoderStepConstructionObligations.toSection7TranslatedBoxDecoderStepConstructionObligations.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

end FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the Figure 18 scaffold-tiling decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations where
  originZeroWindows := h.originZeroWindows
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the Figure 18 scaffold-tiling source-label package to the proof-facing
Section 7 translated-box source-label package.
-/
def toSection7TranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroWindowsFigure18ScaffoldTilesPlane
      h.originZeroWindows h.scaffoldPlane
  labelIndex := h.labelIndex

/-- Convert the source-specialized label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the Figure 18 scaffold-tiling source-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.toSection7TranslatedBoxSourcePositionCodeConstructionObligations.section7
    h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the Figure 18 scaffold-tiling source-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.toSection7TranslatedBoxSourcePositionCodeConstructionObligations.section7
    h.labelIndex

end FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations

set_option linter.style.longLine false in
/--
Project the checked-stack scaffold-tiling package to the canonical-free-site
row-source package.
-/
def toCanonicalFreeSiteConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations where
  canonicalActiveCorner :=
    TM0FoldedReduction.l2c1ActiveCornerOfOriginZeroCheckedStacks h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  sourceRows := h.sourceRows

/--
Project the checked-stack scaffold-tiling package to the origin-zero
row-source package.
-/
def toOriginZeroConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  sourceRows := h.sourceRows

/-- Convert the checked-stack scaffold-tiling row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    FinalReductionInputs :=
  h.toOriginZeroConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, a plane tiling of the
compatible Figure 18 scaffold tiles, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toOriginZeroConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, a plane tiling of the
compatible Figure 18 scaffold tiles, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toOriginZeroConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the checked-stack scaffold-tiling decoder-step package to the
canonical-free-site decoder-step package.
-/
def toCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations where
  canonicalActiveCorner :=
    TM0FoldedReduction.l2c1ActiveCornerOfOriginZeroCheckedStacks h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  decoderStep := h.decoderStep

/--
Project the checked-stack scaffold-tiling decoder-step package to the
origin-zero decoder-step package.
-/
def toOriginZeroDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  decoderStep := h.decoderStep

/-- Convert the checked-stack scaffold-tiling decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  h.toOriginZeroDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from checked origin-zero stacks, a plane tiling of the
compatible Figure 18 scaffold tiles, and the generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toOriginZeroDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from checked origin-zero stacks, a plane tiling of the
compatible Figure 18 scaffold tiles, and the generated position-code decoder
step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toOriginZeroDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the global-label package to the checked-stack decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations where
  checkedStacks := h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations where
  checkedStacks := h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the checked-stack scaffold-tiling global-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the checked-stack scaffold-tiling global-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the checked-stack scaffold-tiling global-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the checked-stack decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations where
  checkedStacks := h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the checked-stack scaffold-tiling source-label package to the
canonical-free-site source-label package.
-/
def toCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations where
  canonicalActiveCorner :=
    TM0FoldedReduction.l2c1ActiveCornerOfOriginZeroCheckedStacks h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  labelIndex := h.labelIndex

/--
Project the checked-stack scaffold-tiling source-label package to the
origin-zero source-label package.
-/
def toOriginZeroSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  scaffoldPlane := h.scaffoldPlane
  labelIndex := h.labelIndex

/-- Convert the checked-stack scaffold-tiling source-label package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the checked-stack scaffold-tiling source-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toOriginZeroSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the checked-stack scaffold-tiling source-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toOriginZeroSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations

set_option linter.style.longLine false in
/--
Project the canonical-free-site scaffold-tiling package to the origin-zero
scaffold-tiling row-source package.
-/
def toOriginZeroConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      h.canonicalActiveCorner
  scaffoldPlane := h.scaffoldPlane
  sourceRows := h.sourceRows

/-- Convert the canonical-free-site row-source package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    FinalReductionInputs :=
  h.toOriginZeroConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from canonical Robinson free-site active/corner recognition,
a plane tiling of the compatible Figure 18 scaffold tiles, and generated
interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toOriginZeroConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from canonical Robinson free-site active/corner recognition,
a plane tiling of the compatible Figure 18 scaffold tiles, and generated
interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toOriginZeroConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project the canonical-free-site scaffold-tiling decoder-step package to the
origin-zero scaffold-tiling decoder-step package.
-/
def toOriginZeroDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      h.canonicalActiveCorner
  scaffoldPlane := h.scaffoldPlane
  decoderStep := h.decoderStep

/-- Convert the canonical-free-site decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  h.toOriginZeroDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded endpoint from canonical Robinson free-site active/corner recognition,
a plane tiling of the compatible Figure 18 scaffold tiles, and the generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toOriginZeroDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from canonical Robinson free-site active/corner recognition,
a plane tiling of the compatible Figure 18 scaffold tiles, and the generated
position-code decoder step.
-/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toOriginZeroDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the global-label package to the canonical-free-site decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  scaffoldPlane := h.scaffoldPlane
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the global-label package into the endpoint. -/
def toFinalReductionInputs
    (h :
      FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the canonical-free-site scaffold-tiling global-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/-- Unencoded endpoint from the canonical-free-site scaffold-tiling global-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toDecoderStepConstructionObligations.domino_problem_undecidable

end FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations

namespace FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the canonical-free-site decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  scaffoldPlane := h.scaffoldPlane
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project the canonical-free-site scaffold-tiling source-label package to the
origin-zero scaffold-tiling source-label package.
-/
def toOriginZeroSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      h.canonicalActiveCorner
  scaffoldPlane := h.scaffoldPlane
  labelIndex := h.labelIndex

/-- Convert the source-specialized label-index package into the endpoint. -/
def toFinalReductionInputs
    (h :
      FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the canonical-free-site scaffold-tiling source-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    h.canonicalActiveCorner h.scaffoldPlane h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the canonical-free-site scaffold-tiling source-label package. -/
theorem domino_problem_undecidable
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    h.canonicalActiveCorner h.scaffoldPlane h.labelIndex

end FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations

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

namespace FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the second checked-stack/layer-patch package and the
generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Unencoded endpoint from the second checked-stack/layer-patch package and the
generated position-code decoder step.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations

namespace FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations where
  scaffold := h.scaffold
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from the second checked-stack/layer-patch package and the
global position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    h.scaffold h.labelIndex

set_option linter.style.longLine false in
/--
Unencoded endpoint from the second checked-stack/layer-patch package and the
global position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    h.scaffold h.labelIndex

end FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations

namespace FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations where
  scaffold := h.scaffold
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from the second checked-stack/layer-patch package and the
source-specialized position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    h.scaffold h.labelIndex

set_option linter.style.longLine false in
/--
Unencoded endpoint from the second checked-stack/layer-patch package and the
source-specialized position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    h.scaffold h.labelIndex

end FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations

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
Project second-candidate checked-stack/valid-translated-box row-source data to
the origin-zero/translated-positive-box source-label final surface.
-/
def toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex :=
    TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
      h.sourceRows

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      (TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
        h.sourceRows))

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      (TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
        h.sourceRows))

end FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations

namespace FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Project second-candidate checked-stack/valid-translated-box data to the
checked-stack/layer-patch decoder-step package.
-/
def toCheckedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  decoderStep := h.decoderStep

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and the generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCheckedStackLayerPatchDecoderStepConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and the generated position-code decoder step.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCheckedStackLayerPatchDecoderStepConstructionObligations.domino_problem_undecidable

end FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations

namespace FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Forget the global label-index target to the source-specialized target. -/
def toSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold := h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the global-label package to the valid-translated-box decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations where
  scaffold := h.scaffold
  decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project second-candidate checked-stack/valid-translated-box data to the
checked-stack/layer-patch global-label package.
-/
def toCheckedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project second-candidate checked-stack/valid-translated-box global-label data
to the origin-zero/translated-positive-box source-label final surface.
-/
def toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and the global position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex))

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and the global position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex))

end FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations

namespace FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/-- Convert the source-label package to the valid-translated-box decoder-step package. -/
def toDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations where
  scaffold := h.scaffold
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/--
Project second-candidate checked-stack/valid-translated-box data to the
checked-stack/layer-patch source-label package.
-/
def toCheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project second-candidate checked-stack/valid-translated-box data to the
origin-zero/translated-positive-box final surface.
-/
def toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and the source-specialized position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate checked origin-zero stacks, valid
translated scaffold boxes, and the source-specialized position-code label-index
decoder.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    (TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData
      h.scaffold)
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations

namespace FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations

set_option linter.style.longLine false in
/--
Project the second-candidate canonical-free-site Figure 16 row-source package
to the source-label package by using the existing generated-row decoder bridge.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations where
  canonicalActiveCorner := h.canonicalActiveCorner
  compatibleLevelChecks := h.compatibleLevelChecks
  labelIndex :=
    TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
      h.sourceRows

set_option linter.style.longLine false in
/--
Project the second-candidate canonical-free-site Figure 16 row-source package
to checked-stack valid translated boxes.
-/
def toCheckedStackValidTranslatedBoxConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalL2C2CheckedStackValidTranslatedBoxConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      h.canonicalActiveCorner h.compatibleLevelChecks
  sourceRows := h.sourceRows

set_option linter.style.longLine false in
/--
Project the second-candidate canonical-free-site Figure 16 row-source package
to the origin-zero/translated-positive-box source-label final surface.
-/
def toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations
    |>.toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate canonical free-site recognition,
finite compatible Figure 16 level checks, and generated interior position-code
rows.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate canonical free-site recognition,
finite compatible Figure 16 level checks, and generated interior position-code
rows.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCheckedStackValidTranslatedBoxConstructionObligations.domino_problem_undecidable

end FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations

namespace FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Project the second-candidate canonical-free-site Figure 16 package to
checked-stack valid translated boxes.
-/
def toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      h.canonicalActiveCorner h.compatibleLevelChecks
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Project the second-candidate canonical-free-site Figure 16 source-label package
to the origin-zero/translated-positive-box source-label final surface.
-/
def toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    |>.toFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from second-candidate canonical free-site recognition,
finite compatible Figure 16 level checks, and the source-specialized
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from second-candidate canonical free-site recognition,
finite compatible Figure 16 level checks, and the source-specialized
position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations

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

namespace FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13 compatible-level
scaffold package and the source-specialized generated position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable
    (h : FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_figure13_l2c2_compatible_level_position_source
    h.compatibleRoutedFreeGrids h.realizes
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
compatible-level scaffold package and the source-specialized generated
position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h : FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_figure13_l2c2_compatible_level_position_source
    h.compatibleRoutedFreeGrids h.realizes
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations

namespace FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13
compatible-level/layer-patch scaffold package and the source-specialized
generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_figure13_l2c2_compatible_layer_patches_position_source
    h.compatibleRoutedFreeGrids h.layerPatches
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
compatible-level/layer-patch scaffold package and the source-specialized
generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_figure13_l2c2_compatible_level_layer_patches_position_source
    h.compatibleRoutedFreeGrids h.layerPatches
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations

set_option linter.style.longLine false
namespace FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert canonical product-witness routing plus finite layer patches to the
compatible-level/layer-patch final route.
-/
def toCompatibleLevelLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations) :
    FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations where
  compatibleRoutedFreeGrids :=
    (NatSiteRobinsonCompatibleLevelObligations.ofL2C2CanonicalProductRoutingLayerPatches
      h.canonicalProductRouting h.layerPatches).levelCompatibleRoutedFreeGrids
  layerPatches := h.layerPatches
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13
canonical-product-routing/layer-patch scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCompatibleLevelLayerPatchSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
canonical-product-routing/layer-patch scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCompatibleLevelLayerPatchSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations
set_option linter.style.longLine true

set_option linter.style.longLine false
namespace FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert canonical product-witness routing plus positive-radius active-corner
indexed boxes to the layer-patch final route.
-/
def toCanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations) :
    FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations where
  canonicalProductRouting := h.canonicalProductRouting
  layerPatches :=
    scaffoldDataOfNatSitesLayerPatchesOfPositiveActiveCornerIndexedBoxes
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      h.positiveIndexedBoxes
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13
canonical-product-routing/positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
canonical-product-routing/positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations
set_option linter.style.longLine true

set_option linter.style.longLine false
namespace FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert canonical product-witness routing plus translated positive-radius
active-corner indexed boxes to the layer-patch final route.
-/
def toCanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations where
  canonicalProductRouting := h.canonicalProductRouting
  layerPatches :=
    scaffoldDataOfNatSitesLayerPatchesOfPositiveTranslatedIndexedBoxes
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
      h.positiveTranslatedIndexedBoxes
  labelIndex := h.labelIndex

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13
canonical-product-routing/translated-positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.toCanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
canonical-product-routing/translated-positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.toCanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations.domino_problem_undecidable

end FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations
set_option linter.style.longLine true

set_option linter.style.longLine false
namespace FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13 ordinary
canonical-routing/translated-positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13 ordinary
canonical-routing/translated-positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_translated_obligations_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations
set_option linter.style.longLine true

set_option linter.style.longLine false
namespace FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13
free-site-rectangle/translated-positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
free-site-rectangle/translated-positive-box scaffold package and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_free_site_rect_translated_obligations_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations
set_option linter.style.longLine true

set_option linter.style.longLine false
namespace FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from the concrete second-candidate Figure 13
origin-zero/translated-positive-box scaffold package and the source-specialized
generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (h :
      FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

set_option linter.style.longLine false in
/--
Unencoded endpoint from the concrete second-candidate Figure 13
origin-zero/translated-positive-box scaffold package and the source-specialized
generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (h :
      FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_origin_zero_translated_obligations_position_source
    h.scaffold
    (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      h.labelIndex)

end FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
set_option linter.style.longLine true

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
Project the origin-zero translated-box package to the proof-facing Section 7
board/free-line translated-box package.
-/
def toSection7TranslatedBoxConstructionObligations
    (h : FinalOriginZeroTranslatedBoxConstructionObligations) :
    FinalSection7TranslatedBoxConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroObligations
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
Project the origin-zero translated-box package to the proof-facing Section 7
translated-box decoder-step package.
-/
def toSection7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalOriginZeroTranslatedBoxDecoderStepConstructionObligations) :
    FinalSection7TranslatedBoxDecoderStepConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroObligations
      h.scaffold
  decoderStep := h.decoderStep

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
Project the origin-zero translated-box package to the proof-facing Section 7
translated-box global-label-index package.
-/
def toSection7TranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroObligations
      h.scaffold
  labelIndex := h.labelIndex

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
Project the origin-zero translated-box package to the proof-facing Section 7
translated-box source-label-index package.
-/
def toSection7TranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalOriginZeroTranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfOriginZeroObligations
      h.scaffold
  labelIndex := h.labelIndex

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

namespace FinalSection7TranslatedBoxDecoderStepConstructionObligations

set_option linter.style.longLine false in
/--
Convert the translated-box decoder-step package to the centered positive-box
decoder-step package.
-/
def toPositiveBoxDecoderStepConstructionObligations
    (h : FinalSection7TranslatedBoxDecoderStepConstructionObligations) :
    FinalSection7PositiveBoxDecoderStepConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfTranslatedBoxData
      h.section7
  decoderStep := h.decoderStep

/-- Convert the translated-box decoder-step package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7TranslatedBoxDecoderStepConstructionObligations) :
    FinalReductionInputs :=
  h.toPositiveBoxDecoderStepConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 translated-box decoder-step package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7TranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 translated-box decoder-step package. -/
theorem domino_problem_undecidable
    (h : FinalSection7TranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
    h.section7
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

end FinalSection7TranslatedBoxDecoderStepConstructionObligations

namespace FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the translated-box global-label-index package to the centered
positive-box global-label-index package.
-/
def toPositiveBoxGlobalPositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalSection7PositiveBoxGlobalPositionCodeConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfTranslatedBoxData
      h.section7
  labelIndex := h.labelIndex

/--
Forget the global decoder target to the source-specialized decoder target used
by the narrowed translated-box Section 7 route.
-/
def toSourcePositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations where
  section7 := h.section7
  labelIndex := sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex

/-- Convert the translated-box global-label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toPositiveBoxGlobalPositionCodeConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 translated-box global-label-index package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 translated-box global-label-index package. -/
theorem domino_problem_undecidable
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex h.labelIndex)

end FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations

namespace FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations

set_option linter.style.longLine false in
/--
Convert the translated-box source-label-index package to the centered
positive-box source-label-index package.
-/
def toPositiveBoxSourcePositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalSection7PositiveBoxSourcePositionCodeConstructionObligations where
  section7 :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLinePositiveBoxDataOfTranslatedBoxData
      h.section7
  labelIndex := h.labelIndex

/--
Convert the translated-box source-specialized label-index package into the
decoder-step package.
-/
def toDecoderStepConstructionObligations
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalSection7TranslatedBoxDecoderStepConstructionObligations where
  section7 := h.section7
  decoderStep := sourceDecoderStepPrimrec_of_sourceLabelIndex h.labelIndex

set_option linter.style.longLine false in
/-- Convert the translated-box source-specialized label-index package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
    FinalReductionInputs :=
  h.toPositiveBoxSourcePositionCodeConstructionObligations.toFinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded endpoint from the paper-facing Section 7 translated-box source-label package. -/
theorem encoded_domino_problem_undecidable
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.section7 h.labelIndex

set_option linter.style.longLine false in
/-- Unencoded endpoint from the paper-facing Section 7 translated-box source-label package. -/
theorem domino_problem_undecidable
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    h.section7 h.labelIndex

end FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations

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
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.section7 h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded endpoint from the paper-facing Section 7 board/free-line
translated-box package.
-/
theorem domino_problem_undecidable
    (h : FinalSection7TranslatedBoxConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_translated_box_data_interiorRows
    h.section7 h.sourceRows
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

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
Encoded Wang domino undecidability from checked origin-zero stacks, valid
translated scaffold boxes, and the primitive recursive generated position-code
decoder step.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackValidTranslatedBoxDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, valid translated
scaffold boxes, and the primitive recursive generated position-code decoder
step.
-/
theorem domino_problem_undecidable_of_checkedStackValidTranslatedBoxDecoderStepConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, valid
translated scaffold boxes, and the global primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, valid translated
scaffold boxes, and the global primitive recursive position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_checkedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, valid
translated scaffold boxes, and the source-specialized primitive recursive
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, valid translated
scaffold boxes, and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_checkedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleConstructionObligations
    (h : FinalFigure16CompatibleConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure16CompatibleConstructionObligations
    (h : FinalFigure16CompatibleConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and the primitive recursive generated position-code
decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and the primitive recursive generated position-code decoder
step.
-/
theorem domino_problem_undecidable_of_figure16CompatibleDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and the global primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and the global primitive recursive position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_figure16CompatibleGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and the source-specialized primitive recursive
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure
16 macro-squares, and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_figure16CompatibleSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
compatible Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleOriginZeroConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure16CompatibleOriginZeroConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
compatible Figure 16 macro-squares, and the primitive recursive generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleOriginZeroDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and the primitive recursive generated position-code
decoder step.
-/
theorem domino_problem_undecidable_of_figure16CompatibleOriginZeroDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
compatible Figure 16 macro-squares, and the global position-code label-index
source target.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and the global position-code label-index source
target.
-/
theorem domino_problem_undecidable_of_figure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
compatible Figure 16 macro-squares, and the source-specialized position-code
label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleOriginZeroSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and the source-specialized position-code label-index
source target.
-/
theorem domino_problem_undecidable_of_figure16CompatibleOriginZeroSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition,
compatible Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, compatible
Figure 16 macro-squares, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition,
compatible Figure 16 macro-squares, and the primitive recursive generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, compatible
Figure 16 macro-squares, and the primitive recursive generated position-code
decoder step.
-/
theorem domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition,
compatible Figure 16 macro-squares, and the global position-code label-index
source target.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, compatible
Figure 16 macro-squares, and the global position-code label-index source
target.
-/
theorem domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition,
compatible Figure 16 macro-squares, and the source-specialized position-code
label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, compatible
Figure 16 macro-squares, and the source-specialized position-code label-index
source target.
-/
theorem domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition, finite
Figure 16 compatible level checks, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecks
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      sourceRows := sourceRows }

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, finite Figure
16 compatible level checks, and generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecks
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      sourceRows := sourceRows }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition, finite
Figure 16 compatible level checks, and the primitive recursive generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecksDecoderStep
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (decoderStep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      decoderStep := decoderStep }

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, finite Figure
16 compatible level checks, and the primitive recursive generated position-code
decoder step.
-/
theorem domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecksDecoderStep
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (decoderStep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteDecoderStepConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      decoderStep := decoderStep }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition, finite
Figure 16 compatible level checks, and the global position-code label-index
source target.
-/
theorem encoded_domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, finite Figure
16 compatible level checks, and the global position-code label-index source
target.
-/
theorem domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site recognition, finite
Figure 16 compatible level checks, and the source-specialized position-code
label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site recognition, finite Figure
16 compatible level checks, and the source-specialized position-code
label-index source target.
-/
theorem domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleMacroSquares := compatibleLevelChecks
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the primitive recursive generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the global position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the global position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from direct board/free-line active-corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneBoardFreeLineSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows, a
plane tiling of the compatible Figure 18 scaffold tiles, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, a plane
tiling of the compatible Figure 18 scaffold tiles, and generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows, a
plane tiling of the compatible Figure 18 scaffold tiles, and the primitive
recursive generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, a plane
tiling of the compatible Figure 18 scaffold tiles, and the primitive recursive
generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows, a
plane tiling of the compatible Figure 18 scaffold tiles, and the global
position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, a plane
tiling of the compatible Figure 18 scaffold tiles, and the global position-code
label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows, a
plane tiling of the compatible Figure 18 scaffold tiles, and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneOriginZeroSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite origin-zero checked stacks, a
plane tiling of the compatible Figure 18 scaffold tiles, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite origin-zero checked stacks, a
plane tiling of the compatible Figure 18 scaffold tiles, and the primitive
recursive generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the primitive recursive
generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite origin-zero checked stacks, a
plane tiling of the compatible Figure 18 scaffold tiles, and the global
position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the global position-code
label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from finite origin-zero checked stacks, a
plane tiling of the compatible Figure 18 scaffold tiles, and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCheckedStacksSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical Robinson free-site
active/corner recognition, a plane tiling of the compatible Figure 18 scaffold
tiles, and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical Robinson free-site active/corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical Robinson free-site
active/corner recognition, a plane tiling of the compatible Figure 18 scaffold
tiles, and the primitive recursive generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical Robinson free-site active/corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and the
primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical Robinson free-site
active/corner recognition, a plane tiling of the compatible Figure 18 scaffold
tiles, and the global position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical Robinson free-site active/corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and the
global position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical Robinson free-site
active/corner recognition, a plane tiling of the compatible Figure 18 scaffold
tiles, and the source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical Robinson free-site active/corner
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalFigure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

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
Encoded Wang domino undecidability from the second checked-stack/layer-patch
scaffold package and the primitive recursive generated position-code decoder
step.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second checked-stack/layer-patch scaffold
package and the primitive recursive generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackLayerPatchDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second checked-stack/layer-patch
scaffold package and the global primitive recursive position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second checked-stack/layer-patch scaffold
package and the global primitive recursive position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second checked-stack/layer-patch
scaffold package and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second checked-stack/layer-patch scaffold
package and the source-specialized primitive recursive position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackLayerPatchSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate checked origin-zero
stacks, valid translated scaffold boxes, and the primitive recursive generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate checked origin-zero stacks,
valid translated scaffold boxes, and the primitive recursive generated
position-code decoder step.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate checked origin-zero
stacks, valid translated scaffold boxes, and the global primitive recursive
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate checked origin-zero stacks,
valid translated scaffold boxes, and the global primitive recursive
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate checked origin-zero
stacks, valid translated scaffold boxes, and the source-specialized primitive
recursive position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate checked origin-zero stacks,
valid translated scaffold boxes, and the source-specialized primitive recursive
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_l2c2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalL2C2CheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second-candidate canonical
free-site/Figure 16 row-source final package.
-/
theorem encoded_domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second-candidate canonical free-site/Figure
16 row-source final package.
-/
theorem domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second-candidate canonical
free-site/Figure 16 source-specialized final package.
-/
theorem encoded_domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second-candidate canonical free-site/Figure
16 source-specialized final package.
-/
theorem domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleLevelChecks := compatibleLevelChecks
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleLevelChecks := compatibleLevelChecks
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeInteriorRows
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleLevelChecks := compatibleLevelChecks
      sourceRows := sourceRows }

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeInteriorRows
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure16CompatibleCanonicalFreeSiteConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      compatibleLevelChecks := compatibleLevelChecks
      sourceRows := sourceRows }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane row-source final package.
-/
theorem encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    h.canonicalActiveCorner h.scaffoldPlane
    (TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
      h.sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane row-source final package.
-/
theorem domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    h.canonicalActiveCorner h.scaffoldPlane
    (TM0FoldedReduction.sourcePositionCodeLabelIndexFromPrimrec_of_positionCodeInteriorRows
      h.sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane decoder-step final package.
-/
theorem encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_position_source
    h.canonicalActiveCorner h.scaffoldPlane
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane decoder-step final package.
-/
theorem domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_position_source
    h.canonicalActiveCorner h.scaffoldPlane
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeDecoderStepCorrect
      h.decoderStep)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane global-label final package.
-/
theorem encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    { canonicalActiveCorner := h.canonicalActiveCorner
      scaffoldPlane := h.scaffoldPlane
      decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex }

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane global-label final package.
-/
theorem domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    { canonicalActiveCorner := h.canonicalActiveCorner
      scaffoldPlane := h.scaffoldPlane
      decoderStep := sourceDecoderStepPrimrec_of_globalLabelIndex h.labelIndex }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane source-label final package.
-/
theorem encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    h.canonicalActiveCorner h.scaffoldPlane h.labelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the second-candidate canonical
free-site/scaffold-plane source-label final package.
-/
theorem domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations
    (h : FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    h.canonicalActiveCorner h.scaffoldPlane h.labelIndex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneSourcePositionCodeInteriorRows
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      sourceRows := sourceRows }

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneSourcePositionCodeInteriorRows
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      sourceRows := sourceRows }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneDecoderStep
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (decoderStep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      decoderStep := decoderStep }

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the generated position-code decoder step.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneDecoderStep
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (decoderStep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      decoderStep := decoderStep }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the global position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneGlobalPositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (labelIndex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the global position-code label-index source target.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneGlobalPositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (labelIndex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneSourcePositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (labelIndex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, a plane tiling of the compatible Figure 18 scaffold tiles, and
the source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneSourcePositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (scaffoldPlane : TilesPlane figure18ScaffoldTiles)
    (labelIndex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations
    { canonicalActiveCorner := canonicalActiveCorner
      scaffoldPlane := scaffoldPlane
      labelIndex := labelIndex }

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and the generated
position-code decoder step.

The compatible Figure 16 checks generate the compatible Figure 18 scaffold
tiling used by the lower-level scaffold-plane route.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksDecoderStep
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (decoderStep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneDecoderStep
    canonicalActiveCorner
    (tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
      compatibleLevelChecks)
    decoderStep

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and the generated
position-code decoder step.

The compatible Figure 16 checks generate the compatible Figure 18 scaffold
tiling used by the lower-level scaffold-plane route.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksDecoderStep
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (decoderStep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneDecoderStep
    canonicalActiveCorner
    (tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
      compatibleLevelChecks)
    decoderStep

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and the global
position-code label-index source target.

The compatible Figure 16 checks generate the compatible Figure 18 scaffold
tiling used by the lower-level scaffold-plane route.
-/
theorem encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneGlobalPositionCodeLabelIndexFrom
    canonicalActiveCorner
    (tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
      compatibleLevelChecks)
    labelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from second-candidate canonical free-site
recognition, finite Figure 16 compatible level checks, and the global
position-code label-index source target.

The compatible Figure 16 checks generate the compatible Figure 18 scaffold
tiling used by the lower-level scaffold-plane route.
-/
theorem domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom
    (canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks :
      TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (labelIndex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneGlobalPositionCodeLabelIndexFrom
    canonicalActiveCorner
    (tilesPlane_figure18ScaffoldTiles_of_canonicalCheckedFigure16RecognizedCompatible
      compatibleLevelChecks)
    labelIndex

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
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
compatible-level scaffold package and the source-specialized position-code
label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations
    (h : FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
compatible-level scaffold package and the source-specialized position-code
label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations
    (h : FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
compatible-level/layer-patch scaffold package and the source-specialized
position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
compatible-level/layer-patch scaffold package and the source-specialized
position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
canonical-product-routing/layer-patch scaffold package and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
canonical-product-routing/layer-patch scaffold package and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
canonical-product-routing/positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
canonical-product-routing/positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
canonical-product-routing/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
canonical-product-routing/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
ordinary canonical-routing/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13 ordinary
canonical-routing/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
free-site-rectangle/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
free-site-rectangle/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete second-candidate Figure 13
origin-zero/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete second-candidate Figure 13
origin-zero/translated-positive-box scaffold package and the
source-specialized position-code label-index source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations
    (h :
      FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations) :
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
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line translated-box package and the primitive recursive generated
position-code decoder step.
-/
theorem encoded_domino_problem_undecidable_of_section7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalSection7TranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
translated-box package and the primitive recursive generated position-code
decoder step.
-/
theorem domino_problem_undecidable_of_section7TranslatedBoxDecoderStepConstructionObligations
    (h : FinalSection7TranslatedBoxDecoderStepConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line translated-box package and the global position-code label-index
source target.
-/
theorem encoded_domino_problem_undecidable_of_section7TranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
translated-box package and the global position-code label-index source target.
-/
theorem domino_problem_undecidable_of_section7TranslatedBoxGlobalPositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxGlobalPositionCodeConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  h.domino_problem_undecidable

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the paper-facing Section 7
board/free-line translated-box package and the source-specialized position-code
label-index source target.
-/
theorem encoded_domino_problem_undecidable_of_section7TranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  h.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the paper-facing Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
source target.
-/
theorem domino_problem_undecidable_of_section7TranslatedBoxSourcePositionCodeConstructionObligations
    (h : FinalSection7TranslatedBoxSourcePositionCodeConstructionObligations) :
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
