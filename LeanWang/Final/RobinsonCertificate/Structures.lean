/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Final.SourceImplications

/-!
Obligation structures for bundled Robinson Figure 13 / Figure 18 scaffold certificates.

This module contains only theorem-facing data surfaces.  The endpoint theorems
and projection namespaces live in `LeanWang.Final.RobinsonCertificate`, so edits
to the remaining source/scaffold interfaces can rebuild separately from the
larger certificate endpoint layer.
-/
namespace LeanWang

open OllingerRobinson
open OllingerRobinson.Figure13Layers
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

set_option linter.style.longLine false in
/--
Concrete scaffold for the second audited L2 blank candidate used by the compact
Robinson certificate routes in this file.
-/
abbrev Figure13L2C2Scaffold : Scaffold :=
  (scaffoldDataOfNatSites
    l2Component2BlankCandidateActiveSiteSpecs
    l2Component2BlankCandidateSanity.activeSiteSpecs_valid
    0 Quadrant.northeast
    l2Component2BlankCandidateSanity.cornerIndex_valid).scaffold

set_option linter.style.longLine false in
/--
Positive-radius active-corner indexed boxes for the concrete L2C2 scaffold.

This is the finite backward-realization target just below active-corner layer
patches: the existing constructor supplies the radius-zero corner patch and
turns these boxes into `L2C2ActiveCornerLayerPatches`.
-/
abbrev Figure13L2C2PositiveActiveCornerIndexedBoxes : Prop :=
  ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox Figure13L2C2Scaffold r)

set_option linter.style.longLine false in
/--
Current theorem-facing concrete L2C2 Robinson/source target.

The scaffold field is the origin-zero active/corner-window plus translated
positive-box package supplied by the Section 7 Robinson geometry route.  The
source field is the remaining source-specialized generated position-code
label-index decoder target.
-/
structure Figure13L2C2OriginZeroSourceLabelIndexObligations : Prop where
  scaffold :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete L2C2 origin-zero/translated-positive-box Robinson target through the
fixed-start source-level generated position-code decoder.

This is the compact origin-zero analogue of the tower/indexed-box fixed-start
route and avoids asking callers for the stronger full offset label-index
decoder.
-/
structure Figure13L2C2OriginZeroSourceLabelIndexStartObligations : Prop where
  scaffold :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceLabelIndexStart : SourcePositionCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete L2C2 origin-zero/translated-positive-box Robinson target through
bounded-interior generated position-code rows at label indices.

This exposes the current geometric certificate route through the direct
position-coded row decoder, without morally depending on canonical row-list
equality.
-/
structure Figure13L2C2OriginZeroSourceBoundedRowsAtIndexObligations : Prop where
  scaffold :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceRows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete L2C2 origin-zero/translated-positive-box Robinson target through
interior generated position-code rows at label indices.

This is the cleanest direct row-at-index source surface currently exposed from
the compact Robinson certificate module.
-/
structure Figure13L2C2OriginZeroSourceInteriorRowsAtIndexObligations : Prop where
  scaffold :
    NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceRows : SourcePositionCodeInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete Section 7 translated-box theorem-facing L2C2 Robinson/source target.

The scaffold field is the paper-facing board/free-line package that asks for
translated active-corner boxes rather than raw Figure 13 board-level macro-square
alignment.  This is the live Section 7 route for the second audited L2 blank
candidate.
-/
structure Figure13L2C2Section7BoardFreeLineTranslatedBoxSourceLabelIndexObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineTranslatedBoxData
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete Section 7 translated-box theorem-facing L2C2 Robinson/source target
through the bounded-search descriptor decoder.

The `statementList_nodup` field is the explicit bridge that identifies
support-search state codes with generated position codes.
-/
structure Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeWithNodupObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineTranslatedBoxData
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete Section 7 translated-box theorem-facing L2C2 Robinson/source target
through the bounded-search fixed-start decoder for ordinary `programData`.

This is the translated-box analogue of the compact layer-patch search-start
route; it avoids the generated-position-code statement-list uniqueness bridge.
-/
structure Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeStartObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineTranslatedBoxData
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box theorem-facing L2C2 Robinson/source target.

This is one step below the layer-patch data package and one step above the
translated-box package: Section 7 supplies board/free-line active-corner
recognition, and positive active-corner indexed boxes supply the finite patch
realization.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataSourceLabelIndexObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box L2C2 Robinson target through the fixed-start
source-level generated position-code decoder.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataLabelIndexStartObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  sourceLabelIndexStart : SourcePositionCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box L2C2 Robinson target through generated interior
position-code rows.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataRowsObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  sourceRows : SourcePositionCodeInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box L2C2 Robinson target through generated one-row
position-code rows.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataOneRowsObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  sourceRows : SourcePositionCodeOneRowsPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box L2C2 Robinson target through generated
bounded-interior position-code rows.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataBoundedRowsObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  sourceRows : SourcePositionCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box L2C2 Robinson target through the generated
position-code decoder step.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataDecoderStepObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  decoderStep : SourcePositionCodeDecoderStepPrimrec

set_option linter.style.longLine false in
/--
Compact Section 7 positive-box L2C2 Robinson target through the global
position-code label-index decoder.
-/
structure Figure13L2C2Section7BoardFreeLinePositiveBoxDataGlobalPositionCodeObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLinePositiveBoxData
  labelIndex : GlobalPositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete Section 7 layer-patch theorem-facing L2C2 Robinson/source target.

This is the current finite-scaffold frontier: Robinson Section 7 supplies the
board/free-line active-corner invariant and the Figure 13/Figure 16 layer
patches directly, without forgetting them to plain translated boxes first.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexObligations :
    Prop where
  section7 :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete Section 7 layer-patch theorem-facing L2C2 Robinson target through the
bounded-search descriptor decoder.

The `statementList_nodup` field is the explicit bridge from bounded-search
state codes to generated position codes.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodupObligations :
    Prop where
  section7 :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete Section 7 layer-patch theorem-facing L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

Unlike the generated-position-code route, this ordinary-source package does
not require a statement-list uniqueness bridge.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartObligations :
    Prop where
  section7 :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete Section 7 layer-patch theorem-facing L2C2 Robinson target through the
bounded-search fixed-start decoder.

The `statementList_nodup` field is the explicit bridge from bounded-search
state codes to generated position codes.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodupObligations :
    Prop where
  section7 :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete Section 7 layer-patch theorem-facing L2C2 Robinson target through the
bounded-search fixed-start decoder and concrete started-TM1 support
uniqueness/disjointness.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjointObligations :
    Prop where
  section7 :
    NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementSupport_nodup : SourceStartedTM1StatementSupportNodup
  statementSupport_pairwiseDisjoint :
    SourceStartedTM1StatementSupportPairwiseDisjoint

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch theorem-facing L2C2 Robinson/source
target.

This uses the lower `L2C2RobinsonSection7BoardFreeLineLayerPatchData` record
directly: board/free-line active-corner recognition plus finite active-corner
layer patches.  The expanded Nat-site obligation record remains available for
certificate-level conversion.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through the
fixed-start source-level generated position-code decoder.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStartObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceLabelIndexStart : SourcePositionCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through the
bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodupObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

This is the compact record-shaped endpoint for the route that avoids generated
position-code statement-list uniqueness.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder and statement-list uniqueness.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodupObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder and concrete started-TM1 support
uniqueness/disjointness.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjointObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementSupport_nodup : SourceStartedTM1StatementSupportNodup
  statementSupport_pairwiseDisjoint :
    SourceStartedTM1StatementSupportPairwiseDisjoint

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through generated
one-row position-code rows.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceRows : SourcePositionCodeOneRowsPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through generated
bounded-interior position-code rows.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceRows : SourcePositionCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through generated
one-row position-code rows at concrete numeric label slots.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndexObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceRows : SourcePositionCodeOneRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through generated
bounded-interior position-code rows at concrete numeric label slots.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndexObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceRows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Compact concrete Section 7 layer-patch L2C2 Robinson target through generated
interior position-code rows at concrete numeric label slots.
-/
structure Figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndexObligations :
    Prop where
  section7 : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData
  sourceRows : SourcePositionCodeInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete finite checked-stack/layer-patch theorem-facing L2C2 Robinson/source
target.

This is the finite scaffold package closest to the Figure 13/Figure 16
transcription: checked origin-zero stacks provide the Section 7 recognition
data, and layer patches provide the active-corner realization data.
-/
structure Figure13L2C2CheckedStackLayerPatchSourceLabelIndexObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete finite checked-stack/layer-patch L2C2 Robinson target through the
bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2CheckedStackLayerPatchSearchCodeWithNodupObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete finite checked-stack/layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

This is the checked finite-scaffold analogue of the Section 7 ordinary-source
search-start endpoint and does not require statement-list uniqueness.
-/
structure Figure13L2C2CheckedStackLayerPatchSearchCodeStartObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete split checked-stack/layer-patch theorem-facing L2C2 Robinson/source
target.

This keeps the two remaining live scaffold facts as separate fields:
checked origin-zero stacks provide the Section 7 recognition data, and layer
patches provide the active-corner realization data.
-/
structure Figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete split checked-stack/layer-patch L2C2 Robinson target through the
bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodupObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete split checked-stack/layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

The split fields are the finite scaffold facts closest to the checked-stack
and layer-patch transcription, still without the generated-position
statement-list uniqueness bridge.
-/
structure Figure13L2C2CheckedStacksAndLayerPatchesSearchCodeStartObligations :
    Prop where
  checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/layer-patch theorem-facing L2C2 Robinson/source
target.

Origin-zero active/corner windows supply the checked-stack recognition side,
while layer patches remain the finite Figure 13/Figure 16 realization witness.
-/
structure Figure13L2C2OriginZeroLayerPatchesSourceLabelIndexObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/layer-patch L2C2 Robinson target through the
bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodupObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

Origin-zero active/corner windows are converted to checked-stack recognition,
and the finite layer patches are kept explicit.  This avoids the
generated-position statement-list uniqueness bridge.
-/
structure Figure13L2C2OriginZeroLayerPatchesSearchCodeStartObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-box theorem-facing L2C2 Robinson/source
target.

This is one step below `Figure13L2C2OriginZeroLayerPatches...`: positive
active-corner indexed boxes are converted to finite layer patches by the
existing scaffold constructor.
-/
structure Figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-box L2C2 Robinson target through the
bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodupObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-box L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

Positive active-corner indexed boxes are converted to finite layer patches by
the existing scaffold constructor.  This route does not require generated
position-code statement-list uniqueness.
-/
structure Figure13L2C2OriginZeroPositiveBoxesSearchCodeStartObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/valid-translated-box theorem-facing L2C2
Robinson/source target.

This is the certificate-level version of the valid-box scaffold route: valid
translated boxes are converted to finite active-corner layer patches by the
audited no-neighbor checks for the second L2 component.
-/
structure Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/valid-translated-box L2C2 Robinson target through
interior generated position-code rows at concrete numeric label slots.

This is the origin-zero valid-box surface for the same at-index source target
used by the canonical-free-site wrapper.
-/
structure Figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndexObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceRows : SourcePositionCodeInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/valid-translated-box L2C2 Robinson target through
bounded-interior generated position-code rows at concrete numeric label slots.

This is the weakest at-index source target currently exposed for the
origin-zero valid-box scaffold route.
-/
structure Figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndexObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceRows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/valid-translated-box L2C2 Robinson target through
the bounded-search fixed-start decoder for ordinary `programData`.

Valid translated boxes are converted to finite active-corner layer patches by
the audited no-neighbor checks for the second L2 component.  This ordinary
source route does not require generated-position statement-list uniqueness.
-/
structure Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete decoded combined-window/valid-translated-box L2C2 Robinson target
through the bounded-search fixed-start decoder for ordinary `programData`.

Decoded combined active/corner windows supply the indexed origin-zero windows;
valid translated boxes supply the finite active-corner layer patches.  This is
the combined-window sibling of the ordinary-source valid-box endpoint.
-/
structure Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations :
    Prop where
  combinedActiveCornerWindows :
    TM0FoldedReduction.L2C2OriginZeroCombinedActiveCornerWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete decoded combined-window/valid-translated-box L2C2 Robinson target
through bounded-interior generated position-code rows at concrete numeric label
slots.

This is the generated-position sibling of
`Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations`.
-/
structure Figure13L2C2CombinedWindowValidTranslatedBoxBoundedRowsAtIndexObligations :
    Prop where
  combinedActiveCornerWindows :
    TM0FoldedReduction.L2C2OriginZeroCombinedActiveCornerWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceRows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/valid-translated-box L2C2 Robinson target through
the bounded-search fixed-start decoder and statement-list uniqueness.
-/
structure Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-board-level L2C2 Robinson/source target.

This is retained as a diagnostic theorem surface.  For the current Figure 13
transcription, positive Robinson board-level aligned macro-squares are
refuted by the raw `2 × 2` obstruction, so the proof-facing scaffold route
should use compatible Figure 18/layer-patch data instead.
-/
structure Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-board-level L2C2 Robinson target through
the bounded-search fixed-start decoder and statement-list uniqueness.
-/
structure Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-board-level L2C2 Robinson target through
the bounded-search fixed-start decoder for ordinary `programData`.

This is the ordinary-source certificate surface for the positive board-level
route and therefore does not require generated-position statement-list
uniqueness.
-/
structure Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete origin-zero-window/positive-board-level L2C2 Robinson target through
bounded-interior bounded-search rows for ordinary `programData`.

This diagnostic row-level surface is vacuous for the current Figure 13
transcription because the positive board-level macro-square assumption is
refuted.
-/
structure Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeBoundedRowsObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceBoundedRows : SourceSearchCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/positive-board-level L2C2 Robinson target through
bounded-interior bounded-search rows for ordinary `programData`.

This diagnostic row-level surface is vacuous for the current Figure 13
transcription because the positive board-level macro-square assumption is
refuted.
-/
structure Figure13L2C2CanonicalFreeSitePositiveBoardLevelAlignedMacroSquaresSearchCodeBoundedRowsObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceBoundedRows : SourceSearchCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/positive-board-level L2C2 Robinson target through
generated position-code bounded rows for `positionProgramData`.

This diagnostic generated-position row-level surface is vacuous for the current
Figure 13 transcription because the positive board-level macro-square
assumption is refuted.  The non-vacuous scaffold route should go through
compatible Figure 18/layer-patch data.
-/
structure Figure13L2C2CanonicalFreeSitePositiveBoardLevelAlignedMacroSquaresPositionCodeBoundedRowsObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceRows : SourcePositionCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/positive-board-level L2C2 Robinson target through
generated position-code bounded rows and statement-list uniqueness.

This is the older diagnostic positive-board route through the canonical
bounded-search row decoder.  It is vacuous for the current Figure 13
transcription because the positive board-level macro-square assumption is
refuted.
-/
structure Figure13L2C2CanonicalFreeSitePositiveBoardLevelAlignedMacroSquaresPositionCodeBoundedRowsWithNodupObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceRows : SourcePositionCodeBoundedInteriorRowsPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/positive-board-level L2C2 Robinson target through
generated position-code bounded rows and concrete started-TM1 support
uniqueness/disjointness.

This is the older diagnostic positive-board route through the support
disjointness bridge.  It is vacuous for the current Figure 13 transcription
because the positive board-level macro-square assumption is refuted.
-/
structure Figure13L2C2CanonicalFreeSitePositiveBoardLevelAlignedMacroSquaresPositionCodeBoundedRowsWithPairwiseDisjointObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceRows : SourcePositionCodeBoundedInteriorRowsPrimrec
  statementSupport_nodup : SourceStartedTM1StatementSupportNodup
  statementSupport_pairwiseDisjoint :
    SourceStartedTM1StatementSupportPairwiseDisjoint

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/layer-patch theorem-facing L2C2 Robinson/source
target.

This is the live Section 7 scaffold surface one step above the split
checked-stack/layer-patch target: canonical free-site active/corner recognition
supplies the checked origin-zero stacks, while layer patches remain the finite
Figure 13/Figure 16 realization witness.
-/
structure Figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/layer-patch L2C2 Robinson target through the
bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodupObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/layer-patch L2C2 Robinson target through the
bounded-search fixed-start decoder for ordinary `programData`.

Canonical free-site active/corner recognition supplies checked origin-zero
stacks, while layer patches stay explicit.  This route avoids generated
position-code statement-list uniqueness.
-/
structure Figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeStartObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/layer-patch theorem-facing L2C2
Robinson/source target.

This exposes the live scaffold surface with the canonical free-site routing
itself as the geometry field; the active/corner recognition used downstream is
derived from that routing.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/layer-patch L2C2 Robinson target through
the bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodupObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/layer-patch L2C2 Robinson target through
the bounded-search fixed-start decoder for ordinary `programData`.

The routing certificate is first converted to canonical active/corner
recognition, then to checked origin-zero stacks.  No generated-position
statement-list uniqueness bridge is required.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeStartObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/positive-box theorem-facing L2C2
Robinson/source target.

This exposes the Section 7 backward-realization obligation as positive
active-corner indexed boxes instead of prebuilt layer patches.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/positive-box L2C2 Robinson target through
the bounded-search descriptor decoder and statement-list uniqueness.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodupObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/positive-box L2C2 Robinson target through
the bounded-search fixed-start decoder for ordinary `programData`.

Routing supplies checked origin-zero stacks via canonical active/corner
recognition, and positive active-corner indexed boxes supply the finite patch
realization.  This is the low finite certificate surface on the ordinary-source
route.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/positive-box L2C2 Robinson target through
the bounded-search fixed-start decoder and statement-list uniqueness.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodupObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/positive-box L2C2 Robinson target through
the bounded-search fixed-start decoder and concrete started-TM1 support
uniqueness/disjointness.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjointObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec
  statementSupport_nodup : SourceStartedTM1StatementSupportNodup
  statementSupport_pairwiseDisjoint :
    SourceStartedTM1StatementSupportPairwiseDisjoint

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/valid-translated-box L2C2 Robinson target
through the bounded-search fixed-start decoder for ordinary `programData`.

Canonical free-site routing supplies the origin-zero active/corner windows,
valid translated boxes supply the active-corner layer patches, and the source
side avoids generated-position statement-list uniqueness.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStartObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/valid-translated-box L2C2 Robinson target
through generated bounded-interior position-code rows.

This is the live non-vacuous certificate surface closest to the current
scaffold proof: canonical free-site routing supplies the Figure 18 geometry,
valid translated boxes supply the active-corner layer patches, and the source
side is the bounded-row generated-position target.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceRows : SourcePositionCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/valid-translated-box L2C2 Robinson target
through generated bounded-interior position-code rows at concrete numeric label
slots.

This is the certificate-facing at-index sibling of
`Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsObligations`.
It exposes the same proof-facing scaffold target while keeping the machine side
at the generated-position bounded-row-at-index granularity.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndexObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceRows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site-routing/valid-translated-box L2C2 Robinson target
through generated interior position-code rows at concrete numeric label slots.

This exposes the current cleanest generated-position source target on the same
canonical-free-site valid-box scaffold surface as the bounded-at-index package.
-/
structure Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndexObligations :
    Prop where
  routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting
  validTranslatedBoxes :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes
  sourceRows : SourcePositionCodeInteriorRowsAtIndexPrimrec

/--
Concrete finite checked-stack/valid-translated-box theorem-facing L2C2
Robinson/source target.

This packages the finite scaffold work just before it is converted to the
Section 7 board/free-line translated-box data.
-/
structure Figure13L2C2CheckedStackValidTranslatedBoxSourceLabelIndexObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  sourceLabelIndex : SourcePositionCodeLabelIndexFromPrimrec

set_option linter.style.longLine false in
/--
Concrete finite checked-stack/valid-translated-box theorem-facing L2C2
Robinson/source target through the bounded-search descriptor decoder.
-/
structure Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeWithNodupObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  sourceSearch : SourceSearchCodeLabelIndexFromPrimrec
  statementList_nodup : SourceStatementListNodup

set_option linter.style.longLine false in
/--
Concrete finite checked-stack/valid-translated-box L2C2 Robinson target through
the bounded-search fixed-start decoder for ordinary `programData`.

This is the checked finite-scaffold valid-translated-box analogue of the
ordinary-source search-start endpoint and does not require statement-list
uniqueness.
-/
structure Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete finite checked-stack/valid-translated-box L2C2 Robinson target through
bounded-interior generated position-code rows at concrete numeric label slots.

This keeps the checked-stack valid-box scaffold package aligned with the
current generated-position source frontier.
-/
structure Figure13L2C2CheckedStackValidTranslatedBoxBoundedRowsAtIndexObligations :
    Prop where
  scaffold : TM0FoldedReduction.L2C2CheckedStackValidTranslatedBoxData
  sourceRows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec

set_option linter.style.longLine false in
/--
Concrete L2C2 canonical-free-site/Figure 16 compatibility target through the
bounded-search fixed-start decoder for ordinary `programData`.

This is a diagnostic surface for the current transcription: the Figure 16
compatible-level premise is formally refuted in `LeanWang.Final.Theorems`.
The live scaffold route should use checked-stack valid-translated-box data or
decoded combined-window valid boxes directly.
-/
structure Figure13L2C2Figure16CompatibleCanonicalFreeSiteSearchCodeStartObligations :
    Prop where
  canonicalActiveCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  compatibleLevelChecks :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Concrete L2C2 origin-zero/Figure 16 compatibility target through the
bounded-search fixed-start decoder for ordinary `programData`.

This is the origin-zero analogue of the direct Figure 16 compatibility
certificate surface and avoids generated-position statement-list uniqueness.
It is diagnostic for the current transcription because the Figure 16
compatible-level premise is formally refuted in `LeanWang.Final.Theorems`.
-/
structure Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  compatibleLevelChecks :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec


end LeanWang
