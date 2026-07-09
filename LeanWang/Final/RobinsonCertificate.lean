/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Final.SourceImplications

/-!
Final endpoints for bundled Robinson Figure 13 / Figure 18 scaffold certificates.

This small module keeps the public route from the theorem-facing Robinson
scaffold certificate to Wang-tile undecidability separate from the larger final
wrapper file.  It is intentionally thin: the geometric and source-side proof
content lives in the imported reduction modules.
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

Positive Robinson board-level aligned macro-squares are the live scaffold
construction surface; they are converted below to valid translated Figure 18
scaffold boxes.
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

This exposes the row-level source frontier directly for the live ordinary-source
positive board-level route.
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

Canonical free-site active/corner recognition supplies the origin-zero window
invariant, so this is the row-level positive-board route one scaffold step
closer to the local recognizability proof.
-/
structure Figure13L2C2CanonicalFreeSitePositiveBoardLevelAlignedMacroSquaresSearchCodeBoundedRowsObligations :
    Prop where
  activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner
  alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares
  sourceBoundedRows : SourceSearchCodeBoundedInteriorRowsPrimrec

set_option linter.style.longLine false in
/--
Concrete canonical-free-site/positive-board-level L2C2 Robinson target through
generated position-code bounded rows and statement-list uniqueness.

The source bridge below turns these generated position-code rows into the
ordinary bounded-search row target used by the positive-board route.
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

This is the lower source frontier for the generated-position bounded-row route:
the source statement-list uniqueness package is recovered from local
duplicate-freeness and pairwise disjointness of statement supports.
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
Concrete L2C2 canonical-free-site/Figure 16 compatibility target through the
bounded-search fixed-start decoder for ordinary `programData`.

This exposes the audited Figure 16 compatibility layer directly at the
certificate surface, before forgetting it to checked valid-translated boxes.
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
-/
structure Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations :
    Prop where
  originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows
  compatibleLevelChecks :
    TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelChecks
  sourceSearchStart : SourceSearchCodeLabelIndexStartPrimrec

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson Figure 13 / Figure 18
scaffold certificate and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    (C : NatSiteRobinsonScaffoldCertificate)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_figure13_robinson_certificate_position_source
    C source

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson Figure 13 / Figure 18
scaffold certificate and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    (C : NatSiteRobinsonScaffoldCertificate)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_figure13_robinson_certificate_position_source
    C source

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson scaffold certificate
and the fixed-start generated position-code source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateLabelIndexStart
    (C : NatSiteRobinsonScaffoldCertificate)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson scaffold certificate and the
fixed-start generated position-code source target.
-/
theorem domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateLabelIndexStart
    (C : NatSiteRobinsonScaffoldCertificate)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson scaffold certificate
and bounded interior generated position-code rows at label indices.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateBoundedRowsAtIndex
    (C : NatSiteRobinsonScaffoldCertificate)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson scaffold certificate and
bounded interior generated position-code rows at label indices.
-/
theorem domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateBoundedRowsAtIndex
    (C : NatSiteRobinsonScaffoldCertificate)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson scaffold certificate
and interior generated position-code rows at label indices.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateInteriorRowsAtIndex
    (C : NatSiteRobinsonScaffoldCertificate)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson scaffold certificate and
interior generated position-code rows at label indices.
-/
theorem domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateInteriorRowsAtIndex
    (C : NatSiteRobinsonScaffoldCertificate)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and generated-position source obligations.

This keeps the current finite Figure 13/Figure 16 layer-patch certificate as a
first-class final endpoint, instead of forcing callers to forget immediately to
the older realization-only Robinson certificate.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C.toScaffoldCertificate source

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    C.toScaffoldCertificate source

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and the fixed-start generated position-code source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateLabelIndexStart
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and the fixed-start generated position-code source target.
-/
theorem domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateLabelIndexStart
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and the source-specialized generated position-code label-index
decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSourceLabelIndexFrom
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and the source-specialized generated position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSourceLabelIndexFrom
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and bounded interior generated position-code rows at label indices.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateBoundedRowsAtIndex
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and bounded interior generated position-code rows at label indices.
-/
theorem domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateBoundedRowsAtIndex
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and interior generated position-code rows at label indices.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateInteriorRowsAtIndex
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from a bundled Robinson layer-patch scaffold
certificate and interior generated position-code rows at label indices.
-/
theorem domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateInteriorRowsAtIndex
    (C : NatSiteRobinsonLayerPatchScaffoldCertificate)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    C (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch scaffold package and generated-position source
obligations.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSource
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    O.toL2C2LayerPatchScaffoldCertificate source

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch scaffold package and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSource
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonLayerPatchScaffoldCertificateSource
    O.toL2C2LayerPatchScaffoldCertificate source

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch scaffold package and the source-specialized
generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSource
    O (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch scaffold package and the source-specialized generated
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSource
    O (TM0FoldedReduction.positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect
      hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch scaffold package, the bounded-search descriptor
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodup
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    O (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch scaffold package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodup
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    O (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch scaffold package, the bounded-search fixed-start
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodup
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    O (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hstart hnodup))

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch scaffold package, the bounded-search fixed-start decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodup
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    O (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hstart hnodup))

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch scaffold package, the bounded-search fixed-start
decoder, and concrete started-TM1 support uniqueness/disjointness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjoint
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodup
    O hstart
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch scaffold package, the bounded-search fixed-start decoder, and
concrete started-TM1 support uniqueness/disjointness.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjoint
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodup
    O hstart
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and the source-specialized generated
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_sourceCodeCorrect
    data hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and the source-specialized generated
position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_sourceCodeCorrect
    data hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package, the bounded-search descriptor
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodup
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    data (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package, the bounded-search descriptor
decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodup
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    data (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package, the bounded-search fixed-start
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodup
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    data (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hstart hnodup))

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package, the bounded-search fixed-start
decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodup
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    data (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hstart hnodup))

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package, the bounded-search fixed-start
decoder, and concrete started-TM1 support uniqueness/disjointness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjoint
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodup
    data hstart
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package, the bounded-search fixed-start
decoder, and concrete started-TM1 support uniqueness/disjointness.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjoint
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodup
    data hstart
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated one-row position-code
rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRows
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_oneRowsCorrect
    data hrows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated one-row position-code
rows.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRows
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_oneRowsCorrect
    data hrows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated bounded-interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRows
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsCorrect
    data hrows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated bounded-interior
position-code rows.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRows
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsCorrect
    data hrows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated one-row position-code
rows at concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndex
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
    data
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated one-row position-code
rows at concrete numeric label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndex
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
    data
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated bounded-interior
position-code rows at concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndex
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    data hrows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated bounded-interior
position-code rows at concrete numeric label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndex
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    data hrows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated interior position-code
rows at concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndex
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
    data
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and generated interior position-code
rows at concrete numeric label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndex
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
    data
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 checked-stack /
layer-patch scaffold package and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2Section7BoardFreeLineLayerPatchObligationsOfCheckedStackLayerPatchData
      scaffold)
    hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 checked-stack / layer-patch
scaffold package and the source-specialized generated position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    (scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2Section7BoardFreeLineLayerPatchObligationsOfCheckedStackLayerPatchData
      scaffold)
    hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 checked-stack /
layer-patch scaffold package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSearchCodeWithNodup
    (scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    scaffold (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 checked-stack / layer-patch
scaffold package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSearchCodeWithNodup
    (scaffold : TM0FoldedReduction.L2C2CheckedStackLayerPatchData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    scaffold (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from split checked origin-zero stacks,
active-corner layer patches, and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    { checkedStacks := checkedStacks, patches := layerPatches }
    hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from split checked origin-zero stacks, active-corner
layer patches, and the source-specialized generated position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    (checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    { checkedStacks := checkedStacks, patches := layerPatches }
    hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from split checked origin-zero stacks,
active-corner layer patches, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodup
    (checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    checkedStacks layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from split checked origin-zero stacks, active-corner
layer patches, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodup
    (checkedStacks : TM0FoldedReduction.L2C2OriginZeroCheckedStacks)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    checkedStacks layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
active-corner layer patches, and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfOriginZeroWindows
      originZeroWindows)
    layerPatches hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, active-corner
layer patches, and the source-specialized generated position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfOriginZeroWindows
      originZeroWindows)
    layerPatches hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
active-corner layer patches, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    originZeroWindows layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows,
active-corner layer patches, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    originZeroWindows layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
positive active-corner indexed boxes, and the source-specialized generated
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    originZeroWindows
    (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfPositiveBoxes
      positiveBoxes)
    hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, positive
active-corner indexed boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    originZeroWindows
    (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfPositiveBoxes
      positiveBoxes)
    hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
positive active-corner indexed boxes, the bounded-search descriptor decoder,
and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexFrom
    originZeroWindows positiveBoxes
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, positive
active-corner indexed boxes, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexFrom
    originZeroWindows positiveBoxes
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
valid translated boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    originZeroWindows
    (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, valid
translated boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    originZeroWindows
    (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
      validTranslatedBoxes)
    hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
valid translated boxes, and the bounded-search fixed-start decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows validTranslatedBoxes
    (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hsearch hnodup))

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, valid
translated boxes, and the bounded-search fixed-start decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows validTranslatedBoxes
    (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hsearch hnodup))

set_option linter.style.longLine false in
/--
Positive Robinson board-level aligned macro-squares provide valid translated
boxes for the concrete L2C2 Figure 18 scaffold.
-/
def figure13L2C2ValidTranslatedBoxesOfRobinsonPositiveBoardLevelAlignedMacroSquares
    (hlevel : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares) :
    TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes := by
  simpa [TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes,
    TM0FoldedReduction.L2C2Figure18ScaffoldTiles] using
    Figure18ScaffoldData.positiveTranslatedValidBoxes_ofFigure18ScaffoldTileableBoxes
      l2Component2Figure18ScaffoldData
      (fun r _hr =>
        tileableBoxes_of_compatibleFigure18ScaffoldSquares
          (compatibleFigure18ScaffoldSquares_of_robinsonPositiveBoardLevelAlignedMacroSquares
            hlevel) r)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
positive Robinson board-level aligned macro-squares, and the source-specialized
generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows
    (figure13L2C2ValidTranslatedBoxesOfRobinsonPositiveBoardLevelAlignedMacroSquares
      alignedMacroSquares)
    hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, positive
Robinson board-level aligned macro-squares, and the source-specialized
generated position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexFrom
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows
    (figure13L2C2ValidTranslatedBoxesOfRobinsonPositiveBoardLevelAlignedMacroSquares
      alignedMacroSquares)
    hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
positive Robinson board-level aligned macro-squares, and the bounded-search
fixed-start decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexFrom
    originZeroWindows alignedMacroSquares
    (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hsearch hnodup))

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, positive
Robinson board-level aligned macro-squares, and the bounded-search fixed-start
decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodup
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (alignedMacroSquares : HasFigure13RobinsonPositiveBoardLevelAlignedMacroSquares)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexFrom
    originZeroWindows alignedMacroSquares
    (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart hsearch hnodup))

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site active/corner
recognition, active-corner layer patches, and the source-specialized generated
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    (activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner
      activeCorner)
    layerPatches hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site active/corner recognition,
active-corner layer patches, and the source-specialized generated position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    (activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner
      activeCorner)
    layerPatches hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site active/corner
recognition, active-corner layer patches, the bounded-search descriptor
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodup
    (activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    activeCorner layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site active/corner recognition,
active-corner layer patches, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodup
    (activeCorner : TM0FoldedReduction.L2C2CanonicalFreeSiteRectActiveCorner)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    activeCorner layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing,
active-corner layer patches, and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2CanonicalFreeSiteRectActiveCornerOfRouting routing)
    layerPatches hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, active-corner layer
patches, and the source-specialized generated position-code label-index
decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    (TM0FoldedReduction.l2c2CanonicalFreeSiteRectActiveCornerOfRouting routing)
    layerPatches hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing,
active-corner layer patches, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodup
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    routing layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, active-corner layer
patches, the bounded-search descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodup
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (layerPatches : TM0FoldedReduction.L2C2ActiveCornerLayerPatches)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    routing layerPatches
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    routing
    (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfPositiveBoxes
      positiveBoxes)
    hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, and the source-specialized generated position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    routing
    (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfPositiveBoxes
      positiveBoxes)
    hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodup
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    routing positiveBoxes
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodup
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    routing positiveBoxes
    (sourceLabelIndexPrimrec_of_searchCodeLabelIndex hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, the bounded-search fixed-start decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodup
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    routing positiveBoxes
    (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
        hsearch hnodup))

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, the bounded-search fixed-start decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodup
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    routing positiveBoxes
    (sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
        hsearch hnodup))

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, the bounded-search fixed-start decoder, and
concrete started-TM1 support uniqueness/disjointness.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjoint
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodup
    routing positiveBoxes hsearch
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, positive
active-corner indexed boxes, the bounded-search fixed-start decoder, and
concrete started-TM1 support uniqueness/disjointness.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjoint
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (positiveBoxes : Figure13L2C2PositiveActiveCornerIndexedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodup
    routing positiveBoxes hsearch
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the Section 7 tower/indexed-box
Robinson scaffold obligations and generated-position source obligations.

This exposes the proof-facing scaffold package directly, avoiding an explicit
detour through `NatSiteRobinsonScaffoldCertificate` at theorem use sites.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSource
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    O.toScaffoldCertificate source

set_option linter.style.longLine false in
/--
Wang domino undecidability from the Section 7 tower/indexed-box Robinson
scaffold obligations and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSource
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateSource
    O.toScaffoldCertificate source

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the Section 7 tower/indexed-box
Robinson scaffold obligations and the fixed-start generated position-code
source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSource
    O (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the Section 7 tower/indexed-box Robinson
scaffold obligations and the fixed-start generated position-code source target.
-/
theorem domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSource
    O (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the Section 7 tower/indexed-box
Robinson scaffold obligations and the source-specialized generated
position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSourceLabelIndexFrom
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    O (sourceLabelIndexStartPrimrec_of_sourceLabelIndex hindex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the Section 7 tower/indexed-box Robinson
scaffold obligations and the source-specialized generated position-code
label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSourceLabelIndexFrom
    {activeSiteSpecs : List (Nat × Quadrant)}
    {activeSiteSpecs_valid :
      Figure18Site.natSpecsValidBool activeSiteSpecs = true}
    {cornerIndex : Nat} {cornerQuadrant : Quadrant}
    {cornerIndex_valid : decide (cornerIndex < 92) = true}
    (O : NatSiteRobinsonTowerIndexedBoxObligations activeSiteSpecs
      activeSiteSpecs_valid cornerIndex cornerQuadrant cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    O (sourceLabelIndexStartPrimrec_of_sourceLabelIndex hindex)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 canonical
free-site-rectangle/translated-positive-box Robinson scaffold obligations and
the fixed-start generated position-code source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxLabelIndexStart
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    O.toL2C2TowerIndexedBoxObligations hstart

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 canonical
free-site-rectangle/translated-positive-box Robinson scaffold obligations and
the fixed-start generated position-code source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxLabelIndexStart
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    O.toL2C2TowerIndexedBoxObligations hstart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 canonical
free-site-rectangle/translated-positive-box Robinson scaffold obligations and
the source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourceLabelIndexFrom
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSourceLabelIndexFrom
    O.toL2C2TowerIndexedBoxObligations hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 canonical
free-site-rectangle/translated-positive-box Robinson scaffold obligations and
the source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourceLabelIndexFrom
    (O : NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSourceLabelIndexFrom
    O.toL2C2TowerIndexedBoxObligations hindex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 origin-zero
active/corner-window plus translated-positive-box Robinson scaffold obligations
and the source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxSourceLabelIndexFrom
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSourceLabelIndexFrom
    O.toL2C2TowerIndexedBoxObligations hindex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 origin-zero active/corner
window plus translated-positive-box Robinson scaffold obligations and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxSourceLabelIndexFrom
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsSourceLabelIndexFrom
    O.toL2C2TowerIndexedBoxObligations hindex

namespace Figure13L2C2OriginZeroSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the current concrete L2C2
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxSourceLabelIndexFrom
    O.scaffold O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the current concrete L2C2 Robinson/source
obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxSourceLabelIndexFrom
    O.scaffold O.sourceLabelIndex

end Figure13L2C2OriginZeroSourceLabelIndexObligations

namespace Figure13L2C2Section7BoardFreeLineTranslatedBoxSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line translated-box Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
    O.section7 O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
translated-box Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
    O.section7 O.sourceLabelIndex

end Figure13L2C2Section7BoardFreeLineTranslatedBoxSourceLabelIndexObligations

namespace Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line translated-box Robinson package, the bounded-search descriptor
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_searchCodeWithNodupCorrect
    O.section7 O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
translated-box Robinson package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_translated_box_data_searchCodeWithNodupCorrect
    O.section7 O.sourceSearch O.statementList_nodup

end Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeWithNodupObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    O.section7 O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexFrom
    O.section7 O.sourceLabelIndex

end Figure13L2C2Section7BoardFreeLineLayerPatchSourceLabelIndexObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch Robinson package, the bounded-search descriptor
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodup
    O.section7 O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch Robinson package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodup
    O.section7 O.sourceSearch O.statementList_nodup

end Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeWithNodupObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch Robinson package, the bounded-search fixed-start
decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodup
    O.section7 O.sourceSearchStart O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch Robinson package, the bounded-search fixed-start decoder, and
statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodup
    O.section7 O.sourceSearchStart O.statementList_nodup

end Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodupObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjointObligations

set_option linter.style.longLine false in
/--
Project the pairwise-disjoint support package to the statement-list `Nodup`
package.
-/
def toSearchCodeStartWithNodupObligations
    (O :
      Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjointObligations) :
    Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithNodupObligations where
  section7 := O.section7
  sourceSearchStart := O.sourceSearchStart
  statementList_nodup :=
    sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      O.statementSupport_nodup O.statementSupport_pairwiseDisjoint

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line layer-patch Robinson package, the bounded-search fixed-start
decoder, and concrete started-TM1 support uniqueness/disjointness.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjointObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toSearchCodeStartWithNodupObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch Robinson package, the bounded-search fixed-start decoder, and
concrete started-TM1 support uniqueness/disjointness.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjointObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toSearchCodeStartWithNodupObligations.domino_problem_undecidable

end Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartWithPairwiseDisjointObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    O.section7 O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexFrom
    O.section7 O.sourceLabelIndex

end Figure13L2C2Section7BoardFreeLineLayerPatchDataSourceLabelIndexObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package, the bounded-search
descriptor decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodup
    O.section7 O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package, the bounded-search
descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodup
    O.section7 O.sourceSearch O.statementList_nodup

end Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeWithNodupObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package, the bounded-search
fixed-start decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodup
    O.section7 O.sourceSearchStart O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package, the bounded-search
fixed-start decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodup
    O.section7 O.sourceSearchStart O.statementList_nodup

end Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodupObligations

set_option linter.style.longLine false
namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjointObligations

set_option linter.style.longLine false in
/--
Project the pairwise-disjoint support package to the statement-list `Nodup`
package.
-/
def toSearchCodeStartWithNodupObligations
    (O :
      Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjointObligations) :
    Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithNodupObligations where
  section7 := O.section7
  sourceSearchStart := O.sourceSearchStart
  statementList_nodup :=
    sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      O.statementSupport_nodup O.statementSupport_pairwiseDisjoint

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package, the bounded-search
fixed-start decoder, and concrete started-TM1 support uniqueness/disjointness.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjointObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toSearchCodeStartWithNodupObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package, the bounded-search
fixed-start decoder, and concrete started-TM1 support uniqueness/disjointness.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjointObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toSearchCodeStartWithNodupObligations.domino_problem_undecidable

end Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartWithPairwiseDisjointObligations
set_option linter.style.longLine true

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package and generated one-row
position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRows
    O.section7 O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package and generated one-row
position-code rows.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRows
    O.section7 O.sourceRows

end Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package and generated
bounded-interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRows
    O.section7 O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data Robinson package and generated
bounded-interior position-code rows.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRows
    O.section7 O.sourceRows

end Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7 layer-patch
data package and generated one-row position-code rows at label indices.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndex
    O.section7 O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 layer-patch data
package and generated one-row position-code rows at label indices.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndex
    O.section7 O.sourceRows

end Figure13L2C2Section7BoardFreeLineLayerPatchDataOneRowsAtIndexObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7 layer-patch
data package and generated bounded-interior position-code rows at label
indices.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndex
    O.section7 O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 layer-patch data
package and generated bounded-interior position-code rows at label indices.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndex
    O.section7 O.sourceRows

end Figure13L2C2Section7BoardFreeLineLayerPatchDataBoundedRowsAtIndexObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7 layer-patch
data package and generated interior position-code rows at label indices.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndex
    O.section7 O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 layer-patch data
package and generated interior position-code rows at label indices.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndex
    O.section7 O.sourceRows

end Figure13L2C2Section7BoardFreeLineLayerPatchDataInteriorRowsAtIndexObligations

namespace Figure13L2C2CheckedStackLayerPatchSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 checked-stack /
layer-patch Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStackLayerPatchSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    O.scaffold O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 checked-stack / layer-patch
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStackLayerPatchSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSourceLabelIndexFrom
    O.scaffold O.sourceLabelIndex

end Figure13L2C2CheckedStackLayerPatchSourceLabelIndexObligations

namespace Figure13L2C2CheckedStackLayerPatchSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 checked-stack /
layer-patch Robinson package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStackLayerPatchSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSearchCodeWithNodup
    O.scaffold O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 checked-stack / layer-patch
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStackLayerPatchSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStackLayerPatchDataSearchCodeWithNodup
    O.scaffold O.sourceSearch O.statementList_nodup

end Figure13L2C2CheckedStackLayerPatchSearchCodeWithNodupObligations

namespace Figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack/layer-patch
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    O.checkedStacks O.layerPatches O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack/layer-patch
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexFrom
    O.checkedStacks O.layerPatches O.sourceLabelIndex

end Figure13L2C2CheckedStacksAndLayerPatchesSourceLabelIndexObligations

namespace Figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack/layer-patch
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodup
    O.checkedStacks O.layerPatches O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack/layer-patch Robinson
package, the bounded-search descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodup
    O.checkedStacks O.layerPatches O.sourceSearch O.statementList_nodup

end Figure13L2C2CheckedStacksAndLayerPatchesSearchCodeWithNodupObligations

namespace Figure13L2C2OriginZeroLayerPatchesSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/layer-patch
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    O.originZeroWindows O.layerPatches O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/layer-patch
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSourceLabelIndexFrom
    O.originZeroWindows O.layerPatches O.sourceLabelIndex

end Figure13L2C2OriginZeroLayerPatchesSourceLabelIndexObligations

namespace Figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/layer-patch
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodup
    O.originZeroWindows O.layerPatches O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/layer-patch Robinson
package, the bounded-search descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodup
    O.originZeroWindows O.layerPatches O.sourceSearch O.statementList_nodup

end Figure13L2C2OriginZeroLayerPatchesSearchCodeWithNodupObligations

namespace Figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/positive-box
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexFrom
    O.originZeroWindows O.positiveBoxes O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/positive-box
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexFrom
    O.originZeroWindows O.positiveBoxes O.sourceLabelIndex

end Figure13L2C2OriginZeroPositiveBoxesSourceLabelIndexObligations

namespace Figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/positive-box
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodup
    O.originZeroWindows O.positiveBoxes O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/positive-box Robinson
package, the bounded-search descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodup
    O.originZeroWindows O.positiveBoxes O.sourceSearch O.statementList_nodup

end Figure13L2C2OriginZeroPositiveBoxesSearchCodeWithNodupObligations

namespace Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/valid-box
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    O.originZeroWindows O.validTranslatedBoxes O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/valid-box
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    O.originZeroWindows O.validTranslatedBoxes O.sourceLabelIndex

end Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations

namespace Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations

set_option linter.style.longLine false in
/-- Project the fixed-start valid-box package to the source-label package. -/
def toSourceLabelIndexObligations
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations) :
    Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations where
  originZeroWindows := O.originZeroWindows
  validTranslatedBoxes := O.validTranslatedBoxes
  sourceLabelIndex :=
    sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
        O.sourceSearchStart O.statementList_nodup)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/valid-box
Robinson package and the bounded-search fixed-start decoder.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toSourceLabelIndexObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/valid-box Robinson
package and the bounded-search fixed-start decoder.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toSourceLabelIndexObligations.domino_problem_undecidable

end Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations

set_option linter.style.longLine false
namespace Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Project the positive-board-level scaffold certificate to the valid-translated
box certificate package.
-/
def toOriginZeroValidTranslatedBoxSourceLabelIndexObligations
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations) :
    Figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexObligations where
  originZeroWindows := O.originZeroWindows
  validTranslatedBoxes :=
    figure13L2C2ValidTranslatedBoxesOfRobinsonPositiveBoardLevelAlignedMacroSquares
      O.alignedMacroSquares
  sourceLabelIndex := O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/positive-board
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toOriginZeroValidTranslatedBoxSourceLabelIndexObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/positive-board
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toOriginZeroValidTranslatedBoxSourceLabelIndexObligations
    |>.domino_problem_undecidable

end Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations
set_option linter.style.longLine true

set_option linter.style.longLine false
namespace Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations

set_option linter.style.longLine false in
/-- Project the fixed-start positive-board certificate to the source-label package. -/
def toSourceLabelIndexObligations
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations) :
    Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSourceLabelIndexObligations where
  originZeroWindows := O.originZeroWindows
  alignedMacroSquares := O.alignedMacroSquares
  sourceLabelIndex :=
    sourceLabelIndexPrimrec_of_labelIndexStart
      (sourceLabelIndexStartPrimrec_of_searchCodeLabelIndexStart
        O.sourceSearchStart O.statementList_nodup)

set_option linter.style.longLine false in
/--
Project the fixed-start positive-board certificate to the fixed-start valid-box
certificate package.
-/
def toOriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations) :
    Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartWithNodupObligations where
  originZeroWindows := O.originZeroWindows
  validTranslatedBoxes :=
    figure13L2C2ValidTranslatedBoxesOfRobinsonPositiveBoardLevelAlignedMacroSquares
      O.alignedMacroSquares
  sourceSearchStart := O.sourceSearchStart
  statementList_nodup := O.statementList_nodup

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/positive-board
Robinson package and the bounded-search fixed-start decoder.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toSourceLabelIndexObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/positive-board Robinson
package and the bounded-search fixed-start decoder.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toSourceLabelIndexObligations.domino_problem_undecidable

end Figure13L2C2OriginZeroPositiveBoardLevelAlignedMacroSquaresSearchCodeStartWithNodupObligations
set_option linter.style.longLine true

namespace Figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site/layer-patch
Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    O.activeCorner O.layerPatches O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site/layer-patch
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexFrom
    O.activeCorner O.layerPatches O.sourceLabelIndex

end Figure13L2C2CanonicalFreeSiteLayerPatchesSourceLabelIndexObligations

namespace Figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site/layer-patch
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodup
    O.activeCorner O.layerPatches O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site/layer-patch Robinson
package, the bounded-search descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodup
    O.activeCorner O.layerPatches O.sourceSearch O.statementList_nodup

end Figure13L2C2CanonicalFreeSiteLayerPatchesSearchCodeWithNodupObligations

namespace Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
layer-patch Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    O.routing O.layerPatches O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / layer-patch
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexFrom
    O.routing O.layerPatches O.sourceLabelIndex

end Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSourceLabelIndexObligations

namespace Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
layer-patch Robinson package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodup
    O.routing O.layerPatches O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / layer-patch
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodup
    O.routing O.layerPatches O.sourceSearch O.statementList_nodup

end Figure13L2C2CanonicalFreeSiteRoutingLayerPatchesSearchCodeWithNodupObligations

namespace Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
positive-box Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    O.routing O.positiveBoxes O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / positive-box
Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexFrom
    O.routing O.positiveBoxes O.sourceLabelIndex

end Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSourceLabelIndexObligations

namespace Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
positive-box Robinson package, the bounded-search descriptor decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodup
    O.routing O.positiveBoxes O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / positive-box
Robinson package, the bounded-search descriptor decoder, and statement-list
uniqueness.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodup
    O.routing O.positiveBoxes O.sourceSearch O.statementList_nodup

end Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeWithNodupObligations

namespace Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
positive-box Robinson package, the bounded-search fixed-start decoder, and
statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodup
    O.routing O.positiveBoxes O.sourceSearchStart O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / positive-box
Robinson package, the bounded-search fixed-start decoder, and statement-list
uniqueness.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodup
    O.routing O.positiveBoxes O.sourceSearchStart O.statementList_nodup

end Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodupObligations

set_option linter.style.longLine false
namespace Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjointObligations

set_option linter.style.longLine false in
/--
Project the pairwise-disjoint support package to the statement-list `Nodup`
package.
-/
def toSearchCodeStartWithNodupObligations
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjointObligations) :
    Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithNodupObligations where
  routing := O.routing
  positiveBoxes := O.positiveBoxes
  sourceSearchStart := O.sourceSearchStart
  statementList_nodup :=
    sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      O.statementSupport_nodup O.statementSupport_pairwiseDisjoint

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
positive-box Robinson package, the bounded-search fixed-start decoder, and
concrete started-TM1 support uniqueness/disjointness.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjointObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toSearchCodeStartWithNodupObligations.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / positive-box
Robinson package, the bounded-search fixed-start decoder, and concrete
started-TM1 support uniqueness/disjointness.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjointObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toSearchCodeStartWithNodupObligations.domino_problem_undecidable

end Figure13L2C2CanonicalFreeSiteRoutingPositiveBoxesSearchCodeStartWithPairwiseDisjointObligations
set_option linter.style.longLine true

namespace Figure13L2C2CheckedStackValidTranslatedBoxSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 finite
checked-stack/valid-translated-box Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
    O.scaffold O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 finite
checked-stack/valid-translated-box Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
    O.scaffold O.sourceLabelIndex

end Figure13L2C2CheckedStackValidTranslatedBoxSourceLabelIndexObligations

namespace Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeWithNodupObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 finite
checked-stack/valid-translated-box Robinson package, the bounded-search
descriptor decoder, and statement-list uniqueness.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_searchCodeWithNodupCorrect
    O.scaffold O.sourceSearch O.statementList_nodup

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 finite
checked-stack/valid-translated-box Robinson package, the bounded-search
descriptor decoder, and statement-list uniqueness.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeWithNodupObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_searchCodeWithNodupCorrect
    O.scaffold O.sourceSearch O.statementList_nodup

end Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeWithNodupObligations

end LeanWang
