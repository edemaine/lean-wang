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
