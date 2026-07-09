/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Final.RobinsonCertificate.Structures

/-!
Final endpoints for bundled Robinson Figure 13 / Figure 18 scaffold certificates.

This small module keeps the public route from the theorem-facing Robinson
scaffold certificate to Wang-tile undecidability separate from the larger final
wrapper file.  The geometric and source-side proof content lives in imported
reduction modules, while the obligation structures are isolated in
`LeanWang.Final.RobinsonCertificate.Structures`.
-/

namespace LeanWang

open OllingerRobinson
open OllingerRobinson.Figure13Layers
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

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
board/free-line layer-patch scaffold package and the bounded-search fixed-start
decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStart
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_scaffold_source
    l2Component2Figure18ScaffoldData.scaffold
    (TM0FoldedReduction.l2c2IsScaffoldOfRobinsonSection7BoardFreeLineLayerPatchData
      { boardFreeLineActiveCorner := O.boardFreeLineActiveCorner
        patches := O.patches })
    (TM0FoldedReduction.sourceObligationsOfSearchCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
layer-patch scaffold package and the bounded-search fixed-start decoder for
ordinary `programData`.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStart
    (O : NatSiteRobinsonSection7BoardFreeLineLayerPatchObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_scaffold_source
    l2Component2Figure18ScaffoldData.scaffold
    (TM0FoldedReduction.l2c2IsScaffoldOfRobinsonSection7BoardFreeLineLayerPatchData
      { boardFreeLineActiveCorner := O.boardFreeLineActiveCorner
        patches := O.patches })
    (TM0FoldedReduction.sourceObligationsOfSearchCodeLabelIndexStartCorrect
      hstart)

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
board/free-line layer-patch data package and the fixed-start source-level
generated position-code decoder.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStart
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_scaffold_position_source
    l2Component2Figure18ScaffoldData.scaffold
    (TM0FoldedReduction.l2c2IsScaffoldOfRobinsonSection7BoardFreeLineLayerPatchData
      data)
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and the fixed-start source-level
generated position-code decoder.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStart
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_scaffold_position_source
    l2Component2Figure18ScaffoldData.scaffold
    (TM0FoldedReduction.l2c2IsScaffoldOfRobinsonSection7BoardFreeLineLayerPatchData
      data)
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and the bounded-search fixed-start
decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_of_scaffold_source
    l2Component2Figure18ScaffoldData.scaffold
    (TM0FoldedReduction.l2c2IsScaffoldOfRobinsonSection7BoardFreeLineLayerPatchData
      data)
    (TM0FoldedReduction.sourceObligationsOfSearchCodeLabelIndexStartCorrect
      hstart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact concrete L2C2 Section 7
board/free-line layer-patch data package and the bounded-search fixed-start
decoder for ordinary `programData`.
-/
theorem domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    (data : TM0FoldedReduction.L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_of_scaffold_source
    l2Component2Figure18ScaffoldData.scaffold
    (TM0FoldedReduction.l2c2IsScaffoldOfRobinsonSection7BoardFreeLineLayerPatchData
      data)
    (TM0FoldedReduction.sourceObligationsOfSearchCodeLabelIndexStartCorrect
      hstart)

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
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsAtIndexCorrect
    data hrows

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
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsAtIndexCorrect
    data hrows

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
valid translated boxes, and interior generated position-code rows at concrete
numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndex
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows validTranslatedBoxes
    (sourceLabelIndexPrimrec_of_interiorRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, valid
translated boxes, and interior generated position-code rows at concrete numeric
label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndex
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows validTranslatedBoxes
    (sourceLabelIndexPrimrec_of_interiorRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
valid translated boxes, and bounded-interior generated position-code rows at
concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndex
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows validTranslatedBoxes
    (sourceLabelIndexPrimrec_of_boundedInteriorRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, valid
translated boxes, and bounded-interior generated position-code rows at concrete
numeric label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndex
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSourceLabelIndexFrom
    originZeroWindows validTranslatedBoxes
    (sourceLabelIndexPrimrec_of_boundedInteriorRowsAtIndex hrows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
valid translated boxes, and the bounded-search fixed-start decoder for
ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    (TM0FoldedReduction.l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfOriginZeroWindows
        originZeroWindows)
      (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
        validTranslatedBoxes))
    hsearch

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, valid
translated boxes, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    (originZeroWindows : TM0FoldedReduction.L2C2OriginZeroWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    (TM0FoldedReduction.l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfOriginZeroWindows
        originZeroWindows)
      (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
        validTranslatedBoxes))
    hsearch

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from decoded origin-zero active/corner
combined windows, valid translated boxes, and the bounded-search fixed-start
decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStart
    (combinedActiveCornerWindows :
      TM0FoldedReduction.L2C2OriginZeroCombinedActiveCornerWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    (TM0FoldedReduction.l2c2OriginZeroWindowsOfCombinedActiveCornerWindows
      combinedActiveCornerWindows)
    validTranslatedBoxes
    hsearch

set_option linter.style.longLine false in
/--
Wang domino undecidability from decoded origin-zero active/corner combined
windows, valid translated boxes, and the bounded-search fixed-start decoder for
ordinary `programData`.
-/
theorem domino_problem_undecidable_of_figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStart
    (combinedActiveCornerWindows :
      TM0FoldedReduction.L2C2OriginZeroCombinedActiveCornerWindows)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    (TM0FoldedReduction.l2c2OriginZeroWindowsOfCombinedActiveCornerWindows
      combinedActiveCornerWindows)
    validTranslatedBoxes
    hsearch

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
Positive Robinson board-level aligned macro-squares, if supplied, imply valid
translated boxes for the concrete L2C2 Figure 18 scaffold.  The premise is
refuted for the current Figure 13 transcription, so this remains a diagnostic
implication rather than a proof-facing construction route.
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
Encoded Wang domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and the bounded-search fixed-start decoder for
ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStart
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    (TM0FoldedReduction.l2c2OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      (TM0FoldedReduction.l2c2CanonicalFreeSiteRectActiveCornerOfRouting
        routing))
    validTranslatedBoxes
    hsearch

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, valid translated
scaffold boxes, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStart
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hsearch : SourceSearchCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    (TM0FoldedReduction.l2c2OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      (TM0FoldedReduction.l2c2CanonicalFreeSiteRectActiveCornerOfRouting
        routing))
    validTranslatedBoxes
    hsearch

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and generated bounded-interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRows
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsCorrect
    routing validTranslatedBoxes hrows

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, valid translated
scaffold boxes, and generated bounded-interior position-code rows.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRows
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsCorrect
    routing validTranslatedBoxes hrows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and bounded-interior generated position-code rows at
concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndex
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsAtIndexCorrect
    routing validTranslatedBoxes hrows

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, valid translated
scaffold boxes, and bounded-interior generated position-code rows at concrete
numeric label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndex
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_boundedRowsAtIndexCorrect
    routing validTranslatedBoxes hrows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical free-site routing, valid
translated scaffold boxes, and interior generated position-code rows at
concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndex
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_interiorRowsAtIndexCorrect
    routing validTranslatedBoxes hrows

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical free-site routing, valid translated
scaffold boxes, and interior generated position-code rows at concrete numeric
label slots.
-/
theorem domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndex
    (routing : TM0FoldedReduction.L2C2CanonicalFreeSiteRectRouting)
    (validTranslatedBoxes :
      TM0FoldedReduction.L2C2Figure18ScaffoldValidTranslatedBoxes)
    (hrows : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_canonical_free_site_routing_valid_translated_boxes_interiorRowsAtIndexCorrect
    routing validTranslatedBoxes hrows

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

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 origin-zero
active/corner-window plus translated-positive-box Robinson scaffold obligations
and the fixed-start generated position-code source target.
-/
theorem encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxCertificateLabelIndexStart
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
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
Wang domino undecidability from the concrete L2C2 origin-zero active/corner
window plus translated-positive-box Robinson scaffold obligations and the
fixed-start generated position-code source target.
-/
theorem domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxCertificateLabelIndexStart
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonTowerIndexedBoxObligationsLabelIndexStart
    O.toL2C2TowerIndexedBoxObligations hstart

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

namespace Figure13L2C2OriginZeroSourceLabelIndexStartObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 origin-zero
translated-positive-box Robinson/source fixed-start obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceLabelIndexStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxCertificateLabelIndexStart
    O.scaffold O.sourceLabelIndexStart

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 origin-zero
translated-positive-box Robinson/source fixed-start obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceLabelIndexStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroTranslatedPositiveBoxCertificateLabelIndexStart
    O.scaffold O.sourceLabelIndexStart

end Figure13L2C2OriginZeroSourceLabelIndexStartObligations

namespace Figure13L2C2OriginZeroSourceBoundedRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 origin-zero
translated-positive-box Robinson/source row-at-index obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateBoundedRowsAtIndex
    (O.scaffold.toL2C2TowerIndexedBoxObligations).toScaffoldCertificate
    O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 origin-zero
translated-positive-box Robinson/source row-at-index obligation package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateBoundedRowsAtIndex
    (O.scaffold.toL2C2TowerIndexedBoxObligations).toScaffoldCertificate
    O.sourceRows

end Figure13L2C2OriginZeroSourceBoundedRowsAtIndexObligations

namespace Figure13L2C2OriginZeroSourceInteriorRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 origin-zero
translated-positive-box Robinson/source interior-row-at-index obligation
package.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateInteriorRowsAtIndex
    (O.scaffold.toL2C2TowerIndexedBoxObligations).toScaffoldCertificate
    O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 origin-zero
translated-positive-box Robinson/source interior-row-at-index obligation
package.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroSourceInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13RobinsonScaffoldCertificateInteriorRowsAtIndex
    (O.scaffold.toL2C2TowerIndexedBoxObligations).toScaffoldCertificate
    O.sourceRows

end Figure13L2C2OriginZeroSourceInteriorRowsAtIndexObligations

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

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataSourceLabelIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and the source-specialized generated position-code
label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataSourceLabelIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7 O.sourceLabelIndex

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and the source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataSourceLabelIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7 O.sourceLabelIndex

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataSourceLabelIndexObligations

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataLabelIndexStartObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and the fixed-start source-level position-code
decoder.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataLabelIndexStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_labelIndexStart O.sourceLabelIndexStart)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and the fixed-start source-level position-code decoder.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataLabelIndexStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_labelIndexStart O.sourceLabelIndexStart)

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataLabelIndexStartObligations

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataRowsObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataRowsObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_interiorRows O.sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and generated interior position-code rows.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataRowsObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_interiorRows O.sourceRows)

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataRowsObligations

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataOneRowsObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and generated one-row position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataOneRowsObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_oneRows O.sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and generated one-row position-code rows.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataOneRowsObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_oneRows O.sourceRows)

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataOneRowsObligations

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataBoundedRowsObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and generated bounded-interior position-code rows.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataBoundedRowsObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_boundedInteriorRows O.sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and generated bounded-interior position-code rows.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataBoundedRowsObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_boundedInteriorRows O.sourceRows)

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataBoundedRowsObligations

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataDecoderStepObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and the generated position-code decoder step.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataDecoderStepObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_decoderStep O.decoderStep)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and the generated position-code decoder step.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataDecoderStepObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_decoderStep O.decoderStep)

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataDecoderStepObligations

namespace Figure13L2C2Section7BoardFreeLinePositiveBoxDataGlobalPositionCodeObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the compact L2C2 Section 7
positive-box data package and the global position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataGlobalPositionCodeObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  TM0FoldedReduction.encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex O.labelIndex)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the compact L2C2 Section 7 positive-box data
package and the global position-code label-index decoder.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLinePositiveBoxDataGlobalPositionCodeObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  TM0FoldedReduction.domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    O.section7
    (sourceLabelIndexPrimrec_of_globalLabelIndex O.labelIndex)

end Figure13L2C2Section7BoardFreeLinePositiveBoxDataGlobalPositionCodeObligations

namespace Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Forget translated boxes to compact layer-patch data while retaining the
ordinary-source bounded-search start decoder.
-/
def toLayerPatchDataSearchCodeStartObligations
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeStartObligations) :
    Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations where
  section7 :=
    TM0FoldedReduction.l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      O.section7
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the concrete L2C2 Section 7
board/free-line translated-box Robinson package and the bounded-search
fixed-start decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    (TM0FoldedReduction.l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      O.section7)
    O.sourceSearchStart

set_option linter.style.longLine false in
/--
Wang domino undecidability from the concrete L2C2 Section 7 board/free-line
translated-box Robinson package and the bounded-search fixed-start decoder for
ordinary `programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    (TM0FoldedReduction.l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfTranslatedBoxData
      O.section7)
    O.sourceSearchStart

end Figure13L2C2Section7BoardFreeLineTranslatedBoxSearchCodeStartObligations

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

namespace Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Forget the expanded Nat-site Section 7 obligation record to compact
layer-patch data while retaining the ordinary-source bounded-search start
decoder.
-/
def toLayerPatchDataSearchCodeStartObligations
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartObligations) :
    Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations where
  section7 :=
    { boardFreeLineActiveCorner := O.section7.boardFreeLineActiveCorner
      patches := O.section7.patches }
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded endpoint from expanded Section 7 layer-patch data and the
bounded-search start decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStart
    O.section7 O.sourceSearchStart

set_option linter.style.longLine false in
/--
Unencoded endpoint from expanded Section 7 layer-patch data and the
bounded-search start decoder for ordinary `programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStart
    O.section7 O.sourceSearchStart

end Figure13L2C2Section7BoardFreeLineLayerPatchSearchCodeStartObligations

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

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStartObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from compact Section 7 layer-patch data and the fixed-start
source-level generated position-code decoder.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStart
    O.section7 O.sourceLabelIndexStart

set_option linter.style.longLine false in
/--
Unencoded endpoint from compact Section 7 layer-patch data and the fixed-start
source-level generated position-code decoder.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStart
    O.section7 O.sourceLabelIndexStart

end Figure13L2C2Section7BoardFreeLineLayerPatchDataLabelIndexStartObligations

namespace Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Encoded endpoint from compact Section 7 layer-patch data and the
bounded-search start decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    O.section7 O.sourceSearchStart

set_option linter.style.longLine false in
/--
Unencoded endpoint from compact Section 7 layer-patch data and the
bounded-search start decoder for ordinary `programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStart
    O.section7 O.sourceSearchStart

end Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations

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

namespace Figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window /
valid-translated-box package and interior generated position-code rows at
label indices.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndex
    O.originZeroWindows O.validTranslatedBoxes O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window /
valid-translated-box package and interior generated position-code rows at label
indices.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndex
    O.originZeroWindows O.validTranslatedBoxes O.sourceRows

end Figure13L2C2OriginZeroValidTranslatedBoxInteriorRowsAtIndexObligations

namespace Figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window /
valid-translated-box package and bounded-interior generated position-code rows
at label indices.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndex
    O.originZeroWindows O.validTranslatedBoxes O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window / valid-translated-box
package and bounded-interior generated position-code rows at label indices.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndex
    O.originZeroWindows O.validTranslatedBoxes O.sourceRows

end Figure13L2C2OriginZeroValidTranslatedBoxBoundedRowsAtIndexObligations

namespace Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Project the origin-zero-window/valid-box fixed-start certificate to compact
Section 7 layer-patch data with the same ordinary-source decoder.
-/
def toLayerPatchDataSearchCodeStartObligations
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations) :
    Figure13L2C2Section7BoardFreeLineLayerPatchDataSearchCodeStartObligations where
  section7 :=
    TM0FoldedReduction.l2c2RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      (TM0FoldedReduction.l2c2OriginZeroCheckedStacksOfOriginZeroWindows
        O.originZeroWindows)
      (TM0FoldedReduction.l2c2ActiveCornerLayerPatchesOfValidTranslatedBoxes
        O.validTranslatedBoxes)
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the origin-zero-window/valid-box
Robinson package and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    O.originZeroWindows O.validTranslatedBoxes O.sourceSearchStart

set_option linter.style.longLine false in
/--
Wang domino undecidability from the origin-zero-window/valid-box Robinson
package and the bounded-search fixed-start decoder for ordinary `programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStart
    O.originZeroWindows O.validTranslatedBoxes O.sourceSearchStart

end Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations

namespace Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Project decoded combined windows plus valid translated boxes to the
origin-zero-window valid-box fixed-start certificate package.
-/
def toOriginZeroValidTranslatedBoxSearchCodeStartObligations
    (O : Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations) :
    Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c2OriginZeroWindowsOfCombinedActiveCornerWindows
      O.combinedActiveCornerWindows
  validTranslatedBoxes := O.validTranslatedBoxes
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from decoded combined windows, valid-box
Robinson data, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStart
    O.combinedActiveCornerWindows O.validTranslatedBoxes O.sourceSearchStart

set_option linter.style.longLine false in
/--
Wang domino undecidability from decoded combined windows, valid-box Robinson
data, and the bounded-search fixed-start decoder for ordinary `programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStart
    O.combinedActiveCornerWindows O.validTranslatedBoxes O.sourceSearchStart

end Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations

namespace Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Project checked-stack/valid-translated-box scaffold data to the decoded
combined-window valid-box certificate package.
-/
def toCombinedWindowValidTranslatedBoxSearchCodeStartObligations
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations) :
    Figure13L2C2CombinedWindowValidTranslatedBoxSearchCodeStartObligations where
  combinedActiveCornerWindows :=
    TM0FoldedReduction.l2c2OriginZeroCombinedActiveCornerWindowsOfCanonicalFreeSiteRectActiveCorner
      (TM0FoldedReduction.l2c2ActiveCornerOfOriginZeroCheckedStacks
        O.scaffold.checkedStacks)
  validTranslatedBoxes := O.scaffold.validTranslatedBoxes
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked-stack/valid-translated-box data
and the bounded-search fixed-start decoder for ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toCombinedWindowValidTranslatedBoxSearchCodeStartObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked-stack/valid-translated-box data and the
bounded-search fixed-start decoder for ordinary `programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toCombinedWindowValidTranslatedBoxSearchCodeStartObligations
    |>.domino_problem_undecidable

end Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations

namespace Figure13L2C2Figure16CompatibleCanonicalFreeSiteSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Project canonical-free-site recognition plus Figure 16 compatibility to the
checked-stack/valid-translated-box certificate package.
-/
def toCheckedStackValidTranslatedBoxSearchCodeStartObligations
    (O : Figure13L2C2Figure16CompatibleCanonicalFreeSiteSearchCodeStartObligations) :
    Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      O.canonicalActiveCorner O.compatibleLevelChecks
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from canonical-free-site recognition, Figure
16 compatibility, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Figure16CompatibleCanonicalFreeSiteSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toCheckedStackValidTranslatedBoxSearchCodeStartObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from canonical-free-site recognition, Figure 16
compatibility, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Figure16CompatibleCanonicalFreeSiteSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toCheckedStackValidTranslatedBoxSearchCodeStartObligations
    |>.domino_problem_undecidable

end Figure13L2C2Figure16CompatibleCanonicalFreeSiteSearchCodeStartObligations

namespace Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Project origin-zero recognition plus Figure 16 compatibility to the
checked-stack/valid-translated-box certificate package.
-/
def toCheckedStackValidTranslatedBoxSearchCodeStartObligations
    (O : Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations) :
    Figure13L2C2CheckedStackValidTranslatedBoxSearchCodeStartObligations where
  scaffold :=
    TM0FoldedReduction.l2c2CheckedStackValidTranslatedBoxDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
      O.originZeroWindows O.compatibleLevelChecks
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero recognition, Figure 16
compatibility, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem encoded_domino_problem_undecidable
    (O : Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  O.toCheckedStackValidTranslatedBoxSearchCodeStartObligations
    |>.encoded_domino_problem_undecidable

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero recognition, Figure 16
compatibility, and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem domino_problem_undecidable
    (O : Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  O.toCheckedStackValidTranslatedBoxSearchCodeStartObligations
    |>.domino_problem_undecidable

end Figure13L2C2Figure16CompatibleOriginZeroSearchCodeStartObligations

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

namespace Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStartObligations

set_option linter.style.longLine false in
/--
Project canonical-free-site routing plus valid translated boxes to the
origin-zero-window valid-box fixed-start certificate package.
-/
def toOriginZeroValidTranslatedBoxSearchCodeStartObligations
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStartObligations) :
    Figure13L2C2OriginZeroValidTranslatedBoxSearchCodeStartObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c2OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      (TM0FoldedReduction.l2c2CanonicalFreeSiteRectActiveCornerOfRouting
        O.routing)
  validTranslatedBoxes := O.validTranslatedBoxes
  sourceSearchStart := O.sourceSearchStart

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
valid-box Robinson package and the bounded-search fixed-start decoder for
ordinary `programData`.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStart
    O.routing O.validTranslatedBoxes O.sourceSearchStart

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing / valid-box
Robinson package and the bounded-search fixed-start decoder for ordinary
`programData`.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStartObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStart
    O.routing O.validTranslatedBoxes O.sourceSearchStart

end Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxSearchCodeStartObligations

namespace Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
valid-translated-box bounded-row Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRows
    O.routing O.validTranslatedBoxes O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing /
valid-translated-box bounded-row Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRows
    O.routing O.validTranslatedBoxes O.sourceRows

end Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsObligations

set_option linter.style.longLine false
namespace Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
valid-translated-box bounded-row-at-index Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndex
    O.routing O.validTranslatedBoxes O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing /
valid-translated-box bounded-row-at-index Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndex
    O.routing O.validTranslatedBoxes O.sourceRows

end Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxBoundedRowsAtIndexObligations

set_option linter.style.longLine false
namespace Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndexObligations

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the canonical-free-site-routing /
valid-translated-box interior-row-at-index Robinson/source obligation package.
-/
theorem encoded_domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndex
    O.routing O.validTranslatedBoxes O.sourceRows

set_option linter.style.longLine false in
/--
Wang domino undecidability from the canonical-free-site-routing /
valid-translated-box interior-row-at-index Robinson/source obligation package.
-/
theorem domino_problem_undecidable
    (O :
      Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndexObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndex
    O.routing O.validTranslatedBoxes O.sourceRows

end Figure13L2C2CanonicalFreeSiteRoutingValidTranslatedBoxInteriorRowsAtIndexObligations

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
