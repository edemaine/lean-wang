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

end LeanWang
