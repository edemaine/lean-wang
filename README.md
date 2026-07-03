# lean-wang

Lean formalization project for the undecidability of plane tiling by Wang tiles.

The proof plan is in [`plan.md`](plan.md). The current implementation starts with
the concrete definitions needed for the Berger/Robinson route:

Primary source PDFs used by the proof plan are checked in as [`cirm.pdf`](cirm.pdf)
and [`robinson.pdf`](robinson.pdf), with provenance notes in [`cirm.txt`](cirm.txt)
and [`robinson.txt`](robinson.txt).

- `LeanWang.Basic`: Wang tiles, plane and quarter-plane tilings, finite rectangle
  tilings, executable finite rectangle search, canonical natural-number
  encoding/decoding for finite tilesets, and the easy compactness restriction
  directions.
- `LeanWang.Compactness`: the proved centered-box compactness theorem
  `tilesPlane_iff_all_tileableBoxes`, plus the square compactness theorem
  `tilesPlane_iff_all_tileableSquares` and seeded quarter-plane compactness
  `tilesQuarterWithSeed_iff_all_fixedCornerSquares`.
- `LeanWang.Machine`: a small deterministic one-sided tape machine model with
  well-formed finite supports for the Wang-tile simulation layer.
- `LeanWang.MachineTiles`: finite local-history Wang-tile data generated from a
  concrete machine.
- `LeanWang.PostMachine`: the finite one-sided TM0 program model. The original
  Post-style names are still present, but the preferred public terminology is
  `FiniteTM0Program`: transitions either move or write, matching Mathlib TM0
  more closely than the older table model. The file also contains the temporary
  finite-TM0-to-`TableProgram` bridge used only to feed the existing Wang-tile
  layer.
- `LeanWang.ToPartrecEncoding`: natural-number encoding support for Mathlib's
  `Turing.ToPartrec.Code`.
- `LeanWang.NatPartrecToToPartrec`: a primitive-recursive translation from
  Mathlib unary `Nat.Partrec.Code` to Mathlib list-based
  `Turing.ToPartrec.Code`, with correctness for the TM2 evaluator.
- `LeanWang.PartrecToTM2Support`: finite reachable-label support facts for
  Mathlib's concrete `PartrecToTM2` evaluator.
- `LeanWang.PartrecToTM2SupportList`: executable list mirrors of Mathlib's
  `PartrecToTM2` support finsets, with membership equivalence to the current
  finite support sets. The TM0 route uses this executable list for its concrete
  downstream label and state enumeration.
- `LeanWang.TM0Route`: a Mathlib TM0 route that wraps the code-dependent
  `PartrecToTM2` start label as the default TM2 label, composes Mathlib's
  TM2-to-TM1 and TM1-to-TM0 translations, and proves the composed TM0 evaluator
  has the same domain as the corresponding started TM2 evaluator. It also
  packages finite state support for the started TM2, translated TM1, and
  translated TM0 machines, plus an explicit finite alphabet list for the
  translated TM0 tape symbols and injective numeric codes for those symbols.
- `LeanWang.TM0FiniteCompiler`: shared helper lemmas for the folded TM0
  reduction, including numeric state codes and label-closure facts for
  supported Mathlib TM0 transitions.
- `LeanWang.TM0FoldedProgram` and `LeanWang.TM0FoldedCompiler`: the current
  finite one-sided TM0 reduction. The folded program stores the two sides of
  Mathlib's TM0 tape in one local tape cell and proves the semantic halting
  equivalence.
- `LeanWang.TM0FoldedPositionReduction`: semantic final wrappers for the
  generated position-coded folded reduction.  This public import is split into
  `SourceObligations` and `Theorems` submodules so edits to theorem surfaces do
  not force unnecessary rechecking of the folded semantic proof.
- `LeanWang.Theorems`: generic scaffold and machine-tiling theorem surfaces.
- `LeanWang.Final`: the current top-level undecidability theorem surface,
  conditional on the two remaining construction interfaces bundled as
  `FinalReductionInputs`.

Current build:

```bash
lake build
```

The build succeeds.

The formerly monolithic generated-position wrapper target is also split and
builds directly:

```bash
lake build LeanWang.TM0FoldedPositionReduction
```

The main theorem surface in `LeanWang.Final` is currently conditional on the
scaffold construction plus a source construction interface.  The current
lowest-level endpoint is `FinalReductionInputs`, whose fields are:

- `TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData`: the
  proof-facing Section 7 scaffold package for the first audited L2 candidate.
- `TM0FoldedReduction.PositionSourceObligations`: the generated-position
  source reduction obligations.

The proof-facing scaffold route closest to the current concrete transcription
is exposed by
`FinalFigure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations`.
Its fields are canonical Robinson free-site active/corner recognition, finite
compatible Figure 16 checks, and `SourcePositionCodeLabelIndexFromPrimrec`.
The first-candidate canonical-free-site Figure 16 wrappers now also project to
the matching `FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers
through the checked-stack/valid-translated-box bridge.

For the finite checked-stack/layer-patch route, the same source target is
exposed as
`FinalCheckedStackLayerPatchSourcePositionCodeConstructionObligations`; its
scaffold field is the concrete finite certificate
`TM0FoldedReduction.L2C1CheckedStackLayerPatchData`.

The broader global-label-index split route remains available as
`FinalGlobalPositionCodeConstructionObligations`.

The still lower-level `FinalReductionInputs` endpoint consists of:

- `TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData`: the
  proof-facing Section 7 scaffold package, combining board/free-line
  active-corner recognition with finite active-corner layer patches for the
  first audited L2 candidate.
- `TM0FoldedReduction.PositionSourceObligations`: the generated-position source
  reduction obligations.

The older row-based, decoder-step, and global-label-index wrappers remain available through
`FinalConstructionObligations`,
`TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec`, and
`FinalDecoderStepConstructionObligations`, but the source-specialized
label-index route is the narrower source target for final use.
`LeanWang.Final` also exposes raw-scaffold aliases
`encoded_domino_problem_undecidable_of_scaffoldAndSourcePositionCodeLabelIndexFrom`,
`domino_problem_undecidable_of_scaffoldAndSourcePositionCodeLabelIndexFrom`,
`encoded_domino_problem_undecidable_of_scaffoldAndSourceGlobalPositionCodeLabelIndexFrom`
and
`domino_problem_undecidable_of_scaffoldAndSourceGlobalPositionCodeLabelIndexFrom`.

`LeanWang.Final` also exposes
`encoded_domino_problem_undecidable_of_checkedStackLayerPatchData` and
`domino_problem_undecidable_of_checkedStackLayerPatchData`, which build the
Section 7 scaffold input from the concrete finite transcription target
`TM0FoldedReduction.L2C1CheckedStackLayerPatchData`.
For the same route with the scaffold obligations split, it exposes
`encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatches` and
`domino_problem_undecidable_of_checkedStacksAndLayerPatches`, whose scaffold
arguments are exactly `TM0FoldedReduction.L2C1OriginZeroCheckedStacks` and
`TM0FoldedReduction.L2C1ActiveCornerLayerPatches`.
The finite rectangle-stack decoding part of the checked-stack target is already
proved for both audited L2 candidates as
`TM0FoldedReduction.l2c1CheckedStacksForListedActiveSiteRectangles` and
`TM0FoldedReduction.l2c2CheckedStacksForListedActiveSiteRectangles`; the
remaining checked-stack bridge is the Robinson geometry that supplies
origin-zero active/corner windows.
Canonical free-site active/corner recognition now feeds this bridge directly
through
`TM0FoldedReduction.l2c1OriginZeroCheckedStacksOfCanonicalFreeSiteRectActiveCorner`
and its L2C2 analogue, and the corresponding
`*_CanonicalFreeSiteCanonicalCheckedCompatibleFig16*` constructors combine it
with the audited Figure 16 data to produce the checked-stack finite packages.
The lower valid-translated-box target also has decoder-step, global-label, and
source-label final packages:
`FinalCheckedStackValidTranslatedBoxDecoderStepConstructionObligations`,
`FinalCheckedStackValidTranslatedBoxGlobalPositionCodeConstructionObligations`,
and
`FinalCheckedStackValidTranslatedBoxSourcePositionCodeConstructionObligations`.
These packages now project to the matching
`FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers via
`TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData`,
so the first-candidate exported endpoints use the origin-zero
translated-positive-box reduction surface before falling back to older
layer-patch compatibility helpers.
The checked-stack plus compatible Figure 16 macro-square route has matching
decoder-step, global-label, and source-label packages that project through this
valid-translated-box target.
Those Figure 16 compatible wrappers now also project to the matching
`FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers, and the
source-label endpoint routes through the checked-stack/valid-box source
endpoint.
The origin-zero-window Figure 16 wrappers expose the same projections by first
recovering checked stacks from the origin-zero active/corner windows and then
using that checked-stack/valid-box bridge.
The generated-position integration layer also exposes the corresponding
semantic-correctness-discharged wrappers for Section 7 translated boxes and
checked-stack/valid-translated-box data.
The second audited L2 candidate has matching decoder-step, global-label, and
source-label packages for both checked-stack/layer-patch data and
checked-stack/valid-translated-box data.
The L2C2 checked-stack/valid-translated-box row-source, global-label, and
source-label endpoints now project directly to
`FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
via
`TM0FoldedReduction.l2c2OriginZeroTranslatedObligationsOfCheckedStackValidTranslatedBoxData`,
so these final routes expose the origin-zero translated-positive-box scaffold
surface rather than only the derived layer-patch package.  The decoder-step
variant remains on the layer-patch path because it does not include enough
source-label information for the origin-zero source endpoint.
The more finite Figure 16 route is exposed through compatible macro-square
and compatible level-check surfaces.  The canonical-free-site aliases
`encoded_domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecks`
and
`domino_problem_undecidable_of_canonicalFreeSiteAndCompatibleFig16LevelChecks`
take canonical Robinson free-site active/corner recognition, finite compatible
Figure 16 level checks, and generated interior source rows.  Decoder-step,
global-label, and source-label variants are exposed under the same
`canonicalFreeSiteAndCompatibleFig16LevelChecks*` naming.  The reduction layer
also exposes the exact source-label endpoints
`encoded_domino_problem_undecidable_l2c1_canonical_free_site_compatible_fig16_sourceCodeCorrect`
and the L2C2/unencoded analogues; the L2C2 source-label final surface is
`FinalL2C2Figure16CompatibleCanonicalFreeSiteSourcePositionCodeConstructionObligations`.
The row-source L2C2 analogue is
`FinalL2C2Figure16CompatibleCanonicalFreeSiteConstructionObligations`, with
top-level aliases ending in
`l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksSourcePositionCodeInteriorRows`.
Both L2C2 canonical-free-site Figure 16 row-source and source-label packages
now project to
`FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
through the checked-stack/valid-translated-box bridge.
The same L2C2 compatible-Figure-16 surface now also exposes decoder-step and
global-label aliases ending in
`l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksDecoderStep` and
`l2c2CanonicalFreeSiteAndCompatibleFig16LevelChecksGlobalPositionCodeLabelIndexFrom`;
these derive the required `TilesPlane figure18ScaffoldTiles` internally from
the compatible Figure 16 checks.
The same second-candidate canonical-free-site route is also exposed with a
direct scaffold-plane input as
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteConstructionObligations`
and the decoder-step/global-label/source-label variants
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteDecoderStepConstructionObligations`,
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteGlobalPositionCodeConstructionObligations`,
and
`FinalL2C2Figure18ScaffoldTilesPlaneCanonicalFreeSiteSourcePositionCodeConstructionObligations`.
The corresponding direct-input aliases end in
`l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneDecoderStep`,
`l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneGlobalPositionCodeLabelIndexFrom`,
and
`l2c2CanonicalFreeSiteAndFigure18ScaffoldTilesPlaneSourcePositionCodeLabelIndexFrom`.
For the concrete Figure 13 scaffold route, `LeanWang.Final` also exposes
`FinalFigure13L2C2CompatibleLevelSourcePositionCodeConstructionObligations`.
This is the current lower-level second-candidate surface: it asks directly for
compatible routed Robinson free grids and realization for the human-audited
L2C2 Figure 13 scaffold data, plus `SourcePositionCodeLabelIndexFromPrimrec`.
The finite-patch sibling
`FinalFigure13L2C2CompatibleLevelLayerPatchSourcePositionCodeConstructionObligations`
replaces realization by `HasActiveCornerLayerBoxPatches` for the same concrete
scaffold data.
The still lower routing sibling
`FinalFigure13L2C2CanonicalProductRoutingLayerPatchSourcePositionCodeConstructionObligations`
uses canonical product-witness routing plus those finite layer patches, deriving
the compatible routed free-grid premise internally.
The positive-box sibling
`FinalFigure13L2C2CanonicalProductRoutingPositiveBoxSourcePositionCodeConstructionObligations`
replaces layer patches by positive-radius `ActiveCornerIndexedBox` witnesses;
the radius-zero patch is supplied by the scaffold corner.
The translated-positive-box sibling
`FinalFigure13L2C2CanonicalProductRoutingTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
allows those positive-radius indexed boxes to be built around arbitrary
origins, then derives the same layer-patch route by recentering.
The preferred ordinary-canonical sibling
`FinalFigure13L2C2CanonicalTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
uses the existing
`NatSiteRobinsonCanonicalTranslatedPositiveBoxObligations` interface, so the
scaffold side only has to supply canonical Robinson-board routing and
translated positive-radius active-corner indexed boxes for the concrete L2C2
Nat-site data.
The more Section-7-shaped sibling
`FinalFigure13L2C2CanonicalFreeSiteRectTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
uses
`NatSiteRobinsonCanonicalFreeSiteRectTranslatedPositiveBoxObligations`, where
the routing field is the selected free/free site rectangle rather than the
generic canonical routing package.
The L2C2 origin-zero sibling
`FinalFigure13L2C2OriginZeroTranslatedPositiveBoxSourcePositionCodeConstructionObligations`
is lower still: origin-zero active/corner windows imply that free-site
rectangle routing, while the translated positive boxes supply the backward
scaffold realization.
The row-major
`TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData`
surface is diagnostic and refuted by
`not_figure18CanonicalCheckedRecognizedCompatibleLevelData`; final routes
should use `Figure18CanonicalCheckedRecognizedCompatibleLevelChecks` instead.
For the Figure 18 scaffold-plane route, `LeanWang.Final` now also exposes
checked-stack variants
`FinalFigure18ScaffoldTilesPlaneCheckedStacksConstructionObligations` and the
decoder-step/global-label/source-label analogues.  These use
`TM0FoldedReduction.l2c1ActiveCornerOfOriginZeroCheckedStacks` as the named
projection from finite origin-zero checked stacks to canonical Robinson
free-site active/corner recognition, while their endpoints reuse the existing
origin-zero scaffold-plane route.
The origin-zero scaffold-plane route itself now projects directly to the
`FinalOriginZeroTranslatedBox*ConstructionObligations` wrappers via
`TM0FoldedReduction.l2c1OriginZeroTranslatedObligationsOfOriginZeroWindowsFigure18ScaffoldTilesPlane`,
so this scaffold-facing surface no longer has to detour through derived
Section 7 layer-patch inputs.
The Section 7 and generated-position wrapper layers expose the same checked
stack plus scaffold-plane route directly through
`l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane`,
`encoded_domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_position_source`,
and the corresponding source-label semantic-correctness-discharged endpoints.
The standalone `TileableSquare figure18ScaffoldTiles` cofinal target is not a
final route: the direct Figure 18 site-square problem is a diagnostic surface,
while the proof-facing scaffold target is the Section 7 checked-stack plus
valid-translated-box/layer-patch route.

The standalone raw Figure 13 positive-board and Figure 16 source/raw-boundary
surfaces are diagnostics, not final assumptions: the raw Figure 13 macro tiles
do not tile even a `2 x 2` square, and the over-strong Figure 16
source/raw-boundary diagnostic has no adjacent two-cell witnesses in the current
transcription.  `LeanWang.OllingerRobinsonFigure13Data` now also proves the
global contradiction wrappers
`not_hasCanonicalFigure16SourceRawBoundaryCheckedLevelData`,
`not_hasCanonicalFigure16SourceRawBoundaryLevelChecks`,
`not_hasCanonicalCheckedFigure16SourceRawBoundaryMacroSquaresBool`, and
`not_hasCanonicalFigure16SourceRawBoundaryBoardLevelChecks`: any all-level
canonical source/raw-boundary route would imply positive-board raw Figure 13
square tilings, contradicting the checked finite obstruction.

There is no direct `PartrecToTM2`/TM2-to-table reduction in the current route.
TM2 remains only as Mathlib's intermediate evaluator on the way to TM0. The
`TableProgram` model is still live because the current Wang-tile construction is
typed against it.

The fixed-domino, fixed-corner, scaffold, final domino, and encoded domino
undecidability reductions are now proved from the TM0 construction interfaces.
