/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.SourceObligations
import LeanWang.OllingerRobinsonFigure18Reduction

/-!
L2C2 layer-patch final theorem wrappers for the generated position-coded folded reduction.
-/

namespace LeanWang

namespace TM0FoldedReduction

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
generated position-code accumulator step, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_decoderStepCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
generated position-code accumulator step, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_decoderStepCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_sourceCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_sourceCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
fixed-start source-level position-code decoder.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_startCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
fixed-start source-level position-code decoder.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_startCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
global generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_globalCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and the
global generated position-code label-index decoder.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_globalCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
generated one-row position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_oneRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
generated one-row position-code rows.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_oneRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
generated bounded-interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_boundedRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
generated bounded-interior position-code rows.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_boundedRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
generated one-row position-code rows at concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_oneRowsAtIndexCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
generated one-row position-code rows at concrete numeric label slots.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_oneRowsAtIndexCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
interior generated position-code rows at concrete numeric label slots.
-/
theorem encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRowsAtIndexCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate using
origin-zero active/corner windows, finite active-corner layer patches, and
interior generated position-code rows at concrete numeric label slots.
-/
theorem domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRowsAtIndexCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    originZeroWindows patches
    (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
the leaner decoded-site origin-zero active/corner window target, finite
active-corner layer patches, and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_l2c2_combined_active_corner_layer_patches_position_source
    (windows : L2C2OriginZeroCombinedActiveCornerWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    (l2c2OriginZeroWindowsOfCombinedActiveCornerWindows windows)
    patches source

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate
using the leaner decoded-site origin-zero active/corner window target, finite
active-corner layer patches, and generated-position source obligations.
-/
theorem domino_problem_undecidable_l2c2_combined_active_corner_layer_patches_position_source
    (windows : L2C2OriginZeroCombinedActiveCornerWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    (l2c2OriginZeroWindowsOfCombinedActiveCornerWindows windows)
    patches source

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second audited L2-blank candidate using
canonical free-site active/corner recognition, finite active-corner layer
patches, and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_layer_patches_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (patches : L2C2ActiveCornerLayerPatches)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    (l2c2OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      canonicalActiveCorner)
    patches source

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second audited L2-blank candidate
using canonical free-site active/corner recognition, finite active-corner layer
patches, and generated-position source obligations.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_layer_patches_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (patches : L2C2ActiveCornerLayerPatches)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
    (l2c2OriginZeroWindowsOfCanonicalFreeSiteRectActiveCorner
      canonicalActiveCorner)
    patches source

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated one-row-at-index position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsAtIndexCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch
Section 7 certificate and the generated one-row-at-index position-code decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsAtIndexCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and bounded-interior generated position-code rows at concrete
numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsAtIndexCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch
Section 7 certificate and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsAtIndexCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and interior generated position-code rows at concrete numeric
label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsAtIndexCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch
Section 7 certificate and interior generated position-code rows at concrete
numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsAtIndexCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the bounded-search label-index decoder, using statement-list
uniqueness to recover the generated position-coded source route.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_searchCodeWithNodupCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data
    (positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodupCorrect
      hsearch hnodup)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch
Section 7 certificate and the bounded-search label-index decoder, using
statement-list uniqueness to recover the generated position-coded source route.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_searchCodeWithNodupCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data
    (positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodupCorrect
      hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the source-specialized position-code start decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_startCodeCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch
Section 7 certificate and the source-specialized position-code start decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_startCodeCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated one-row position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated one-row position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    data (sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/layer-patch Section
7 certificate and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (data : L2C2CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    data (sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site active/corner
recognition, checked compatible Figure 16 macro-squares, and generated-position
source obligations.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_checked_fig16_layer_patches_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    (l2c2CheckedStackLayerPatchDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      canonicalActiveCorner hlevel)
    source

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site active/corner
recognition, checked compatible Figure 16 macro-squares, and generated-position
source obligations.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_checked_fig16_layer_patches_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    (l2c2CheckedStackLayerPatchDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
      canonicalActiveCorner hlevel)
    source

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site active/corner
recognition, checked compatible Figure 16 level data, and generated-position
source obligations.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_checked_fig16_level_data_layer_patches_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    (l2c2CheckedStackLayerPatchDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16LevelData
      canonicalActiveCorner hlevel)
    source

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site active/corner
recognition, checked compatible Figure 16 level data, and generated-position
source obligations.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_checked_fig16_level_data_layer_patches_position_source
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_position_source
    (l2c2CheckedStackLayerPatchDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16LevelData
      canonicalActiveCorner hlevel)
    source

set_option linter.style.longLine false in
/--
Encoded domino undecidability from canonical free-site active/corner
recognition, checked compatible Figure 16 level data, and the
source-specialized generated position-code label-index decoder.
-/
theorem encoded_domino_problem_undecidable_l2c2_canonical_free_site_checked_fig16_level_data_layer_patches_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16LevelData
      canonicalActiveCorner hlevel)
    hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from canonical free-site active/corner
recognition, checked compatible Figure 16 level data, and the
source-specialized generated position-code label-index decoder.
-/
theorem domino_problem_undecidable_l2c2_canonical_free_site_checked_fig16_level_data_layer_patches_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hlevel : Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16LevelData
      canonicalActiveCorner hlevel)
    hindex

end TM0FoldedReduction

end LeanWang
