/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.L2C1LayerPatches
import LeanWang.TM0FoldedPositionReduction.Theorems.LayerPatches.L2C2LayerPatches

/-!
Valid-translated-box final theorem wrappers for the generated position-coded
folded reduction.

This is the scaffold-side decoding target one step below checked
stack/layer-patch data: valid translated boxes are converted to active-corner
layer patches by the audited no-neighbor checks in the Figure 18 scaffold data.
-/

namespace LeanWang

namespace TM0FoldedReduction

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_decoderStepCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_decoderStepCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_decoderStepCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_decoderStepCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the generated one-row-at-index position-code decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_oneRowsAtIndexCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsAtIndexCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the generated one-row-at-index position-code decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_oneRowsAtIndexCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsAtIndexCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and bounded-interior generated position-code rows at concrete
numeric label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_boundedRowsAtIndexCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsAtIndexCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and bounded-interior generated position-code rows at concrete
numeric label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_boundedRowsAtIndexCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsAtIndexCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and interior generated position-code rows at concrete numeric
label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_interiorRowsAtIndexCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsAtIndexCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and interior generated position-code rows at concrete numeric
label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_interiorRowsAtIndexCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsAtIndexCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_sourceCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_sourceCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_sourceCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_sourceCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code start decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_startCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_startCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstart

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code start decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_startCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_startCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstart

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and generated one-row position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_oneRowsCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and generated one-row position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_oneRowsCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_boundedRowsCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_boundedRowsCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_interiorRowsCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
Section 7 package and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_valid_translated_boxes_interiorRowsCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_decoderStepCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_decoderStepCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the generated one-row-at-index position-code decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_oneRowsAtIndexCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsAtIndexCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the generated one-row-at-index position-code decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_oneRowsAtIndexCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsAtIndexCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and bounded-interior generated position-code rows at concrete
numeric label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_boundedRowsAtIndexCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsAtIndexCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and bounded-interior generated position-code rows at concrete
numeric label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_boundedRowsAtIndexCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsAtIndexCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and interior generated position-code rows at concrete numeric
label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_interiorRowsAtIndexCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsAtIndexCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and interior generated position-code rows at concrete numeric
label slots, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_interiorRowsAtIndexCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsAtIndexCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_sourceCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_sourceCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code start decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_startCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_startCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstart

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and the source-specialized position-code start decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_startCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_startCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hstart

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and generated one-row position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_oneRowsCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and generated one-row position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_oneRowsCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_boundedRowsCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_boundedRowsCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_interiorRowsCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
Section 7 package and generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_valid_translated_boxes_interiorRowsCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackValidTranslatedBoxData data) hinterior

end TM0FoldedReduction

end LeanWang
