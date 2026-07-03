/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.SourceObligations
import LeanWang.OllingerRobinsonFigure18Reduction

/-!
Layer-patch final theorem wrappers for the generated position-coded folded
reduction.
-/


namespace LeanWang

namespace TM0FoldedReduction

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/layer-patch Section 7
certificate and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_decoderStepCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_layer_patches_decoderStepCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/layer-patch Section 7
certificate and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_globalCodeCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_layer_patches_globalCodeCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_sourceCodeCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_layer_patches_sourceCodeCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/layer-patch Section 7
certificate and the generated one-row position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the generated one-row position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/layer-patch Section 7
certificate and the generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the generated bounded-interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_position_source
    data (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/layer-patch Section 7
certificate and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    data (sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/layer-patch Section
7 certificate and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
    (data : L2C1CheckedStackLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    data (sourcePositionCodeBoundedInteriorRowsPrimrec_of_interior hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using the generated position-code accumulator step with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_positive_boxes_decoderStepCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_decoderStepCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from first checked stacks and positive
centered active-corner boxes, using the generated position-code accumulator
step with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_positive_boxes_decoderStepCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_decoderStepCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using the global position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_positive_boxes_globalCodeCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_globalCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using the global position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_positive_boxes_globalCodeCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_globalCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using the source-specialized position-code label-index
decoder with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_positive_boxes_sourceCodeCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_sourceCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using the source-specialized position-code label-index
decoder with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_positive_boxes_sourceCodeCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_sourceCodeCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using generated one-row position-code data with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_positive_boxes_oneRowsCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using generated one-row position-code data with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_positive_boxes_oneRowsCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_oneRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using generated bounded-interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_positive_boxes_boundedRowsCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using generated bounded-interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_positive_boxes_boundedRowsCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_boundedRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using generated interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_checked_stack_positive_boxes_interiorRowsCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from first checked stacks and positive centered
active-corner boxes, using generated interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_checked_stack_positive_boxes_interiorRowsCorrect
    (data : L2C1CheckedStackPositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
    (l2c1CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hinterior

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
Encoded domino undecidability from the second checked signal-tower board
package, using the generated position-code accumulator step with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_decoderStepCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked signal-tower board
package, using the generated position-code accumulator step with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_board_layer_patches_decoderStepCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked signal-tower board
package, using the global position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_globalCodeCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked signal-tower board
package, using the global position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_board_layer_patches_globalCodeCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked signal-tower board
package, using the source-specialized position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_sourceCodeCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked signal-tower board
package, using the source-specialized position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_board_layer_patches_sourceCodeCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked signal-tower board
package, using generated one-row position-code data with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_oneRowsCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked signal-tower board
package, using generated one-row position-code data with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_board_layer_patches_oneRowsCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked signal-tower board
package, using generated bounded-interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_boundedRowsCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked signal-tower board
package, using generated bounded-interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_board_layer_patches_boundedRowsCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked signal-tower board
package, using generated interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_interiorRowsCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked signal-tower board
package, using generated interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_board_layer_patches_interiorRowsCorrect
    (data : L2C2CheckedSignalTowerBoardData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedBoardData data) hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and the source-specialized
position-code label-index decoder, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_sourceCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_sourceCodeCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and the source-specialized
position-code label-index decoder, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_sourceCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_sourceCodeCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and generated one-row
position-code data, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_oneRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_oneRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and generated one-row
position-code data, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_oneRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_oneRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and generated bounded-interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_boundedRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_boundedRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and generated bounded-interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_boundedRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_boundedRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and generated interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_interiorRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
row-major checked raw-boundary board levels, and generated interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_checked_board_levels_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevels : Figure18CanonicalRawBoundaryCheckedBoardLevels)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_interiorRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindows
      originZeroWindows boardLevels)
    hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and the source-specialized
position-code label-index decoder, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_sourceCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_sourceCodeCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and the source-specialized
position-code label-index decoder, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_sourceCodeCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_sourceCodeCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and generated one-row
position-code data, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_oneRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_oneRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and generated one-row
position-code data, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_oneRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_oneRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and generated bounded-interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_boundedRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_boundedRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and generated bounded-interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_boundedRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_boundedRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and generated interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_board_layer_patches_interiorRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second origin-zero active/corner windows,
finite checked raw-boundary board-level checks, and generated interior
position-code rows, routed through the Section 7 layer patches.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_board_level_checks_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (boardLevelChecks : Figure18CanonicalRawBoundaryBoardLevelChecks)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_board_layer_patches_interiorRowsCorrect
    (l2c2CheckedSignalTowerBoardDataOfOriginZeroWindowsBoardLevelChecks
      originZeroWindows boardLevelChecks)
    hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second checked stacks and positive centered
active-corner boxes, using the generated position-code accumulator step with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_positive_boxes_decoderStepCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second checked stacks and positive
centered active-corner boxes, using the generated position-code accumulator
step with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_positive_boxes_decoderStepCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_decoderStepCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second checked stacks and positive centered
active-corner boxes, using the global position-code label-index decoder with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_positive_boxes_globalCodeCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second checked stacks and positive
centered active-corner boxes, using the global position-code label-index
decoder with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_positive_boxes_globalCodeCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_globalCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second checked stacks and positive centered
active-corner boxes, using the source-specialized position-code label-index
decoder with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_positive_boxes_sourceCodeCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second checked stacks and positive
centered active-corner boxes, using the source-specialized position-code
label-index decoder with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_positive_boxes_sourceCodeCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_sourceCodeCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second checked stacks and positive centered
active-corner boxes, using generated one-row position-code data with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_positive_boxes_oneRowsCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second checked stacks and positive
centered active-corner boxes, using generated one-row position-code data with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_positive_boxes_oneRowsCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_oneRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second checked stacks and positive centered
active-corner boxes, using generated bounded-interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_positive_boxes_boundedRowsCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hbounded

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second checked stacks and positive
centered active-corner boxes, using generated bounded-interior position-code
rows with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_positive_boxes_boundedRowsCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_boundedRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hbounded

set_option linter.style.longLine false in
/--
Encoded domino undecidability from second checked stacks and positive centered
active-corner boxes, using generated interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_checked_stack_positive_boxes_interiorRowsCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from second checked stacks and positive
centered active-corner boxes, using generated interior position-code rows with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_checked_stack_positive_boxes_interiorRowsCorrect
    (data : L2C2CheckedStackPositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_l2c2_checked_stack_layer_patches_interiorRowsCorrect
    (l2c2CheckedStackLayerPatchDataOfCheckedStackPositiveBoxData data) hinterior

end TM0FoldedReduction

end LeanWang
