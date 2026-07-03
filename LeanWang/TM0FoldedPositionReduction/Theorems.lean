/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.SourceObligations
import LeanWang.OllingerRobinsonTranscription
import LeanWang.OllingerRobinsonFigure18Reduction

/-!
Semantic final theorem wrappers for the generated position-coded folded
reduction.

This module keeps the theorem-facing wrappers separate from the semantic source
obligation constructors so edits to final theorem surfaces do not require
rechecking the constructor module.
-/


namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the generated interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsCorrect hinterior)

/--
Encoded domino undecidability from a scaffold and the generated position-code
accumulator step, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_decoderStepCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

/--
Unencoded domino undecidability from a scaffold and the generated position-code
accumulator step, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_decoderStepCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

/--
Encoded domino undecidability from a scaffold and the global position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_globalCodeCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from a scaffold and the global position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_globalCodeCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

/--
Encoded domino undecidability from a scaffold and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_sourceCodeCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from a scaffold and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_sourceCodeCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

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

/--
Encoded domino undecidability from a scaffold and the generated one-row
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_oneRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsCorrect hvarRows)

/--
Unencoded domino undecidability from a scaffold and the generated one-row
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_oneRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeOneRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsCorrect hvarRows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the packaged generated
one-row position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_oneRowsPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsWithStatementNodupCorrect
      hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the packaged generated
one-row position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_oneRowsPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hrows : SourcePositionCodeOneRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsWithStatementNodupCorrect
      hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the raw-TM1-support one-row
position-code package, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_oneRowsRawTM1SupportPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hrows : SourcePositionCodeOneRowsWithRawTM1StatementSupport) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsWithRawTM1StatementSupportCorrect
      hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the raw-TM1-support one-row
position-code package, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_oneRowsRawTM1SupportPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hrows : SourcePositionCodeOneRowsWithRawTM1StatementSupport) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsWithRawTM1StatementSupportCorrect
      hrows)

/--
Encoded domino undecidability from a scaffold and the generated
bounded-interior position-code rows, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_boundedRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

/--
Unencoded domino undecidability from a scaffold and the generated
bounded-interior position-code rows, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_boundedRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeBoundedInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the packaged generated
bounded-interior position-code rows, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_boundedRowsPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodupCorrect
      hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the packaged generated
bounded-interior position-code rows, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_boundedRowsPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithStatementNodupCorrect
      hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the raw-TM1-support
bounded-interior position-code package, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_boundedRowsRawTM1SupportPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithRawTM1StatementSupport) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithRawTM1StatementSupportCorrect
      hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the raw-TM1-support
bounded-interior position-code package, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_boundedRowsRawTM1SupportPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : SourcePositionCodeBoundedInteriorRowsWithRawTM1StatementSupport) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsWithRawTM1StatementSupportCorrect
      hbounded)

/--
Unencoded domino undecidability from a scaffold and the generated interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsCorrect hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the packaged generated
interior position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_interiorRowsPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
      hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the packaged generated
interior position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_interiorRowsPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodupCorrect
      hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the raw-TM1-support interior
position-code package, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_interiorRowsRawTM1SupportPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsWithRawTM1StatementSupport) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsWithRawTM1StatementSupportCorrect
      hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the raw-TM1-support
interior position-code package, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_interiorRowsRawTM1SupportPackageCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsWithRawTM1StatementSupport) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsWithRawTM1StatementSupportCorrect
      hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRowsCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeInteriorRowsCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRowsCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeInteriorRowsCorrect hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_sourceCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_sourceCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a checked flexible finite scaffold
transcription and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_checked_transcription_position_source_interiorRowsCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRowsCorrect
    D.toPresentedFlexibleInstance hinterior

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_checked_transcription_position_source_interiorRowsCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRowsCorrect
    D.toPresentedFlexibleInstance hinterior

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a checked flexible finite scaffold
transcription and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_checked_transcription_position_source_sourceCodeCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source_sourceCodeCorrect
    D.toPresentedFlexibleInstance hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_checked_transcription_position_source_sourceCodeCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source_sourceCodeCorrect
    D.toPresentedFlexibleInstance hindex

end TM0FoldedReduction

end LeanWang
