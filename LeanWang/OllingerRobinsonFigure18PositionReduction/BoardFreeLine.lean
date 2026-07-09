/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction.Basic

/-!
Board/free-line Figure 18 position-reduction wrappers with generated
folded-position correctness imported.
-/

namespace LeanWang

open Nat.Partrec (Code)
open OllingerRobinson
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

namespace TM0FoldedReduction

set_option linter.style.longLine false

/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRows
      data hinterior
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the fixed-start source-level
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_startCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the fixed-start source-level
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_startCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first finite-check-facing Section 7
board/free-line layer-patch package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the fixed-start source-level
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_startCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the fixed-start source-level
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_startCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated one-row position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_oneRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hrows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeOneRowsCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and the generated bounded-interior
position-code rows, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second finite-check-facing Section 7
board/free-line layer-patch package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_interiorRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineLayerPatchData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_layer_patch_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first paper-facing Section 7
board/free-line positive-box package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_interiorRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second paper-facing Section 7
board/free-line positive-box package and interior generated position-code rows
at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_interiorRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLinePositiveBoxData)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_positive_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package, the bounded-search label-index decoder, and
duplicate-free source statement supports.  Statement uniqueness identifies the
generated position codes with the support-search state codes.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_searchCodeWithNodupCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodupCorrect
        hsearch hnodup)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package, the bounded-search label-index decoder, and
duplicate-free source statement supports.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_searchCodeWithNodupCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodupCorrect
        hsearch hnodup)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second Section 7 board/free-line
translated-box package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_position_source
      data
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_decoderStepCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_decoderStepCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_decoderStepCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_globalCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_globalCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_globalCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C1CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package, the bounded-search label-index decoder, and
duplicate-free source statement supports.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_searchCodeWithNodupCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_searchCodeWithNodupCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hsearch hnodup

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second checked-stack/valid-translated-box
finite scaffold package, the bounded-search label-index decoder, and
duplicate-free source statement supports.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_searchCodeWithNodupCorrect
    (data : L2C2CheckedStackValidTranslatedBoxData)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_searchCodeWithNodupCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStackValidTranslatedBoxData
        data)
      hsearch hnodup

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c1CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second canonical free-site
active/corner recognition package, finite compatible Figure 16 level checks,
and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_free_site_compatible_fig16_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (compatibleLevelChecks : Figure18CanonicalCheckedRecognizedCompatibleLevelChecks)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_checked_stack_valid_translated_box_data_sourceCodeCorrect
      (l2c2CheckedStackValidTranslatedBoxDataOfCanonicalFreeSiteCanonicalCheckedCompatibleFig16
        canonicalActiveCorner compatibleLevelChecks)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C1CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second canonical free-site
active/corner recognition package, a plane tiling of the compatible Figure 18
scaffold tiles, and the source-specialized position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_canonical_free_site_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (canonicalActiveCorner : L2C2CanonicalFreeSiteRectActiveCorner)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCanonicalFreeSiteFigure18ScaffoldTilesPlane
        canonicalActiveCorner hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the first audited L2 candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the first audited L2 candidate.
-/
theorem
    domino_problem_undecidable_l2c1_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C1OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c1RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Encoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the second audited L2 candidate.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from finite origin-zero checked stacks, a plane
tiling of the compatible Figure 18 scaffold tiles, and the source-specialized
position-code label-index decoder, with `positionProgramData` semantic
correctness discharged for the second audited L2 candidate.
-/
theorem
    domino_problem_undecidable_l2c2_checked_stacks_figure18_scaffold_tiles_plane_sourceCodeCorrect
    (hchecked : L2C2OriginZeroCheckedStacks)
    (hplane : TilesPlane figure18ScaffoldTiles)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_translated_box_data_sourceCodeCorrect
      (l2c2RobinsonSection7BoardFreeLineTranslatedBoxDataOfCheckedStacksFigure18ScaffoldTilesPlane
        hchecked hplane)
      hindex


end TM0FoldedReduction

end LeanWang
