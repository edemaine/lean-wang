/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction.BoardFreeLine

/-!
Indexed-window Figure 18 position-reduction wrappers with generated
folded-position correctness imported.
-/

noncomputable section

namespace LeanWang

open Nat.Partrec (Code)
open OllingerRobinson
open OllingerRobinson.Figure13Layers.LayeredFigure18ScaffoldData.ConcreteData

namespace TM0FoldedReduction

set_option linter.style.longLine false

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first origin-zero Section 7 layer-patch
obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first origin-zero Section 7 layer-patch
obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second origin-zero Section 7 layer-patch
obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second origin-zero Section 7
layer-patch obligation surface, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_interiorRowsCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first origin-zero Section 7 layer-patch
obligation surface and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_boundedRowsAtIndexCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first origin-zero Section 7
layer-patch obligation surface and bounded-interior generated position-code
rows at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_boundedRowsAtIndexCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component1BlankCandidateActiveSiteSpecs
      l2Component1BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.southwest
      l2Component1BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_section7_layer_patches_position_source
      O (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second origin-zero Section 7 layer-patch
obligation surface and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_boundedRowsAtIndexCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second origin-zero Section 7
layer-patch obligation surface and bounded-interior generated position-code
rows at concrete numeric label slots, with `positionProgramData` semantic
correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_boundedRowsAtIndexCorrect
    (O : NatSiteRobinsonOriginZeroTranslatedPositiveBoxObligations
      l2Component2BlankCandidateActiveSiteSpecs
      l2Component2BlankCandidateSanity.activeSiteSpecs_valid
      0 Quadrant.northeast
      l2Component2BlankCandidateSanity.cornerIndex_valid)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_section7_layer_patches_position_source
      O (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

/--
Encoded domino undecidability from origin-zero active/corner windows and finite
active-corner layer patches for the first audited L2-blank candidate, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from origin-zero active/corner windows and
finite active-corner layer patches for the first audited L2-blank candidate,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from origin-zero active/corner windows and finite
active-corner layer patches for the second audited L2-blank candidate, with
`positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from origin-zero active/corner windows and
finite active-corner layer patches for the second audited L2-blank candidate,
with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_interiorRowsCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from origin-zero active/corner windows and finite
active-corner layer patches for the first audited L2-blank candidate, with
bounded-interior generated position-code rows at concrete numeric label slots.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_boundedRowsAtIndexCorrect
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from origin-zero active/corner windows and
finite active-corner layer patches for the first audited L2-blank candidate,
with bounded-interior generated position-code rows at concrete numeric label
slots.
-/
theorem
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_boundedRowsAtIndexCorrect
    (originZeroWindows : L2C1OriginZeroWindows)
    (patches : L2C1ActiveCornerLayerPatches)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from origin-zero active/corner windows and finite
active-corner layer patches for the second audited L2-blank candidate, with
bounded-interior generated position-code rows at concrete numeric label slots.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_boundedRowsAtIndexCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from origin-zero active/corner windows and
finite active-corner layer patches for the second audited L2-blank candidate,
with bounded-interior generated position-code rows at concrete numeric label
slots.
-/
theorem
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_boundedRowsAtIndexCorrect
    (originZeroWindows : L2C2OriginZeroWindows)
    (patches : L2C2ActiveCornerLayerPatches)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_origin_zero_layer_patches_position_source
      originZeroWindows patches
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_interiorRowsCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_sourceCode
      data hindex
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_sourceCodeCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_sourceCode
      data hindex
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_sourceCode
      data hindex
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and the source-specialized position-code label-index
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_sourceCodeCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_sourceCode
      data hindex
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the first proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_boundedRowsAtIndexCorrect
    (data : L2C1RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the second proof-facing Robinson Section 7
board/free-line package and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_boundedRowsAtIndexCorrect
    (data : L2C2RobinsonSection7BoardFreeLineData)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_robinson_section7_board_free_line_data_position_source
      data
      (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and exact positive board-level raw Figure 13 square tilings, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hsquares : Figure13PositiveBoardLevelTileableSquares)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_position_source
      boardFreeLineActiveCorner hsquares
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and a raw Figure 13 plane tiling, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_board_free_line_fig13_tiles_plane_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hplane : TilesPlane fig13Tiles)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_pos_board_squares_interiorRowsCorrect
      boardFreeLineActiveCorner
      (positiveBoardLevelTileableSquares_of_tilesPlane_fig13Tiles hplane)
      hinterior

/--
Encoded domino undecidability from the first proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the first proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component1Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c1_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Encoded domino undecidability from the second proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

/--
Unencoded domino undecidability from the second proof-facing board/free-line
invariant and finite raw Figure 13 boxes, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_interiorRowsCorrect
    (boardFreeLineActiveCorner :
      Section7BoardFreeLineActiveCornerInvariant
        l2Component2Figure18ScaffoldData)
    (hboxes : Figure13TileableBoxes)
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_l2c2_board_free_line_fig13_boxes_position_source
      boardFreeLineActiveCorner hboxes
      (positionSourceObligationsOfPositionCodeInteriorRowsCorrect
        hinterior)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the generated position-code decoder step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_decoderStepCorrect
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the generated position-code decoder step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_decoderStepCorrect
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_globalCodeCorrect
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_globalCodeCorrect
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_sourceCodeCorrect
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    encoded_domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from the concrete human-audited Figure 13 layer
table, raw checked active Figure 18 site specs, indexed active-corner windows,
realization, and the source-specialized position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_sourceCodeCorrect
    (activeSiteSpecs : List (Nat × Quadrant))
    (activeSiteSpecs_valid :
      OllingerRobinson.Figure18Site.natSpecsValidBool activeSiteSpecs = true)
    (cornerIndex : Nat) (cornerQuadrant : Quadrant)
    (cornerIndex_valid : decide (cornerIndex < 92) = true)
    (indexedActiveWindows :
      OllingerRobinson.HasFigure18IndexedActiveCornerWindows
        (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
          cornerIndex cornerQuadrant cornerIndex_valid).table.toRoleTable)
    (realizes :
      (figure18ScaffoldDataOfNatSites activeSiteSpecs activeSiteSpecs_valid
        cornerIndex cornerQuadrant cornerIndex_valid).HasRealizationInvariant)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    domino_problem_undecidable_of_figure13_nat_sites_indexed_windows_position_source
      activeSiteSpecs activeSiteSpecs_valid cornerIndex cornerQuadrant
      cornerIndex_valid indexedActiveWindows realizes
      (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)


end TM0FoldedReduction

end LeanWang
