/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction

/-!
Final theorem surface for the Wang-tile undecidability proof.

This module keeps the public endpoint small.  The remaining work is isolated in
`FinalReductionInputs`: the finite-transcription-facing Robinson Section 7
board/free-line layer-patch scaffold package and the source-uniform generated
row primitive-recursion proof for the folded TM0 reduction.  Constructors below
also expose the origin-zero-window route, which derives the checked stacks from
the geometric origin-zero scaffold invariant and the audited finite Figure 13 /
Figure 16 pair-compatibility table.
-/

noncomputable section

namespace LeanWang

/--
The two remaining construction interfaces for the current preferred route to
the domino problem.

`scaffold` packages the Section 7 board/free-line active-corner recognition and
the finite active-corner layer patches for the audited first L2 candidate.
`sourceRows` is the source-uniform generated position-code row
primitive-recursion proof for the folded TM0 reduction.  The final
`positionProgramData` route does not need the stronger statement-list
uniqueness package used by the older canonical-row-equality route.
-/
structure FinalReductionInputs : Prop where
  scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

namespace FinalReductionInputs

/--
Build the final inputs from the two split finite scaffold obligations for the
first audited L2 candidate: checked origin-zero stacks and finite active-corner
layer patches.
-/
def ofCheckedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs where
  scaffold :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches
  sourceRows := sourceRows

/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate.  This is the current finite transcription target for the scaffold
side: checked origin-zero stacks imply the Section 7 board/free-line
active-corner recognition field, while the supplied patches give the backward
active-corner box realization.
-/
def ofCheckedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs where
  scaffold :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold
  sourceRows := sourceRows

/--
Build the final inputs from checked origin-zero stacks plus compatible Figure
16 macro-squares.  The Figure 16 certificate supplies the active-corner layer
patches for the first audited L2 candidate.
-/
def ofCheckedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchData
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      checkedStacks fig16)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus compatible
Figure 16 macro-squares.  The checked-stack part is derived from the
origin-zero windows using the audited finite Figure 13/Figure 16
pair-compatibility table.
-/
def ofOriginZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchData
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
      originZeroWindows fig16)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus row-major checked
compatible Figure 16 level data.
-/
def ofCheckedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchData
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16LevelData
      checkedStacks fig16)
    sourceRows

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus row-major
checked compatible Figure 16 level data.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchData
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16LevelData
      originZeroWindows fig16)
    sourceRows

end FinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded Wang domino undecidability from the final construction inputs. -/
theorem encoded_domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsCorrect
      h.scaffold h.sourceRows

set_option linter.style.longLine false in
/-- Wang domino undecidability from the final construction inputs. -/
theorem domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_interiorRowsCorrect
      h.scaffold h.sourceRows

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchData scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the split checked-stack and layer-patch
finite scaffold obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatches
      checkedStacks patches sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the split checked-stack and layer-patch finite
scaffold obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndLayerPatches
      checkedStacks patches sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks and
compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks and compatible
Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
compatible Figure 16 macro-squares.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and
compatible Figure 16 macro-squares.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from checked origin-zero stacks and row-major
checked compatible Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelData
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks and row-major checked
compatible Figure 16 level data.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelData
      checkedStacks fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows and
row-major checked compatible Figure 16 level data.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelData
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows and row-major
checked compatible Figure 16 level data.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelData
      originZeroWindows fig16 sourceRows)

end LeanWang

end
