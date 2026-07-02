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
board/free-line layer-patch scaffold package and the generated-position source
obligations for the folded TM0 reduction.  Constructors below also expose the
source-row route and the origin-zero-window route, which derives the checked
stacks from the geometric origin-zero scaffold invariant and the audited finite
Figure 13 / Figure 16 pair-compatibility table.
-/

noncomputable section

namespace LeanWang

/--
The two remaining construction interfaces for the current preferred route to
the domino problem.

`scaffold` packages the Section 7 board/free-line active-corner recognition and
the finite active-corner layer patches for the audited first L2 candidate.
`source` packages the generated-position source reduction obligations.  The
final `positionProgramData` route does not need the stronger statement-list
uniqueness package used by the older canonical-row-equality route.
-/
structure FinalReductionInputs : Prop where
  scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData
  source : TM0FoldedReduction.PositionSourceObligations

/--
Preferred remaining proof obligations for the current construction route.

These are the three proof-facing facts still to be supplied by the scaffold
and source-code construction:
* the Section 7 origin-zero active/corner window invariant for the first
  audited L2 blank candidate;
* row-major checked compatible Figure 16 level data, which supplies the finite
  active-corner layer patches;
* the packaged generated-position source decoder.
-/
structure FinalConstructionObligations : Prop where
  originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup

/--
Finite-check-facing variant of the preferred remaining proof obligations.

The checked stack field is a finite transcription target for the audited first
L2 blank candidate.  It implies the origin-zero active/corner window invariant
used by the scaffold package, so this is the cleaner theorem surface for the
next scaffold-instantiation step.
-/
structure FinalCheckedConstructionObligations : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup

namespace FinalReductionInputs

/-- Build the final inputs directly from the scaffold package and source obligations. -/
def ofScaffoldAndSource
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs where
  scaffold := scaffold
  source := source

/--
Build the final inputs directly from the scaffold package and generated
interior position-code rows.
-/
def ofScaffoldAndSourceRows
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs directly from the scaffold package and the packaged
generated interior position-code decoder.

This is the proof-facing source route: the package carries the row generator
and translated statement-list uniqueness, while
`positionProgramData_haltsEmpty_iff_tm0_eval_dom` discharges semantic
correctness against the Mathlib TM0 evaluator.
-/
def ofScaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofScaffoldAndSource scaffold
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
      sourceRows
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom)

/--
Build the final inputs from the two split finite scaffold obligations for the
first audited L2 candidate: checked origin-zero stacks and finite active-corner
layer patches.
-/
def ofCheckedStacksAndLayerPatchesSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs where
  scaffold :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches
  source := source

/--
Build the final inputs from the two split finite scaffold obligations and
generated interior position-code rows.
-/
def ofCheckedStacksAndLayerPatches
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (patches : TM0FoldedReduction.L2C1ActiveCornerLayerPatches)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStacks
      checkedStacks patches)
    sourceRows

/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate.  This is the current finite transcription target for the scaffold
side: checked origin-zero stacks imply the Section 7 board/free-line
active-corner recognition field, while the supplied patches give the backward
active-corner box realization.
-/
def ofCheckedStackLayerPatchDataSource
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs where
  scaffold :=
    TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold
  source := source

/--
Build the final inputs from the concrete checked-stack/layer-patch finite
certificate and generated interior position-code rows.
-/
def ofCheckedStackLayerPatchData
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofScaffoldAndSourceRows
    (TM0FoldedReduction.l2c1RobinsonSection7BoardFreeLineLayerPatchDataOfCheckedStackLayerPatchData
      scaffold)
    sourceRows

/--
Build the final inputs from checked origin-zero stacks plus compatible Figure
16 macro-squares.  The Figure 16 certificate supplies the active-corner layer
patches for the first audited L2 candidate.
-/
def ofCheckedStacksAndCompatibleFig16Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16
      checkedStacks fig16)
    source

/--
Build the final inputs from checked origin-zero stacks, compatible Figure 16
macro-squares, and generated interior position-code rows.
-/
def ofCheckedStacksAndCompatibleFig16
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16Source
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus compatible
Figure 16 macro-squares.  The checked-stack part is derived from the
origin-zero windows using the audited finite Figure 13/Figure 16
pair-compatibility table.
-/
def ofOriginZeroWindowsAndCompatibleFig16Source
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16
      originZeroWindows fig16)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and generated interior position-code rows.
-/
def ofOriginZeroWindowsAndCompatibleFig16
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16Source
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks plus row-major checked
compatible Figure 16 level data.
-/
def ofCheckedStacksAndCompatibleFig16LevelDataSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16LevelData
      checkedStacks fig16)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and generated interior position-code rows.
-/
def ofCheckedStacksAndCompatibleFig16LevelData
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofCheckedStacksAndCompatibleFig16LevelDataSource
    checkedStacks fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows plus row-major
checked compatible Figure 16 level data.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    FinalReductionInputs :=
  ofCheckedStackLayerPatchDataSource
    (TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfOriginZeroWindowsCanonicalCheckedCompatibleFig16LevelData
      originZeroWindows fig16)
    source

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and generated interior position-code
rows.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelData
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsCorrect
      sourceRows)

set_option linter.style.longLine false in
/--
Build the final inputs from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
def ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    FinalReductionInputs :=
  ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
    originZeroWindows fig16
    (TM0FoldedReduction.positionSourceObligationsOfPositionCodeInteriorRowsWithStatementNodup
      sourceRows
      TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom)

end FinalReductionInputs

namespace FinalConstructionObligations

/-- Convert the preferred final obligation package into the low-level endpoint. -/
def toFinalReductionInputs
    (h : FinalConstructionObligations) :
    FinalReductionInputs :=
  FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
    h.originZeroWindows h.fig16 h.sourceRows

end FinalConstructionObligations

namespace FinalCheckedConstructionObligations

/--
Convert the finite-check-facing obligation package into the window-based
preferred final obligation package.
-/
def toConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    FinalConstructionObligations where
  originZeroWindows :=
    TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks
  fig16 := h.fig16
  sourceRows := h.sourceRows

/-- Convert the finite-check-facing obligation package into the endpoint. -/
def toFinalReductionInputs
    (h : FinalCheckedConstructionObligations) :
    FinalReductionInputs :=
  h.toConstructionObligations.toFinalReductionInputs

end FinalCheckedConstructionObligations

set_option linter.style.longLine false in
/-- Encoded Wang domino undecidability from the final construction inputs. -/
theorem encoded_domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      h.scaffold h.source

set_option linter.style.longLine false in
/-- Wang domino undecidability from the final construction inputs. -/
theorem domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_board_free_line_layer_patch_data_position_source
      h.scaffold h.source

/-- Encoded Wang domino undecidability from the preferred final obligations. -/
theorem encoded_domino_problem_undecidable_of_constructionObligations
    (h : FinalConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/-- Wang domino undecidability from the preferred final obligations. -/
theorem domino_problem_undecidable_of_constructionObligations
    (h : FinalConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

/--
Encoded Wang domino undecidability from the finite-check-facing preferred
final obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable h.toFinalReductionInputs

/--
Wang domino undecidability from the finite-check-facing preferred final
obligations.
-/
theorem domino_problem_undecidable_of_checkedConstructionObligations
    (h : FinalCheckedConstructionObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable h.toFinalReductionInputs

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and packaged source decoder.
-/
theorem encoded_domino_problem_undecidable_of_scaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourcePackage scaffold sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the proof-facing Robinson Section 7
board/free-line layer-patch package and packaged source decoder.
-/
theorem domino_problem_undecidable_of_scaffoldAndSourcePackage
    (scaffold : TM0FoldedReduction.L2C1RobinsonSection7BoardFreeLineLayerPatchData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofScaffoldAndSourcePackage scaffold sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from the checked-stack/layer-patch finite
scaffold certificate and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStackLayerPatchDataSource
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataSource scaffold source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from the checked-stack/layer-patch finite scaffold
certificate and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStackLayerPatchDataSource
    (scaffold : TM0FoldedReduction.L2C1CheckedStackLayerPatchData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStackLayerPatchDataSource scaffold source)

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
Encoded Wang domino undecidability from checked origin-zero stacks, compatible
Figure 16 macro-squares, and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16Source
      checkedStacks fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, compatible Figure 16
macro-squares, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16Source
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16Source
      checkedStacks fig16 source)

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
Encoded Wang domino undecidability from origin-zero active/corner windows,
compatible Figure 16 macro-squares, and generated-position source obligations.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16Source
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16Source
      originZeroWindows fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, compatible
Figure 16 macro-squares, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16Source
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleMacroSquares)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16Source
      originZeroWindows fig16 source)

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
Encoded Wang domino undecidability from checked origin-zero stacks, row-major
checked compatible Figure 16 level data, and generated-position source
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSource
      checkedStacks fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from checked origin-zero stacks, row-major checked
compatible Figure 16 level data, and generated-position source obligations.
-/
theorem domino_problem_undecidable_of_checkedStacksAndCompatibleFig16LevelDataSource
    (checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofCheckedStacksAndCompatibleFig16LevelDataSource
      checkedStacks fig16 source)

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

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
row-major checked compatible Figure 16 level data, and the packaged generated
interior position-code decoder.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataPackage
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and the packaged generated interior
position-code decoder.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataPackage
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsWithStatementNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataPackage
      originZeroWindows fig16 sourceRows)

set_option linter.style.longLine false in
/--
Encoded Wang domino undecidability from origin-zero active/corner windows,
row-major checked compatible Figure 16 level data, and generated-position
source obligations.
-/
theorem encoded_domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
      originZeroWindows fig16 source)

set_option linter.style.longLine false in
/--
Wang domino undecidability from origin-zero active/corner windows, row-major
checked compatible Figure 16 level data, and generated-position source
obligations.
-/
theorem domino_problem_undecidable_of_originZeroWindowsAndCompatibleFig16LevelDataSource
    (originZeroWindows : TM0FoldedReduction.L2C1OriginZeroWindows)
    (fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData)
    (source : TM0FoldedReduction.PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable
    (FinalReductionInputs.ofOriginZeroWindowsAndCompatibleFig16LevelDataSource
      originZeroWindows fig16 source)

end LeanWang

end
