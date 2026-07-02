/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure18PositionReduction

/-!
Final theorem surface for the Wang-tile undecidability proof.

This module keeps the public endpoint small.  The remaining work is isolated in
`FinalReductionInputs`: the checked finite scaffold certificates and the
source-uniform generated row primitive-recursion proof for the folded TM0
reduction.
-/

noncomputable section

namespace LeanWang

/--
The two remaining construction interfaces for the current preferred route to
the domino problem.

`checkedStacks` is the finite origin-zero checked-stack certificate for the
audited first L2 candidate.  `fig16` is the row-major checked compatible
Figure 16 level data that supplies active-corner layer patches.
`sourceRows` is the source-uniform generated position-code row
primitive-recursion proof for the folded TM0 reduction.  The final
`positionProgramData` route does not need the stronger statement-list
uniqueness package used by the older canonical-row-equality route.
-/
structure FinalReductionInputs : Prop where
  checkedStacks : TM0FoldedReduction.L2C1OriginZeroCheckedStacks
  fig16 : TM0FoldedReduction.Figure18CanonicalCheckedRecognizedCompatibleLevelData
  sourceRows : TM0FoldedReduction.SourcePositionCodeInteriorRowsPrimrec

namespace FinalReductionInputs

set_option linter.style.longLine false in
/--
The two scaffold-side final inputs package into the finite-check-facing Section
7 scaffold data used by the current reduction chain.
-/
def checkedStackLayerPatchData (h : FinalReductionInputs) :
    TM0FoldedReduction.L2C1CheckedStackLayerPatchData :=
  TM0FoldedReduction.l2c1CheckedStackLayerPatchDataOfCheckedStacksCanonicalCheckedCompatibleFig16LevelData
    h.checkedStacks h.fig16

/--
The checked-stack certificate also supplies the origin-zero active/corner
windows used by older intermediate theorem surfaces.
-/
def originZeroWindows (h : FinalReductionInputs) :
    TM0FoldedReduction.L2C1OriginZeroWindows :=
  TM0FoldedReduction.l2c1OriginZeroWindowsOfCheckedStacks h.checkedStacks

end FinalReductionInputs

set_option linter.style.longLine false in
/-- Encoded Wang domino undecidability from the final construction inputs. -/
theorem encoded_domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  exact
    TM0FoldedReduction.encoded_domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
      h.checkedStackLayerPatchData h.sourceRows

set_option linter.style.longLine false in
/-- Wang domino undecidability from the final construction inputs. -/
theorem domino_problem_undecidable (h : FinalReductionInputs) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  exact
    TM0FoldedReduction.domino_problem_undecidable_l2c1_checked_stack_layer_patches_interiorRowsCorrect
      h.checkedStackLayerPatchData h.sourceRows

end LeanWang

end
