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
row primitive-recursion proof for the folded TM0 reduction.
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

end LeanWang

end
