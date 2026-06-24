/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction
import LeanWang.TM0FoldedPositionCorrect

/-!
Semantic final packaging for the generated position-coded folded reduction.

`TM0FoldedReduction` stays lightweight and keeps semantic correctness as an
explicit parameter.  This module imports the folded semantic proof and
instantiates that parameter for downstream final-theorem use.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

/--
Generated-position source obligations from only the source-level computability
proof, using the semantic correctness theorem for `positionProgramData`.
-/
def positionSourceObligationsOfProgramDataCorrect
    (hprogram : Computable (fun c : Code =>
      TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c))) :
    PositionSourceObligations :=
  positionSourceObligationsOfProgramData hprogram
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated position-code descriptor rows gives
the full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfLabelIndexFromWithPositionCodeCorrect
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfLabelIndexFromWithPositionCode hindex
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Primitive recursiveness of the generated interior position-code rows gives the
full generated-position source obligations once the semantic folded proof is
imported.
-/
def positionSourceObligationsOfPositionCodeInteriorRowsCorrect
    (hinterior : Primrec (fun p : Code × Nat × Nat × TM0Route.PartrecVar =>
      sourcePositionCodeInteriorRowsIndexVar p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    PositionSourceObligations :=
  positionSourceObligationsOfPositionCodeInteriorRows hinterior
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

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

end TM0FoldedReduction

end LeanWang
