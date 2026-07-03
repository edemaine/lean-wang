/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.SourceObligations

/-!
Scaffold-generic final theorem wrappers for the generated position-coded
folded reduction.
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

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the generated one-row-at-index
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_oneRowsAtIndexCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the generated
one-row-at-index position-code decoder, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_oneRowsAtIndexCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_boundedRowsAtIndexCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and bounded-interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_boundedRowsAtIndexCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_interiorRowsAtIndexCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and interior generated
position-code rows at concrete numeric label slots, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_interiorRowsAtIndexCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRowsAtIndexCorrect hinterior)

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

end TM0FoldedReduction

end LeanWang
