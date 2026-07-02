/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.SourceObligations
import LeanWang.OllingerRobinsonTranscription

/-!
Semantic final theorem wrappers for the generated position-coded folded
reduction.

This module keeps the theorem-facing wrappers separate from the semantic source
obligation constructors so edits to final theorem surfaces do not require
rechecking the constructor module.
-/

noncomputable section

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
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

/--
Unencoded domino undecidability from a scaffold and the generated position-code
accumulator step, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_decoderStepCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
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

end TM0FoldedReduction

end LeanWang
