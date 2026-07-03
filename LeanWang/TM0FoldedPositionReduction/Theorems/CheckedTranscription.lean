/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.PresentedFlexible

/-!
Checked-transcription final theorem wrappers for the generated position-coded
folded reduction.
-/


namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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
transcription and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_checked_transcription_position_source_decoderStepCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source_decoderStepCorrect
    D.toPresentedFlexibleInstance hstep

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and the generated position-code accumulator step, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_checked_transcription_position_source_decoderStepCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source_decoderStepCorrect
    D.toPresentedFlexibleInstance hstep

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a checked flexible finite scaffold
transcription and the generated one-row-at-index position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_checked_transcription_position_source_oneRowsAtIndexCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source_oneRowsAtIndexCorrect
    D.toPresentedFlexibleInstance hrows

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and the generated one-row-at-index position-code decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_checked_transcription_position_source_oneRowsAtIndexCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source_oneRowsAtIndexCorrect
    D.toPresentedFlexibleInstance hrows

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a checked flexible finite scaffold
transcription and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_checked_transcription_position_source_globalCodeCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source_globalCodeCorrect
    D.toPresentedFlexibleInstance hindex

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a checked flexible finite scaffold
transcription and the global position-code label-index decoder, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_checked_transcription_position_source_globalCodeCorrect
    (D : OllingerRobinson.CheckedFlexibleTranscription)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source_globalCodeCorrect
    D.toPresentedFlexibleInstance hindex

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
