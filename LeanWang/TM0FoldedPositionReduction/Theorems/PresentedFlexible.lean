/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionReduction.Theorems.Scaffold
import LeanWang.OllingerRobinsonTranscription

/-!
Presented-flexible-instance final theorem wrappers for the generated
position-coded folded reduction.
-/


namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-code accumulator step,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_decoderStepCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-code accumulator step,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_decoderStepCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hstep : SourcePositionCodeDecoderStepPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeDecoderStepCorrect hstep)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the source-specialized position-code start
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_startCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the source-specialized position-code start
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_startCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hstart : SourcePositionCodeLabelIndexStartPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeLabelIndexStartCorrect hstart)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated one-row-at-index position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_oneRowsAtIndexCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated one-row-at-index position-code
decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_oneRowsAtIndexCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hrows : SourcePositionCodeOneRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeOneRowsAtIndexCorrect hrows)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_boundedRowsAtIndexCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and bounded-interior generated position-code rows at
concrete numeric label slots, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_boundedRowsAtIndexCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hbounded : SourcePositionCodeBoundedInteriorRowsAtIndexPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfPositionCodeBoundedInteriorRowsAtIndexCorrect hbounded)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the global position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_globalCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the global position-code label-index decoder,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_globalCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hindex : GlobalPositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfGlobalPositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source_sourceCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the source-specialized position-code
label-index decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_sourceCodeCorrect
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hindex : SourcePositionCodeLabelIndexFromPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_flexible_position_source
    I (positionSourceObligationsOfSourcePositionCodeLabelIndexFromCorrect hindex)

end TM0FoldedReduction

end LeanWang
