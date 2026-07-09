/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Theorems.PositionCode
import LeanWang.TM0FoldedReduction.Theorems.Presented

/-!
Presented and checked wrappers for generated interior position-code row frontiers.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
Encoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

/--
Unencoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated interior position-code rows, with `positionProgramData` semantic
correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRowsCorrect
    (I : OllingerRobinson.PresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I hinterior TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated interior position-code rows, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRowsCorrect
    (I : OllingerRobinson.PresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I hinterior TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.CheckedPresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I.toPresentedInstance hinterior hcorrect

/--
Unencoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.CheckedPresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source_positionCodeInteriorRows
    I.toPresentedInstance hinterior hcorrect

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a checked finite-data Ollinger/Robinson
scaffold and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRowsCorrect
    (I : OllingerRobinson.CheckedPresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRows
    I hinterior TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a checked finite-data Ollinger/Robinson
scaffold and the generated interior position-code rows, with
`positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRowsCorrect
    (I : OllingerRobinson.CheckedPresentedInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_checked_position_source_positionCodeInteriorRows
    I hinterior TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem
encoded_domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated interior position-code rows.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source_positionCodeInteriorRows
    (I : OllingerRobinson.PresentedFlexibleInstance)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    I.presentation.toScaffold I.isScaffold hinterior hcorrect

end TM0FoldedReduction

end LeanWang
