/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Theorems.PositionScaffold

/-!
Scaffold theorem wrappers for generated position-code decoder frontiers.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
Encoded domino undecidability from a scaffold and the generated position-coded
descriptor decoder.  This uses `positionProgramData` directly, so no
row-equivalence proof against the canonical folded rows is required.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCode
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfLabelIndexFromWithPositionCode hindex hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated
position-coded descriptor decoder.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCode
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfLabelIndexFromWithPositionCode hindex hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the generated position-coded
descriptor decoder, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCode
    S hS hindex TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the generated
position-coded descriptor decoder, with `positionProgramData` semantic
correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hindex : Primrec (fun p : Code × Nat × Nat × Nat =>
      sourceSimStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCode
    S hS hindex TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and duplicate-free source statement supports.  Statement uniqueness
identifies the generated position codes with the canonical support-search state
codes.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodup
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodup
      hsearch hnodup hcorrect)

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and duplicate-free source statement supports.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodup
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfSearchCodeLabelIndexFromWithStatementNodup
      hsearch hnodup hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and duplicate-free source statement supports, with `positionProgramData`
semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodupCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodup
    S hS hsearch hnodup
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and duplicate-free source statement supports, with `positionProgramData`
semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodupCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hnodup : SourceStatementListNodup) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodup
    S hS hsearch hnodup
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and concrete started-TM1 statement-support uniqueness/disjointness.

This exposes the proof target below the opaque source statement-list `Nodup`:
local TM1 statement supports must be duplicate-free and pairwise disjoint across
distinct started TM1 labels.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithPairwiseDisjoint
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodup
    S hS hsearch
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)
    hcorrect

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and concrete started-TM1 statement-support uniqueness/disjointness.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_searchCodeWithPairwiseDisjoint
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_searchCodeWithStatementNodup
    S hS hsearch
    (sourceStatementListNodup_of_startedTM1StatementSupportPairwiseDisjoint
      hstmt hdisj)
    hcorrect

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and concrete started-TM1 statement-support uniqueness/disjointness,
with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithPairwiseDisjointCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_searchCodeWithPairwiseDisjoint
    S hS hsearch hstmt hdisj
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold, the bounded-search descriptor
decoder, and concrete started-TM1 statement-support uniqueness/disjointness,
with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_searchCodeWithPairwiseDisjointCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hsearch : SourceSearchCodeLabelIndexFromPrimrec)
    (hstmt : SourceStartedTM1StatementSupportNodup)
    (hdisj : SourceStartedTM1StatementSupportPairwiseDisjoint) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_searchCodeWithPairwiseDisjoint
    S hS hsearch hstmt hdisj
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from a scaffold and the generated position-code
accumulator step.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStep
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated position-code
accumulator step.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStep
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2))
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeDecoderStep hstep hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the generated position-code
accumulator step, with `positionProgramData` semantic correctness discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStepCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStep
    S hS hstep TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the generated position-code
accumulator step, with `positionProgramData` semantic correctness discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStepCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hstep : Primrec (fun p : Code × SourceSearchCodeDecoderState =>
      sourcePositionCodeDecoderStep p.1 p.2)) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeDecoderStep
    S hS hstep TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from a scaffold and the generated one-row
position-code decoder.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRows
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRows hvarRows hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated one-row
position-code decoder.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRows
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : SourcePositionCodeOneRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeOneRows hvarRows hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the generated one-row
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRows
    S hS hvarRows TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the generated one-row
position-code decoder, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hvarRows : SourcePositionCodeOneRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeOneRows
    S hS hvarRows TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from a scaffold and the generated bounded
interior position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRows
      hinterior hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated bounded
interior position-code rows.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeBoundedInteriorRows
      hinterior hcorrect)

set_option linter.style.longLine false in
/--
Encoded domino undecidability from a scaffold and the generated bounded
interior position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRows
    S hS hinterior
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

set_option linter.style.longLine false in
/--
Unencoded domino undecidability from a scaffold and the generated bounded
interior position-code rows, with `positionProgramData` semantic correctness
discharged.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRowsCorrect
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeBoundedInteriorRowsPrimrec) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source_positionCodeBoundedRows
    S hS hinterior
    TM0FoldedCompiler.positionProgramData_haltsEmpty_iff_tm0_eval_dom

/--
Encoded domino undecidability from a scaffold and the generated interior
position-code rows.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRows
      hinterior hcorrect)

/--
Unencoded domino undecidability from a scaffold and the generated interior
position-code rows.
-/
theorem domino_problem_undecidable_of_scaffold_position_source_positionCodeInteriorRows
    (S : Scaffold) (hS : IsScaffold S)
    (hinterior : SourcePositionCodeInteriorRowsPrimrec)
    (hcorrect : ∀ tc : Turing.ToPartrec.Code,
      (TM0FoldedCompiler.positionProgramData tc).HaltsEmpty ↔
        (Turing.TM0.eval
          (TM0Route.partrecStartedTM0Machine tc)
          TM0Route.partrecStartedTM0Input).Dom) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source S hS
    (positionSourceObligationsOfPositionCodeInteriorRows
      hinterior hcorrect)

end TM0FoldedReduction

end LeanWang
