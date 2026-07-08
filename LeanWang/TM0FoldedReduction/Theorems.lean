/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Obligations

/-!
This module is split out from `LeanWang.TM0FoldedReduction` so Lake can
cache the machine-side reduction layers separately while preserving the old
public import path.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
The current lowest-level folded computability target, phrased at source-code
level: primitive recursiveness of the fully offset label-index descriptor
decoder implies computability of the normalized folded finite-TM0 program data
used by the final reduction.
-/
theorem sourceProgramData_computable_of_global_labelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFrom hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFrom'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFrom hindex).of_eq fun _ => rfl

/--
Global canonical numeric-state decoder bridge for the source reduction.
This is the non-source-specialized version of
`sourceProgramData_computable_of_source_labelIndexStartWithCode`.
-/
theorem sourceProgramData_computable_of_global_labelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexStartWithCode
      hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexStartWithCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexStartWithCode hindex).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_global_labelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFromWithCode hindex).comp
    NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFromWithCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFromWithCode hindex).of_eq fun _ => rfl

theorem sourceProgramData_computable_of_global_labelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable sourceProgramData :=
  (TM0FoldedCompiler.programData_computable_of_simStepDataForLabelIndexFromWithSearchCode
    hindex).comp NatPartrecToToPartrec.translate_computable

theorem sourceProgramData_computable_of_global_labelIndexFromWithSearchCode'
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      TM0FoldedCompiler.simStepDataForLabelIndexFromWithSearchCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)) :=
  (sourceProgramData_computable_of_global_labelIndexFromWithSearchCode hindex).of_eq fun _ => rfl

/--
Fixed-domino instance produced directly from the generated position-coded
folded program for a source partial-recursive code.
-/
noncomputable def sourcePositionFixedDominoReduction
    (_h : PositionSourceObligations) (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData
    (PostProgram.toTableProgram
      (TM0FoldedCompiler.positionProgramData (NatPartrecToToPartrec.translate c)))

theorem sourcePositionFixedDominoReduction_computable
    (h : PositionSourceObligations) :
    Computable (sourcePositionFixedDominoReduction h) := by
  exact tableProgramFixedDominoData_computable.comp
    (PostProgram.toTableProgram_computable.comp h.program_computable)

theorem sourcePositionFixedDominoReduction_correct
    (h : PositionSourceObligations) (c : Code) :
    TilesQuarterWithSeed (sourcePositionFixedDominoReduction h c).1
        (sourcePositionFixedDominoReduction h c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold sourcePositionFixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff
      (PostProgram.toTableProgram
        (TM0FoldedCompiler.positionProgramData
          (NatPartrecToToPartrec.translate c))))]
  rw [tableProgramFixedDomino_correct]
  rw [PostProgram.toTableProgram_toMachine_haltsEmpty_iff]
  rw [h.correct c]

/--
Final scaffolded tileset produced from the generated position-coded folded
program for a source partial-recursive code.
-/
noncomputable def sourcePositionDominoReduction
    (S : Scaffold) (h : PositionSourceObligations) (c : Code) : TileSet :=
  combineWithScaffold S (sourcePositionFixedDominoReduction h c).1
    (sourcePositionFixedDominoReduction h c).2

theorem sourcePositionDominoReduction_computable
    (S : Scaffold) (h : PositionSourceObligations) :
    Computable (sourcePositionDominoReduction S h) := by
  exact (combineWithScaffold_computable S).comp
    (sourcePositionFixedDominoReduction_computable h)

theorem sourcePositionDominoReduction_correct
    {S : Scaffold} (hS : IsScaffold S) (h : PositionSourceObligations) (c : Code) :
    TilesPlane (sourcePositionDominoReduction S h c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourcePositionDominoReduction]
  exact (scaffold_reduction_correct hS
    (sourcePositionFixedDominoReduction h c).1
    (sourcePositionFixedDominoReduction h c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (sourcePositionFixedDominoReduction h c).1
        (sourcePositionFixedDominoReduction h c).2).symm.trans
          (sourcePositionFixedDominoReduction_correct h c))

/-- Encoded version of the generated position-coded source folded reduction. -/
noncomputable def sourcePositionDominoReductionCode
    (S : Scaffold) (h : PositionSourceObligations) (c : Code) : Nat :=
  encodeTileSet (sourcePositionDominoReduction S h c)

theorem sourcePositionDominoReductionCode_computable
    (S : Scaffold) (h : PositionSourceObligations) :
    Computable (sourcePositionDominoReductionCode S h) := by
  exact encodeTileSet_computable.comp (sourcePositionDominoReduction_computable S h)

theorem sourcePositionDominoReductionCode_correct
    {S : Scaffold} (hS : IsScaffold S) (h : PositionSourceObligations) (c : Code) :
    TilesPlane (decodeTileSet (sourcePositionDominoReductionCode S h c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourcePositionDominoReductionCode, decodeTileSet_encodeTileSet]
  exact sourcePositionDominoReduction_correct hS h c

/--
Encoded domino undecidability from the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_position_source
    (S : Scaffold) (hS : IsScaffold S) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro hdec
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (sourcePositionDominoReductionCode S h c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (sourcePositionDominoReductionCode_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hencoded.of_eq fun c => sourcePositionDominoReductionCode_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Unencoded domino undecidability from the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_scaffold_position_source
    (S : Scaffold) (hS : IsScaffold S) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro hdec
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (sourcePositionDominoReduction S h c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (sourcePositionDominoReduction_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hdomino.of_eq fun c => sourcePositionDominoReduction_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Encoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated position-coded source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_presented_position_source
    (I : OllingerRobinson.PresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Unencoded domino undecidability from a presented Ollinger/Robinson scaffold and
the generated position-coded source-route obligations.
-/
theorem domino_problem_undecidable_of_presented_position_source
    (I : OllingerRobinson.PresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Encoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_presented_flexible_position_source
    (I : OllingerRobinson.PresentedFlexibleInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Unencoded domino undecidability from a flexibly certified presented
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_presented_flexible_position_source
    (I : OllingerRobinson.PresentedFlexibleInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_position_source
    I.presentation.toScaffold I.isScaffold h

/--
Encoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem encoded_domino_problem_undecidable_of_checked_position_source
    (I : OllingerRobinson.CheckedPresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

/--
Unencoded domino undecidability from a checked finite-data
Ollinger/Robinson scaffold and the generated position-coded source-route
obligations.
-/
theorem domino_problem_undecidable_of_checked_position_source
    (I : OllingerRobinson.CheckedPresentedInstance) (h : PositionSourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_presented_position_source
    I.toPresentedInstance h

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
