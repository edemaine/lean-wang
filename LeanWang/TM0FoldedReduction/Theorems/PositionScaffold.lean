/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Obligations
import LeanWang.TM0FoldedCompiler.CorrectnessPosition

/-!
Generated position-coded source-route fixed-domino and scaffold reductions.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

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

end TM0FoldedReduction

end LeanWang
