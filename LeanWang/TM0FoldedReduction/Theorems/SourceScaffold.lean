/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedReduction.Obligations
import LeanWang.TM0FoldedCompiler.CorrectnessPosition

/-!
Ordinary source-route fixed-domino and scaffold reductions.
-/

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/--
Fixed-domino instance produced directly from the normalized folded program for
a source partial-recursive code.
-/
noncomputable def sourceFixedDominoReduction
    (_h : SourceObligations) (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData
    (PostProgram.toTableProgram
      (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)))

theorem sourceFixedDominoReduction_computable
    (h : SourceObligations) :
    Computable (sourceFixedDominoReduction h) := by
  exact tableProgramFixedDominoData_computable.comp
    (PostProgram.toTableProgram_computable.comp h.program_computable)

theorem sourceFixedDominoReduction_correct
    (h : SourceObligations) (c : Code) :
    TilesQuarterWithSeed (sourceFixedDominoReduction h c).1
        (sourceFixedDominoReduction h c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold sourceFixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff
      (PostProgram.toTableProgram
        (TM0FoldedCompiler.programData
          (NatPartrecToToPartrec.translate c))))]
  rw [tableProgramFixedDomino_correct]
  rw [PostProgram.toTableProgram_toMachine_haltsEmpty_iff]
  rw [h.correct c]

/--
Final scaffolded tileset produced from the normalized folded program for a
source partial-recursive code.
-/
noncomputable def sourceDominoReduction
    (S : Scaffold) (h : SourceObligations) (c : Code) : TileSet :=
  combineWithScaffold S (sourceFixedDominoReduction h c).1
    (sourceFixedDominoReduction h c).2

theorem sourceDominoReduction_computable
    (S : Scaffold) (h : SourceObligations) :
    Computable (sourceDominoReduction S h) := by
  exact (combineWithScaffold_computable S).comp
    (sourceFixedDominoReduction_computable h)

theorem sourceDominoReduction_correct
    {S : Scaffold} (hS : IsScaffold S) (h : SourceObligations) (c : Code) :
    TilesPlane (sourceDominoReduction S h c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourceDominoReduction]
  exact (scaffold_reduction_correct hS
    (sourceFixedDominoReduction h c).1
    (sourceFixedDominoReduction h c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (sourceFixedDominoReduction h c).1
        (sourceFixedDominoReduction h c).2).symm.trans
          (sourceFixedDominoReduction_correct h c))

/-- Encoded version of the normalized source folded reduction. -/
noncomputable def sourceDominoReductionCode
    (S : Scaffold) (h : SourceObligations) (c : Code) : Nat :=
  encodeTileSet (sourceDominoReduction S h c)

theorem sourceDominoReductionCode_computable
    (S : Scaffold) (h : SourceObligations) :
    Computable (sourceDominoReductionCode S h) := by
  exact encodeTileSet_computable.comp (sourceDominoReduction_computable S h)

theorem sourceDominoReductionCode_correct
    {S : Scaffold} (hS : IsScaffold S) (h : SourceObligations) (c : Code) :
    TilesPlane (decodeTileSet (sourceDominoReductionCode S h c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourceDominoReductionCode, decodeTileSet_encodeTileSet]
  exact sourceDominoReduction_correct hS h c

/--
Encoded domino undecidability from ordinary source-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold_source
    (S : Scaffold) (hS : IsScaffold S) (h : SourceObligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro hdec
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (sourceDominoReductionCode S h c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (sourceDominoReductionCode_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hencoded.of_eq fun c => sourceDominoReductionCode_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Unencoded domino undecidability from ordinary source-route obligations.
-/
theorem domino_problem_undecidable_of_scaffold_source
    (S : Scaffold) (hS : IsScaffold S) (h : SourceObligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro hdec
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (sourceDominoReduction S h c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (sourceDominoReduction_computable S h)) hdec
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hdomino.of_eq fun c => sourceDominoReduction_correct hS h c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

end TM0FoldedReduction

end LeanWang
