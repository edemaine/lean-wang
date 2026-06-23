/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram
import LeanWang.Theorems

/-!
Packaging the folded finite-TM0 construction as the machine-side reduction.

`TM0FoldedProgram` provides the executable finite program data. This file
isolates the exact obligations needed to instantiate the main theorem surface:
computability of that program map and its semantic correctness against Mathlib's
translated TM0 evaluator.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedReduction

open Nat.Partrec (Code)

/-- The remaining obligations for the folded finite-TM0 route. -/
structure Obligations where
  program_computable :
    Computable (fun tc : Turing.ToPartrec.Code => TM0FoldedCompiler.program tc)
  correct : ∀ tc : Turing.ToPartrec.Code,
    (TM0FoldedCompiler.program tc).HaltsEmpty ↔
      (Turing.TM0.eval
        (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom

/--
The folded finite-TM0 construction packaged as the `TM0FiniteCompiler`
interface used by the main theorem surface.
-/
def compiler (h : Obligations) : TM0FiniteCompiler where
  compile := TM0FoldedCompiler.program
  compile_computable := h.program_computable
  correct := h.correct

/--
The exact obligations needed for the final reduction from `Nat.Partrec.Code`.

This avoids asking for computability of the folded compiler on every
`Turing.ToPartrec.Code`; the undecidability proof only uses codes reached by the
computable translation `NatPartrecToToPartrec.translate`.
-/
structure SourceObligations where
  program_computable :
    Computable (fun c : Code =>
      TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))
  correct : ∀ c : Code,
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c)).HaltsEmpty ↔
      (Nat.Partrec.Code.eval c 0).Dom

/-- Broad folded-route obligations imply the source-code obligations actually used. -/
def Obligations.toSource (h : Obligations) : SourceObligations where
  program_computable := by
    exact (h.program_computable.comp NatPartrecToToPartrec.translate_computable).of_eq
      fun c => (TM0FoldedCompiler.programData_eq_program
        (NatPartrecToToPartrec.translate c)).symm
  correct := by
    intro c
    rw [TM0FoldedCompiler.programData_eq_program]
    exact (h.correct (NatPartrecToToPartrec.translate c)).trans
      ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2
          (NatPartrecToToPartrec.translate c)).trans
        ((TM0Route.partrecStartedTM2_eval_dom_iff_partrec
            (NatPartrecToToPartrec.translate c)).trans
          (NatPartrecToToPartrec.translate_tm2_dom c)))

/-- Apply the folded source-code reduction and then the current table bridge. -/
def sourceTableProgram (_h : SourceObligations) (c : Code) : TableProgram :=
  PostProgram.toTableProgram
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))

theorem sourceTableProgram_computable (h : SourceObligations) :
    Computable (sourceTableProgram h) := by
  exact PostProgram.toTableProgram_computable.comp h.program_computable

theorem sourceTableProgram_correct (h : SourceObligations) (c : Code) :
    Machine.HaltsEmpty (sourceTableProgram h c).toMachine ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  exact (PostProgram.toTableProgram_toMachine_haltsEmpty_iff
    (TM0FoldedCompiler.programData (NatPartrecToToPartrec.translate c))).trans
      (h.correct c)

/-- Fixed-domino instance produced directly from a source partial-recursive code. -/
def sourceFixedDominoReduction (h : SourceObligations) (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData (sourceTableProgram h c)

theorem sourceFixedDominoReduction_computable (h : SourceObligations) :
    Computable (sourceFixedDominoReduction h) := by
  exact tableProgramFixedDominoData_computable.comp (sourceTableProgram_computable h)

theorem sourceFixedDominoReduction_correct (h : SourceObligations) (c : Code) :
    TilesQuarterWithSeed (sourceFixedDominoReduction h c).1
        (sourceFixedDominoReduction h c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold sourceFixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff (sourceTableProgram h c))]
  rw [tableProgramFixedDomino_correct]
  rw [sourceTableProgram_correct h]

/-- Final scaffolded tileset produced directly from a source partial-recursive code. -/
def sourceDominoReduction (S : Scaffold) (h : SourceObligations) (c : Code) : TileSet :=
  combineWithScaffold S (sourceFixedDominoReduction h c).1
    (sourceFixedDominoReduction h c).2

theorem sourceDominoReduction_computable (S : Scaffold) (h : SourceObligations) :
    Computable (sourceDominoReduction S h) := by
  exact (combineWithScaffold_computable S).comp (sourceFixedDominoReduction_computable h)

theorem sourceDominoReduction_correct
    {S : Scaffold} (hS : IsScaffold S) (h : SourceObligations) (c : Code) :
    TilesPlane (sourceDominoReduction S h c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [sourceDominoReduction]
  exact (scaffold_reduction_correct hS
    (sourceFixedDominoReduction h c).1 (sourceFixedDominoReduction h c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (sourceFixedDominoReduction h c).1
        (sourceFixedDominoReduction h c).2).symm.trans
          (sourceFixedDominoReduction_correct h c))

/-- Encoded version of the source-code folded reduction. -/
def sourceDominoReductionCode
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
Encoded domino undecidability from a scaffold and the folded finite-TM0 route,
assuming the isolated folded-route obligations.
-/
theorem encoded_domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (h : Obligations) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) :=
  encoded_domino_problem_undecidable_of_scaffold_tm0Compiler
    S hS (compiler h)

/--
Unencoded domino undecidability from a scaffold and the folded finite-TM0 route,
assuming the isolated folded-route obligations.
-/
theorem domino_problem_undecidable_of_scaffold
    (S : Scaffold) (hS : IsScaffold S) (h : Obligations) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) :=
  domino_problem_undecidable_of_scaffold_tm0Compiler
    S hS (compiler h)

/--
Encoded domino undecidability from the exact source-code folded-route
obligations.
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
Unencoded domino undecidability from the exact source-code folded-route
obligations.
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

end
