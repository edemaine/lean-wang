/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonScaffold
import LeanWang.RoutedScaffold
import LeanWang.Theorems
import LeanWang.UniversalTM0TableauData
import Mathlib.Computability.Reduce

/-!
# Direct-input fixed-universal-machine Wang reduction

The simulation control and all normal simulation rows are constants. A source
code changes only the finite input word forced directly along the bottom Wang
row; no machine initializer writes or rewinds that input.

Compared with the old source-program route, no theorem here needs to decode a
dependent `Turing.ToPartrec.Code` statement or prove that such a decoder is
uniformly primitive recursive. Compared with the generated-initializer route,
the executable reduction also avoids compiling input-specific machine states.
-/

noncomputable section

namespace LeanWang

namespace UniversalFoldedReduction

open Nat.Partrec (Code)

/-- Fixed-corner Wang instance with the source input forced on its bottom row. -/
def fixedDominoReduction (c : Code) : TileSet × WangTile :=
  UniversalTM0Tableau.fixedDominoData (UniversalTM0Semantic.input c)

theorem fixedDominoReduction_computable : Computable fixedDominoReduction := by
  exact UniversalTM0Tableau.fixedDominoData_computable.comp
    UniversalTM0Semantic.input_computable

theorem fixedDominoReduction_correct (c : Code) :
    TilesQuarterWithSeed (fixedDominoReduction c).1
        (fixedDominoReduction c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  exact (UniversalTM0Tableau.tilesQuarterWithSeed_iff_not_dom
    (UniversalTM0Semantic.input c)).trans
      (not_congr (UniversalTM0Semantic.tm0_eval_dom_iff c))

/-- Plane-tiling instance after applying any proved scaffold. -/
def dominoReduction (S : Scaffold) (c : Code) : TileSet :=
  combineWithScaffold S (fixedDominoReduction c).1
    (fixedDominoReduction c).2

theorem dominoReduction_computable (S : Scaffold) :
    Computable (dominoReduction S) := by
  exact (combineWithScaffold_computable S).comp fixedDominoReduction_computable

theorem dominoReduction_correct
    {S : Scaffold} (hS : IsScaffold S) (c : Code) :
    TilesPlane (dominoReduction S c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [dominoReduction]
  exact (scaffold_reduction_correct hS
    (fixedDominoReduction c).1 (fixedDominoReduction c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (fixedDominoReduction c).1 (fixedDominoReduction c).2).symm.trans
          (fixedDominoReduction_correct c))

def dominoReductionCode (S : Scaffold) (c : Code) : Nat :=
  encodeTileSet (dominoReduction S c)

theorem dominoReductionCode_computable (S : Scaffold) :
    Computable (dominoReductionCode S) := by
  exact encodeTileSet_computable.comp (dominoReduction_computable S)

theorem dominoReductionCode_correct
    {S : Scaffold} (hS : IsScaffold S) (c : Code) :
    TilesPlane (decodeTileSet (dominoReductionCode S c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [dominoReductionCode, decodeTileSet_encodeTileSet]
  exact dominoReduction_correct hS c

/-- Encoded domino undecidability from the fixed-universal-machine route. -/
theorem encoded_domino_problem_undecidable
    (S : Scaffold) (hS : IsScaffold S) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro hdec
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (dominoReductionCode S c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (dominoReductionCode_computable S)) hdec
  have hnonhalting : ComputablePred
      (fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom) :=
    hencoded.of_eq fun c => dominoReductionCode_correct hS c
  exact ComputablePred.halting_problem 0
    ((hnonhalting.not).of_eq fun _ => not_not)

/-- Unencoded domino undecidability from the fixed-universal-machine route. -/
theorem domino_problem_undecidable
    (S : Scaffold) (hS : IsScaffold S) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro hdec
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (dominoReduction S c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (dominoReduction_computable S)) hdec
  have hnonhalting : ComputablePred
      (fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom) :=
    hdomino.of_eq fun c => dominoReduction_correct hS c
  exact ComputablePred.halting_problem 0
    ((hnonhalting.not).of_eq fun _ => not_not)

/-- Plane-tiling instance after applying a channel-aware routed scaffold. -/
def routedDominoReduction (S : RoutedScaffold) (c : Code) : TileSet :=
  combineWithRoutedScaffold S (fixedDominoReduction c).1
    (fixedDominoReduction c).2

theorem routedDominoReduction_computable (S : RoutedScaffold) :
    Computable (routedDominoReduction S) := by
  exact (combineWithRoutedScaffold_computable S).comp
    fixedDominoReduction_computable

theorem routedDominoReduction_correct
    {S : RoutedScaffold} (hS : IsRoutedScaffold S) (c : Code) :
    TilesPlane (routedDominoReduction S c) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [routedDominoReduction]
  exact (routedScaffold_reduction_correct hS
    (fixedDominoReduction c).1 (fixedDominoReduction c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (fixedDominoReduction c).1 (fixedDominoReduction c).2).symm.trans
          (fixedDominoReduction_correct c))

def routedDominoReductionCode (S : RoutedScaffold) (c : Code) : Nat :=
  encodeTileSet (routedDominoReduction S c)

theorem routedDominoReductionCode_computable (S : RoutedScaffold) :
    Computable (routedDominoReductionCode S) := by
  exact encodeTileSet_computable.comp (routedDominoReduction_computable S)

theorem routedDominoReductionCode_correct
    {S : RoutedScaffold} (hS : IsRoutedScaffold S) (c : Code) :
    TilesPlane (decodeTileSet (routedDominoReductionCode S c)) ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [routedDominoReductionCode, decodeTileSet_encodeTileSet]
  exact routedDominoReduction_correct hS c

/-- Encoded domino undecidability from a channel-aware routed scaffold. -/
theorem encoded_domino_problem_undecidable_of_routed
    (S : RoutedScaffold) (hS : IsRoutedScaffold S) :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro hdec
  have hencoded : ComputablePred
      (fun c : Code =>
        TilesPlane (decodeTileSet (routedDominoReductionCode S c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        (routedDominoReductionCode_computable S)) hdec
  have hnonhalting : ComputablePred
      (fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom) :=
    hencoded.of_eq fun c => routedDominoReductionCode_correct hS c
  exact ComputablePred.halting_problem 0
    ((hnonhalting.not).of_eq fun _ => not_not)

/-- Unencoded domino undecidability from a channel-aware routed scaffold. -/
theorem domino_problem_undecidable_of_routed
    (S : RoutedScaffold) (hS : IsRoutedScaffold S) :
    ¬ ComputablePred (fun T : TileSet => TilesPlane T) := by
  intro hdec
  have hdomino : ComputablePred
      (fun c : Code => TilesPlane (routedDominoReduction S c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun T : TileSet => TilesPlane T)
        (routedDominoReduction_computable S)) hdec
  have hnonhalting : ComputablePred
      (fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom) :=
    hdomino.of_eq fun c => routedDominoReduction_correct hS c
  exact ComputablePred.halting_problem 0
    ((hnonhalting.not).of_eq fun _ => not_not)

end UniversalFoldedReduction

end LeanWang
