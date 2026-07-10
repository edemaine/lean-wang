/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonScaffold
import LeanWang.Theorems
import LeanWang.TM0FoldedInput.Computability
import LeanWang.TM0FoldedPositionCorrect
import LeanWang.UniversalTM0
import Mathlib.Computability.Reduce

/-!
# Fixed-universal-machine Wang reduction

This is the simplified machine side of the domino reduction.  The simulation
control and all simulation rows below are constants.  A source code changes
only the finite input word written by the initialization prelude.

Compared with the old source-program route, no theorem here needs to decode a
dependent `Turing.ToPartrec.Code` statement or prove that such a decoder is
uniformly primitive recursive.
-/

noncomputable section

namespace LeanWang

namespace UniversalFoldedReduction

open Nat.Partrec (Code)

/-- Numeric state support of the one fixed universal TM0 machine. -/
def stateCount : Nat :=
  TM0Route.partrecStartedTM0StateCount UniversalTM0.code

/-- Position-coded simulation descriptors of the fixed universal control. -/
def simulationSteps : List TM0FoldedCompiler.SimStepData :=
  TM0FoldedCompiler.simStepDataByLabelIndexWithPositionCode UniversalTM0.code

/--
The finite folded program for source code `c`.  Its simulation rows are fixed;
only `UniversalTM0.input c` is compiled into initialization rows.
-/
def program (c : Code) : FiniteTM0Program :=
  TM0FoldedCompiler.positionProgramDataOnInput UniversalTM0.code
    (UniversalTM0.input c)

theorem program_computable : Computable program := by
  exact
    (TM0FoldedCompiler.positionProgramDataForInput_computable_fixed
      stateCount simulationSteps).comp UniversalTM0.input_computable

/--
Correctness of the varying-input prelude followed by the fixed folded
simulation.  This is the only machine-simulation theorem needed by the new
route.
-/
theorem program_haltsEmpty_iff (c : Code) :
    (program c).HaltsEmpty ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  sorry

/-- Fixed-corner Wang instance generated from the fixed universal program. -/
def fixedDominoReduction (c : Code) : TileSet × WangTile :=
  tableProgramFixedDominoData (PostProgram.toTableProgram (program c))

theorem fixedDominoReduction_computable : Computable fixedDominoReduction := by
  exact tableProgramFixedDominoData_computable.comp
    (PostProgram.toTableProgram_computable.comp program_computable)

theorem fixedDominoReduction_correct (c : Code) :
    TilesQuarterWithSeed (fixedDominoReduction c).1
        (fixedDominoReduction c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold fixedDominoReduction
  rw [tableProgramFixedDominoData_seed_eq]
  rw [tilesQuarterWithSeed_congr
    (tableProgramFixedDominoData_mem_iff
      (PostProgram.toTableProgram (program c)))]
  rw [tableProgramFixedDomino_correct]
  rw [PostProgram.toTableProgram_toMachine_haltsEmpty_iff]
  rw [program_haltsEmpty_iff]

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

end UniversalFoldedReduction

end LeanWang
