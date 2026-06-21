/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Compactness
import LeanWang.Machine
import LeanWang.MachineTiles
import Mathlib.Computability.Reduce

/-!
Main theorem surface for the Wang-tile undecidability proof.

The definitions in this file are placeholders for later constructions. The theorems
record the proof obligations from the plan, so the rest of the development has a
concrete target in Lean.
-/

namespace LeanWang

open Nat.Partrec (Code)

/-- A dummy machine used until the compiler from partial-recursive codes is implemented. -/
def dummyMachine : Machine where
  symbols := [0]
  states := [0, 1]
  blank := 0
  start := 0
  halt := 1
  step := fun _ _ => (0, 1, Move.right)
  blank_mem := by simp
  start_mem := by simp
  halt_mem := by simp
  step_symbol_mem := by simp
  step_state_mem := by simp

/-- Compile a Mathlib partial-recursive code into the concrete one-tape machine model. -/
def programMachine (_c : Code) : Machine :=
  dummyMachine

/-- Correctness target for the compiler from partial-recursive codes to concrete machines. -/
theorem programMachine_correct (c : Code) :
    Machine.HaltsEmpty (programMachine c) ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  sorry

/-- Correctness of the machine-to-Wang-tile fixed domino construction. -/
theorem machineTiles_correct (M : Machine) :
    TilesQuarterWithSeed (machineTiles M) (machineSeed M) ↔ ¬ Machine.HaltsEmpty M := by
  sorry

/-- Fixed domino instance produced from a partial-recursive code. -/
def fixedDominoReduction (c : Code) : TileSet × WangTile :=
  let M := programMachine c
  (machineTiles M, machineSeed M)

/-- Correctness of the fixed domino reduction from nonhalting. -/
theorem fixedDominoReduction_correct (c : Code) :
    TilesQuarterWithSeed (fixedDominoReduction c).1 (fixedDominoReduction c).2 ↔
      ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  unfold fixedDominoReduction
  rw [machineTiles_correct, programMachine_correct]

/-- The fixed domino problem is undecidable, in reduction form. -/
theorem fixed_domino_problem_undecidable :
    ¬ ComputablePred
      (fun c : Code =>
        TilesQuarterWithSeed (fixedDominoReduction c).1 (fixedDominoReduction c).2) := by
  intro h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    h.of_eq fun c => fixedDominoReduction_correct c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/-- The fixed-corner finite-square problem is undecidable, in reduction form. -/
theorem fixed_corner_square_problem_undecidable :
    ¬ ComputablePred
      (fun c : Code =>
        ∀ n : Nat, 0 < n →
          TileableFixedCornerSquare (fixedDominoReduction c).1 (fixedDominoReduction c).2 n) := by
  intro h
  apply fixed_domino_problem_undecidable
  exact h.of_eq fun c =>
    (tilesQuarterWithSeed_iff_all_fixedCornerSquares
      (fixedDominoReduction c).1 (fixedDominoReduction c).2).symm

/-- Data for a scaffold tileset used to force arbitrarily large free squares. -/
structure Scaffold where
  tiles : TileSet

/-- Combine a scaffold with a fixed-corner square instance. -/
def combineWithScaffold (_S : Scaffold) (_T : TileSet) (_seed : WangTile) : TileSet :=
  []

/-- The abstract property required of a scaffold for the Berger/Robinson reduction. -/
def IsScaffold (S : Scaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    TilesPlane (combineWithScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n

/-- The concrete Ollinger/Robinson scaffold tileset. -/
def ollingerScaffold : Scaffold where
  tiles := []

/-- The Ollinger/Robinson scaffold satisfies the abstract scaffold property. -/
theorem ollingerScaffold_isScaffold : IsScaffold ollingerScaffold := by
  sorry

/-- Abstract scaffold reduction from fixed-corner squares to ordinary plane tiling. -/
theorem scaffold_reduction_correct {S : Scaffold} (hS : IsScaffold S)
    (T : TileSet) (seed : WangTile) :
    TilesPlane (combineWithScaffold S T seed) ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n :=
  hS T seed

/-- The final Berger/Robinson tileset produced from a partial-recursive code. -/
def dominoReduction (c : Code) : TileSet :=
  combineWithScaffold ollingerScaffold (fixedDominoReduction c).1 (fixedDominoReduction c).2

/-- Correctness of the final domino reduction from nonhalting. -/
theorem dominoReduction_correct (c : Code) :
    TilesPlane (dominoReduction c) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [dominoReduction]
  exact (scaffold_reduction_correct ollingerScaffold_isScaffold
    (fixedDominoReduction c).1 (fixedDominoReduction c).2).trans
      ((tilesQuarterWithSeed_iff_all_fixedCornerSquares
        (fixedDominoReduction c).1 (fixedDominoReduction c).2).symm.trans
          (fixedDominoReduction_correct c))

/-- Encoded version of `dominoReduction`, using the canonical finite tileset encoding. -/
def dominoReductionCode (c : Code) : Nat :=
  encodeTileSet (dominoReduction c)

/-- Computability target for the encoded final reduction. -/
theorem dominoReductionCode_computable : Computable dominoReductionCode := by
  unfold dominoReductionCode dominoReduction combineWithScaffold encodeTileSet
  exact Computable.const (Encodable.encode ([] : TileSet))

/-- Correctness target for the encoded final reduction. -/
theorem dominoReductionCode_correct (c : Code) :
    TilesPlane (decodeTileSet (dominoReductionCode c)) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [dominoReductionCode, decodeTileSet_encodeTileSet]
  exact dominoReduction_correct c

/-- The domino problem is undecidable for encoded finite Wang tilesets. -/
theorem encoded_domino_problem_undecidable :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  intro h
  have hencoded : ComputablePred
      (fun c : Code => TilesPlane (decodeTileSet (dominoReductionCode c))) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun n : Nat => TilesPlane (decodeTileSet n))
        dominoReductionCode_computable) h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    hencoded.of_eq fun c => dominoReductionCode_correct c
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

end LeanWang
