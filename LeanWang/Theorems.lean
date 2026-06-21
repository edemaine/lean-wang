/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Machine

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

/-- Compile a Mathlib partial-recursive code into the concrete one-tape machine model. -/
def programMachine (_c : Code) : Machine :=
  dummyMachine

/-- Correctness target for the compiler from partial-recursive codes to concrete machines. -/
theorem programMachine_correct (c : Code) :
    Machine.HaltsEmpty (programMachine c) ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  sorry

/-- The tileset produced from a concrete machine for the fixed domino construction. -/
def machineTiles (_M : Machine) : TileSet :=
  []

/-- The distinguished origin/corner tile for the fixed domino construction. -/
def machineSeed (_M : Machine) : WangTile :=
  monochromeTile

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
  sorry

/-- The fixed domino problem is undecidable, in reduction form. -/
theorem fixed_domino_problem_undecidable :
    ¬ ComputablePred
      (fun c : Code =>
        TilesQuarterWithSeed (fixedDominoReduction c).1 (fixedDominoReduction c).2) := by
  sorry

/-- The fixed-corner finite-square problem is undecidable, in reduction form. -/
theorem fixed_corner_square_problem_undecidable :
    ¬ ComputablePred
      (fun c : Code =>
        ∀ n : Nat, 0 < n →
          TileableFixedCornerSquare (fixedDominoReduction c).1 (fixedDominoReduction c).2 n) := by
  sorry

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
  sorry

/-- Decode natural-number inputs as tilesets for an encoded statement of the domino problem. -/
def decodeTileSet (_n : Nat) : TileSet :=
  []

/-- Encoded version of `dominoReduction`; later this should be the computable tile encoding. -/
def dominoReductionCode (_c : Code) : Nat :=
  0

/-- Computability target for the encoded final reduction. -/
theorem dominoReductionCode_computable : Computable dominoReductionCode := by
  sorry

/-- Correctness target for the encoded final reduction. -/
theorem dominoReductionCode_correct (c : Code) :
    TilesPlane (decodeTileSet (dominoReductionCode c)) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  sorry

/-- The domino problem is undecidable for encoded finite Wang tilesets. -/
theorem encoded_domino_problem_undecidable :
    ¬ ComputablePred (fun n : Nat => TilesPlane (decodeTileSet n)) := by
  sorry

end LeanWang
