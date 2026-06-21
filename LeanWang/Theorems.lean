/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Compactness
import LeanWang.Machine
import LeanWang.MachineTiles
import Mathlib.Computability.Reduce
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Main theorem surface for the Wang-tile undecidability proof.

The definitions in this file are placeholders for later constructions. The theorems
record the proof obligations from the plan, so the rest of the development has a
concrete target in Lean.
-/

namespace LeanWang

open Nat.Partrec (Code)

theorem part_dom_map_iff {α β : Type} (f : α → β) (p : Part α) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

/--
Bounded Mathlib code evaluation succeeds at some fuel exactly when full
evaluation is defined.
-/
theorem code_eval_dom_iff_exists_evaln (c : Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔
      ∃ k x : Nat, x ∈ Nat.Partrec.Code.evaln k c n := by
  constructor
  · intro hdom
    rcases Part.dom_iff_mem.1 hdom with ⟨x, hx⟩
    rcases Nat.Partrec.Code.evaln_complete.1 hx with ⟨k, hk⟩
    exact ⟨k, x, hk⟩
  · rintro ⟨k, x, hx⟩
    exact Part.dom_iff_mem.2 ⟨x, Nat.Partrec.Code.evaln_sound hx⟩

/-- Boolean bounded halting predicate for `Nat.Partrec.Code.evaln`. -/
def codeEvalnHalts (c : Code) (n k : Nat) : Bool :=
  (Nat.Partrec.Code.evaln k c n).isSome

theorem code_eval_dom_iff_exists_codeEvalnHalts (c : Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔ ∃ k : Nat, codeEvalnHalts c n k = true := by
  rw [code_eval_dom_iff_exists_evaln]
  constructor
  · rintro ⟨k, x, hx⟩
    refine ⟨k, ?_⟩
    cases h : Nat.Partrec.Code.evaln k c n with
    | none =>
        simp [Option.mem_def, h] at hx
    | some y =>
        simp [codeEvalnHalts, h]
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c n with
    | none =>
        simp [codeEvalnHalts, h] at hk
    | some x =>
        exact ⟨k, x, by simp [Option.mem_def, h]⟩

theorem codeEvalnHalts_primrec :
    Primrec fun a : (Nat × Code) × Nat => codeEvalnHalts a.1.2 a.2 a.1.1 := by
  simpa [codeEvalnHalts] using
    Primrec.option_isSome.comp Nat.Partrec.Code.primrec_evaln

theorem codeEvaln_nonhalting_undecidable :
    ¬ ComputablePred (fun c : Code => ¬ ∃ k : Nat, codeEvalnHalts c 0 k = true) := by
  intro h
  have hnonhalting : ComputablePred fun c : Code => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    h.of_eq fun c => by
      rw [code_eval_dom_iff_exists_codeEvalnHalts]
  exact ComputablePred.halting_problem 0 ((hnonhalting.not).of_eq fun _ => not_not)

/--
Every Mathlib `Nat.Partrec.Code` has a corresponding `Turing.ToPartrec.Code`
whose singleton-list output is defined exactly when the original unary code is
defined.
-/
theorem exists_toPartrecCode_for_natPartrecCode (c : Code) :
    ∃ tc : Turing.ToPartrec.Code,
      ∀ n : Nat,
        (Turing.ToPartrec.Code.eval tc [n]).Dom ↔
          (Nat.Partrec.Code.eval c n).Dom := by
  have hpart : Partrec (Nat.Partrec.Code.eval c) :=
    (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id).of_eq
      fun n => by rfl
  rcases Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 hpart) with
    ⟨tc, htc⟩
  refine ⟨tc, fun n => ?_⟩
  let v : List.Vector Nat 1 := ⟨[n], by simp⟩
  have hv : v.head = n := rfl
  have htc' :
      Turing.ToPartrec.Code.eval tc [n] =
        pure <$> Nat.Partrec.Code.eval c n := by
    simpa [v, hv] using htc v
  rw [htc']
  exact part_dom_map_iff pure (Nat.Partrec.Code.eval c n)

/--
Mathlib's TM2 evaluator for the translated `ToPartrec.Code` halts exactly when
the original `Nat.Partrec.Code` halts on input `0`.
-/
theorem exists_tm2_for_natPartrecCode (c : Code) :
    ∃ tc : Turing.ToPartrec.Code,
      (StateTransition.eval
          (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init tc [0])).Dom ↔
        (Nat.Partrec.Code.eval c 0).Dom := by
  rcases exists_toPartrecCode_for_natPartrecCode c with ⟨tc, htc⟩
  refine ⟨tc, ?_⟩
  rw [Turing.PartrecToTM2.tr_eval tc [0]]
  exact (part_dom_map_iff Turing.PartrecToTM2.halt
    (Turing.ToPartrec.Code.eval tc [0])).trans (htc 0)

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
  constructor
  · intro htiles hhalts
    rcases hhalts with ⟨n, hhalt⟩
    exact not_tilesQuarterWithSeed_machineTiles_of_halts_at n hhalt htiles
  · intro hnonhalts
    exact tilesQuarterWithSeed_machineTiles_of_not_halts hnonhalts

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
def combineWithScaffold (S : Scaffold) (T : TileSet) (_seed : WangTile) : TileSet :=
  productTileSet S.tiles T

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
  unfold dominoReductionCode dominoReduction combineWithScaffold productTileSet
    ollingerScaffold encodeTileSet
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
