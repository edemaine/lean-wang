/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanWang.Final
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Proofs of the formal abstract

A change of representation preserves a decision problem when it preserves
solutions and is computable in both directions. This module establishes such
a correspondence between the abstract and the main proof, then transfers
co-RE-completeness and undecidability.
-/

namespace LeanWang.AbstractBridge

/--
A plane tiling places an allowed tile at every integer cell with matching
colors on touching edges. This spells out the abstract's predicate with
directions numbered north = 0, south = 1, east = 2, west = 3.
-/
def TilesPlane (T : List (Fin 4 → ℕ)) : Prop :=
  ∃ t : ℤ → ℤ → (Fin 4 → ℕ), ∀ x y,
    t x y ∈ T ∧
    t x y 2 = t (x + 1) y 3 ∧
    t x y 0 = t x (y + 1) 1

/--
An edge-preserving translation sends a tile to one with the same four colors.
Here `![n, s, e, w]` is the function assigning those four colors to `Fin 4`.
-/
def toTile (t : WangTile) : Fin 4 → ℕ :=
  ![t.n, t.s, t.e, t.w]

/--
An inverse translation recovers the original tile from its translated
representation. Here it returns an abstract tile to the main proof's format,
copying its four edge labels.
-/
def toWangTile (t : Fin 4 → ℕ) : WangTile :=
  ⟨t 0, t 1, t 2, t 3⟩

/-
Mutually inverse maps recover each input when composed in either order.
These two equalities express that property for the tile translations;
`@[simp]` lets Lean use them automatically when simplifying expressions.
-/
@[simp] theorem toWangTile_toTile (t : WangTile) : toWangTile (toTile t) = t := rfl

@[simp] theorem toTile_toWangTile (t : Fin 4 → ℕ) : toTile (toWangTile t) = t := by
  funext i
  fin_cases i <;> rfl

/-
A primitive recursive map is built from zero, successor, and projections
by composition and recursion with a base case and a step computing
`f(n + 1)` from `n` and `f(n)`. These translations copy four labels;
`Primrec` certifies their primitive recursiveness under Mathlib's encodings.
-/
theorem toTile_primrec : Primrec toTile := by
  have h : Primrec₂ fun i : Fin 4 => fun t : WangTile => toTile t i :=
    Primrec.fin_curry₁.2 fun i => by
      fin_cases i
      · exact WangTile.n_primrec
      · exact WangTile.s_primrec
      · exact WangTile.e_primrec
      · exact WangTile.w_primrec
  exact Primrec.fin_curry.2 h.swap

theorem toWangTile_primrec : Primrec toWangTile := by
  have h (i : Fin 4) : Primrec (fun t : Fin 4 → ℕ => t i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  exact WangTile.ofTuple_primrec.comp
    (Primrec.pair (h 0) (Primrec.pair (h 1) (Primrec.pair (h 2) (h 3))))

/-
A computable map is computed by an algorithm that halts on every input.
Translating a finite tile collection is computable in both directions.
`List.map` applies a translation to each tile, and `Computable` certifies the map.
-/
theorem toTiles_computable : Computable (List.map toTile) :=
  (Primrec.list_map Primrec.id (toTile_primrec.comp Primrec.snd).to₂).to_comp

theorem toWangTiles_computable : Computable (List.map toWangTile) :=
  (Primrec.list_map Primrec.id (toWangTile_primrec.comp Primrec.snd).to₂).to_comp

/--
Equivalent tiling problems have exactly the same tileable instances after
translation. Here `↔` states that equivalence; the main proof stores each placed
tile together with its membership proof in a subtype, whereas the abstract
states membership as a condition on the placement function.
-/
theorem tilesPlane_iff (T : List (Fin 4 → ℕ)) :
    TilesPlane T ↔ DominoProblem.Holds (T.map toWangTile) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun p => ⟨toWangTile (t p.1 p.2), List.mem_map.mpr
      ⟨t p.1 p.2, (ht p.1 p.2).1, rfl⟩⟩, ?_, ?_⟩
    · intro p
      exact (ht p.1 p.2).2.1
    · intro p
      exact (ht p.1 p.2).2.2
  · rintro ⟨t, hH, hV⟩
    refine ⟨fun x y => toTile (t (x, y)).1, fun x y => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨tile, htile, heq⟩ := List.mem_map.mp (t (x, y)).2
      simpa only [← heq, toTile_toWangTile] using htile
    · exact hH (x, y)
    · exact hV (x, y)

/--
Equivalent presentations agree on whether corresponding tile collections
tile the plane. Here `T.map toTile` translates the main proof's collection
into abstract tiles, giving the equivalence in the reverse direction.
-/
theorem tilesPlane_map_toTile_iff (T : TileSet) :
    TilesPlane (T.map toTile) ↔ DominoProblem.Holds T := by
  simpa only [List.map_map, Function.comp_def, toWangTile_toTile, List.map_id']
    using tilesPlane_iff (T.map toTile)

/--
Co-RE-completeness means the complement is recognizable and every problem with
recognizable complement has a computable, answer-preserving reduction to it.
This theorem transfers both properties to the plane tiling predicate above.
Its expanded statement lets Abstract.lean define co-RE and completeness itself.
-/
theorem coRE_complete :
    REPred (fun T => ¬ TilesPlane T) ∧
    ∀ p : ℕ → Prop, REPred (fun n => ¬ p n) →
      ∃ f : ℕ → List (Fin 4 → ℕ), Computable f ∧ ∀ n, p n ↔ TilesPlane (f n) := by
  constructor
  · exact _root_.REPred.of_eq
      (LeanWang.REPred.comp domino_problem_coRE toWangTiles_computable)
      fun T => not_congr (tilesPlane_iff T).symm
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := domino_problem_coRE_hard p hp
    refine ⟨fun n => (f n).map toTile,
      toTiles_computable.comp hf, fun n => ?_⟩
    exact (hcorrect n).trans (tilesPlane_map_toTile_iff (f n)).symm

/--
Undecidability means no always-halting algorithm correctly decides every instance.
A decision algorithm for the abstract would decide the main proof's problem
by translating its input tiles, contradicting the existing undecidability theorem.
-/
theorem undecidable : ¬ ComputablePred TilesPlane := by
  intro h
  apply domino_problem_undecidable
  exact ComputablePred.computable_of_manyOneReducible
    ⟨List.map toTile, toTiles_computable,
      fun T => (tilesPlane_map_toTile_iff T).symm⟩ h

end LeanWang.AbstractBridge
