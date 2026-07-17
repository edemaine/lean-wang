/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.CoRE
import LeanWang.Compactness
import LeanWang.FiniteSearch

/-!
# Proof-neutral Wang domino problem interface

This module states the Wang domino problem independently of any particular
undecidability construction.  A `DominoProblem.Reduction` packages a computable
many-one reduction from the complement of Mathlib's fixed-input halting problem.
Concrete proof techniques, currently the Robinson construction, provide values
of this structure in their own module trees.

The shared reduction certificate supplies co-r.e. hardness via universality of
Mathlib's partial-recursive evaluator.  Independently, exhaustive finite-square
search and compactness supply co-r.e. membership.  Thus co-r.e. completeness,
as well as undecidability, is a generic consequence of any concrete reduction
certificate.
-/

noncomputable section

namespace LeanWang
namespace DominoProblem

open Nat.Partrec (Code)

/-- The unencoded Wang domino problem. -/
def Holds (T : TileSet) : Prop :=
  TilesPlane T

/-- The Wang domino problem transported to natural-number tileset codes. -/
def EncodedHolds (n : Nat) : Prop :=
  Holds (decodeTileSet n)

/-- Nonhalting of Mathlib's universal partial-recursive evaluator on fixed input `0`. -/
def FixedNonhalting (c : Code) : Prop :=
  ¬ (Nat.Partrec.Code.eval c 0).Dom

/-- The proof-neutral statement that the Wang domino problem is undecidable. -/
def Undecidable : Prop :=
  ¬ ComputablePred Holds

/-- The encoded proof-neutral Wang domino undecidability statement. -/
def EncodedUndecidable : Prop :=
  ¬ ComputablePred EncodedHolds

/-- The proof-neutral statement that the Wang domino problem is co-r.e.-hard. -/
def CoREHard : Prop :=
  LeanWang.CoREHard Holds

/-- The proof-neutral statement that the Wang domino problem is co-r.e.-complete. -/
def CoREComplete : Prop :=
  LeanWang.CoREComplete Holds

/-- Co-r.e. hardness of the natural-number-coded Wang domino problem. -/
def EncodedCoREHard : Prop :=
  LeanWang.CoREHard EncodedHolds

/-- Co-r.e. completeness of the natural-number-coded Wang domino problem. -/
def EncodedCoREComplete : Prop :=
  LeanWang.CoREComplete EncodedHolds

/--
A computable translation from universal-program codes to Wang tilesets, with
plane tilability equivalent to nonhalting.  Different undecidability proofs can
share this exact endpoint while implementing `tiles` and `correct` differently.
-/
structure Reduction where
  tiles : Code → TileSet
  tiles_computable : Computable tiles
  correct : ∀ c, Holds (tiles c) ↔ FixedNonhalting c

/-- Non-tilability is r.e., witnessed by a finite square obstruction. -/
theorem coRE : LeanWang.CoREPred Holds := by
  unfold LeanWang.CoREPred
  have hnotSquare : ComputablePred fun p : TileSet × Nat =>
      ¬ TileableSquare p.1 p.2 :=
    tileableSquare_computablePred.not
  have hexists : REPred fun T : TileSet => ∃ n, ¬ TileableSquare T n :=
    REPred.exists_nat hnotSquare
  exact hexists.of_eq fun T => by
    simpa only [Holds, not_forall] using
      (not_congr (tilesPlane_iff_all_tileableSquares T)).symm

/-- Encoded plane tilability is co-r.e. by computable decoding. -/
theorem encodedCoRE : LeanWang.CoREPred EncodedHolds := by
  unfold LeanWang.CoREPred
  exact (coRE.comp decodeTileSet_computable).of_eq fun n => by
    simp only [EncodedHolds]

namespace Reduction

/-- Encode the tileset produced by a proof-neutral domino reduction. -/
def encodedTiles (r : Reduction) (c : Code) : Nat :=
  encodeTileSet (r.tiles c)

theorem encodedTiles_computable (r : Reduction) :
    Computable r.encodedTiles :=
  encodeTileSet_computable.comp r.tiles_computable

theorem encodedTiles_correct (r : Reduction) (c : Code) :
    EncodedHolds (r.encodedTiles c) ↔ FixedNonhalting c := by
  rw [encodedTiles, EncodedHolds, Holds, decodeTileSet_encodeTileSet]
  exact r.correct c

/-- Every reduction certificate is, in particular, a computable many-one reduction. -/
theorem manyOneReducible (r : Reduction) :
    FixedNonhalting ≤₀ Holds :=
  ⟨r.tiles, r.tiles_computable, fun c => (r.correct c).symm⟩

/-- The encoded many-one reduction derived uniformly from a reduction certificate. -/
theorem encodedManyOneReducible (r : Reduction) :
    FixedNonhalting ≤₀ EncodedHolds :=
  ⟨r.encodedTiles, r.encodedTiles_computable,
    fun c => (r.encodedTiles_correct c).symm⟩

/-- Any shared reduction certificate proves co-r.e. hardness. -/
theorem coREHard (r : Reduction) : DominoProblem.CoREHard := by
  intro alpha _ p hp
  have hfixed : p ≤₀ FixedNonhalting := by
    change p ≤₀ fun c : Code => ¬ (Code.eval c 0).Dom
    exact coRE_manyOneReducible_fixedNonhalting p hp
  exact hfixed.trans r.manyOneReducible

/-- The encoded target is co-r.e.-hard by the same reduction certificate. -/
theorem encodedCoREHard (r : Reduction) : DominoProblem.EncodedCoREHard := by
  intro alpha _ p hp
  have hfixed : p ≤₀ FixedNonhalting := by
    change p ≤₀ fun c : Code => ¬ (Code.eval c 0).Dom
    exact coRE_manyOneReducible_fixedNonhalting p hp
  exact hfixed.trans r.encodedManyOneReducible

/-- Co-r.e. completeness is a generic corollary of a reduction certificate. -/
theorem coREComplete (r : Reduction) : DominoProblem.CoREComplete :=
  ⟨DominoProblem.coRE, r.coREHard⟩

/-- Encoded co-r.e. completeness is a generic corollary as well. -/
theorem encodedCoREComplete (r : Reduction) : DominoProblem.EncodedCoREComplete :=
  ⟨DominoProblem.encodedCoRE, r.encodedCoREHard⟩

private theorem fixedNonhalting_not_computable :
    ¬ ComputablePred FixedNonhalting := by
  intro nonhaltingComputable
  exact ComputablePred.halting_problem 0
    ((nonhaltingComputable.not).of_eq fun _ => not_not)

/-- Undecidability is a generic corollary of a domino reduction certificate. -/
theorem undecidable (r : Reduction) : Undecidable := by
  intro targetComputable
  exact fixedNonhalting_not_computable
    (ComputablePred.computable_of_manyOneReducible
      r.manyOneReducible targetComputable)

/-- Encoded undecidability is a generic corollary of the same certificate. -/
theorem encodedUndecidable (r : Reduction) : EncodedUndecidable := by
  intro targetComputable
  exact fixedNonhalting_not_computable
    (ComputablePred.computable_of_manyOneReducible
      r.encodedManyOneReducible targetComputable)

end Reduction
end DominoProblem
end LeanWang

end
