/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic
import Mathlib.Computability.Reduce

/-!
# Proof-neutral Wang domino problem interface

This module states the Wang domino problem independently of any particular
undecidability construction.  A `DominoProblem.Reduction` packages a computable
many-one reduction from the complement of Mathlib's fixed-input halting problem.
Concrete proof techniques, currently the Robinson construction, provide values
of this structure in their own module trees.

Mathlib provides `REPred` and computable many-one reducibility, but does not
currently provide definitions of co-r.e. hardness or completeness.  The
many-one reductions exposed here are intended to be the hardness component of
that later result; co-r.e. membership of plane tiling additionally needs the
independent finite-obstruction argument.
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

/--
A computable translation from universal-program codes to Wang tilesets, with
plane tilability equivalent to nonhalting.  Different undecidability proofs can
share this exact endpoint while implementing `tiles` and `correct` differently.
-/
structure Reduction where
  tiles : Code → TileSet
  tiles_computable : Computable tiles
  correct : ∀ c, Holds (tiles c) ↔ FixedNonhalting c

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
