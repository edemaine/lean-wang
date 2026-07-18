/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedConverse
import LeanWang.Kari.AffineTMImmortality

/-!
# Effective affine endpoint of Hooper's construction

This file is independent of the command-family proofs.  Given the two local
guarded converse laws, it composes the finite controller with Kari's generic
finite-TM-to-affine compiler and packages the resulting Wang tiles as the
shared proof-neutral domino reduction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlAffineReduction

open BoundedMarkerProgram CounterControlPlan

noncomputable section

/-- Wang tiles obtained by applying Kari's affine compiler to the effective
Hooper controller table. -/
def tiles (c : Nat.Partrec.Code) : TileSet :=
  AffineTMSystem.tiles (CounterControlReduction.table c)

/-- The complete code-to-Wang-tiles translation is computable. -/
theorem tiles_computable : Computable tiles := by
  exact AffineTMSystem.tiles_computable.comp
    CounterControlReduction.table_computable

/-- Under the local guarded converse laws, plane tilability of the compiled
affine system is exactly fixed-input nonhalting. -/
theorem tilesPlane_iff_fixedNonhalting_of_laws
    (c : Nat.Partrec.Code)
    (hlaws : CounterControlGuardedConverse.Laws
      CounterControlReduction.base c) :
    TilesPlane (tiles c) ↔ DominoProblem.FixedNonhalting c := by
  exact
    (AffineTMImmortality.tilesPlane_iff_immortal
      (CounterControlReduction.table_deterministic c)
      (blankSymbol : Symbol numTags)).trans
    (CounterControlGuardedConverse.table_immortal_iff_fixedNonhalting_of_laws
      c hlaws)

/-- A uniform proof of the two local controller laws yields the repository's
proof-neutral domino-reduction certificate. -/
def reduction_of_laws
    (hlaws : ∀ c : Nat.Partrec.Code,
      CounterControlGuardedConverse.Laws CounterControlReduction.base c) :
    DominoProblem.Reduction where
  tiles := tiles
  tiles_computable := tiles_computable
  correct := fun c => tilesPlane_iff_fixedNonhalting_of_laws c (hlaws c)

end

end CounterControlAffineReduction
end Hooper
end Kari
end LeanWang
