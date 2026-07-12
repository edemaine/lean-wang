/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphPathRefinement

/-!
# Coarse coordinates for two-level Robinson refinement

The literal sparse quarters occur at residues zero and one modulo eight.  A
fine coordinate is assigned to the unique coarse interval beginning at one of
those retained quarters.  These bounds are the arithmetic interface used by
the pair-cover refinement proof.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RefinedCoordinateProjection

open RedShadeCycles RedShadeGraphRefinement

/-- Coarse quarter whose retained interval contains a fine quarter. -/
def coarseCoordinate (coordinate : Nat) : Nat :=
  if coordinate % 8 = 0 then 2 * (coordinate / 8)
  else 2 * (coordinate / 8) + 1

@[simp] theorem sparseCoordinate_two_mul (block : Nat) :
    sparseCoordinate (2 * block) = 8 * block := by
  simp [sparseCoordinate, macroOrigin, localCoordinate]

@[simp] theorem sparseCoordinate_two_mul_add_one (block : Nat) :
    sparseCoordinate (2 * block + 1) = 8 * block + 1 := by
  simp [sparseCoordinate, macroOrigin, localCoordinate]
  omega

/-- A fine coordinate lies in the half-open sparse interval selected by its
coarse coordinate. -/
theorem coarseCoordinate_spec (coordinate : Nat) :
    sparseCoordinate (coarseCoordinate coordinate) ≤ coordinate ∧
      coordinate < sparseCoordinate (coarseCoordinate coordinate + 1) := by
  have hmod := Nat.mod_lt coordinate (by decide : 0 < 8)
  have hdecompose := Nat.mod_add_div coordinate 8
  by_cases hzero : coordinate % 8 = 0
  · simp only [coarseCoordinate, hzero, if_true,
      sparseCoordinate_two_mul]
    have hsucc : 2 * (coordinate / 8) + 1 =
        2 * (coordinate / 8) + 1 := rfl
    rw [hsucc, sparseCoordinate_two_mul_add_one]
    omega
  · simp only [coarseCoordinate, hzero, if_false,
      sparseCoordinate_two_mul_add_one]
    have hnext : 2 * (coordinate / 8) + 1 + 1 =
        2 * (coordinate / 8 + 1) := by omega
    rw [hnext, sparseCoordinate_two_mul]
    omega

theorem sparseCoordinate_mono {first second : Nat} (hle : first ≤ second) :
    sparseCoordinate first ≤ sparseCoordinate second := by
  rcases hle.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact Nat.le_of_lt (sparseCoordinate_strictMono hlt)

/-- Strict coarse bounds imply the corresponding strict sparse bounds for the
original fine coordinate. -/
theorem sparse_bounds_of_coarse_bounds
    {lower coordinate upper : Nat}
    (hlower : lower < coarseCoordinate coordinate)
    (hupper : coarseCoordinate coordinate < upper) :
    sparseCoordinate lower < coordinate ∧
      coordinate < sparseCoordinate upper := by
  have spec := coarseCoordinate_spec coordinate
  constructor
  · exact (sparseCoordinate_strictMono hlower).trans_le spec.1
  · exact spec.2.trans_le (sparseCoordinate_mono (by omega))

/-- Strict sparse bounds recover a weak lower and strict upper coarse bound.
Equality at the lower bound is precisely the newly created boundary interval. -/
theorem coarse_bounds_of_sparse_bounds
    {lower coordinate upper : Nat}
    (hlower : sparseCoordinate lower < coordinate)
    (hupper : coordinate < sparseCoordinate upper) :
    lower ≤ coarseCoordinate coordinate ∧
      coarseCoordinate coordinate < upper := by
  have spec := coarseCoordinate_spec coordinate
  constructor
  · by_contra hnot
    have hnext : coarseCoordinate coordinate + 1 ≤ lower := by omega
    have := spec.2.trans_le (sparseCoordinate_mono hnext)
    omega
  · by_contra hnot
    have hle : upper ≤ coarseCoordinate coordinate := by omega
    have := (sparseCoordinate_mono hle).trans spec.1
    omega

theorem fine_board_bounds_of_coarse_bounds
    {west east coordinate : Nat}
    (hwest : quarterWest west < coarseCoordinate coordinate)
    (heast : coarseCoordinate coordinate < quarterEast east) :
    quarterWest (4 * west) < coordinate ∧
      coordinate < quarterEast (4 * east) := by
  simpa only [sparseCoordinate_quarterWest, sparseCoordinate_quarterEast] using
    sparse_bounds_of_coarse_bounds hwest heast

theorem coarse_board_bounds_of_fine_bounds
    {west east coordinate : Nat}
    (hwest : quarterWest (4 * west) < coordinate)
    (heast : coordinate < quarterEast (4 * east)) :
    quarterWest west ≤ coarseCoordinate coordinate ∧
      coarseCoordinate coordinate < quarterEast east := by
  apply coarse_bounds_of_sparse_bounds
  · simpa only [sparseCoordinate_quarterWest] using hwest
  · simpa only [sparseCoordinate_quarterEast] using heast

end RefinedCoordinateProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
