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

@[simp] theorem coarseCoordinate_sparseCoordinate (coordinate : Nat) :
    coarseCoordinate (sparseCoordinate coordinate) = coordinate := by
  have hmod := Nat.mod_lt coordinate (by decide : 0 < 2)
  have hdecompose := Nat.mod_add_div coordinate 2
  have hcases : coordinate % 2 = 0 ∨ coordinate % 2 = 1 := by omega
  rcases hcases with h | h
  · have hcoordinate : coordinate = 2 * (coordinate / 2) := by omega
    rw [hcoordinate, sparseCoordinate_two_mul]
    simp [coarseCoordinate]
  · have hcoordinate : coordinate = 2 * (coordinate / 2) + 1 := by omega
    rw [hcoordinate, sparseCoordinate_two_mul_add_one]
    have hdiv : (8 * (coordinate / 2) + 1) / 8 = coordinate / 2 := by
      omega
    simp [coarseCoordinate, hdiv]

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

theorem sparseCoordinate_lt_iff {first second : Nat} :
    sparseCoordinate first < sparseCoordinate second ↔ first < second := by
  constructor
  · intro hlt
    by_contra hnot
    exact (Nat.not_lt_of_ge (sparseCoordinate_mono (by omega))) hlt
  · exact sparseCoordinate_strictMono

/-- Coordinates retained literally by two-level refinement. -/
def IsSparseCoordinate (coordinate : Nat) : Prop :=
  ∃ coarse, sparseCoordinate coarse = coordinate

theorem isSparseCoordinate_iff (coordinate : Nat) :
    IsSparseCoordinate coordinate ↔
      sparseCoordinate (coarseCoordinate coordinate) = coordinate := by
  constructor
  · rintro ⟨coarse, rfl⟩
    simp
  · exact fun equality => ⟨coarseCoordinate coordinate, equality⟩

/-- A fine coordinate is either the literal retained quarter selected by its
coarse interval or is genuinely created inside that interval. -/
theorem sparse_or_created (coordinate : Nat) :
    IsSparseCoordinate coordinate ∨
      sparseCoordinate (coarseCoordinate coordinate) < coordinate := by
  have spec := coarseCoordinate_spec coordinate
  rcases spec.1.eq_or_lt with equality | created
  · exact Or.inl ((isSparseCoordinate_iff coordinate).2 equality)
  · exact Or.inr created

/-- Assigning fine coordinates to retained sparse intervals is monotone. -/
theorem coarseCoordinate_mono {first second : Nat} (hle : first ≤ second) :
    coarseCoordinate first ≤ coarseCoordinate second := by
  by_contra hnot
  have hnext : coarseCoordinate second + 1 ≤ coarseCoordinate first := by omega
  have firstSpec := coarseCoordinate_spec first
  have secondSpec := coarseCoordinate_spec second
  have hsparse := secondSpec.2.trans_le (sparseCoordinate_mono hnext)
  omega

/-- A point strictly below a literal sparse coordinate projects strictly below
that coordinate's coarse source. -/
theorem coarseCoordinate_lt_of_lt_sparseCoordinate
    {fine coarse : Nat} (below : fine < sparseCoordinate coarse) :
    coarseCoordinate fine < coarse := by
  by_contra notBelow
  have sourceLe : coarse ≤ coarseCoordinate fine := by omega
  have fineSpec := coarseCoordinate_spec fine
  have := (sparseCoordinate_mono sourceLe).trans fineSpec.1
  omega

/-- A point strictly above a literal sparse coordinate projects weakly above
its coarse source.  Equality is possible inside the source's created
interval. -/
theorem le_coarseCoordinate_of_sparseCoordinate_lt
    {coarse fine : Nat} (above : sparseCoordinate coarse < fine) :
    coarse ≤ coarseCoordinate fine := by
  by_contra notAbove
  have nextLe : coarseCoordinate fine + 1 ≤ coarse := by omega
  have fineSpec := coarseCoordinate_spec fine
  have := fineSpec.2.trans_le (sparseCoordinate_mono nextLe)
  omega

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
