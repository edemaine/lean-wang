/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineBranching

/-!
# Canonical free-line coordinates in the even shade phase

The coordinates are a translated copy of the common canonical offset tree.
At depth `d`, offset `o` is placed at `2 * 4^d + 1 + o`.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLineCoordinates

open RedShadeCycles CanonicalFreeLineBranching

def coordinate (depth offset : Nat) : Nat :=
  2 * 4 ^ depth + 1 + offset

def coordinates (depth : Nat) : List Nat :=
  (offsets depth).map (coordinate depth)

theorem coordinates_length (depth : Nat) :
    (coordinates depth).length = depth + 1 := by
  simp [coordinates, offsets_length]

private theorem coordinate_strictMono (depth : Nat) {first second : Nat}
    (hlt : first < second) : coordinate depth first < coordinate depth second := by
  simp [coordinate]
  omega

theorem coordinates_pairwise (depth : Nat) :
    (coordinates depth).Pairwise (fun first second => first < second) := by
  rw [coordinates, List.pairwise_map]
  exact (offsets_pairwise depth).imp fun hlt => coordinate_strictMono depth hlt

theorem mem_coordinates_iff {depth coordinateValue : Nat} :
    coordinateValue ∈ coordinates depth ↔
      ∃ offset ∈ offsets depth, coordinateValue = coordinate depth offset := by
  simp only [coordinates, List.mem_map]
  constructor
  · rintro ⟨offset, hoffset, heq⟩
    exact ⟨offset, hoffset, heq.symm⟩
  · rintro ⟨offset, hoffset, rfl⟩
    exact ⟨offset, hoffset, rfl⟩

theorem mem_coordinates_bounds (depth : Nat) {coordinateValue : Nat}
    (hcoordinate : coordinateValue ∈ coordinates depth) :
    quarterSouth (4 ^ depth) < coordinateValue ∧
      coordinateValue < quarterNorth (3 * 4 ^ depth) := by
  rw [mem_coordinates_iff] at hcoordinate
  rcases hcoordinate with ⟨offset, hoffset, rfl⟩
  have positive := offsets_positive depth hoffset
  have upper := offsets_upper depth hoffset
  simp only [coordinate, quarterSouth, quarterNorth]
  omega

private theorem coordinates_cons (depth : Nat) :
    ∃ tail, coordinates depth = (4 * 4 ^ depth + 1) :: tail := by
  rcases offsets_cons depth with ⟨tail, htail⟩
  rw [coordinates, htail, List.map_cons]
  have firstEq : coordinate depth (2 * 4 ^ depth) = 4 * 4 ^ depth + 1 := by
    simp [coordinate]
    omega
  rw [firstEq]
  exact ⟨_, rfl⟩

def coordinateAt (depth : Nat)
    (index : Fin (coordinates depth).length) : Nat :=
  (coordinates depth).get index

/-- The first coordinate is the retained northeast marker coordinate. -/
theorem coordinateAt_zero (depth : Nat)
    (positive : 0 < (coordinates depth).length) :
    coordinateAt depth ⟨0, positive⟩ = 4 * 4 ^ depth + 1 := by
  rcases coordinates_cons depth with ⟨tail, h⟩
  unfold coordinateAt
  rw [List.get_eq_getElem]
  simp [h]

theorem coordinateAt_mem (depth : Nat)
    (index : Fin (coordinates depth).length) :
    coordinateAt depth index ∈ coordinates depth :=
  List.get_mem _ _

theorem coordinateAt_strictMono (depth : Nat)
    {first second : Fin (coordinates depth).length} (hlt : first < second) :
    coordinateAt depth first < coordinateAt depth second :=
  (coordinates_pairwise depth).rel_get_of_lt hlt

theorem coordinateAt_bounds (depth : Nat)
    (index : Fin (coordinates depth).length) :
    quarterSouth (4 ^ depth) < coordinateAt depth index ∧
      coordinateAt depth index < quarterNorth (3 * 4 ^ depth) :=
  mem_coordinates_bounds depth (coordinateAt_mem depth index)

end CanonicalFreeLineCoordinates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
