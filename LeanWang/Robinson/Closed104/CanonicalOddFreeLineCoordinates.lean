/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeCycles

/-!
# Coordinates for odd canonical free lines

Offsets are measured from `4 * 4^depth + 1`.  An even offset has two
children and an odd offset has one, while exactly one offset remains even.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddFreeLineCoordinates

open RedShadeCycles

def children (offset : Nat) : List Nat :=
  if offset % 2 = 0 then [4 * offset, 4 * offset + 1]
  else [4 * offset + 3]

def offsets : Nat → List Nat
  | 0 => [2]
  | depth + 1 => (offsets depth).flatMap children

def coordinate (depth offset : Nat) : Nat :=
  4 * 4 ^ depth + 1 + 2 * offset

def coordinates (depth : Nat) : List Nat :=
  (offsets depth).map (coordinate depth)

@[simp] theorem offsets_zero : offsets 0 = [2] := rfl

@[simp] theorem offsets_succ (depth : Nat) :
    offsets (depth + 1) = (offsets depth).flatMap children := rfl

theorem mem_children_cases {offset child : Nat}
    (hchild : child ∈ children offset) :
    (offset % 2 = 0 ∧
        (child = 4 * offset ∨ child = 4 * offset + 1)) ∨
      (offset % 2 = 1 ∧ child = 4 * offset + 3) := by
  by_cases heven : offset % 2 = 0
  · left
    simpa [children, heven] using And.intro heven hchild
  · have hodd : offset % 2 = 1 := by omega
    right
    simpa [children, heven] using And.intro hodd hchild

theorem children_pairwise (offset : Nat) :
    (children offset).Pairwise (fun first second => first < second) := by
  by_cases heven : offset % 2 = 0 <;> simp [children, heven]

theorem children_separated {first second : Nat} (hlt : first < second)
    {firstChild secondChild : Nat}
    (hfirst : firstChild ∈ children first)
    (hsecond : secondChild ∈ children second) :
    firstChild < secondChild := by
  rcases mem_children_cases hfirst with
    ⟨firstEven, rfl | rfl⟩ | ⟨firstOdd, rfl⟩ <;>
    rcases mem_children_cases hsecond with
      ⟨secondEven, rfl | rfl⟩ | ⟨secondOdd, rfl⟩ <;> omega

theorem offsets_pairwise (depth : Nat) :
    (offsets depth).Pairwise (fun first second => first < second) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [offsets_succ, List.pairwise_flatMap]
      exact ⟨fun offset _ => children_pairwise offset,
        ih.imp fun hlt _ hfirst _ hsecond =>
          children_separated hlt hfirst hsecond⟩

theorem offsets_nodup (depth : Nat) : (offsets depth).Nodup :=
  (offsets_pairwise depth).imp fun hlt => Nat.ne_of_lt hlt

def evenCount : List Nat → Nat
  | [] => 0
  | offset :: rest =>
      (if offset % 2 = 0 then 1 else 0) + evenCount rest

theorem evenCount_append (first second : List Nat) :
    evenCount (first ++ second) = evenCount first + evenCount second := by
  induction first with
  | nil => simp [evenCount]
  | cons offset rest ih => simp [evenCount, ih, Nat.add_assoc]

theorem evenCount_children (offset : Nat) :
    evenCount (children offset) = if offset % 2 = 0 then 1 else 0 := by
  by_cases heven : offset % 2 = 0
  · have firstEven : (4 * offset) % 2 = 0 := by omega
    have secondOdd : (4 * offset + 1) % 2 = 1 := by omega
    simp [children, evenCount, heven, firstEven, secondOdd]
  · have hodd : offset % 2 = 1 := by omega
    have childOdd : (4 * offset + 3) % 2 = 1 := by omega
    simp [children, evenCount, hodd, childOdd]

theorem evenCount_flatMap_children (values : List Nat) :
    evenCount (values.flatMap children) = evenCount values := by
  induction values with
  | nil => rfl
  | cons offset rest ih =>
      simp only [List.flatMap_cons, evenCount_append,
        evenCount_children, ih]
      rfl

theorem offsets_evenCount (depth : Nat) : evenCount (offsets depth) = 1 := by
  induction depth with
  | zero => decide
  | succ depth ih => rw [offsets_succ, evenCount_flatMap_children, ih]

theorem children_length (offset : Nat) :
    (children offset).length = if offset % 2 = 0 then 2 else 1 := by
  by_cases heven : offset % 2 = 0 <;> simp [children, heven]

theorem length_flatMap_children (values : List Nat) :
    (values.flatMap children).length = values.length + evenCount values := by
  induction values with
  | nil => rfl
  | cons offset rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        children_length, ih]
      by_cases heven : offset % 2 = 0 <;>
        simp [evenCount, heven] <;> omega

theorem offsets_length (depth : Nat) : (offsets depth).length = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [offsets_succ, length_flatMap_children,
        offsets_evenCount, ih]

theorem coordinates_length (depth : Nat) :
    (coordinates depth).length = depth + 1 := by
  simp [coordinates, offsets_length]

theorem offsets_positive (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) : 0 < offset := by
  induction depth generalizing offset with
  | zero =>
      simp only [offsets_zero, List.mem_singleton] at hoffset
      subst offset
      decide
  | succ depth ih =>
      rw [offsets_succ, List.mem_flatMap] at hoffset
      rcases hoffset with ⟨old, hold, hchild⟩
      have oldPositive := ih hold
      rcases mem_children_cases hchild with
        ⟨oldEven, rfl | rfl⟩ | ⟨oldOdd, rfl⟩ <;> omega

theorem offsets_upper (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) : offset < 4 * 4 ^ depth := by
  induction depth generalizing offset with
  | zero =>
      simp only [offsets_zero, List.mem_singleton] at hoffset
      subst offset
      decide
  | succ depth ih =>
      rw [offsets_succ, List.mem_flatMap] at hoffset
      rcases hoffset with ⟨old, hold, hchild⟩
      have oldUpper := ih hold
      rcases mem_children_cases hchild with
        ⟨oldEven, rfl | rfl⟩ | ⟨oldOdd, rfl⟩ <;>
        rw [pow_succ] <;> omega

theorem coordinate_strictMono (depth : Nat) {first second : Nat}
    (hlt : first < second) : coordinate depth first < coordinate depth second := by
  simp [coordinate]
  omega

theorem coordinates_pairwise (depth : Nat) :
    (coordinates depth).Pairwise (fun first second => first < second) := by
  rw [coordinates, List.pairwise_map]
  exact (offsets_pairwise depth).imp fun hlt => coordinate_strictMono depth hlt

theorem coordinates_nodup (depth : Nat) : (coordinates depth).Nodup :=
  (coordinates_pairwise depth).imp fun hlt => Nat.ne_of_lt hlt

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
    quarterSouth (2 * 4 ^ depth) < coordinateValue ∧
      coordinateValue < quarterNorth (6 * 4 ^ depth) := by
  rw [mem_coordinates_iff] at hcoordinate
  rcases hcoordinate with ⟨offset, hoffset, rfl⟩
  have positive := offsets_positive depth hoffset
  have upper := offsets_upper depth hoffset
  simp only [coordinate, quarterSouth, quarterNorth]
  omega

private theorem offsets_cons (depth : Nat) :
    ∃ tail, offsets depth = (2 * 4 ^ depth) :: tail := by
  induction depth with
  | zero => exact ⟨[], rfl⟩
  | succ depth ih =>
      rcases ih with ⟨tail, ih⟩
      rw [offsets_succ, ih, List.flatMap_cons]
      have heven : (2 * 4 ^ depth) % 2 = 0 := by simp
      unfold children
      rw [if_pos heven]
      have firstEq : 4 * (2 * 4 ^ depth) = 2 * 4 ^ (depth + 1) := by
        rw [pow_succ]
        omega
      rw [firstEq]
      exact ⟨_, rfl⟩

private theorem coordinates_cons (depth : Nat) :
    ∃ tail, coordinates depth = (8 * 4 ^ depth + 1) :: tail := by
  rcases offsets_cons depth with ⟨tail, htail⟩
  rw [coordinates, htail, List.map_cons]
  have firstEq : coordinate depth (2 * 4 ^ depth) = 8 * 4 ^ depth + 1 := by
    simp [coordinate]
    omega
  rw [firstEq]
  exact ⟨_, rfl⟩

def coordinateAt (depth : Nat)
    (index : Fin (coordinates depth).length) : Nat :=
  (coordinates depth).get index

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
    quarterSouth (2 * 4 ^ depth) < coordinateAt depth index ∧
      coordinateAt depth index < quarterNorth (6 * 4 ^ depth) :=
  mem_coordinates_bounds depth (coordinateAt_mem depth index)

theorem coordinateAt_zero (depth : Nat)
    (positive : 0 < (coordinates depth).length) :
    coordinateAt depth ⟨0, positive⟩ = 8 * 4 ^ depth + 1 := by
  rcases coordinates_cons depth with ⟨tail, hcoordinates⟩
  unfold coordinateAt
  rw [List.get_eq_getElem]
  simp [hcoordinates]

end CanonicalOddFreeLineCoordinates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
