/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeCycles

/-!
# A direct base-four family of canonical free lines

An odd coordinate has two clear children; every even coordinate has one.  The
unique odd coordinate therefore adds exactly one line at each two-level
refinement.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLineCoordinates

open RedShadeCycles

def children (coordinate : Nat) : List Nat :=
  if coordinate % 2 = 1 then
    [4 * coordinate - 3, 4 * coordinate - 2]
  else
    [4 * coordinate]

def coordinates : Nat → List Nat
  | 0 => [5]
  | depth + 1 => (coordinates depth).flatMap children

@[simp] theorem coordinates_zero : coordinates 0 = [5] := rfl

@[simp] theorem coordinates_succ (depth : Nat) :
    coordinates (depth + 1) = (coordinates depth).flatMap children := rfl

theorem mem_children_cases {coordinate child : Nat}
    (hchild : child ∈ children coordinate) :
    (coordinate % 2 = 1 ∧
        (child = 4 * coordinate - 3 ∨ child = 4 * coordinate - 2)) ∨
      (coordinate % 2 = 0 ∧ child = 4 * coordinate) := by
  by_cases hodd : coordinate % 2 = 1
  · left
    simpa [children, hodd] using And.intro hodd hchild
  · have heven : coordinate % 2 = 0 := by omega
    right
    simpa [children, hodd] using And.intro heven hchild

theorem children_pairwise (coordinate : Nat) :
    (children coordinate).Pairwise (fun first second => first < second) := by
  by_cases hodd : coordinate % 2 = 1
  · have positive : 0 < coordinate := by omega
    simp [children, hodd]
    omega
  · simp [children, hodd]

theorem children_separated {first second : Nat} (hlt : first < second)
    {firstChild secondChild : Nat}
    (hfirst : firstChild ∈ children first)
    (hsecond : secondChild ∈ children second) :
    firstChild < secondChild := by
  rcases mem_children_cases hfirst with
    ⟨firstOdd, rfl | rfl⟩ | ⟨firstEven, rfl⟩ <;>
    rcases mem_children_cases hsecond with
      ⟨secondOdd, rfl | rfl⟩ | ⟨secondEven, rfl⟩ <;> omega

theorem coordinates_pairwise (depth : Nat) :
    (coordinates depth).Pairwise (fun first second => first < second) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [coordinates_succ, List.pairwise_flatMap]
      exact ⟨fun coordinate _ => children_pairwise coordinate,
        ih.imp fun hlt _ hfirst _ hsecond =>
          children_separated hlt hfirst hsecond⟩

theorem coordinates_nodup (depth : Nat) : (coordinates depth).Nodup :=
  (coordinates_pairwise depth).imp fun hlt => Nat.ne_of_lt hlt

def oddCount : List Nat → Nat
  | [] => 0
  | coordinate :: rest =>
      (if coordinate % 2 = 1 then 1 else 0) + oddCount rest

theorem oddCount_append (first second : List Nat) :
    oddCount (first ++ second) = oddCount first + oddCount second := by
  induction first with
  | nil => simp [oddCount]
  | cons coordinate rest ih => simp [oddCount, ih, Nat.add_assoc]

theorem oddCount_children (coordinate : Nat) :
    oddCount (children coordinate) = if coordinate % 2 = 1 then 1 else 0 := by
  by_cases hodd : coordinate % 2 = 1
  · have positive : 0 < coordinate := by omega
    have firstOdd : (4 * coordinate - 3) % 2 = 1 := by omega
    have secondEven : (4 * coordinate - 2) % 2 = 0 := by omega
    simp [children, oddCount, hodd, firstOdd, secondEven]
  · have heven : coordinate % 2 = 0 := by omega
    have childEven : (4 * coordinate) % 2 = 0 := by omega
    simp [children, oddCount, hodd, childEven]

theorem oddCount_flatMap_children (values : List Nat) :
    oddCount (values.flatMap children) = oddCount values := by
  induction values with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [List.flatMap_cons, oddCount_append, oddCount_children, ih]
      rfl

theorem coordinates_oddCount (depth : Nat) : oddCount (coordinates depth) = 1 := by
  induction depth with
  | zero => decide
  | succ depth ih => rw [coordinates_succ, oddCount_flatMap_children, ih]

theorem children_length (coordinate : Nat) :
    (children coordinate).length = if coordinate % 2 = 1 then 2 else 1 := by
  by_cases hodd : coordinate % 2 = 1 <;> simp [children, hodd]

theorem length_flatMap_children (values : List Nat) :
    (values.flatMap children).length = values.length + oddCount values := by
  induction values with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        children_length, ih]
      by_cases hodd : coordinate % 2 = 1 <;>
        simp [oddCount, hodd] <;> omega

theorem coordinates_length (depth : Nat) :
    (coordinates depth).length = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [coordinates_succ, length_flatMap_children,
        coordinates_oddCount, ih]

private theorem coordinates_cons (depth : Nat) :
    ∃ tail, coordinates depth = (4 * 4 ^ depth + 1) :: tail := by
  induction depth with
  | zero => exact ⟨[], rfl⟩
  | succ depth ih =>
      rcases ih with ⟨tail, ih⟩
      rw [coordinates_succ, ih, List.flatMap_cons]
      have hodd : (4 * 4 ^ depth + 1) % 2 = 1 := by
        simp [Nat.add_mod, Nat.mul_mod]
      unfold children
      rw [if_pos hodd]
      have firstEq :
          4 * (4 * 4 ^ depth + 1) - 3 = 4 * 4 ^ (depth + 1) + 1 := by
        rw [pow_succ]
        omega
      rw [firstEq]
      exact ⟨_, rfl⟩

theorem mem_coordinates_bounds (depth : Nat) {coordinate : Nat}
    (hcoordinate : coordinate ∈ coordinates depth) :
    quarterSouth (4 ^ depth) < coordinate ∧
      coordinate < quarterNorth (3 * 4 ^ depth) := by
  induction depth generalizing coordinate with
  | zero =>
      simp only [coordinates_zero, List.mem_singleton] at hcoordinate
      subst coordinate
      decide
  | succ depth ih =>
      rw [coordinates_succ, List.mem_flatMap] at hcoordinate
      rcases hcoordinate with ⟨old, hold, hchild⟩
      have oldBounds := ih hold
      rcases mem_children_cases hchild with
        ⟨hodd, rfl | rfl⟩ | ⟨heven, rfl⟩ <;>
        simp only [quarterSouth, quarterNorth, pow_succ] at oldBounds ⊢ <;>
        omega

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
