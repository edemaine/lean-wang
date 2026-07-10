/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedCycleExpansion

/-!
Coordinate-level doubling of corrected-Ollinger red cycles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedCycles

set_option maxRecDepth 20000

/-- Parity bit as an offset in a `2 x 2` substitution block. -/
def parityOffset (coordinate : Nat) : Fin 2 :=
  ⟨coordinate % 2, Nat.mod_lt _ (by decide)⟩

/-- Simultaneously substitute every index in a first-quadrant grid. -/
def refineIndexGrid (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  fun x y => childBlock (grid (x / 2) (y / 2))
    (parityOffset x) (parityOffset y)

@[simp]
theorem refineIndexGrid_even_even (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x) (2 * y) = southwestChild (grid x y) := by
  have hxDiv : (2 * x) / 2 = x := by omega
  have hyDiv : (2 * y) / 2 = y := by omega
  have hxOffset : parityOffset (2 * x) = ⟨0, by decide⟩ := by
    apply Fin.ext
    simp [parityOffset]
  have hyOffset : parityOffset (2 * y) = ⟨0, by decide⟩ := by
    apply Fin.ext
    simp [parityOffset]
  unfold refineIndexGrid
  rw [hxDiv, hyDiv, hxOffset, hyOffset]
  unfold southwestChild
  apply congrArg₂ (childBlock (grid x y)) <;> apply Fin.ext <;> rfl

@[simp]
theorem refineIndexGrid_odd_even (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x + 1) (2 * y) = southeastChild (grid x y) := by
  have hdiv : (2 * x + 1) / 2 = x := by omega
  have hyDiv : (2 * y) / 2 = y := by omega
  have hxOffset : parityOffset (2 * x + 1) = ⟨1, by decide⟩ := by
    apply Fin.ext
    simp [parityOffset]
  have hyOffset : parityOffset (2 * y) = ⟨0, by decide⟩ := by
    apply Fin.ext
    simp [parityOffset]
  unfold refineIndexGrid
  rw [hdiv, hyDiv, hxOffset, hyOffset]
  unfold southeastChild
  apply congrArg₂ (childBlock (grid x y)) <;> apply Fin.ext <;> rfl

@[simp]
theorem refineIndexGrid_even_odd (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x) (2 * y + 1) = northwestChild (grid x y) := by
  have hdiv : (2 * y + 1) / 2 = y := by omega
  have hxDiv : (2 * x) / 2 = x := by omega
  have hxOffset : parityOffset (2 * x) = ⟨0, by decide⟩ := by
    apply Fin.ext
    simp [parityOffset]
  have hyOffset : parityOffset (2 * y + 1) = ⟨1, by decide⟩ := by
    apply Fin.ext
    simp [parityOffset]
  unfold refineIndexGrid
  rw [hxDiv, hdiv, hxOffset, hyOffset]
  unfold northwestChild
  apply congrArg₂ (childBlock (grid x y)) <;> apply Fin.ext <;> rfl

/-- Proposition-level red cycle in an index grid. -/
structure RedCycleOn (grid : Nat → Nat → Index)
    (west east south north : Nat) : Prop where
  west_lt_east : west < east
  south_lt_north : south < north
  southwest : indexThick (grid west south) = .b
  southeast : indexThick (grid east south) = .c
  northwest : indexThick (grid west north) = .a
  northeast : indexThick (grid east north) = .d
  horizontal : ∀ x, west < x → x < east →
    hasRedHorizontal (indexThick (grid x south)) = true ∧
      hasRedHorizontal (indexThick (grid x north)) = true
  vertical : ∀ y, south < y → y < north →
    hasRedVertical (indexThick (grid west y)) = true ∧
      hasRedVertical (indexThick (grid east y)) = true

/-- Substitution doubles both dimensions of a red rectangular cycle. -/
theorem RedCycleOn.refine {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : RedCycleOn grid west east south north) :
    RedCycleOn (refineIndexGrid grid)
      (2 * west) (2 * east) (2 * south) (2 * north) where
  west_lt_east := by
    have := cycle.west_lt_east
    omega
  south_lt_north := by
    have := cycle.south_lt_north
    omega
  southwest := by
    simp only [refineIndexGrid_even_even]
    exact southwestChild_thick_b cycle.southwest
  southeast := by
    simp only [refineIndexGrid_even_even]
    exact southwestChild_thick_c cycle.southeast
  northwest := by
    simp only [refineIndexGrid_even_even]
    exact southwestChild_thick_a cycle.northwest
  northeast := by
    simp only [refineIndexGrid_even_even]
    exact southwestChild_thick_d cycle.northeast
  horizontal := by
    intro x hxWest hxEast
    let parentX := x / 2
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by
      have hlt := Nat.mod_lt x (by decide : 0 < 2)
      omega
    have hdecomp := Nat.mod_add_div x 2
    rcases hmod with heven | hodd
    · have hx : x = 2 * parentX := by
        dsimp [parentX]
        omega
      have hparentWest : west < parentX := by omega
      have hparentEast : parentX < east := by omega
      have hlines := cycle.horizontal parentX hparentWest hparentEast
      rw [hx, refineIndexGrid_even_even, refineIndexGrid_even_even]
      exact ⟨(redHorizontal_children hlines.1).1,
        (redHorizontal_children hlines.2).1⟩
    · have hx : x = 2 * parentX + 1 := by
        dsimp [parentX]
        omega
      have hparentWest : west ≤ parentX := by omega
      have hparentEast : parentX < east := by omega
      by_cases hwest : parentX = west
      · rw [hx, refineIndexGrid_odd_even, refineIndexGrid_odd_even, hwest]
        exact ⟨southeastChild_redHorizontal_of_thick_b cycle.southwest,
          southeastChild_redHorizontal_of_thick_a cycle.northwest⟩
      · have hparentWest' : west < parentX := by omega
        have hlines := cycle.horizontal parentX hparentWest' hparentEast
        rw [hx, refineIndexGrid_odd_even, refineIndexGrid_odd_even]
        exact ⟨(redHorizontal_children hlines.1).2,
          (redHorizontal_children hlines.2).2⟩
  vertical := by
    intro y hySouth hyNorth
    let parentY := y / 2
    have hmod : y % 2 = 0 ∨ y % 2 = 1 := by
      have hlt := Nat.mod_lt y (by decide : 0 < 2)
      omega
    have hdecomp := Nat.mod_add_div y 2
    rcases hmod with heven | hodd
    · have hy : y = 2 * parentY := by
        dsimp [parentY]
        omega
      have hparentSouth : south < parentY := by omega
      have hparentNorth : parentY < north := by omega
      have hlines := cycle.vertical parentY hparentSouth hparentNorth
      rw [hy, refineIndexGrid_even_even, refineIndexGrid_even_even]
      exact ⟨(redVertical_children hlines.1).1,
        (redVertical_children hlines.2).1⟩
    · have hy : y = 2 * parentY + 1 := by
        dsimp [parentY]
        omega
      have hparentSouth : south ≤ parentY := by omega
      have hparentNorth : parentY < north := by omega
      by_cases hsouth : parentY = south
      · rw [hy, refineIndexGrid_even_odd, refineIndexGrid_even_odd, hsouth]
        exact ⟨northwestChild_redVertical_of_thick_b cycle.southwest,
          northwestChild_redVertical_of_thick_c cycle.southeast⟩
      · have hparentSouth' : south < parentY := by omega
        have hlines := cycle.vertical parentY hparentSouth' hparentNorth
        rw [hy, refineIndexGrid_even_odd, refineIndexGrid_even_odd]
        exact ⟨(redVertical_children hlines.1).2,
          (redVertical_children hlines.2).2⟩

end RedCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
