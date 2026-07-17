/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.BorderCoverage

/-!
# Bounded displacement of successor free lines

Each child free line stays within six quarter-cells of the sparse copy of its
parent line. This is the arithmetic input for replacing growing whole-board
coverage searches by bounded substitution-neighborhood templates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace BorderCoverageOffsets

open RedShadeCycles RedShadeGraphRefinement ShadedFreeLineOffsets
  ShadedFreeLineRecurrence

theorem lineCoordinate_even (depth offset : Nat) :
    lineCoordinate .even depth offset = 2 * 4 ^ depth + 1 + offset := by
  simp [lineCoordinate, quarterStart, west, scale, Phase.factor, quarterWest]

theorem lineCoordinate_odd (depth offset : Nat) :
    lineCoordinate .odd depth offset = 4 * 4 ^ depth + 1 + 2 * offset := by
  simp [lineCoordinate, quarterStart, west, scale, Phase.factor, quarterWest]
  omega

theorem sparseCoordinate_of_even {coordinate : Nat}
    (heven : coordinate % 2 = 0) :
    sparseCoordinate coordinate = 4 * coordinate := by
  have hdecomp := Nat.mod_add_div coordinate 2
  simp [sparseCoordinate, macroOrigin, localCoordinate, heven]
  omega

theorem sparseCoordinate_of_odd {coordinate : Nat}
    (hodd : coordinate % 2 = 1) :
    sparseCoordinate coordinate + 3 = 4 * coordinate := by
  have hdecomp := Nat.mod_add_div coordinate 2
  simp [sparseCoordinate, macroOrigin, localCoordinate, hodd]
  omega

set_option linter.flexible false in
theorem childLine_even_boundedDisplacement
    (depth oldOffset child : Nat) (hchild : child ∈ expandOffset oldOffset) :
    ∃ delta ≤ 6,
      lineCoordinate .even (depth + 1) child + delta =
          sparseCoordinate (lineCoordinate .even depth oldOffset) ∨
        lineCoordinate .even (depth + 1) child =
          sparseCoordinate (lineCoordinate .even depth oldOffset) + delta := by
  have hdecomp := Nat.mod_add_div oldOffset 2
  have hmodlt := Nat.mod_lt oldOffset (by decide : 0 < 2)
  by_cases heven : oldOffset % 2 = 0
  · have hparity : (lineCoordinate .even depth oldOffset) % 2 = 1 := by
      rw [lineCoordinate_even]
      omega
    have hsparse := sparseCoordinate_of_odd hparity
    rw [lineCoordinate_even] at hsparse
    simp [expandOffset, heven] at hchild
    rcases hchild with rfl | rfl
    · refine ⟨0, by decide, Or.inr ?_⟩
      rw [lineCoordinate_even, lineCoordinate_even, pow_succ]
      omega
    · refine ⟨1, by decide, Or.inr ?_⟩
      rw [lineCoordinate_even, lineCoordinate_even, pow_succ]
      omega
  · have hodd : oldOffset % 2 = 1 := by omega
    have hparity : (lineCoordinate .even depth oldOffset) % 2 = 0 := by
      rw [lineCoordinate_even]
      omega
    have hsparse := sparseCoordinate_of_even hparity
    rw [lineCoordinate_even] at hsparse
    simp [expandOffset, heven] at hchild
    rcases hchild with rfl | rfl
    · refine ⟨1, by decide, Or.inl ?_⟩
      rw [lineCoordinate_even, lineCoordinate_even, pow_succ]
      omega
    · refine ⟨0, by decide, Or.inr ?_⟩
      rw [lineCoordinate_even, lineCoordinate_even, pow_succ]
      omega

set_option linter.flexible false in
theorem childLine_odd_boundedDisplacement
    (depth oldOffset child : Nat) (hchild : child ∈ expandOffset oldOffset) :
    ∃ delta ≤ 6,
      lineCoordinate .odd (depth + 1) child + delta =
          sparseCoordinate (lineCoordinate .odd depth oldOffset) ∨
        lineCoordinate .odd (depth + 1) child =
          sparseCoordinate (lineCoordinate .odd depth oldOffset) + delta := by
  have hparity : (lineCoordinate .odd depth oldOffset) % 2 = 1 := by
    rw [lineCoordinate_odd]
    omega
  have hsparse := sparseCoordinate_of_odd hparity
  rw [lineCoordinate_odd] at hsparse
  by_cases heven : oldOffset % 2 = 0
  · simp [expandOffset, heven] at hchild
    rcases hchild with rfl | rfl
    · refine ⟨0, by decide, Or.inr ?_⟩
      rw [lineCoordinate_odd, lineCoordinate_odd, pow_succ]
      omega
    · refine ⟨2, by decide, Or.inr ?_⟩
      rw [lineCoordinate_odd, lineCoordinate_odd, pow_succ]
      omega
  · simp [expandOffset, heven] at hchild
    rcases hchild with rfl | rfl
    · refine ⟨4, by decide, Or.inr ?_⟩
      rw [lineCoordinate_odd, lineCoordinate_odd, pow_succ]
      omega
    · refine ⟨6, by decide, Or.inr ?_⟩
      rw [lineCoordinate_odd, lineCoordinate_odd, pow_succ]
      omega

theorem childLine_boundedDisplacement
    (phase : Phase) (depth oldOffset child : Nat)
    (hchild : child ∈ expandOffset oldOffset) :
    ∃ delta ≤ 6,
      lineCoordinate phase (depth + 1) child + delta =
          sparseCoordinate (lineCoordinate phase depth oldOffset) ∨
        lineCoordinate phase (depth + 1) child =
          sparseCoordinate (lineCoordinate phase depth oldOffset) + delta := by
  cases phase
  · exact childLine_even_boundedDisplacement depth oldOffset child hchild
  · exact childLine_odd_boundedDisplacement depth oldOffset child hchild

theorem leftLine_even_displacement (depth : Nat) :
    lineCoordinate .even (depth + 1) 1 =
      sparseCoordinate (quarterWest (west .even depth)) + 1 := by
  have hparity : (quarterWest (west .even depth)) % 2 = 1 := by
    simp [west, scale, Phase.factor, quarterWest]
  have hsparse := sparseCoordinate_of_odd hparity
  rw [show quarterWest (west .even depth) = 2 * 4 ^ depth + 1 by
    simp [west, scale, Phase.factor, quarterWest]] at hsparse
  have hsparse' : sparseCoordinate (quarterWest (west .even depth)) =
      8 * 4 ^ depth + 1 := by
    rw [show quarterWest (west .even depth) = 2 * 4 ^ depth + 1 by
      simp [west, scale, Phase.factor, quarterWest]]
    omega
  rw [hsparse']
  rw [lineCoordinate_even, pow_succ]
  omega

theorem leftLine_odd_displacement (depth : Nat) :
    lineCoordinate .odd (depth + 1) 1 =
      sparseCoordinate (quarterWest (west .odd depth)) + 2 := by
  have hparity : (quarterWest (west .odd depth)) % 2 = 1 := by
    simp [west, scale, Phase.factor, quarterWest]
  have hsparse := sparseCoordinate_of_odd hparity
  rw [show quarterWest (west .odd depth) = 4 * 4 ^ depth + 1 by
    simp [west, scale, Phase.factor, quarterWest]
    omega] at hsparse
  have hsparse' : sparseCoordinate (quarterWest (west .odd depth)) =
      16 * 4 ^ depth + 1 := by
    rw [show quarterWest (west .odd depth) = 4 * 4 ^ depth + 1 by
      simp [west, scale, Phase.factor, quarterWest]
      omega]
    omega
  rw [hsparse']
  rw [lineCoordinate_odd, pow_succ]
  omega

theorem leftLine_boundedDisplacement (phase : Phase) (depth : Nat) :
    ∃ delta ≤ 2,
      lineCoordinate phase (depth + 1) 1 =
        sparseCoordinate (quarterWest (west phase depth)) + delta := by
  cases phase
  · exact ⟨1, by decide, leftLine_even_displacement depth⟩
  · exact ⟨2, by decide, leftLine_odd_displacement depth⟩

theorem rightLine_even_displacement (depth : Nat) :
    lineCoordinate .even (depth + 1) (4 ^ (depth + 2) - 2) + 1 =
      sparseCoordinate (quarterEast (east .even depth)) := by
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) depth
  have hparity : (quarterEast (east .even depth)) % 2 = 0 := by
    simp [east, scale, Phase.factor, quarterEast]
  have hsparse := sparseCoordinate_of_even hparity
  rw [show quarterEast (east .even depth) = 6 * 4 ^ depth by
    simp [east, scale, Phase.factor, quarterEast]
    omega] at hsparse
  have hsparse' : sparseCoordinate (quarterEast (east .even depth)) =
      24 * 4 ^ depth := by
    rw [show quarterEast (east .even depth) = 6 * 4 ^ depth by
      simp [east, scale, Phase.factor, quarterEast]
      omega]
    omega
  rw [hsparse']
  rw [lineCoordinate_even, pow_succ, pow_succ]
  omega

theorem rightLine_odd_displacement (depth : Nat) :
    lineCoordinate .odd (depth + 1) (4 ^ (depth + 2) - 2) + 3 =
      sparseCoordinate (quarterEast (east .odd depth)) := by
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) depth
  have hparity : (quarterEast (east .odd depth)) % 2 = 0 := by
    simp [east, scale, Phase.factor, quarterEast]
  have hsparse := sparseCoordinate_of_even hparity
  rw [show quarterEast (east .odd depth) = 12 * 4 ^ depth by
    simp [east, scale, Phase.factor, quarterEast]
    omega] at hsparse
  have hsparse' : sparseCoordinate (quarterEast (east .odd depth)) =
      48 * 4 ^ depth := by
    rw [show quarterEast (east .odd depth) = 12 * 4 ^ depth by
      simp [east, scale, Phase.factor, quarterEast]
      omega]
    omega
  rw [hsparse']
  rw [lineCoordinate_odd, pow_succ, pow_succ]
  omega

theorem rightLine_boundedDisplacement (phase : Phase) (depth : Nat) :
    ∃ delta ≤ 3,
      lineCoordinate phase (depth + 1) (4 ^ (depth + 2) - 2) + delta =
        sparseCoordinate (quarterEast (east phase depth)) := by
  cases phase
  · exact ⟨1, by decide, rightLine_even_displacement depth⟩
  · exact ⟨3, by decide, rightLine_odd_displacement depth⟩

end BorderCoverageOffsets
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
