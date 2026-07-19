/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.QuarterGeometry

/-!
Red cycles with the exact thick-line lane on each side.

The obstruction-signal rule distinguishes the inward-facing lanes, so the
coarser `hasRedHorizontal`/`hasRedVertical` invariant is strengthened to `R1`
on the south, `R3` on the north, `R0` on the west, and `R2` on the east.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedRedCycles

open RedCycles QuarterGeometry

set_option maxRecDepth 20000

/- Finite audit of exact red-lane preservation under substitution. -/
set_option linter.style.nativeDecide false in
theorem expansionRules (parent : Index) :
    (containsLine (indexThick parent) .r1 = true →
      containsLine (indexThick (southwestChild parent)) .r1 = true ∧
      containsLine (indexThick (southeastChild parent)) .r1 = true) ∧
    (containsLine (indexThick parent) .r3 = true →
      containsLine (indexThick (southwestChild parent)) .r3 = true ∧
      containsLine (indexThick (southeastChild parent)) .r3 = true) ∧
    (containsLine (indexThick parent) .r0 = true →
      containsLine (indexThick (southwestChild parent)) .r0 = true ∧
      containsLine (indexThick (northwestChild parent)) .r0 = true) ∧
    (containsLine (indexThick parent) .r2 = true →
      containsLine (indexThick (southwestChild parent)) .r2 = true ∧
      containsLine (indexThick (northwestChild parent)) .r2 = true) ∧
    (indexThick parent = .b →
      containsLine (indexThick (southeastChild parent)) .r1 = true) ∧
    (indexThick parent = .a →
      containsLine (indexThick (southeastChild parent)) .r3 = true) ∧
    (indexThick parent = .b →
      containsLine (indexThick (northwestChild parent)) .r0 = true) ∧
    (indexThick parent = .c →
      containsLine (indexThick (northwestChild parent)) .r2 = true) := by
  revert parent
  native_decide

theorem r1_children {parent : Index}
    (h : containsLine (indexThick parent) .r1 = true) :
    containsLine (indexThick (southwestChild parent)) .r1 = true ∧
      containsLine (indexThick (southeastChild parent)) .r1 = true :=
  (expansionRules parent).1 h

theorem r3_children {parent : Index}
    (h : containsLine (indexThick parent) .r3 = true) :
    containsLine (indexThick (southwestChild parent)) .r3 = true ∧
      containsLine (indexThick (southeastChild parent)) .r3 = true :=
  (expansionRules parent).2.1 h

theorem r0_children {parent : Index}
    (h : containsLine (indexThick parent) .r0 = true) :
    containsLine (indexThick (southwestChild parent)) .r0 = true ∧
      containsLine (indexThick (northwestChild parent)) .r0 = true :=
  (expansionRules parent).2.2.1 h

theorem r2_children {parent : Index}
    (h : containsLine (indexThick parent) .r2 = true) :
    containsLine (indexThick (southwestChild parent)) .r2 = true ∧
      containsLine (indexThick (northwestChild parent)) .r2 = true :=
  (expansionRules parent).2.2.2.1 h

theorem southeastChild_r1_of_b {parent : Index}
    (h : indexThick parent = .b) :
    containsLine (indexThick (southeastChild parent)) .r1 = true :=
  (expansionRules parent).2.2.2.2.1 h

theorem southeastChild_r3_of_a {parent : Index}
    (h : indexThick parent = .a) :
    containsLine (indexThick (southeastChild parent)) .r3 = true :=
  (expansionRules parent).2.2.2.2.2.1 h

theorem northwestChild_r0_of_b {parent : Index}
    (h : indexThick parent = .b) :
    containsLine (indexThick (northwestChild parent)) .r0 = true :=
  (expansionRules parent).2.2.2.2.2.2.1 h

theorem northwestChild_r2_of_c {parent : Index}
    (h : indexThick parent = .c) :
    containsLine (indexThick (northwestChild parent)) .r2 = true :=
  (expansionRules parent).2.2.2.2.2.2.2 h

/-- A red cycle whose four sides carry their exact inward-facing lanes. -/
structure CycleOn (grid : Nat → Nat → Index)
    (west east south north : Nat) : Prop extends
    RedCycleOn grid west east south north where
  southLane : ∀ x, west < x → x < east →
    containsLine (indexThick (grid x south)) .r1 = true
  northLane : ∀ x, west < x → x < east →
    containsLine (indexThick (grid x north)) .r3 = true
  westLane : ∀ y, south < y → y < north →
    containsLine (indexThick (grid west y)) .r0 = true
  eastLane : ∀ y, south < y → y < north →
    containsLine (indexThick (grid east y)) .r2 = true

private theorem refinedHorizontalLane
    {grid : Nat → Nat → Index} {west east row : Nat}
    (line : Figure16.ThickLine)
    (parentLane : ∀ x, west < x → x < east →
      containsLine (indexThick (grid x row)) line = true)
    (children : ∀ {parent : Index},
      containsLine (indexThick parent) line = true →
        containsLine (indexThick (southwestChild parent)) line = true ∧
        containsLine (indexThick (southeastChild parent)) line = true)
    (boundary : containsLine
      (indexThick (southeastChild (grid west row))) line = true) :
    ∀ x, 2 * west < x → x < 2 * east →
      containsLine (indexThick (refineIndexGrid grid x (2 * row))) line = true := by
  intro x hxWest hxEast
  let parentX := x / 2
  have hmod : x % 2 = 0 ∨ x % 2 = 1 := by
    have hlt := Nat.mod_lt x (by decide : 0 < 2)
    omega
  have hdecomp := Nat.mod_add_div x 2
  rcases hmod with heven | hodd
  · have hx : x = 2 * parentX := by dsimp [parentX]; omega
    rw [hx, refineIndexGrid_even_even]
    exact (children (parentLane parentX (by omega) (by omega))).1
  · have hx : x = 2 * parentX + 1 := by dsimp [parentX]; omega
    by_cases atBoundary : parentX = west
    · rw [hx, refineIndexGrid_odd_even, atBoundary]
      exact boundary
    · rw [hx, refineIndexGrid_odd_even]
      exact (children (parentLane parentX (by omega) (by omega))).2

private theorem refinedVerticalLane
    {grid : Nat → Nat → Index} {south north column : Nat}
    (line : Figure16.ThickLine)
    (parentLane : ∀ y, south < y → y < north →
      containsLine (indexThick (grid column y)) line = true)
    (children : ∀ {parent : Index},
      containsLine (indexThick parent) line = true →
        containsLine (indexThick (southwestChild parent)) line = true ∧
        containsLine (indexThick (northwestChild parent)) line = true)
    (boundary : containsLine
      (indexThick (northwestChild (grid column south))) line = true) :
    ∀ y, 2 * south < y → y < 2 * north →
      containsLine (indexThick (refineIndexGrid grid (2 * column) y)) line = true := by
  intro y hySouth hyNorth
  let parentY := y / 2
  have hmod : y % 2 = 0 ∨ y % 2 = 1 := by
    have hlt := Nat.mod_lt y (by decide : 0 < 2)
    omega
  have hdecomp := Nat.mod_add_div y 2
  rcases hmod with heven | hodd
  · have hy : y = 2 * parentY := by dsimp [parentY]; omega
    rw [hy, refineIndexGrid_even_even]
    exact (children (parentLane parentY (by omega) (by omega))).1
  · have hy : y = 2 * parentY + 1 := by dsimp [parentY]; omega
    by_cases atBoundary : parentY = south
    · rw [hy, refineIndexGrid_even_odd, atBoundary]
      exact boundary
    · rw [hy, refineIndexGrid_even_odd]
      exact (children (parentLane parentY (by omega) (by omega))).2

/-- Substitution doubles an oriented red cycle and preserves all four lanes. -/
theorem CycleOn.refine {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    CycleOn (refineIndexGrid grid)
      (2 * west) (2 * east) (2 * south) (2 * north) where
  toRedCycleOn := cycle.toRedCycleOn.refine
  southLane := refinedHorizontalLane .r1 cycle.southLane r1_children
    (southeastChild_r1_of_b cycle.southwest)
  northLane := refinedHorizontalLane .r3 cycle.northLane r3_children
    (southeastChild_r3_of_a cycle.northwest)
  westLane := refinedVerticalLane .r0 cycle.westLane r0_children
    (northwestChild_r0_of_b cycle.southwest)
  eastLane := refinedVerticalLane .r2 cycle.eastLane r2_children
    (northwestChild_r2_of_c cycle.southeast)

/-- Exact oriented form of the universal depth-two board certificate. -/
theorem depthTwo_supertile_has_orientedCycleOn (parent : Index) :
    CycleOn (fun x y => gridAt (supertile 2 parent) x y) 1 3 1 3 := by
  have horiented := fixedBoard_oriented parent
  refine {
    toRedCycleOn := depthTwo_supertile_has_fixed_redCycleOn parent
    southLane := ?_
    northLane := ?_
    westLane := ?_
    eastLane := ?_
  }
  · intro x hxWest hxEast
    have hx : x = 2 := by omega
    subst x
    simpa only [indexThick_eq, thickAt] using horiented.2.2.2.2.1
  · intro x hxWest hxEast
    have hx : x = 2 := by omega
    subst x
    simpa only [indexThick_eq, thickAt] using horiented.2.2.2.2.2.1
  · intro y hySouth hyNorth
    have hy : y = 2 := by omega
    subst y
    simpa only [indexThick_eq, thickAt] using horiented.2.2.2.2.2.2.1
  · intro y hySouth hyNorth
    have hy : y = 2 := by omega
    subst y
    simpa only [indexThick_eq, thickAt] using horiented.2.2.2.2.2.2.2

/-- Oriented cycles persist through arbitrarily many refinements. -/
theorem CycleOn.iterateRefine {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : CycleOn grid west east south north) (level : Nat) :
    CycleOn (RedCycles.iterateRefine level grid)
      (doubleN level west) (doubleN level east)
      (doubleN level south) (doubleN level north) := by
  induction level with
  | zero => exact cycle
  | succ level ih => exact ih.refine

end OrientedRedCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
