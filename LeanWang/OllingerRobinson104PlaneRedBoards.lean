/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104IteratedEmbedding

/-!
Unbounded red boards at concrete coordinates in every valid corrected-Ollinger plane.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PlaneRedBoards

open Hierarchy HierarchyEmbedding RedCycles

set_option maxRecDepth 20000

/-- Transfer a red cycle across pointwise equality on a bounding square. -/
theorem RedCycleOn.congr_of_eq_on
    {first second : Nat → Nat → Index} {west east south north bound : Nat}
    (cycle : RedCycleOn first west east south north)
    (heast : east < bound) (hnorth : north < bound)
    (heq : ∀ x y, x < bound → y < bound → first x y = second x y) :
    RedCycleOn second west east south north := by
  have hwest : west < bound := cycle.west_lt_east.trans heast
  have hsouth : south < bound := cycle.south_lt_north.trans hnorth
  refine {
  west_lt_east := cycle.west_lt_east
  south_lt_north := cycle.south_lt_north
  southwest := by
    rw [← heq west south hwest hsouth]
    exact cycle.southwest
  southeast := by
    rw [← heq east south heast hsouth]
    exact cycle.southeast
  northwest := by
    rw [← heq west north hwest hnorth]
    exact cycle.northwest
  northeast := by
    rw [← heq east north heast hnorth]
    exact cycle.northeast
  horizontal := by
    intro x hxWest hxEast
    have hlines := cycle.horizontal x hxWest hxEast
    constructor
    · rw [← heq x south (hxEast.trans heast) hsouth]
      exact hlines.1
    · rw [← heq x north (hxEast.trans heast) hnorth]
      exact hlines.2
  vertical := by
    intro y hySouth hyNorth
    have hlines := cycle.vertical y hySouth hyNorth
    constructor
    · rw [← heq west y hwest (hyNorth.trans hnorth)]
      exact hlines.1
    · rw [← heq east y heast (hyNorth.trans hnorth)]
      exact hlines.2
  }

/- The list and function presentations of a depth-two supertile agree. -/
set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem depthTwo_supertile_eq_iterateRefine :
    ∀ (parent : Index) (x y : Fin 4),
      gridAt (supertile 2 parent) x.val y.val =
        iterateRefine 2 (fun _ _ => parent) x.val y.val := by
  native_decide


theorem constantGrid_depthTwo_has_fixed_redCycleOn (parent : Index) :
    RedCycleOn (iterateRefine 2 (fun _ _ => parent)) 1 3 1 3 := by
  apply PlaneRedBoards.RedCycleOn.congr_of_eq_on
    (bound := 4) (depthTwo_supertile_has_fixed_redCycleOn parent)
    (by decide) (by decide)
  intro x y hx hy
  exact depthTwo_supertile_eq_iterateRefine parent ⟨x, hx⟩ ⟨y, hy⟩

theorem iterateRefine_two_apply (grid : Nat → Nat → Index) (x y : Nat) :
    iterateRefine 2 grid x y =
      childBlock
        (childBlock (grid ((x / 2) / 2) ((y / 2) / 2))
          (parityOffset (x / 2)) (parityOffset (y / 2)))
        (parityOffset x) (parityOffset y) := by
  rfl

/-- A depth-two block depends only on the one coarse tile below it. -/
theorem iterateRefine_two_local (grid : Nat → Nat → Index)
    {x y : Nat} (hx : x < 4) (hy : y < 4) :
    iterateRefine 2 grid x y =
      iterateRefine 2 (fun _ _ => grid 0 0) x y := by
  rw [iterateRefine_two_apply, iterateRefine_two_apply]
  have hxZero : (x / 2) / 2 = 0 := by omega
  have hyZero : (y / 2) / 2 = 0 := by omega
  rw [hxZero, hyZero]


theorem grid_depthTwo_has_fixed_redCycleOn (grid : Nat → Nat → Index) :
    RedCycleOn (iterateRefine 2 grid) 1 3 1 3 := by
  apply PlaneRedBoards.RedCycleOn.congr_of_eq_on
    (bound := 4) (constantGrid_depthTwo_has_fixed_redCycleOn (grid 0 0))
    (by decide) (by decide)
  intro x y hx hy
  exact (iterateRefine_two_local grid hx hy).symm

theorem iterateRefine_add (first second : Nat)
    (grid : Nat → Nat → Index) :
    RedCycles.iterateRefine first (RedCycles.iterateRefine second grid) =
      RedCycles.iterateRefine (first + second) grid := by
  induction first with
  | zero => simp only [RedCycles.iterateRefine, Nat.zero_add]
  | succ first ih =>
      have hindex : (first + 1) + second = (first + second) + 1 := by omega
      rw [hindex]
      change refineIndexGrid
          (RedCycles.iterateRefine first (RedCycles.iterateRefine second grid)) =
        refineIndexGrid (RedCycles.iterateRefine (first + second) grid)
      rw [ih]


end PlaneRedBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
