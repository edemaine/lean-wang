/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedRedCycles

/-!
Unbounded oriented red boards at concrete coordinates in hierarchy planes.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedPlaneRedBoards

open Hierarchy HierarchyEmbedding RedCycles PlaneRedBoards
  OrientedRedCycles

set_option maxRecDepth 20000

/-- Transfer an oriented cycle across pointwise equality on a bounding square. -/
theorem CycleOn.congr_of_eq_on
    {first second : Nat → Nat → Index} {west east south north bound : Nat}
    (cycle : CycleOn first west east south north)
    (heast : east < bound) (hnorth : north < bound)
    (heq : ∀ x y, x < bound → y < bound → first x y = second x y) :
    CycleOn second west east south north := by
  have hwest : west < bound := cycle.west_lt_east.trans heast
  have hsouth : south < bound := cycle.south_lt_north.trans hnorth
  refine {
    toRedCycleOn := PlaneRedBoards.RedCycleOn.congr_of_eq_on
      cycle.toRedCycleOn heast hnorth heq
    southLane := ?_
    northLane := ?_
    westLane := ?_
    eastLane := ?_
  }
  · intro x hxWest hxEast
    rw [← heq x south (hxEast.trans heast) hsouth]
    exact cycle.southLane x hxWest hxEast
  · intro x hxWest hxEast
    rw [← heq x north (hxEast.trans heast) hnorth]
    exact cycle.northLane x hxWest hxEast
  · intro y hySouth hyNorth
    rw [← heq west y hwest (hyNorth.trans hnorth)]
    exact cycle.westLane y hySouth hyNorth
  · intro y hySouth hyNorth
    rw [← heq east y heast (hyNorth.trans hnorth)]
    exact cycle.eastLane y hySouth hyNorth

theorem constantGrid_depthTwo_has_orientedCycleOn (parent : Index) :
    CycleOn (iterateRefine 2 (fun _ _ => parent)) 1 3 1 3 := by
  apply OrientedPlaneRedBoards.CycleOn.congr_of_eq_on
    (bound := 4) (depthTwo_supertile_has_orientedCycleOn parent)
    (by decide) (by decide)
  intro x y hx hy
  exact depthTwo_supertile_eq_iterateRefine parent ⟨x, hx⟩ ⟨y, hy⟩

theorem grid_depthTwo_has_orientedCycleOn (grid : Nat → Nat → Index) :
    CycleOn (iterateRefine 2 grid) 1 3 1 3 := by
  apply OrientedPlaneRedBoards.CycleOn.congr_of_eq_on
    (bound := 4) (constantGrid_depthTwo_has_orientedCycleOn (grid 0 0))
    (by decide) (by decide)
  intro x y hx hy
  exact (iterateRefine_two_local grid hx hy).symm

/-- Every hierarchy plane contains canonical oriented boards at unbounded scale. -/
theorem Tower.has_fixed_unbounded_orientedCycles
    {base : ValidPlane} (tower : Tower base) (level : Nat) :
    ∃ origin : Int × Int,
      CycleOn (natGridAt base.tiling origin)
        (2 ^ level) (2 ^ level * 3) (2 ^ level) (2 ^ level * 3) := by
  let coarseGrid :=
    natGridAt (tower.plane (level + 2)).tiling (0, 0)
  have seedCycle := grid_depthTwo_has_orientedCycleOn coarseGrid
  have scaledCycle := seedCycle.iterateRefine level
  simp only [doubleN_eq, Nat.mul_one] at scaledCycle
  have hadd : iterateRefine level (iterateRefine 2 coarseGrid) =
      iterateRefine (level + 2) coarseGrid :=
    iterateRefine_add level 2 coarseGrid
  rw [hadd] at scaledCycle
  have hembed := HierarchyEmbedding.Tower.natGridAt_descendOrigin
    tower (level + 2) 0 (0, 0)
  have hembed' :
      natGridAt (tower.plane 0).tiling
          (descendOrigin tower 0 (level + 2) (0, 0)) =
        iterateRefine (level + 2) coarseGrid := by
    simpa only [Nat.zero_add, coarseGrid] using hembed
  rw [← hembed'] at scaledCycle
  rw [tower.zero] at scaledCycle
  exact ⟨descendOrigin tower 0 (level + 2) (0, 0), scaledCycle⟩

end OrientedPlaneRedBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
