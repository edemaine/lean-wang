/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycles
import LeanWang.OllingerRobinson104OrientedPlaneRedBoards

/-!
Two comparable canonical boards crossing in the same refined grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCrossingBoards

open RedCycles PlaneRedBoards OrientedRedCycles OrientedPlaneRedBoards
open RedShadePaths

set_option maxRecDepth 20000

/-- The usual canonical board at refinement level `level`. -/
theorem largeCycle (grid : Nat → Nat → Index) (level : Nat) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) := by
  have cycle := grid_depthTwo_has_orientedCycleOn grid |>.iterateRefine level
  simp only [doubleN_eq, Nat.mul_one] at cycle
  have hgrid : iterateRefine level (iterateRefine 2 grid) =
      iterateRefine (level + 2) grid :=
    iterateRefine_add level 2 grid
  rw [hgrid] at cycle
  simpa [mul_comm] using cycle

/-- A board seeded one refinement later, of half the side length. -/
theorem smallCycle (grid : Nat → Nat → Index) {level : Nat}
    (hlevel : 1 ≤ level) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) := by
  have cycle := grid_depthTwo_has_orientedCycleOn (iterateRefine 1 grid)
    |>.iterateRefine (level - 1)
  simp only [doubleN_eq, Nat.mul_one] at cycle
  have hgrid :
      iterateRefine (level - 1) (iterateRefine 2 (iterateRefine 1 grid)) =
        iterateRefine (level + 2) grid := by
    rw [iterateRefine_add (level - 1) 2,
      iterateRefine_add (level - 1 + 2) 1]
    congr 1
    omega
  rw [hgrid] at cycle
  simpa [mul_comm] using cycle

/-- The half-scale board crosses the southwest sides of the large board. -/
theorem crossing_coordinates {level : Nat} (hlevel : 1 ≤ level) :
    2 ^ (level - 1) < 2 ^ level ∧
      2 ^ level < 3 * 2 ^ (level - 1) ∧
      3 * 2 ^ (level - 1) < 3 * 2 ^ level := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  simp only [Nat.add_sub_cancel_left]
  have hsucc : 2 ^ (1 + extra) = 2 * 2 ^ extra := by
    calc
      2 ^ (1 + extra) = 2 ^ (extra + 1) := by rw [Nat.add_comm]
      _ = 2 ^ extra * 2 := pow_succ 2 extra
      _ = 2 * 2 ^ extra := by ac_rfl
  rw [hsucc]
  have hpow : 0 < 2 ^ extra := pow_pos (by decide) _
  omega

/-- Uniform, opposite shades of the two crossing canonical boards. -/
def OppositeCycleShades (stateGrid : Nat → Nat → RedShades.State)
    (level : Nat) : Prop :=
  ∃ largeShade smallShade,
    RedShadeCycles.CycleShade stateGrid
      (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) largeShade ∧
    RedShadeCycles.CycleShade stateGrid
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) smallShade ∧
    largeShade ≠ smallShade

set_option maxHeartbeats 500000 in
-- The comparison composes two dependent path prefixes at the crossing point.
/-- The comparable crossing boards necessarily have opposite shades. -/
theorem oppositeCycleShades (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State} {level : Nat}
    (hlevel : 1 ≤ level) (valid : ValidShadeGrid
      (iterateRefine (level + 2) grid) stateGrid) :
    OppositeCycleShades stateGrid level := by
  let large := largeCycle grid level
  let small := smallCycle grid hlevel
  rcases RedShadeCycles.CycleOn.exists_cycleShade large valid with
    ⟨largeShade, largeShaded⟩
  rcases RedShadeCycles.CycleOn.exists_cycleShade small valid with
    ⟨smallShade, smallShaded⟩
  let largeWest := 2 ^ level
  let largeNorth := 3 * 2 ^ level
  let smallWest := 2 ^ (level - 1)
  let smallEast := 3 * 2 ^ (level - 1)
  let crossingX := RedShadeCycles.quarterWest largeWest
  let crossingY := RedShadeCycles.quarterNorth smallEast
  have hcoordinates := crossing_coordinates hlevel
  have hsmallWest : RedShadeCycles.quarterWest smallWest < crossingX := by
    dsimp [crossingX, largeWest, smallWest]
    unfold RedShadeCycles.quarterWest
    omega
  have hsmallEast : crossingX < RedShadeCycles.quarterEast smallEast := by
    dsimp [crossingX, largeWest, smallEast]
    unfold RedShadeCycles.quarterWest RedShadeCycles.quarterEast
    omega
  have hlargeSouth : RedShadeCycles.quarterSouth largeWest < crossingY := by
    dsimp [crossingY, largeWest, smallEast]
    unfold RedShadeCycles.quarterSouth RedShadeCycles.quarterNorth
    omega
  have hlargeNorth : crossingY < RedShadeCycles.quarterNorth largeNorth := by
    dsimp [crossingY, smallEast, largeNorth]
    unfold RedShadeCycles.quarterNorth
    omega
  dsimp only [largeWest, largeNorth, smallWest, smallEast,
    crossingX, crossingY] at *
  have hlargeWestEq : largeWest = 2 ^ level := rfl
  have hlargeNorthEq : largeNorth = 3 * 2 ^ level := rfl
  have hsmallWestEq : smallWest = 2 ^ (level - 1) := rfl
  have hsmallEastEq : smallEast = 3 * 2 ^ (level - 1) := rfl
  have hcrossingXEq : crossingX =
      RedShadeCycles.quarterWest (2 ^ level) := rfl
  have hcrossingYEq : crossingY =
      RedShadeCycles.quarterNorth (3 * 2 ^ (level - 1)) := rfl
  have hlargeStart :
      (stateGrid (RedShadeCycles.quarterWest largeWest)
        (RedShadeCycles.quarterSouth largeWest)).north = some largeShade := by
    rw [← valid.east_north_corner_eq
      (RedShadeCycles.quarterWest largeWest)
      (RedShadeCycles.quarterSouth largeWest)
      (RedShadeCycles.CycleOn.southwest_corner large).1
      (RedShadeCycles.CycleOn.southwest_corner large).2]
    exact largeShaded.southwest
  have hlargeFlow :
      (stateGrid (RedShadeCycles.quarterWest largeWest)
        (RedShadeCycles.quarterSouth largeWest)).north =
      (stateGrid crossingX crossingY).south := by
    have hflow := vertical_shade_across
      (fun qy => stateGrid crossingX qy)
      (RedShadeCycles.quarterSouth largeWest)
      (crossingY - RedShadeCycles.quarterSouth largeWest - 1)
      (fun i hi => valid.vmatch crossingX
        (RedShadeCycles.quarterSouth largeWest + i))
      (fun i hi => valid.vertical_eq crossingX
        (RedShadeCycles.quarterSouth largeWest + i + 1)
        (RedShadeCycles.CycleOn.west_path large
          (by dsimp [largeWest] at *; omega)
          (by
            dsimp [largeWest, largeNorth, crossingY, smallEast] at *
            omega)))
    have hend : RedShadeCycles.quarterSouth largeWest +
        (crossingY - RedShadeCycles.quarterSouth largeWest - 1) + 1 =
          crossingY := by
      dsimp [largeWest, crossingY, smallEast] at *
      omega
    simpa only [crossingX, hend] using hflow
  have hlargeAt : (stateGrid crossingX crossingY).south = some largeShade :=
    hlargeFlow.symm.trans hlargeStart
  have hsmallFlow :
      (stateGrid (RedShadeCycles.quarterWest smallWest)
        (RedShadeCycles.quarterNorth smallEast)).east =
      (stateGrid crossingX crossingY).west := by
    have hflow := horizontal_shade_across
      (fun qx => stateGrid qx crossingY)
      (RedShadeCycles.quarterWest smallWest)
      (crossingX - RedShadeCycles.quarterWest smallWest - 1)
      (fun i hi => valid.hmatch
        (RedShadeCycles.quarterWest smallWest + i) crossingY)
      (fun i hi => valid.horizontal_eq
        (RedShadeCycles.quarterWest smallWest + i + 1) crossingY
        (RedShadeCycles.CycleOn.north_path small
          (by dsimp [smallWest] at *; omega)
          (by
            dsimp [smallWest, smallEast, crossingX, largeWest] at *
            omega)))
    have hend : RedShadeCycles.quarterWest smallWest +
        (crossingX - RedShadeCycles.quarterWest smallWest - 1) + 1 =
          crossingX := by
      dsimp [smallWest, crossingX, largeWest] at *
      omega
    simpa only [crossingY, hend] using hflow
  have hsmallAt : (stateGrid crossingX crossingY).west = some smallShade :=
    hsmallFlow.symm.trans smallShaded.northwest
  have hopposite := valid.crossing_opposite crossingX crossingY
    (RedShadeCycles.CycleOn.north_path small hsmallWest hsmallEast)
    (RedShadeCycles.CycleOn.west_path large hlargeSouth hlargeNorth)
  have hshadeOpposite : largeShade ≠ smallShade := by
    intro heq
    apply hopposite
    rw [hsmallAt, hlargeAt, heq]
  exact ⟨largeShade, smallShade, largeShaded, smallShaded, hshadeOpposite⟩

end RedShadeCrossingBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
