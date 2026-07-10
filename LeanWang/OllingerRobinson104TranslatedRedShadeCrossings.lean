/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104OrientedRedBoardTranslations
import LeanWang.OllingerRobinson104RedShadeCycles

/-!
Opposite shades for translated Robinson boards at consecutive scales.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace TranslatedRedShadeCrossings

open OrientedRedBoardTranslations OrientedRedCycles PlaneRedBoards RedCycles
  RedShadeCycles RedShadePaths

set_option maxRecDepth 20000

theorem shades_ne_of_north_crosses_west
    {grid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    {largeWest largeEast largeSouth largeNorth : Nat}
    {smallWest smallEast smallSouth smallNorth : Nat}
    {largeShade smallShade : RedShades.Shade}
    (large : CycleOn grid largeWest largeEast largeSouth largeNorth)
    (small : CycleOn grid smallWest smallEast smallSouth smallNorth)
    (largeShaded : CycleShade stateGrid largeWest largeEast
      largeSouth largeNorth largeShade)
    (smallShaded : CycleShade stateGrid smallWest smallEast
      smallSouth smallNorth smallShade)
    (valid : ValidShadeGrid grid stateGrid)
    (hsmallWest : smallWest < largeWest)
    (hsmallEast : largeWest < smallEast)
    (hlargeSouth : largeSouth < smallNorth)
    (hlargeNorth : smallNorth < largeNorth) :
    largeShade ≠ smallShade := by
  let crossingX := quarterWest largeWest
  let crossingY := quarterNorth smallNorth
  have hsmallAt := smallShaded.north_at small valid
    (qx := crossingX) (by
      dsimp [crossingX]
      unfold quarterWest
      omega) (by
      dsimp [crossingX]
      unfold quarterWest quarterEast
      omega)
  have hlargeAt := largeShaded.west_at large valid
    (qy := crossingY) (by
      dsimp [crossingY]
      unfold quarterSouth quarterNorth
      omega) (by
      dsimp [crossingY]
      unfold quarterNorth
      omega)
  have hopposite := valid.crossing_opposite crossingX crossingY
    (CycleOn.north_path small (by
      dsimp [crossingX]
      unfold quarterWest
      omega) (by
      dsimp [crossingX]
      unfold quarterWest quarterEast
      omega))
    (CycleOn.west_path large (by
      dsimp [crossingY]
      unfold quarterSouth quarterNorth
      omega) (by
      dsimp [crossingY]
      unfold quarterNorth
      omega))
  intro heq
  apply hopposite
  rw [hsmallAt.1, hlargeAt.1, heq]

/-- The southwest half-scale board, expressed in the same refined grid. -/
theorem southwestSmallCycle (grid : Nat → Nat → Index)
    {level : Nat} (hlevel : 1 ≤ level) (blockX blockY : Nat) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ (level - 1) * (4 * (2 * blockX) + 1))
      (2 ^ (level - 1) * (4 * (2 * blockX) + 3))
      (2 ^ (level - 1) * (4 * (2 * blockY) + 1))
      (2 ^ (level - 1) * (4 * (2 * blockY) + 3)) := by
  have cycle := at_scale (iterateRefine 1 grid) (level - 1)
    (2 * blockX) (2 * blockY)
  have hgrid :
      iterateRefine (level - 1 + 2) (iterateRefine 1 grid) =
        iterateRefine (level + 2) grid := by
    rw [iterateRefine_add]
    congr 1
    omega
  rw [hgrid] at cycle
  exact cycle

theorem southwest_crossing_coordinates
    {level : Nat} (hlevel : 1 ≤ level) (blockX blockY : Nat) :
    2 ^ (level - 1) * (4 * (2 * blockX) + 1) <
        2 ^ level * (4 * blockX + 1) ∧
      2 ^ level * (4 * blockX + 1) <
        2 ^ (level - 1) * (4 * (2 * blockX) + 3) ∧
      2 ^ level * (4 * blockY + 1) <
        2 ^ (level - 1) * (4 * (2 * blockY) + 3) ∧
      2 ^ (level - 1) * (4 * (2 * blockY) + 3) <
        2 ^ level * (4 * blockY + 3) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  simp only [Nat.add_sub_cancel_left]
  have hpow : 2 ^ (1 + extra) = 2 * 2 ^ extra := by
    rw [Nat.add_comm, pow_succ]
    omega
  rw [hpow]
  have hpositive : 0 < 2 ^ extra := pow_pos (by decide) _
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · constructor <;> nlinarith

/-- Every translated board has an opposite-shaded southwest half-scale board. -/
theorem exists_opposite_southwest_shades
    (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    {level : Nat} (hlevel : 1 ≤ level) (blockX blockY : Nat)
    (valid : ValidShadeGrid (iterateRefine (level + 2) grid) stateGrid) :
    ∃ largeShade smallShade,
      CycleShade stateGrid
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) largeShade ∧
      CycleShade stateGrid
        (2 ^ (level - 1) * (4 * (2 * blockX) + 1))
        (2 ^ (level - 1) * (4 * (2 * blockX) + 3))
        (2 ^ (level - 1) * (4 * (2 * blockY) + 1))
        (2 ^ (level - 1) * (4 * (2 * blockY) + 3)) smallShade ∧
      largeShade ≠ smallShade := by
  let large := at_scale grid level blockX blockY
  let small := southwestSmallCycle grid hlevel blockX blockY
  rcases CycleOn.exists_cycleShade large valid with
    ⟨largeShade, largeShaded⟩
  rcases CycleOn.exists_cycleShade small valid with
    ⟨smallShade, smallShaded⟩
  have hcoordinates := southwest_crossing_coordinates hlevel blockX blockY
  exact ⟨largeShade, smallShade, largeShaded, smallShaded,
    shades_ne_of_north_crosses_west large small largeShaded smallShaded valid
      hcoordinates.1 hcoordinates.2.1 hcoordinates.2.2.1
      hcoordinates.2.2.2⟩

end TranslatedRedShadeCrossings
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
