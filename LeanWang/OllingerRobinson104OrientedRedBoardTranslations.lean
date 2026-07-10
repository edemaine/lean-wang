/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104OrientedPlaneRedBoards
import LeanWang.OllingerRobinson104SignalFreeCellEmbedding

/-!
Translated copies of the universal oriented Robinson board in every refined
coarse-grid block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedRedBoardTranslations

open OrientedRedCycles RedCycles

set_option maxRecDepth 20000

theorem CycleOn.translate
    {localGrid globalGrid : Nat → Nat → Index}
    {west east south north offsetX offsetY : Nat}
    (cycle : CycleOn localGrid west east south north)
    (heq : ∀ x y, x ≤ east → y ≤ north →
      localGrid x y = globalGrid (offsetX + x) (offsetY + y)) :
    CycleOn globalGrid
      (offsetX + west) (offsetX + east)
      (offsetY + south) (offsetY + north) where
  west_lt_east := Nat.add_lt_add_left cycle.west_lt_east offsetX
  south_lt_north := Nat.add_lt_add_left cycle.south_lt_north offsetY
  southwest := by
    rw [← heq west south (Nat.le_of_lt cycle.west_lt_east)
      (Nat.le_of_lt cycle.south_lt_north)]
    exact cycle.southwest
  southeast := by
    rw [← heq east south le_rfl (Nat.le_of_lt cycle.south_lt_north)]
    exact cycle.southeast
  northwest := by
    rw [← heq west north (Nat.le_of_lt cycle.west_lt_east) le_rfl]
    exact cycle.northwest
  northeast := by
    rw [← heq east north le_rfl le_rfl]
    exact cycle.northeast
  horizontal := by
    intro x hxWest hxEast
    let localX := x - offsetX
    have hx : offsetX + localX = x := by omega
    have hlocalWest : west < localX := by omega
    have hlocalEast : localX < east := by omega
    have hlines := cycle.horizontal localX hlocalWest hlocalEast
    constructor
    · rw [← hx, ← heq localX south (Nat.le_of_lt hlocalEast)
        (Nat.le_of_lt cycle.south_lt_north)]
      exact hlines.1
    · rw [← hx, ← heq localX north (Nat.le_of_lt hlocalEast) le_rfl]
      exact hlines.2
  vertical := by
    intro y hySouth hyNorth
    let localY := y - offsetY
    have hy : offsetY + localY = y := by omega
    have hlocalSouth : south < localY := by omega
    have hlocalNorth : localY < north := by omega
    have hlines := cycle.vertical localY hlocalSouth hlocalNorth
    constructor
    · rw [← hy, ← heq west localY (Nat.le_of_lt cycle.west_lt_east)
        (Nat.le_of_lt hlocalNorth)]
      exact hlines.1
    · rw [← hy, ← heq east localY le_rfl (Nat.le_of_lt hlocalNorth)]
      exact hlines.2
  southLane := by
    intro x hxWest hxEast
    let localX := x - offsetX
    have hx : offsetX + localX = x := by omega
    have hlocalWest : west < localX := by omega
    have hlocalEast : localX < east := by omega
    rw [← hx, ← heq localX south (Nat.le_of_lt hlocalEast)
      (Nat.le_of_lt cycle.south_lt_north)]
    exact cycle.southLane localX hlocalWest hlocalEast
  northLane := by
    intro x hxWest hxEast
    let localX := x - offsetX
    have hx : offsetX + localX = x := by omega
    have hlocalWest : west < localX := by omega
    have hlocalEast : localX < east := by omega
    rw [← hx, ← heq localX north (Nat.le_of_lt hlocalEast) le_rfl]
    exact cycle.northLane localX hlocalWest hlocalEast
  westLane := by
    intro y hySouth hyNorth
    let localY := y - offsetY
    have hy : offsetY + localY = y := by omega
    have hlocalSouth : south < localY := by omega
    have hlocalNorth : localY < north := by omega
    rw [← hy, ← heq west localY (Nat.le_of_lt cycle.west_lt_east)
      (Nat.le_of_lt hlocalNorth)]
    exact cycle.westLane localY hlocalSouth hlocalNorth
  eastLane := by
    intro y hySouth hyNorth
    let localY := y - offsetY
    have hy : offsetY + localY = y := by omega
    have hlocalSouth : south < localY := by omega
    have hlocalNorth : localY < north := by omega
    rw [← hy, ← heq east localY le_rfl (Nat.le_of_lt hlocalNorth)]
    exact cycle.eastLane localY hlocalSouth hlocalNorth

/-- Every coarse-grid coordinate contains the universal depth-two board. -/
theorem depthTwo_at (grid : Nat → Nat → Index) (blockX blockY : Nat) :
    CycleOn (iterateRefine 2 grid)
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) := by
  let localGrid := iterateRefine 2 (fun _ _ => grid blockX blockY)
  have cycle :=
    OrientedPlaneRedBoards.constantGrid_depthTwo_has_orientedCycleOn
      (grid blockX blockY)
  apply CycleOn.translate (offsetX := 4 * blockX) (offsetY := 4 * blockY)
    cycle
  intro x y hx hy
  have hx4 : x < 4 := by omega
  have hy4 : y < 4 := by omega
  simpa only [localGrid, Nat.zero_add, iterateRefine] using
    (Signals.FreeCellEmbedding.iterateRefine_two_block
      grid 0 blockX blockY x y hx4 hy4).symm

/-- Every coarse block contains the same board at every larger scale. -/
theorem at_scale (grid : Nat → Nat → Index)
    (level blockX blockY : Nat) :
    CycleOn (iterateRefine (level + 2) grid)
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) := by
  have cycle := (depthTwo_at grid blockX blockY).iterateRefine level
  simp only [RedCycles.doubleN_eq] at cycle
  rw [PlaneRedBoards.iterateRefine_add] at cycle
  exact cycle

end OrientedRedBoardTranslations
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
