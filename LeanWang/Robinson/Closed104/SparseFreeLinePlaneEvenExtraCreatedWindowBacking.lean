/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeCycleEvenDescendants
import LeanWang.Robinson.Closed104.SparseFreeLinePlaneEvenExtraCreatedWindowClosure
import LeanWang.Robinson.Closed104.SparseFreeLineEvenExtraCycleRoute

/-!
# Backing created exceptional routes by the canonical cycle

The finite route search starts on one of nine depth-two cell cycles.  This file
translates that local start into the recursive grid and uses the even
base-four descendant bridge to back it by the enclosing canonical cycle.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneEvenExtraCreatedWindowBacking

open OrientedRedCycles OrientedRedBoardTranslations RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeGraphTranslation
  RedShadeCrossingBoards
  RedShadeCycleBridgeComposition RedShadeCycleEvenDescendants
  ShadedFreeLineRecurrence ShadedFreeLinePatternRefinement
  SparseFreeLineLocalProjection
  SparseFreeLineEvenExtraCycleRoute
  SparseFreeLineEvenExtraCreatedWindowAudit
  SparseFreeLinePlaneEvenExtraCreatedWindowClosure

set_option maxRecDepth 20000

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
/-- Translating a local cell-cycle port translates its cell coordinates. -/
theorem onCycle_translate_cell
    (originX originY x y : Nat) {port : Port}
    (onCycle : OnCycle (4 * x + 1) (4 * x + 3)
      (4 * y + 1) (4 * y + 3) port) :
    OnCycle (4 * (originX + x) + 1) (4 * (originX + x) + 3)
      (4 * (originY + y) + 1) (4 * (originY + y) + 3)
      (translatePort port (8 * originX) (8 * originY)) := by
  cases onCycle with
  | southWest qx hwest heast =>
      convert
        (OnCycle.southWest
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originX + qx) (by simp_all [quarterWest]; omega)
          (by simp_all [quarterEast]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | southEast qx hwest heast =>
      convert
        (OnCycle.southEast
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originX + qx) (by simp_all [quarterWest]; omega)
          (by simp_all [quarterEast]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | northWest qx hwest heast =>
      convert
        (OnCycle.northWest
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originX + qx) (by simp_all [quarterWest]; omega)
          (by simp_all [quarterEast]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | northEast qx hwest heast =>
      convert
        (OnCycle.northEast
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originX + qx) (by simp_all [quarterWest]; omega)
          (by simp_all [quarterEast]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | westSouth qy hsouth hnorth =>
      convert
        (OnCycle.westSouth
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originY + qy) (by simp_all [quarterSouth]; omega)
          (by simp_all [quarterNorth]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | westNorth qy hsouth hnorth =>
      convert
        (OnCycle.westNorth
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originY + qy) (by simp_all [quarterSouth]; omega)
          (by simp_all [quarterNorth]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | eastSouth qy hsouth hnorth =>
      convert
        (OnCycle.eastSouth
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originY + qy) (by simp_all [quarterSouth]; omega)
          (by simp_all [quarterNorth]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega
  | eastNorth qy hsouth hnorth =>
      convert
        (OnCycle.eastNorth
          (west := 4 * (originX + x) + 1) (east := 4 * (originX + x) + 3)
          (south := 4 * (originY + y) + 1) (north := 4 * (originY + y) + 3)
          (8 * originY + qy) (by simp_all [quarterSouth]; omega)
          (by simp_all [quarterNorth]; omega)) using 1 <;>
        simp [translatePort, quarterWest, quarterEast, quarterSouth,
          quarterNorth] <;> omega

/-- An enumerated local start lies on the corresponding translated global
cell cycle, which exists in every refined index grid. -/
theorem translatedStart_on_cell_cycle
    {window : Window} {start : RedShadeGraphWeightedSearch.WeightedStart}
    (hstart : start ∈ windowStarts window)
    (grid : Nat → Nat → Index) (originX originY : Nat) :
    ∃ x < 3, ∃ y < 3,
      start.parity = false ∧
      CycleOn (iterateRefine 2 grid)
        (4 * (originX + x) + 1) (4 * (originX + x) + 3)
        (4 * (originY + y) + 1) (4 * (originY + y) + 3) ∧
      OnCycle (4 * (originX + x) + 1) (4 * (originX + x) + 3)
        (4 * (originY + y) + 1) (4 * (originY + y) + 3)
        (translatePort start.port (8 * originX) (8 * originY)) := by
  rcases start_on_cell_cycle hstart with
    ⟨x, hx, y, hy, hparity, onCycle⟩
  exact ⟨x, hx, y, hy, hparity, depthTwo_at grid (originX + x) (originY + y),
    onCycle_translate_cell originX originY x y onCycle⟩

/-- A created-window route inside the root descendant block projects from the
enclosing even-phase canonical cycle. -/
theorem projectsTo_of_shiftedCreatedRoute
    {depth : Nat} {grid : Nat → Nat → Index} {originX originY : Nat}
    {window : Window} {target : Port}
    (horiginX : originX + 2 < 4 ^ (depth + 2))
    (horiginY : originY + 2 < 4 ^ (depth + 2))
    (route : ShiftedBoundedRoute (oldGrid depth grid) originX originY
      24 24 (windowStarts window) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth grid)
      (west := west .even (depth + 1)) (east := east .even (depth + 1))
      (south := west .even (depth + 1)) (north := east .even (depth + 1))
      (translatePort target (8 * originX) (8 * originY))) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases translatedStart_on_cell_cycle hstart (oldGrid depth grid)
      originX originY with
    ⟨x, hx, y, hy, hparity, descendantCycle, startOnCycle⟩
  have tail := SparseFreeLineLocalTransport.boundedPath_shift
    (oldGrid depth grid) originX originY path
  have tail' : Path (iterateRefine 2 (oldGrid depth grid))
      (translatePort start.port (8 * originX) (8 * originY))
      (translatePort target (8 * originX) (8 * originY)) true := by
    simpa [hparity] using tail
  have globalLive : portPresent (iterateRefine 2 (oldGrid depth grid))
      (translatePort target (8 * originX) (8 * originY)) = true := by
    rw [SparseFreeLineLocalTransport.portPresent_shift] at targetLive
    exact targetLive
  have bridgeRoot := rootDescendantBridge (depth + 2)
    grid (originX + x) (originY + y)
    (by omega) (by omega)
  have hbridgeGrid :
      iterateRefine (2 * (depth + 2) + 2) grid =
        iterateRefine 2 (oldGrid depth grid) := by
    rw [oldGrid, SparseFreeLinePlaneBase.refinedGrid,
      PlaneRedBoards.iterateRefine_add]
    congr 1
    simp [refinementDepth, Phase.extra]
    omega
  rw [hbridgeGrid] at bridgeRoot
  have bridge : EvenCycleBridge (iterateRefine 2 (oldGrid depth grid))
      (4 * west .even (depth + 1)) (4 * east .even (depth + 1))
      (4 * west .even (depth + 1)) (4 * east .even (depth + 1))
      (4 * (originX + x) + 1) (4 * (originX + x) + 3)
      (4 * (originY + y) + 1) (4 * (originY + y) + 3) := by
    simpa [west, east, scale, Phase.factor, Nat.add_assoc, pow_succ, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using bridgeRoot
  have oldCycle : CycleOn (oldGrid depth grid)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1)) := by
    have cycle := RedShadeCrossingBoards.largeCycle grid (2 * (depth + 1))
    have hpow : 2 ^ (2 * (depth + 1)) = 4 ^ (depth + 1) := by
      rw [pow_mul]
      norm_num
    rw [hpow] at cycle
    simpa [oldGrid, SparseFreeLinePlaneBase.refinedGrid, refinementDepth,
      Phase.extra, west, east, scale, Phase.factor, pow_succ,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      cycle
  have fineCycle := oldCycle.iterateRefine 2
  simp only [RedCycles.doubleN_eq] at fineCycle
  let source : Port :=
    ⟨quarterWest (west .even (depth + 1)) + 1,
      quarterSouth (west .even (depth + 1)), .west⟩
  have sourceOnCycle : OnCycle (west .even (depth + 1))
      (east .even (depth + 1)) (west .even (depth + 1))
      (east .even (depth + 1)) source := by
    dsimp [source]
    apply OnCycle.southWest
    · omega
    · simp [quarterWest, quarterEast, west, east, scale, Phase.factor]
      have hpow : 0 < 4 ^ (depth + 1) := pow_pos (by decide) _
      omega
  exact projectsTo_of_evenBridgeTail oldCycle (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using fineCycle)
    descendantCycle bridge sourceOnCycle startOnCycle tail' globalLive

/-- A routed created segment in a recursive row window projects from the
canonical cycle. -/
theorem verticalWindowRoute_projectsTo
    {depth : Nat} {grid : Nat → Nat → Index} {blockX delta : Nat} {target : Port}
    (hblockX : blockX = firstBlock depth + delta)
    (hdelta : delta ≤ blockCount depth)
    (route : Route (verticalWindowAt depth grid blockX) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth grid)
      (west := west .even (depth + 1)) (east := east .even (depth + 1))
      (south := west .even (depth + 1)) (north := east .even (depth + 1))
      (translatePort target (8 * (blockX - 1))
        (8 * (centerBlock depth - 1)))) := by
  apply projectsTo_of_shiftedCreatedRoute
  · have hfirst : firstBlock depth = 4 * 4 ^ depth := by
      rw [firstBlock, pow_succ]
      ac_rfl
    have hcount : blockCount depth = 8 * 4 ^ depth := by
      rw [blockCount_eq, pow_succ]
      omega
    have hroot : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
      rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [hfirst] at hblockX
    rw [hcount] at hdelta
    rw [hroot]
    have hpow : 0 < 4 ^ depth := pow_pos (by decide) _
    omega
  · have hroot : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
      rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [centerBlock, firstBlock, pow_succ, hroot]
    have hpow : 0 < 4 ^ depth := pow_pos (by decide) _
    omega
  · exact shiftedRoute_of_verticalWindowAt route

/-- A routed created segment in a recursive column window projects from the
canonical cycle. -/
theorem horizontalWindowRoute_projectsTo
    {depth : Nat} {grid : Nat → Nat → Index} {blockY delta : Nat} {target : Port}
    (hblockY : blockY = firstBlock depth + delta)
    (hdelta : delta ≤ blockCount depth)
    (route : Route (horizontalWindowAt depth grid blockY) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth grid)
      (west := west .even (depth + 1)) (east := east .even (depth + 1))
      (south := west .even (depth + 1)) (north := east .even (depth + 1))
      (translatePort target (8 * (centerBlock depth - 1))
        (8 * (blockY - 1)))) := by
  apply projectsTo_of_shiftedCreatedRoute
  · have hroot : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
      rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [centerBlock, firstBlock, pow_succ, hroot]
    have hpow : 0 < 4 ^ depth := pow_pos (by decide) _
    omega
  · have hfirst : firstBlock depth = 4 * 4 ^ depth := by
      rw [firstBlock, pow_succ]
      ac_rfl
    have hcount : blockCount depth = 8 * 4 ^ depth := by
      rw [blockCount_eq, pow_succ]
      omega
    have hroot : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
      rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [hfirst] at hblockY
    rw [hcount] at hdelta
    rw [hroot]
    have hpow : 0 < 4 ^ depth := pow_pos (by decide) _
    omega
  · exact shiftedRoute_of_horizontalWindowAt route

end SparseFreeLinePlaneEvenExtraCreatedWindowBacking
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
