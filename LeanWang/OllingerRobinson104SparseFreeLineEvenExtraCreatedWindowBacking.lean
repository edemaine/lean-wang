/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleEvenDescendants
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedWindowClosure
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleRoute

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
namespace SparseFreeLineEvenExtraCreatedWindowBacking

open OrientedRedCycles OrientedRedBoardTranslations RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeGraphTranslation
  RedShadeCycleBridgeComposition RedShadeCycleEvenDescendants
  ShadedFreeLineRecurrence ShadedFreeLinePatternRefinement
  SparseFreeLineLocalProjection
  SparseFreeLineEvenExtraCycleRoute
  SparseFreeLineEvenExtraCreatedWindowAudit
  SparseFreeLineEvenExtraCreatedWindowClosure

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
    {depth : Nat} {parent : Index} {originX originY : Nat}
    {window : Window} {target : Port}
    (horiginX : originX + 2 < 4 ^ (depth + 2))
    (horiginY : originY + 2 < 4 ^ (depth + 2))
    (route : ShiftedBoundedRoute (oldGrid depth parent) originX originY
      24 24 (windowStarts window) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth parent)
      (west := west .even (depth + 1)) (east := east .even (depth + 1))
      (south := west .even (depth + 1)) (north := east .even (depth + 1))
      (translatePort target (8 * originX) (8 * originY))) := by
  rcases route with ⟨start, hstart, path, targetLive⟩
  rcases translatedStart_on_cell_cycle hstart (oldGrid depth parent)
      originX originY with
    ⟨x, hx, y, hy, hparity, descendantCycle, startOnCycle⟩
  have tail := SparseFreeLineLocalTransport.boundedPath_shift
    (oldGrid depth parent) originX originY path
  have tail' : Path (iterateRefine 2 (oldGrid depth parent))
      (translatePort start.port (8 * originX) (8 * originY))
      (translatePort target (8 * originX) (8 * originY)) true := by
    simpa [hparity] using tail
  have globalLive : portPresent (iterateRefine 2 (oldGrid depth parent))
      (translatePort target (8 * originX) (8 * originY)) = true := by
    rw [SparseFreeLineLocalTransport.portPresent_shift] at targetLive
    exact targetLive
  have bridgeRoot := rootDescendantBridge (depth + 2)
    (fun _ _ => parent) (originX + x) (originY + y)
    (by omega) (by omega)
  have hbridgeGrid :
      iterateRefine (2 * (depth + 2) + 2) (fun _ _ => parent) =
        iterateRefine 2 (oldGrid depth parent) := by
    rw [oldGrid, localGrid, PlaneRedBoards.iterateRefine_add]
    congr 1
    simp [refinementDepth, Phase.extra]
    omega
  rw [hbridgeGrid] at bridgeRoot
  have bridge : EvenCycleBridge (iterateRefine 2 (oldGrid depth parent))
      (4 * west .even (depth + 1)) (4 * east .even (depth + 1))
      (4 * west .even (depth + 1)) (4 * east .even (depth + 1))
      (4 * (originX + x) + 1) (4 * (originX + x) + 3)
      (4 * (originY + y) + 1) (4 * (originY + y) + 3) := by
    simpa [west, east, scale, Phase.factor, Nat.add_assoc, pow_succ, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using bridgeRoot
  have oldCycle := canonicalCycle .even (depth + 1) parent
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
    {depth : Nat} {parent : Index} {blockX : Nat} {target : Port}
    (hblockX : blockX ≤ blockCount depth)
    (route : Route (verticalWindowAt depth parent blockX) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth parent)
      (west := west .even (depth + 1)) (east := east .even (depth + 1))
      (south := west .even (depth + 1)) (north := east .even (depth + 1))
      (translatePort target (8 * (blockX - 1))
        (8 * (centerBlock depth - 1)))) := by
  apply projectsTo_of_shiftedCreatedRoute
  · have hcount : blockCount depth = 8 * 4 ^ depth := by
      rw [blockCount_eq, pow_succ]
      omega
    have hroot : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
      rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [hcount] at hblockX
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
    {depth : Nat} {parent : Index} {blockY : Nat} {target : Port}
    (hblockY : blockY ≤ blockCount depth)
    (route : Route (horizontalWindowAt depth parent blockY) target) :
    Nonempty (ProjectsTo (grid := oldGrid depth parent)
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
  · have hcount : blockCount depth = 8 * 4 ^ depth := by
      rw [blockCount_eq, pow_succ]
      omega
    have hroot : 4 ^ (depth + 2) = 16 * 4 ^ depth := by
      rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [hcount] at hblockY
    rw [hroot]
    have hpow : 0 < 4 ^ depth := pow_pos (by decide) _
    omega
  · exact shiftedRoute_of_horizontalWindowAt route

end SparseFreeLineEvenExtraCreatedWindowBacking
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
