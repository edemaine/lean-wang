/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseComplete
import LeanWang.OllingerRobinson104PairCoverSeamPathTranslation

/-!
# Transport the canonical residual-source base

The finite audit runs on a constant-parent block.  This module retains whether
its route starts on the large or small base cycle, transports the bounded path
into an arbitrary coarse-grid block, and only then packages the globally named
canonical ancestor.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalAncestorBaseTransport

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeGraphTranslation
  RefinementTranslation
  OrientedRedBoardTranslations PairCoverSeamShadePaths
  PairCoverSeamPathTranslation
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualCanonicalAncestorBaseAudit
  ShadedFreeLineRecurrence Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option linter.unnecessarySeqFocus false in
private theorem onCycle_translate
    {west east south north offsetX offsetY : Nat} {port : Port}
    (onCycle : OnCycle west east south north port) :
    OnCycle (offsetX + west) (offsetX + east)
      (offsetY + south) (offsetY + north)
      (translatePort port (2 * offsetX) (2 * offsetY)) := by
  cases onCycle with
  | southWest qx hwest heast =>
      convert OnCycle.southWest
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterSouth] <;> omega
  | southEast qx hwest heast =>
      convert OnCycle.southEast
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterSouth] <;> omega
  | northWest qx hwest heast =>
      convert OnCycle.northWest
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterNorth] <;> omega
  | northEast qx hwest heast =>
      convert OnCycle.northEast
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetX + qx) (by simp [quarterWest] at *; omega)
        (by simp [quarterEast] at *; omega) using 1 <;>
        simp [translatePort, quarterNorth] <;> omega
  | westSouth qy hsouth hnorth =>
      convert OnCycle.westSouth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterWest] <;> omega
  | westNorth qy hsouth hnorth =>
      convert OnCycle.westNorth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterWest] <;> omega
  | eastSouth qy hsouth hnorth =>
      convert OnCycle.eastSouth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterEast] <;> omega
  | eastNorth qy hsouth hnorth =>
      convert OnCycle.eastNorth
        (west := offsetX + west) (east := offsetX + east)
        (south := offsetY + south) (north := offsetY + north)
        (2 * offsetY + qy) (by simp [quarterSouth] at *; omega)
        (by simp [quarterNorth] at *; omega) using 1 <;>
        simp [translatePort, quarterEast] <;> omega

private theorem horizontalRoute
    {phase : Phase} {parent : Index} {column boundary : Nat}
    (columnBounds : InCollar (largeWest phase) (largeEast phase) column)
    (boundaryBounds : InCollar (largeWest phase) (largeEast phase) boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (baseGrid phase parent) column boundary)
      (quadrantAt column boundary) ≠ none) :
    BaseRoute phase parent
      (horizontalPort (baseGrid phase parent) column boundary) := by
  have checked := complete phase parent
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at checked
  have atTarget := checked.1 column (mem_collarCoordinates columnBounds)
    boundary (mem_collarCoordinates boundaryBounds)
  have required : (Signals.horizontalInterior?
      (componentAt (baseGrid phase parent) column boundary)
      (quadrantAt column boundary)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAt, required, Bool.not_true, Bool.false_or] at atTarget
  exact reachesEven_sound atTarget

private theorem verticalRoute
    {phase : Phase} {parent : Index} {boundary row : Nat}
    (boundaryBounds : InCollar (largeWest phase) (largeEast phase) boundary)
    (rowBounds : InCollar (largeWest phase) (largeEast phase) row)
    (interior : Signals.verticalInterior?
      (componentAt (baseGrid phase parent) boundary row)
      (quadrantAt boundary row) ≠ none) :
    BaseRoute phase parent
      (verticalPort (baseGrid phase parent) boundary row) := by
  have checked := complete phase parent
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at checked
  have atTarget := checked.2 boundary (mem_collarCoordinates boundaryBounds)
    row (mem_collarCoordinates rowBounds)
  have required : (Signals.verticalInterior?
      (componentAt (baseGrid phase parent) boundary row)
      (quadrantAt boundary row)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAt, required, Bool.not_true, Bool.false_or] at atTarget
  exact reachesEven_sound atTarget

set_option maxHeartbeats 3000000 in
-- Translating a bounded route changes both dependent endpoints and cycle indices.
private theorem BaseRoute.translate
    {phase : Phase} {parent : Index} {target : Port}
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (parentEq : grid blockX blockY = parent)
    (route : BaseRoute phase parent target) :
    CanonicalCycleAncestor (iterateRefine (levels phase) grid)
      (translatePort target
        (2 ^ (levels phase + 1) * blockX)
        (2 ^ (levels phase + 1) * blockY)) := by
  rcases route with ⟨entry, onLarge | onSmall, path⟩
  all_goals
    have componentsEq : ∀ x y, x < width phase → y < width phase →
        componentAt (baseGrid phase parent) x y =
          componentAt (iterateRefine (levels phase)
            (shiftGrid grid blockX blockY)) x y := by
      intro x y hx hy
      rw [baseGrid, ← parentEq]
      exact (componentAt_shift_eq_constant (levels phase) grid blockX blockY
        x y (by simpa [width] using hx) (by simpa [width] using hy)).symm
    have shiftedPath :=
      (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
        componentsEq path).path
    have globalPath := path_translate (grid := grid)
      (blockX := blockX) (blockY := blockY) shiftedPath
  · refine ⟨largeLevel phase, blockX, blockY, ?_,
      translatePort entry (2 ^ (levels phase + 1) * blockX)
        (2 ^ (levels phase + 1) * blockY), ?_, path_symm globalPath⟩
    · cases phase with
      | even =>
          simpa [levels, largeLevel, refinementDepth, Phase.extra,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            at_scale grid 2 blockX blockY
      | odd =>
          simpa [levels, largeLevel, refinementDepth, Phase.extra,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            at_scale grid 3 blockX blockY
    · have translated := onCycle_translate
        (offsetX := 2 ^ levels phase * blockX)
        (offsetY := 2 ^ levels phase * blockY) onLarge
      cases phase <;>
        convert translated using 1 <;>
        simp [levels, largeLevel, largeWest, largeEast, refinementDepth,
          Phase.extra, translatePort] <;> ring_nf <;> simp
  · refine ⟨smallLevel phase, 2 * blockX, 2 * blockY, ?_,
      translatePort entry (2 ^ (levels phase + 1) * blockX)
        (2 ^ (levels phase + 1) * blockY), ?_, path_symm globalPath⟩
    · cases phase with
      | even =>
          have cycle := at_scale (iterateRefine 1 grid) 1
            (2 * blockX) (2 * blockY)
          rw [PlaneRedBoards.iterateRefine_add] at cycle
          simpa [levels, smallLevel, refinementDepth, Phase.extra,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using cycle
      | odd =>
          have cycle := at_scale (iterateRefine 1 grid) 2
            (2 * blockX) (2 * blockY)
          rw [PlaneRedBoards.iterateRefine_add] at cycle
          simpa [levels, smallLevel, refinementDepth, Phase.extra,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using cycle
    · have translated := onCycle_translate
        (offsetX := 2 ^ levels phase * blockX)
        (offsetY := 2 ^ levels phase * blockY) onSmall
      cases phase <;>
        convert translated using 1 <;>
        simp [levels, smallLevel, smallWest, smallEast, refinementDepth,
          Phase.extra, translatePort] <;> ring_nf <;> simp

theorem sourceAncestorsIn (phase : Phase) (grid : Nat → Nat → Index)
    (blockX blockY : Nat) :
    SourceAncestorsIn (iterateRefine (levels phase) grid)
      (2 ^ levels phase * blockX + largeWest phase)
      (2 ^ levels phase * blockX + largeEast phase)
      (2 ^ levels phase * blockY + largeWest phase)
      (2 ^ levels phase * blockY + largeEast phase) := by
  let offsetX := 2 ^ (levels phase + 1) * blockX
  let offsetY := 2 ^ (levels phase + 1) * blockY
  have offsetX_eq : offsetX = 2 * (2 ^ levels phase * blockX) := by
    dsimp [offsetX]
    rw [pow_succ]
    ring
  have offsetY_eq : offsetY = 2 * (2 ^ levels phase * blockY) := by
    dsimp [offsetY]
    rw [pow_succ]
    ring
  constructor
  · intro column boundary columnBounds boundaryBounds interior
    let localX := column - offsetX
    let localY := boundary - offsetY
    have hcolumn : offsetX + localX = column := by
      dsimp [localX]
      apply Nat.add_sub_of_le
      unfold InCollar quarterWest at columnBounds
      rw [offsetX_eq]
      omega
    have hboundary : offsetY + localY = boundary := by
      dsimp [localY]
      apply Nat.add_sub_of_le
      unfold InCollar quarterWest at boundaryBounds
      rw [offsetY_eq]
      omega
    have localXBounds : InCollar (largeWest phase) (largeEast phase) localX := by
      unfold InCollar quarterWest quarterEast at columnBounds ⊢
      dsimp [localX] at hcolumn ⊢
      rw [offsetX_eq] at hcolumn
      omega
    have localYBounds : InCollar (largeWest phase) (largeEast phase) localY := by
      unfold InCollar quarterWest quarterEast at boundaryBounds ⊢
      dsimp [localY] at hboundary ⊢
      rw [offsetY_eq] at hboundary
      omega
    have hx : localX < width phase := by
      cases phase <;> simp [width, levels, largeWest, largeEast, largeLevel,
        refinementDepth,
        Phase.extra, InCollar, quarterEast] at localXBounds ⊢ <;> omega
    have hy : localY < width phase := by
      cases phase <;> simp [width, levels, largeWest, largeEast, largeLevel,
        refinementDepth,
        Phase.extra, InCollar, quarterEast] at localYBounds ⊢ <;> omega
    have shiftedInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine (levels phase)
          (shiftGrid grid blockX blockY)) localX localY)
        (quadrantAt localX localY) ≠ none := by
      rw [horizontalInterior_iterateRefine_shift]
      simpa only [offsetX, offsetY, hcolumn, hboundary] using interior
    have componentEq := componentAt_shift_eq_constant (levels phase) grid
      blockX blockY localX localY (by simpa [width] using hx)
      (by simpa [width] using hy)
    rw [componentEq] at shiftedInterior
    have localInterior : Signals.horizontalInterior?
        (componentAt (baseGrid phase (grid blockX blockY)) localX localY)
        (quadrantAt localX localY) ≠ none := by
      simpa [baseGrid] using shiftedInterior
    have ancestor := BaseRoute.translate grid blockX blockY rfl
      (horizontalRoute localXBounds localYBounds localInterior)
    have portEq : horizontalPort
        (baseGrid phase (grid blockX blockY)) localX localY =
        horizontalPort (iterateRefine (levels phase)
          (shiftGrid grid blockX blockY)) localX localY := by
      unfold horizontalPort
      simp only [baseGrid]
      rw [componentEq]
      rfl
    rw [portEq, horizontalPort_translate] at ancestor
    simpa only [offsetX, offsetY, hcolumn, hboundary] using ancestor
  · intro boundary row boundaryBounds rowBounds interior
    let localX := boundary - offsetX
    let localY := row - offsetY
    have hboundary : offsetX + localX = boundary := by
      dsimp [localX]
      apply Nat.add_sub_of_le
      unfold InCollar quarterWest at boundaryBounds
      rw [offsetX_eq]
      omega
    have hrow : offsetY + localY = row := by
      dsimp [localY]
      apply Nat.add_sub_of_le
      unfold InCollar quarterWest at rowBounds
      rw [offsetY_eq]
      omega
    have localXBounds : InCollar (largeWest phase) (largeEast phase) localX := by
      unfold InCollar quarterWest quarterEast at boundaryBounds ⊢
      dsimp [localX] at hboundary ⊢
      rw [offsetX_eq] at hboundary
      omega
    have localYBounds : InCollar (largeWest phase) (largeEast phase) localY := by
      unfold InCollar quarterWest quarterEast at rowBounds ⊢
      dsimp [localY] at hrow ⊢
      rw [offsetY_eq] at hrow
      omega
    have hx : localX < width phase := by
      cases phase <;> simp [width, levels, largeWest, largeEast, largeLevel,
        refinementDepth,
        Phase.extra, InCollar, quarterEast] at localXBounds ⊢ <;> omega
    have hy : localY < width phase := by
      cases phase <;> simp [width, levels, largeWest, largeEast, largeLevel,
        refinementDepth,
        Phase.extra, InCollar, quarterEast] at localYBounds ⊢ <;> omega
    have shiftedInterior : Signals.verticalInterior?
        (componentAt (iterateRefine (levels phase)
          (shiftGrid grid blockX blockY)) localX localY)
        (quadrantAt localX localY) ≠ none := by
      rw [verticalInterior_iterateRefine_shift]
      simpa only [offsetX, offsetY, hboundary, hrow] using interior
    have componentEq := componentAt_shift_eq_constant (levels phase) grid
      blockX blockY localX localY (by simpa [width] using hx)
      (by simpa [width] using hy)
    rw [componentEq] at shiftedInterior
    have localInterior : Signals.verticalInterior?
        (componentAt (baseGrid phase (grid blockX blockY)) localX localY)
        (quadrantAt localX localY) ≠ none := by
      simpa [baseGrid] using shiftedInterior
    have ancestor := BaseRoute.translate grid blockX blockY rfl
      (verticalRoute localXBounds localYBounds localInterior)
    have portEq : verticalPort
        (baseGrid phase (grid blockX blockY)) localX localY =
        verticalPort (iterateRefine (levels phase)
          (shiftGrid grid blockX blockY)) localX localY := by
      unfold verticalPort
      simp only [baseGrid]
      rw [componentEq]
      rfl
    rw [portEq, verticalPort_translate] at ancestor
    simpa only [offsetX, offsetY, hboundary, hrow] using ancestor

end PairCoverSeamResidualCanonicalAncestorBaseTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
