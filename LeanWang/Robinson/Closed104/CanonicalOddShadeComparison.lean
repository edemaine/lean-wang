/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeBase
import LeanWang.Robinson.Closed104.CanonicalOddShadeGeometry
import LeanWang.Robinson.Closed104.CanonicalShadeComparisonCore
import LeanWang.Robinson.Closed104.RedShadeCycleOddDescendants

/-! Comparing arbitrary and raw canonical shades at odd root scale. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeComparison

open OrientedRedCycles RedCycles RedShades RedShadePaths RedShadeCycles
  RedShadeGraph RedShadeGraphBoards RedShadeGraphColoring
  RedShadeGraphLocalCoverage RedShadeGraphRefinement
  RedShadeGraphBoundedPath RedShadeGraphTranslation
  RedShadeCycleConnectivity
  RedShadeCycleOddDescendants OrientedRedBoardTranslations
  RefinementTranslation Signals.FreeCellLocal ShadedSubstitution
  CanonicalOddFreeLineCoordinates CanonicalOddFreeLines
  CanonicalOddShadeGeometry CanonicalShadeComparisonCore

set_option maxRecDepth 20000

def scale (depth : Nat) : Nat := 2 * 4 ^ depth

private theorem pow_four_add_two (depth : Nat) :
    4 ^ (depth + 2) = 16 * 4 ^ depth := by
  simp only [pow_succ]
  omega

private theorem scale_succ (depth : Nat) :
    scale (depth + 1) = 4 * scale depth := by
  simp only [scale, pow_succ]
  omega

def actualGrid (depth : Nat) (coarse : Nat → Nat → Index) :
    Nat → Nat → Index :=
  iterateRefine (2 * depth + 4) coarse

private theorem rootCycle (depth : Nat) (coarse : Nat → Nat → Index) :
    CycleOn (actualGrid depth coarse)
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) := by
  have cycle := RedShadeCrossingBoards.smallCycle coarse
    (level := 2 * depth + 2) (by omega)
  have hpow : 2 ^ (2 * depth + 1) = scale depth := by
    rw [show 2 * depth + 1 = 1 + 2 * depth by omega, pow_add, pow_mul]
    norm_num [scale]
  rw [show 2 * depth + 2 - 1 = 2 * depth + 1 by omega, hpow] at cycle
  simpa only [actualGrid, show 2 * depth + 2 + 2 = 2 * depth + 4 by omega]
    using cycle

private theorem value_succ_block (level blockX blockY : Nat) (port : Port)
    (hx : port.x < 8) (hy : port.y < 8) :
    value (shadeGrid (level + 1))
        (translatePort port (8 * blockX) (8 * blockY)) =
      value (supertileShadeGrid 1
        (supertileNodeGrid level seedNode blockX blockY)) port := by
  rcases port with ⟨x, y, side⟩
  have stateEq := CanonicalOddShadeGeometry.shadeGrid_succ_block
    level blockX blockY x y hx hy
  cases side <;> simpa [value, translatePort] using congrArg _ stateEq

private theorem value_succ_sparse (level : Nat) (port : Port) :
    value (shadeGrid (level + 1)) (sparsePort port) =
      value (shadeGrid level) port := by
  rcases port with ⟨x, y, side⟩
  have stateEq := CanonicalOddShadeGeometry.shadeGrid_succ_sparse level x y
  cases side <;> simpa [value, sparsePort] using congrArg _ stateEq

private theorem value_of_cyclePort
    {states : Nat → Nat → RedShades.State} {port : Port}
    (shaded : CycleShade states 2 6 2 6 .light)
    (hport : port ∈ CanonicalOddShadeBase.cyclePorts) :
    value states port = some .light := by
  simp only [CanonicalOddShadeBase.cyclePorts, List.mem_cons,
    List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl
  · simpa [value, quarterWest, quarterSouth] using shaded.southwest
  · simpa [value, quarterEast, quarterSouth] using shaded.southeast
  · simpa [value, quarterEast, quarterNorth] using shaded.northeast
  · simpa [value, quarterWest, quarterNorth] using shaded.northwest

private theorem base_component_actual (coarse : Nat → Nat → Index)
    (coarseRoot : coarse 0 0 = 0) (x y : Nat)
    (hx : x < 16) (hy : y < 16) :
    componentAt CanonicalOddShadeBase.indexGrid x y =
      componentAt (actualGrid 0 coarse) x y := by
  have localized := componentAt_shift_eq_constant 4 coarse 0 0 x y
    (by norm_num; omega) (by norm_num; omega)
  have shiftZero : shiftGrid coarse 0 0 = coarse := by
    funext gridX gridY
    simp [shiftGrid]
  rw [shiftZero, coarseRoot] at localized
  simpa [CanonicalOddShadeBase.indexGrid, actualGrid] using localized.symm

private theorem canonicalIndex_base :
    indexGrid 2 = CanonicalOddShadeBase.indexGrid := by
  unfold CanonicalOddFreeLines.indexGrid CanonicalOddShadeBase.indexGrid
  rw [CanonicalShadeGeometry.supertileIndexGrid_eq_iterateRefine,
    seedNode_parent]

private theorem canonicalValid_base :
    ValidShadeRectangle (indexGrid 2) (shadeGrid 2) 16 16 := by
  have valid := CanonicalOddShadeGeometry.validRectangle 2
  constructor
  · intro x y hx hy
    exact valid.allowed x y (by omega) (by omega)
  · intro x y hx hy
    exact valid.hmatch x y (by omega) (by omega)
  · intro x y hx hy
    exact valid.vmatch x y (by omega) (by omega)

private noncomputable def localStates (depth blockX blockY : Nat) :
    Nat → Nat → RedShades.State :=
  supertileShadeGrid 1
    (supertileNodeGrid (depth + 2) seedNode blockX blockY)

private theorem baseAgreement (coarse : Nat → Nat → Index)
    (coarseRoot : coarse 0 0 = 0)
    (states : Nat → Nat → RedShades.State)
    (valid : ValidShadeGrid (actualGrid 0 coarse) states)
    (shaded : CycleShade states 2 6 2 6 .light)
    (target : Port)
    (targetWest : 4 ≤ target.x) (targetEast : target.x < 12)
    (targetSouth : 4 ≤ target.y) (targetNorth : target.y < 12)
    (targetPresent : portPresent (actualGrid 0 coarse) target = true) :
    value states target = value (shadeGrid 2) target := by
  have targetMem : target ∈ portsIn 16 16 :=
    mem_portsIn (by omega) (by omega)
  have basePresent : portPresent CanonicalOddShadeBase.indexGrid target = true := by
    have targetBounds := bounds_of_mem_portsIn targetMem
    rcases target with ⟨x, y, side⟩
    cases side <;> simp only [portPresent] <;>
      rw [base_component_actual coarse coarseRoot x y
        targetBounds.1 targetBounds.2] <;>
      exact targetPresent
  rcases CanonicalOddShadeBase.exists_boundedPath targetMem
      targetWest targetEast targetSouth targetNorth basePresent with
    ⟨start, parity, startMem, basePath⟩
  have actualPath := BoundedPath.congr_of_component_eq
    (fun x y hx hy => base_component_actual coarse coarseRoot x y hx hy)
    basePath
  have actualStart := value_of_cyclePort shaded startMem
  have actualRelation := actualPath.path.sound valid
  rw [actualStart] at actualRelation
  have canonicalPath : BoundedPath (indexGrid 2) 16 16
      start target parity := by
    simpa [canonicalIndex_base] using basePath
  have canonicalStart := value_of_cyclePort
    CanonicalOddShadeGeometry.rootCycle_light startMem
  have canonicalRelation :=
    boundedPath_soundOnRectangle canonicalValid_base canonicalPath
  rw [canonicalStart] at canonicalRelation
  exact Related.right_unique actualRelation canonicalRelation

private theorem localValid (depth : Nat) (coarse : Nat → Nat → Index)
    (coarseRoot : coarse 0 0 = 0) (blockX blockY : Nat)
    (_blockXLower : scale depth ≤ blockX)
    (blockXUpper : blockX < 3 * scale depth)
    (_blockYLower : scale depth ≤ blockY)
    (blockYUpper : blockY < 3 * scale depth) :
    ValidShadeRectangle (fineGrid (actualGrid depth coarse blockX blockY))
      (localStates depth blockX blockY) 8 8 := by
  have blockXCanonical : blockX < 4 ^ (depth + 2) := by
    rw [show 4 ^ (depth + 2) = 8 * scale depth by
      rw [pow_four_add_two]
      unfold scale
      omega]
    omega
  have blockYCanonical : blockY < 4 ^ (depth + 2) := by
    rw [show 4 ^ (depth + 2) = 8 * scale depth by
      rw [pow_four_add_two]
      unfold scale
      omega]
    omega
  let node := supertileNodeGrid (depth + 2) seedNode blockX blockY
  have parentEq : node.data.parent = actualGrid depth coarse blockX blockY := by
    change supertileIndexGrid (depth + 2) seedNode blockX blockY = _
    change supertileIndexGrid (depth + 2) seedNode blockX blockY =
      iterateRefine (2 * depth + 4) coarse blockX blockY
    rw [← show 2 * (depth + 2) = 2 * depth + 4 by omega]
    exact CanonicalShadeGeometry.supertileIndexGrid_eq_coarse
      (depth + 2) seedNode coarse
      (coarseRoot.trans seedNode_parent.symm)
      blockXCanonical blockYCanonical
  have canonicalValid := supertile_validShadeRectangle 1 node
  have localIndexEq : supertileIndexGrid 1 node =
      fineGrid (actualGrid depth coarse blockX blockY) := by
    simpa [CanonicalEvenFreeLines.indexGrid] using
      localGrid_eq node (actualGrid depth coarse blockX blockY) parentEq
  rw [localIndexEq] at canonicalValid
  exact canonicalValid

private theorem cycleSourceAgreement (depth : Nat)
    (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State) (blockX blockY : Nat)
    (valid : ValidShadeGrid (actualGrid (depth + 1) coarse) states)
    (shaded : CycleShade states
      (scale (depth + 1)) (3 * scale (depth + 1))
      (scale (depth + 1)) (3 * scale (depth + 1)) .light)
    (_blockXLower : scale depth ≤ blockX)
    (blockXUpper : blockX < 3 * scale depth)
    (_blockYLower : scale depth ≤ blockY)
    (blockYUpper : blockY < 3 * scale depth)
    (cellCycle : CycleOn (actualGrid (depth + 1) coarse)
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3)) :
    value states (translatePort cycleSource (8 * blockX) (8 * blockY)) =
      value (localStates depth blockX blockY) cycleSource := by
  have blockXDescendant : blockX < 2 * 4 ^ (depth + 1) := by
    simp only [scale] at blockXUpper
    rw [pow_succ]
    omega
  have blockYDescendant : blockY < 2 * 4 ^ (depth + 1) := by
    simp only [scale] at blockYUpper
    rw [pow_succ]
    omega
  have bridge := RedShadeCycleOddDescendants.rootDescendantBridge
    (depth + 1) coarse blockX blockY
    blockXDescendant blockYDescendant
  have bridge' : RedShadeCycleCrossingPaths.OddCycleBridge
      (actualGrid (depth + 1) coarse)
      (scale (depth + 1)) (3 * scale (depth + 1))
      (scale (depth + 1)) (3 * scale (depth + 1))
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) := by
    simpa only [actualGrid, scale, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using bridge
  have actualSource :
      value states (translatePort cycleSource (8 * blockX) (8 * blockY)) =
        some .dark := by
    rcases related_of_cycleBridge valid
      (rootCycle (depth + 1) coarse) shaded cellCycle bridge'
      (sourceOnCell blockX blockY) with ⟨pathShade, shadeEq, targetEq⟩
    have : pathShade = .light := Option.some.inj shadeEq.symm
    subst pathShade
    simpa [RedShades.Shade.opposite] using targetEq
  have canonicalSource := CanonicalOddShadeGeometry.cycleSource_dark
    (supertileNodeGrid (depth + 2) seedNode blockX blockY)
  exact actualSource.trans canonicalSource.symm

/-- Every live central port agrees with the raw canonical odd assignment. -/
theorem present_value_eq (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light)
    (target : Port)
    (targetWest : 2 * scale depth ≤ target.x)
    (targetEast : target.x < 6 * scale depth)
    (targetSouth : 2 * scale depth ≤ target.y)
    (targetNorth : target.y < 6 * scale depth)
    (targetPresent : portPresent (actualGrid depth coarse) target = true) :
    value states target = value (shadeGrid (depth + 2)) target := by
  apply present_value_eq_of_refinement
    scale (fun phaseDepth => actualGrid phaseDepth coarse)
    (fun phaseDepth => shadeGrid (phaseDepth + 2))
    localStates
  · exact scale_succ
  · intro phaseDepth
    dsimp [actualGrid]
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  · exact fun phaseDepth => rootCycle phaseDepth coarse
  · intro baseStates baseValid baseShaded baseTarget baseWest baseEast
      baseSouth baseNorth basePresent
    simpa [scale] using baseAgreement coarse coarseRoot baseStates
      baseValid baseShaded baseTarget baseWest baseEast baseSouth baseNorth
      basePresent
  · intro phaseDepth blockX blockY blockXLower blockXUpper
      blockYLower blockYUpper
    exact localValid phaseDepth coarse coarseRoot blockX blockY
      blockXLower blockXUpper blockYLower blockYUpper
  · intro phaseDepth blockX blockY port portX portY
    exact value_succ_block (phaseDepth + 2) blockX blockY
      port portX portY
  · intro phaseDepth port
    exact value_succ_sparse (phaseDepth + 2) port
  · intro phaseDepth phaseStates blockX blockY phaseValid phaseShaded
      blockXLower blockXUpper blockYLower blockYUpper cellCycle
    exact cycleSourceAgreement phaseDepth coarse phaseStates blockX blockY
      phaseValid phaseShaded blockXLower blockXUpper blockYLower
      blockYUpper cellCycle
  · exact valid
  · exact shaded
  · exact targetWest
  · exact targetEast
  · exact targetSouth
  · exact targetNorth
  · exact targetPresent

private theorem index_canonical_eq (depth : Nat)
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0)
    (x y : Nat) (xEast : x < 8 * scale depth)
    (yNorth : y < 8 * scale depth) :
    indexGrid (depth + 2) (x / 2) (y / 2) =
      actualGrid depth coarse (x / 2) (y / 2) := by
  have xBound : x / 2 < 4 ^ (depth + 2) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    simp only [scale] at xEast
    rw [show 4 ^ (depth + 2) = 16 * 4 ^ depth by
      exact pow_four_add_two depth]
    omega
  have yBound : y / 2 < 4 ^ (depth + 2) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    simp only [scale] at yNorth
    rw [show 4 ^ (depth + 2) = 16 * 4 ^ depth by
      exact pow_four_add_two depth]
    omega
  change supertileIndexGrid (depth + 2) seedNode (x / 2) (y / 2) =
    iterateRefine (2 * depth + 4) coarse (x / 2) (y / 2)
  rw [← show 2 * (depth + 2) = 2 * depth + 4 by omega]
  exact CanonicalShadeGeometry.supertileIndexGrid_eq_coarse
    (depth + 2) seedNode coarse
    (coarseRoot.trans seedNode_parent.symm) xBound yBound

/-- The odd phase packages live-port agreement and common geometry. -/
theorem comparison (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light) :
    PhaseComparison (actualGrid depth coarse) (indexGrid (depth + 2))
      states (shadeGrid (depth + 2)) (scale depth)
      (2 * 4 ^ (depth + 2)) := by
  refine {
    actualValid := valid
    canonicalValid := CanonicalOddShadeGeometry.validRectangle (depth + 2)
    extent_large := ?_
    component_eq := ?_
    present_value_eq := ?_
  }
  · rw [pow_four_add_two]
    simp only [scale]
    omega
  · intro x y xEast yNorth
    simp only [componentAt]
    rw [index_canonical_eq depth coarse coarseRoot x y xEast yNorth]
  · intro port portWest portEast portSouth portNorth portPresent
    exact present_value_eq depth coarse states coarseRoot valid shaded
      port portWest portEast portSouth portNorth portPresent

/-- Every coordinate in the canonical family is a free row and column in the
arbitrary light-root shade assignment. -/
theorem freeCoordinates (depth : Nat)
    (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light) :
    PhaseComparison.FreeCoordinateFamily
      (actualGrid depth coarse) states (scale depth) (coordinates depth) := by
  apply (comparison depth coarse states coarseRoot valid shaded)
    |>.freeCoordinateFamily (coordinates depth)
  · intro selected selectedMem
    simpa only [scale, show 3 * (2 * 4 ^ depth) = 6 * 4 ^ depth by omega] using
      mem_coordinates_bounds depth selectedMem
  · intro axis selected selectedMem
    rw [show 3 * scale depth = 6 * 4 ^ depth by
      unfold scale
      omega]
    cases axis
    · exact CanonicalOddFreeLines.coordinate_isFreeRow depth selectedMem
    · exact CanonicalOddFreeLines.coordinate_isFreeColumn depth selectedMem

end CanonicalOddShadeComparison
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
