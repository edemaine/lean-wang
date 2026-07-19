/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeGeometry
import LeanWang.Robinson.Closed104.CanonicalShadeComparisonCore
import LeanWang.Robinson.Closed104.RedShadeCycleEvenDescendants

/-!
# Comparing arbitrary and canonical shade assignments

Inside an even-depth root supertile, a valid shade assignment whose root
cycle is light agrees with the canonical assignment on every live red port.
The proof recursively coarsens the arbitrary assignment.  At each step, one
finite local path certificate is interpreted both in the arbitrary assignment
and in the canonical level-one supertile.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalShadeComparison

open OrientedRedCycles RedCycles RedShades RedShadePaths RedShadeCycles
  RedShadeGraph RedShadeGraphBoards
  RedShadeGraphColoring RedShadeGraphLocalCoverage RedShadeGraphRefinement
  RedShadeGraphBoundedPath RedShadeGraphTranslation
  RedShadeCycleConnectivity RedShadeCycleBridgeComposition
  RedShadeCycleEvenDescendants OrientedRedBoardTranslations
  ShadedSubstitution CanonicalFreeLineCoordinates CanonicalEvenFreeLines
  CanonicalShadeGeometry CanonicalShadeComparisonCore
  ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 20000

def scale (depth : Nat) : Nat := 4 ^ depth

def actualGrid (depth : Nat) (coarse : Nat → Nat → Index) :
    Nat → Nat → Index :=
  iterateRefine (2 * depth + 2) coarse

private theorem rootCycle (depth : Nat) (coarse : Nat → Nat → Index) :
    CycleOn (actualGrid depth coarse)
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) := by
  have cycle := at_scale coarse (2 * depth) 0 0
  have hpow : 2 ^ (2 * depth) = scale depth := by
    rw [pow_mul]
    norm_num [scale]
  rw [hpow] at cycle
  simpa [actualGrid, Nat.mul_comm] using cycle

private theorem value_succ_block (level : Nat) (root : Node)
    (blockX blockY : Nat) (port : Port)
    (hx : port.x < 8) (hy : port.y < 8) :
    value (shadeGrid root (level + 1))
        (translatePort port (8 * blockX) (8 * blockY)) =
      value (shadeGrid (supertileNodeGrid level root blockX blockY) 1)
        port := by
  rcases port with ⟨x, y, side⟩
  have stateEq := shadeGrid_succ_block level root blockX blockY x y hx hy
  cases side <;> simpa [value, translatePort] using congrArg _ stateEq

private theorem value_succ_sparse (level : Nat) (root : Node) (port : Port) :
    value (shadeGrid root (level + 1)) (sparsePort port) =
      value (shadeGrid root level) port := by
  rcases port with ⟨x, y, side⟩
  have stateEq := shadeGrid_succ_sparse level root x y
  cases side <;> simpa [value, sparsePort] using congrArg _ stateEq

private noncomputable def localStates (root : Node) (depth blockX blockY : Nat) :
    Nat → Nat → RedShades.State :=
  shadeGrid (supertileNodeGrid (depth + 1) root blockX blockY) 1

private theorem baseAgreement (coarse : Nat → Nat → Index)
    (root : Node) (coarseRoot : coarse 0 0 = 0)
    (rootParent : root.data.parent = 0)
    (states : Nat → Nat → RedShades.State)
    (valid : ValidShadeGrid (actualGrid 0 coarse) states)
    (shaded : CycleShade states 1 3 1 3 .light)
    (target : Port)
    (targetWest : 2 ≤ target.x) (targetEast : target.x < 6)
    (targetSouth : 2 ≤ target.y) (targetNorth : target.y < 6)
    (targetPresent : portPresent (actualGrid 0 coarse) target = true) :
    value states target = value (shadeGrid root 1) target := by
  have targetMem : target ∈ portsIn 8 8 :=
    mem_portsIn (by omega) (by omega)
  have localPresent : portPresent (fineGrid 0) target = true := by
    have comparison := portPresent_two_block coarse 0 0 target
      (by omega) (by omega)
    rw [coarseRoot] at comparison
    have targetPresent' :
        portPresent (iterateRefine 2 coarse)
          (translatePort target (8 * 0) (8 * 0)) = true := by
      simpa [actualGrid, translatePort] using targetPresent
    exact comparison.trans targetPresent'
  rcases base_exists_boundedPath targetMem targetWest targetEast
      targetSouth targetNorth localPresent with
    ⟨parity, localPath⟩
  have localPath' : BoundedPath (fineGrid (coarse 0 0)) 8 8
      cycleSource target parity := by
    simpa [coarseRoot] using localPath
  have actualPath := boundedPath_two_block coarse 0 0 localPath'
  have actualRelation : Related parity (some .light) (value states target) := by
    have sourceValue := localCycleSource_onCycle.value_eq
      (rootCycle 0 coarse) shaded valid
    have relation := actualPath.sound valid
    simpa [actualGrid, translatePort, sourceValue] using relation
  have canonicalValid := validRectangle 1 root
  have gridEq : indexGrid root 1 = fineGrid 0 :=
    localGrid_eq root 0 rootParent
  rw [gridEq] at canonicalValid
  have canonicalRelation :
      Related parity (some .light) (value (shadeGrid root 1) target) := by
    have relation := boundedPath_soundOnRectangle canonicalValid localPath
    simpa [cycleSource_light root] using relation
  exact Related.right_unique actualRelation canonicalRelation

private theorem localValid (depth : Nat) (coarse : Nat → Nat → Index)
    (root : Node) (rootEq : coarse 0 0 = root.data.parent)
    (blockX blockY : Nat)
    (_blockXLower : scale depth ≤ blockX)
    (blockXUpper : blockX < 3 * scale depth)
    (_blockYLower : scale depth ≤ blockY)
    (blockYUpper : blockY < 3 * scale depth) :
    ValidShadeRectangle (fineGrid (actualGrid depth coarse blockX blockY))
      (localStates root depth blockX blockY) 8 8 := by
  have blockXBound : blockX < 4 ^ (depth + 1) := by
    rw [show 4 ^ (depth + 1) = 4 * scale depth by
      simp [scale, pow_succ, Nat.mul_comm]]
    omega
  have blockYBound : blockY < 4 ^ (depth + 1) := by
    rw [show 4 ^ (depth + 1) = 4 * scale depth by
      simp [scale, pow_succ, Nat.mul_comm]]
    omega
  let node := supertileNodeGrid (depth + 1) root blockX blockY
  have parentEq : node.data.parent = actualGrid depth coarse blockX blockY := by
    change supertileIndexGrid (depth + 1) root blockX blockY = _
    change supertileIndexGrid (depth + 1) root blockX blockY =
      iterateRefine (2 * depth + 2) coarse blockX blockY
    rw [← show 2 * (depth + 1) = 2 * depth + 2 by omega]
    exact supertileIndexGrid_eq_coarse (depth + 1) root coarse rootEq
      blockXBound blockYBound
  have canonicalValid := validRectangle 1 node
  have localIndexEq : indexGrid node 1 =
      fineGrid (actualGrid depth coarse blockX blockY) :=
    localGrid_eq node (actualGrid depth coarse blockX blockY) parentEq
  rw [localIndexEq] at canonicalValid
  exact canonicalValid

private theorem cycleSourceAgreement (depth : Nat)
    (coarse : Nat → Nat → Index) (root : Node)
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
      value (localStates root depth blockX blockY) cycleSource := by
  have blockXBound : blockX < 4 ^ (depth + 1) := by
    simp only [scale] at blockXUpper
    rw [pow_succ]
    omega
  have blockYBound : blockY < 4 ^ (depth + 1) := by
    simp only [scale] at blockYUpper
    rw [pow_succ]
    omega
  have bridge := rootDescendantBridge (depth + 1) coarse
    blockX blockY blockXBound blockYBound
  have actualSource :
      value states (translatePort cycleSource (8 * blockX) (8 * blockY)) =
        some .light :=
    value_eq_of_evenCycleBridge valid (rootCycle (depth + 1) coarse)
      shaded cellCycle bridge (sourceOnCell blockX blockY)
  have canonicalSource := cycleSource_light
    (supertileNodeGrid (depth + 1) root blockX blockY)
  exact actualSource.trans canonicalSource.symm

/-- Every live port in the central square has the same shade in an arbitrary
valid light-root assignment and in the selected canonical assignment. -/
theorem present_value_eq (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State) (root : Node)
    (coarseRoot : coarse 0 0 = 0) (rootParent : root.data.parent = 0)
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
    value states target = value (shadeGrid root (depth + 1)) target := by
  apply present_value_eq_of_refinement
    scale (fun phaseDepth => actualGrid phaseDepth coarse)
    (fun phaseDepth => shadeGrid root (phaseDepth + 1))
    (localStates root)
  · intro phaseDepth
    simp [scale, pow_succ, Nat.mul_comm]
  · intro phaseDepth
    dsimp [actualGrid]
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  · exact fun phaseDepth => rootCycle phaseDepth coarse
  · intro baseStates baseValid baseShaded baseTarget baseWest baseEast
      baseSouth baseNorth basePresent
    exact baseAgreement coarse root coarseRoot rootParent baseStates
      baseValid baseShaded baseTarget baseWest baseEast baseSouth baseNorth
      basePresent
  · intro phaseDepth blockX blockY blockXLower blockXUpper
      blockYLower blockYUpper
    exact localValid phaseDepth coarse root
      (coarseRoot.trans rootParent.symm) blockX blockY
      blockXLower blockXUpper blockYLower blockYUpper
  · intro phaseDepth blockX blockY port portX portY
    exact value_succ_block (phaseDepth + 1) root blockX blockY
      port portX portY
  · intro phaseDepth port
    exact value_succ_sparse (phaseDepth + 1) root port
  · intro phaseDepth phaseStates blockX blockY phaseValid phaseShaded
      blockXLower blockXUpper blockYLower blockYUpper cellCycle
    exact cycleSourceAgreement phaseDepth coarse root phaseStates
      blockX blockY phaseValid phaseShaded blockXLower blockXUpper
      blockYLower blockYUpper cellCycle
  · exact valid
  · exact shaded
  · exact targetWest
  · exact targetEast
  · exact targetSouth
  · exact targetNorth
  · exact targetPresent

private theorem index_canonical_eq (depth : Nat)
    (coarse : Nat → Nat → Index) (root : Node)
    (rootEq : coarse 0 0 = root.data.parent) (x y : Nat)
    (xEast : x < 8 * scale depth) (yNorth : y < 8 * scale depth) :
    indexGrid root (depth + 1) (x / 2) (y / 2) =
      actualGrid depth coarse (x / 2) (y / 2) := by
  have xBound : x / 2 < 4 ^ (depth + 1) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    rw [pow_succ]
    simp only [scale] at xEast
    omega
  have yBound : y / 2 < 4 ^ (depth + 1) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    rw [pow_succ]
    simp only [scale] at yNorth
    omega
  change supertileIndexGrid (depth + 1) root (x / 2) (y / 2) =
    iterateRefine (2 * depth + 2) coarse (x / 2) (y / 2)
  rw [← show 2 * (depth + 1) = 2 * depth + 2 by omega]
  exact supertileIndexGrid_eq_coarse (depth + 1) root coarse rootEq
    xBound yBound

/-- The even phase packages live-port agreement and common geometry. -/
theorem comparison (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State) (root : Node)
    (coarseRoot : coarse 0 0 = 0) (rootParent : root.data.parent = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light) :
    PhaseComparison (actualGrid depth coarse) (indexGrid root (depth + 1))
      states (shadeGrid root (depth + 1)) (scale depth)
      (2 * 4 ^ (depth + 1)) := by
  refine {
    actualValid := valid
    canonicalValid := validRectangle (depth + 1) root
    extent_large := ?_
    component_eq := ?_
    present_value_eq := ?_
  }
  · rw [pow_succ]
    simp only [scale]
    omega
  · intro x y xEast yNorth
    simp only [componentAt]
    rw [index_canonical_eq depth coarse root
      (coarseRoot.trans rootParent.symm) x y xEast yNorth]
  · intro port portWest portEast portSouth portNorth portPresent
    exact present_value_eq depth coarse states root coarseRoot rootParent
      valid shaded port portWest portEast portSouth portNorth portPresent

/-- Every coordinate in the canonical family is a free row and column in the
arbitrary light-root shade assignment. -/
theorem freeCoordinates (depth : Nat)
    (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State) (root : Node)
    (coarseRoot : coarse 0 0 = 0) (rootParent : root.data.parent = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light) :
    PhaseComparison.FreeCoordinateFamily
      (actualGrid depth coarse) states (scale depth) (coordinates depth) := by
  apply (comparison depth coarse states root coarseRoot rootParent valid shaded)
    |>.freeCoordinateFamily (coordinates depth)
  · intro selected selectedMem
    simpa only [scale] using mem_coordinates_bounds depth selectedMem
  · intro axis selected selectedMem
    cases axis
    · exact CanonicalEvenFreeLines.coordinate_isFreeRow root depth selectedMem
    · exact CanonicalEvenFreeLines.coordinate_isFreeColumn root depth selectedMem

end CanonicalShadeComparison
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
