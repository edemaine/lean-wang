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
  induction depth generalizing states target with
  | zero =>
      have targetMem : target ∈ portsIn 16 16 :=
        mem_portsIn (by simp [scale] at targetEast ⊢; omega)
          (by simp [scale] at targetNorth ⊢; omega)
      have targetWest' : 4 ≤ target.x := by simpa [scale] using targetWest
      have targetEast' : target.x < 12 := by simpa [scale] using targetEast
      have targetSouth' : 4 ≤ target.y := by simpa [scale] using targetSouth
      have targetNorth' : target.y < 12 := by simpa [scale] using targetNorth
      have basePresent : portPresent CanonicalOddShadeBase.indexGrid target = true := by
        have targetBounds := bounds_of_mem_portsIn targetMem
        rcases target with ⟨x, y, side⟩
        cases side <;> simp only [portPresent] <;>
          rw [base_component_actual coarse coarseRoot x y
            targetBounds.1 targetBounds.2] <;>
          exact targetPresent
      rcases CanonicalOddShadeBase.exists_boundedPath targetMem
          targetWest' targetEast' targetSouth' targetNorth' basePresent with
        ⟨start, parity, startMem, basePath⟩
      have actualPath := BoundedPath.congr_of_component_eq
        (fun x y hx hy => base_component_actual coarse coarseRoot x y hx hy)
        basePath
      have actualStart := value_of_cyclePort (by simpa [scale] using shaded)
        startMem
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
  | succ depth ih =>
      let oldGrid := actualGrid depth coarse
      let newGrid := actualGrid (depth + 1) coarse
      have gridEq : iterateRefine 2 oldGrid = newGrid := by
        dsimp [oldGrid, newGrid, actualGrid]
        rw [PlaneRedBoards.iterateRefine_add]
        congr 1
        omega
      have validFine : ValidShadeGrid (iterateRefine 2 oldGrid) states := by
        rw [gridEq]
        exact valid
      let coarseStates := RedShadeGraphCoarsening.stateGrid validFine
      have coarseValid : ValidShadeGrid oldGrid coarseStates :=
        RedShadeGraphCoarsening.valid validFine
      have scaleSucc : scale (depth + 1) = 4 * scale depth := by
        exact scale_succ depth
      have coarseShaded : CycleShade coarseStates
          (scale depth) (3 * scale depth)
          (scale depth) (3 * scale depth) .light := by
        apply RedShadeGraphCoarsening.cycleShade validFine
          (rootCycle depth coarse)
        convert shaded using 1 <;> rw [scaleSucc] <;> omega
      let blockX := target.x / 8
      let blockY := target.y / 8
      let localTarget : Port :=
        ⟨target.x % 8, target.y % 8, target.side⟩
      have localTargetX : localTarget.x < 8 := Nat.mod_lt _ (by decide)
      have localTargetY : localTarget.y < 8 := Nat.mod_lt _ (by decide)
      have targetEq :
          translatePort localTarget (8 * blockX) (8 * blockY) = target := by
        rcases target with ⟨x, y, side⟩
        simp only [localTarget, blockX, blockY, translatePort]
        have hx := Nat.mod_add_div x 8
        have hy := Nat.mod_add_div y 8
        congr <;> omega
      have localPresent :
          portPresent (fineGrid (oldGrid blockX blockY)) localTarget = true := by
        rw [portPresent_two_block oldGrid blockX blockY localTarget
          localTargetX localTargetY, gridEq, targetEq]
        exact targetPresent
      rcases exists_boundedPath (oldGrid blockX blockY)
          (mem_portsIn localTargetX localTargetY) localPresent with
        ⟨source, sourceMem, parity, localPath⟩
      have actualPath := boundedPath_two_block oldGrid blockX blockY localPath
      rw [gridEq, targetEq] at actualPath
      have scalePos : 0 < scale depth := by simp [scale]
      have blockXLower : scale depth ≤ blockX := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        rw [scaleSucc] at targetWest
        omega
      have blockXUpper : blockX < 3 * scale depth := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2
        rw [scaleSucc] at targetEast
        omega
      have blockYLower : scale depth ≤ blockY := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        rw [scaleSucc] at targetSouth
        omega
      have blockYUpper : blockY < 3 * scale depth := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2
        rw [scaleSucc] at targetNorth
        omega
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
      have blockXDescendant : blockX < 2 * 4 ^ (depth + 1) := by
        simp only [scale] at blockXUpper
        rw [pow_succ]
        omega
      have blockYDescendant : blockY < 2 * 4 ^ (depth + 1) := by
        simp only [scale] at blockYUpper
        rw [pow_succ]
        omega
      let node := supertileNodeGrid (depth + 2) seedNode blockX blockY
      have parentEq : node.data.parent = oldGrid blockX blockY := by
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
          fineGrid (oldGrid blockX blockY) := by
        simpa [CanonicalEvenFreeLines.indexGrid] using
          localGrid_eq node (oldGrid blockX blockY) parentEq
      rw [localIndexEq] at canonicalValid
      have canonicalRelation :=
        boundedPath_soundOnRectangle canonicalValid localPath
      have canonicalTarget := value_succ_block (depth + 2)
        blockX blockY localTarget localTargetX localTargetY
      rw [targetEq] at canonicalTarget
      have finish
          (sourceValues :
            value states (translatePort source (8 * blockX) (8 * blockY)) =
              value (supertileShadeGrid 1 node) source) :
          value states target = value (shadeGrid (depth + 3)) target := by
        have actualRelation := actualPath.sound valid
        have actualRelation' : Related parity
            (value (supertileShadeGrid 1 node) source) (value states target) := by
          simpa [sourceValues] using actualRelation
        have targetRelation : Related parity
            (value (supertileShadeGrid 1 node) source)
            (value (shadeGrid (depth + 3)) target) := by
          rw [canonicalTarget]
          exact canonicalRelation
        exact Related.right_unique actualRelation' targetRelation
      rcases source_cases sourceMem with sourceEq | inherited
      · subst source
        have cellCycle : CycleOn newGrid
            (4 * blockX + 1) (4 * blockX + 3)
            (4 * blockY + 1) (4 * blockY + 3) := by
          have cycle := depthTwo_at oldGrid blockX blockY
          rw [gridEq] at cycle
          exact cycle
        have bridge := RedShadeCycleOddDescendants.rootDescendantBridge
          (depth + 1) coarse blockX blockY
          blockXDescendant blockYDescendant
        have bridge' : RedShadeCycleCrossingPaths.OddCycleBridge newGrid
            (scale (depth + 1)) (3 * scale (depth + 1))
            (scale (depth + 1)) (3 * scale (depth + 1))
            (4 * blockX + 1) (4 * blockX + 3)
            (4 * blockY + 1) (4 * blockY + 3) := by
          simpa only [newGrid, actualGrid, scale, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm] using bridge
        have actualSource :
            value states
                (translatePort cycleSource (8 * blockX) (8 * blockY)) =
              some .dark := by
          have result := value_eq_of_oddCycleBridge valid
            (rootCycle (depth + 1) coarse) shaded cellCycle bridge'
            (sourceOnCell blockX blockY)
          simpa [RedShades.Shade.opposite] using result
        have canonicalSource := CanonicalOddShadeGeometry.cycleSource_dark node
        exact finish (actualSource.trans canonicalSource.symm)
      · rcases inherited with ⟨old, oldMem, oldLocalPresent, sourceEq⟩
        subst source
        have oldBounds := bounds_of_mem_portsIn oldMem
        let oldGlobal := translatePort old (2 * blockX) (2 * blockY)
        have oldPresent : portPresent oldGrid oldGlobal = true := by
          rw [← portPresent_old_block oldGrid blockX blockY old
            oldBounds.1 oldBounds.2]
          exact oldLocalPresent
        have oldWest : 2 * scale depth ≤ oldGlobal.x := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldEast : oldGlobal.x < 6 * scale depth := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldSouth : 2 * scale depth ≤ oldGlobal.y := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldNorth : oldGlobal.y < 6 * scale depth := by
          dsimp [oldGlobal, translatePort]
          omega
        have oldAgreement := ih coarseStates coarseValid coarseShaded oldGlobal
          oldWest oldEast oldSouth oldNorth oldPresent
        have refinedEq :
            value states (sparsePort oldGlobal) =
              value states (refinedPort oldGlobal) :=
          (livePortPath oldGrid oldGlobal oldPresent).sound validFine
        have coarseValue :
            value coarseStates oldGlobal =
              value states (refinedPort oldGlobal) :=
          RedShadeGraphCoarsening.value_stateGrid validFine oldGlobal
        have actualToPrevious :
            value states (sparsePort oldGlobal) =
              value (shadeGrid (depth + 2)) oldGlobal :=
          refinedEq.trans (coarseValue.symm.trans oldAgreement)
        have canonicalSparse := value_succ_sparse (depth + 2) oldGlobal
        have sourceGlobalEq :
            sparsePort oldGlobal =
              translatePort (sparsePort old) (8 * blockX) (8 * blockY) :=
          sparsePort_two_block blockX blockY old oldBounds.1 oldBounds.2
        have canonicalBlock := value_succ_block (depth + 2)
          blockX blockY (sparsePort old)
          (sources_inBounds (oldGrid blockX blockY) (sparsePort old)
            sourceMem).1
          (sources_inBounds (oldGrid blockX blockY) (sparsePort old)
            sourceMem).2
        rw [← sourceGlobalEq] at canonicalBlock
        have sourceValues :
            value states
                (translatePort (sparsePort old) (8 * blockX) (8 * blockY)) =
              value (supertileShadeGrid 1 node) (sparsePort old) := by
          rw [← sourceGlobalEq]
          exact actualToPrevious.trans
            (canonicalSparse.symm.trans canonicalBlock)
        exact finish sourceValues

private theorem portPresent_canonical_eq (depth : Nat)
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0)
    (port : Port) (portEast : port.x < 8 * scale depth)
    (portNorth : port.y < 8 * scale depth) :
    portPresent (indexGrid (depth + 2)) port =
      portPresent (actualGrid depth coarse) port := by
  have xBound : port.x / 2 < 4 ^ (depth + 2) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    simp only [scale] at portEast
    rw [show 4 ^ (depth + 2) = 16 * 4 ^ depth by
      exact pow_four_add_two depth]
    omega
  have yBound : port.y / 2 < 4 ^ (depth + 2) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    simp only [scale] at portNorth
    rw [show 4 ^ (depth + 2) = 16 * 4 ^ depth by
      exact pow_four_add_two depth]
    omega
  have indexEq :
      indexGrid (depth + 2) (port.x / 2) (port.y / 2) =
        actualGrid depth coarse (port.x / 2) (port.y / 2) := by
    change supertileIndexGrid (depth + 2) seedNode
        (port.x / 2) (port.y / 2) =
      iterateRefine (2 * depth + 4) coarse
        (port.x / 2) (port.y / 2)
    rw [← show 2 * (depth + 2) = 2 * depth + 4 by omega]
    exact CanonicalShadeGeometry.supertileIndexGrid_eq_coarse
      (depth + 2) seedNode coarse
      (coarseRoot.trans seedNode_parent.symm) xBound yBound
  rcases port with ⟨x, y, side⟩
  simp only at indexEq
  cases side <;> simp only [portPresent, componentAt] <;> rw [indexEq]

theorem value_eq (depth : Nat) (coarse : Nat → Nat → Index)
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
    (targetNorth : target.y < 6 * scale depth) :
    value states target = value (shadeGrid (depth + 2)) target := by
  by_cases present : portPresent (actualGrid depth coarse) target = true
  · exact present_value_eq depth coarse states coarseRoot valid shaded target
      targetWest targetEast targetSouth targetNorth present
  · have canonicalBounds : PortInBounds target
        (2 * 4 ^ (depth + 2)) (2 * 4 ^ (depth + 2)) := by
      constructor <;> simp only [scale] at targetEast targetNorth ⊢ <;>
        rw [show 4 ^ (depth + 2) = 16 * 4 ^ depth by
          exact pow_four_add_two depth] <;>
        omega
    have canonicalValid := CanonicalOddShadeGeometry.validRectangle (depth + 2)
    have actualSome :=
      RedShadeGraphCoarsening.value_isSome_eq_portPresent valid target
    have canonicalSome :=
      RedShadeGraphColoring.value_isSome_eq_portPresent
        canonicalValid target canonicalBounds
    have presentEq := portPresent_canonical_eq depth coarse coarseRoot target
      (by omega) (by omega)
    rw [presentEq] at canonicalSome
    have absent : portPresent (actualGrid depth coarse) target = false :=
      Bool.eq_false_of_not_eq_true present
    rw [absent] at actualSome canonicalSome
    cases actualValue : value states target <;>
      cases canonicalValue : value (shadeGrid (depth + 2)) target <;>
      simp_all

theorem state_eq (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light)
    (x y : Nat)
    (xWest : 2 * scale depth ≤ x) (xEast : x < 6 * scale depth)
    (ySouth : 2 * scale depth ≤ y) (yNorth : y < 6 * scale depth) :
    states x y = shadeGrid (depth + 2) x y := by
  have west := value_eq depth coarse states coarseRoot valid shaded
    ⟨x, y, .west⟩ xWest xEast ySouth yNorth
  have east := value_eq depth coarse states coarseRoot valid shaded
    ⟨x, y, .east⟩ xWest xEast ySouth yNorth
  have south := value_eq depth coarse states coarseRoot valid shaded
    ⟨x, y, .south⟩ xWest xEast ySouth yNorth
  have north := value_eq depth coarse states coarseRoot valid shaded
    ⟨x, y, .north⟩ xWest xEast ySouth yNorth
  rcases actualEq : states x y with ⟨actualWest, actualEast,
    actualSouth, actualNorth⟩
  rcases canonicalEq : shadeGrid (depth + 2) x y with
    ⟨canonicalWest, canonicalEast, canonicalSouth, canonicalNorth⟩
  simp only [value, actualEq, canonicalEq] at west east south north
  subst canonicalWest
  subst canonicalEast
  subst canonicalSouth
  subst canonicalNorth
  rfl

private theorem componentAt_canonical_eq (depth : Nat)
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0)
    (x y : Nat) (xEast : x < 8 * scale depth)
    (yNorth : y < 8 * scale depth) :
    componentAt (indexGrid (depth + 2)) x y =
      componentAt (actualGrid depth coarse) x y := by
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
  have indexEq : indexGrid (depth + 2) (x / 2) (y / 2) =
      actualGrid depth coarse (x / 2) (y / 2) := by
    change supertileIndexGrid (depth + 2) seedNode (x / 2) (y / 2) =
      iterateRefine (2 * depth + 4) coarse (x / 2) (y / 2)
    rw [← show 2 * (depth + 2) = 2 * depth + 4 by omega]
    exact CanonicalShadeGeometry.supertileIndexGrid_eq_coarse
      (depth + 2) seedNode coarse
      (coarseRoot.trans seedNode_parent.symm) xBound yBound
  simp only [componentAt]
  rw [indexEq]

theorem coordinate_isFreeRow (depth : Nat)
    (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light)
    {row : Nat} (rowMem : row ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeRow (actualGrid depth coarse) states
      (scale depth) (3 * scale depth) row := by
  have canonicalFree := CanonicalOddFreeLines.coordinate_isFreeRow depth rowMem
  have rowBounds := mem_coordinates_bounds depth rowMem
  intro quarterX westBound eastBound
  have xWest : 2 * scale depth ≤ quarterX := by
    unfold quarterWest at westBound
    omega
  have xEast : quarterX < 6 * scale depth := by
    unfold quarterEast at eastBound
    omega
  have ySouth : 2 * scale depth ≤ row := by
    unfold quarterSouth at rowBounds
    simp only [scale] at rowBounds ⊢
    omega
  have yNorth : row < 6 * scale depth := by
    unfold quarterNorth at rowBounds
    simp only [scale] at rowBounds ⊢
    omega
  have stateAgreement := state_eq depth coarse states coarseRoot valid shaded
    quarterX row xWest xEast ySouth yNorth
  have componentAgreement := componentAt_canonical_eq depth coarse coarseRoot
    quarterX row (by omega) (by omega)
  rw [← componentAgreement, stateAgreement]
  have eastScale : 3 * scale depth = 6 * 4 ^ depth := by
    unfold scale
    omega
  rw [eastScale] at eastBound
  exact canonicalFree quarterX westBound eastBound

theorem coordinate_isFreeColumn (depth : Nat)
    (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light)
    {column : Nat} (columnMem : column ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeColumn (actualGrid depth coarse) states
      (scale depth) (3 * scale depth) column := by
  have canonicalFree := CanonicalOddFreeLines.coordinate_isFreeColumn
    depth columnMem
  have columnBounds := mem_coordinates_bounds depth columnMem
  intro quarterY southBound northBound
  have xWest : 2 * scale depth ≤ column := by
    unfold quarterSouth at columnBounds
    simp only [scale] at columnBounds ⊢
    omega
  have xEast : column < 6 * scale depth := by
    unfold quarterNorth at columnBounds
    simp only [scale] at columnBounds ⊢
    omega
  have ySouth : 2 * scale depth ≤ quarterY := by
    unfold quarterSouth at southBound
    omega
  have yNorth : quarterY < 6 * scale depth := by
    unfold quarterNorth at northBound
    omega
  have stateAgreement := state_eq depth coarse states coarseRoot valid shaded
    column quarterY xWest xEast ySouth yNorth
  have componentAgreement := componentAt_canonical_eq depth coarse coarseRoot
    column quarterY (by omega) (by omega)
  rw [← componentAgreement, stateAgreement]
  have northScale : 3 * scale depth = 6 * 4 ^ depth := by
    unfold scale
    omega
  rw [northScale] at northBound
  exact canonicalFree quarterY southBound northBound

end CanonicalOddShadeComparison
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
