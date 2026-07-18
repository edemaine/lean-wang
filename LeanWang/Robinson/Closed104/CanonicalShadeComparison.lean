/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeGeometry
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

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphColoring RedShadeGraphLocalCoverage RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphTranslation
  RedShadeCycleConnectivity RedShadeCycleBridgeComposition
  RedShadeCycleEvenDescendants OrientedRedBoardTranslations
  ShadedSubstitution CanonicalEvenFreeLines CanonicalShadeGeometry

set_option maxRecDepth 20000

def scale (depth : Nat) : Nat := 4 ^ depth

def actualGrid (depth : Nat) (coarse : Nat → Nat → Index) :
    Nat → Nat → Index :=
  iterateRefine (2 * depth + 2) coarse

private theorem Related.right_unique
    {parity : Bool} {first second third : Option RedShades.Shade}
    (secondRelation : Related parity first second)
    (thirdRelation : Related parity first third) :
    second = third := by
  cases parity
  · exact secondRelation.symm.trans thirdRelation
  · rcases secondRelation with ⟨secondShade, firstEq, secondEq⟩
    rcases thirdRelation with ⟨thirdShade, firstEq', thirdEq⟩
    have shadeEq : secondShade = thirdShade :=
      Option.some.inj (firstEq.symm.trans firstEq')
    subst thirdShade
    exact secondEq.trans thirdEq.symm

private theorem value_eq_of_evenCycleBridge
    {grid : Nat → Nat → Index}
    {states : Nat → Nat → RedShades.State}
    {firstWest firstEast firstSouth firstNorth : Nat}
    {secondWest secondEast secondSouth secondNorth : Nat}
    {shade : RedShades.Shade} {target : Port}
    (valid : ValidShadeGrid grid states)
    (firstCycle : CycleOn grid
      firstWest firstEast firstSouth firstNorth)
    (firstShaded : CycleShade states
      firstWest firstEast firstSouth firstNorth shade)
    (secondCycle : CycleOn grid
      secondWest secondEast secondSouth secondNorth)
    (bridge : EvenCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      secondWest secondEast secondSouth secondNorth)
    (targetOn : OnCycle
      secondWest secondEast secondSouth secondNorth target) :
    value states target = some shade := by
  rcases bridge with ⟨firstPort, secondPort, firstOn, secondOn, path⟩
  have firstValue := firstOn.value_eq firstCycle firstShaded valid
  have bridgeEq : value states firstPort = value states secondPort :=
    path.sound valid
  have secondValue : value states secondPort = some shade :=
    bridgeEq.symm.trans firstValue
  have around := onCycle_connected secondCycle secondOn targetOn
  have aroundEq : value states secondPort = value states target :=
    around.sound valid
  exact aroundEq.symm.trans secondValue

private theorem mem_portsIn {width height : Nat} {port : Port}
    (hx : port.x < width) (hy : port.y < height) :
    port ∈ portsIn width height := by
  rcases port with ⟨x, y, side⟩
  simp only [portsIn, List.mem_flatMap, List.mem_range]
  refine ⟨y, hy, x, hx, ?_⟩
  cases side <;> simp

private theorem bounds_of_mem_portsIn {width height : Nat} {port : Port}
    (portMem : port ∈ portsIn width height) :
    port.x < width ∧ port.y < height := by
  unfold portsIn at portMem
  rw [List.mem_flatMap] at portMem
  rcases portMem with ⟨y, hy, portMem⟩
  rw [List.mem_flatMap] at portMem
  rcases portMem with ⟨x, hx, portMem⟩
  simp only [List.mem_range] at hy hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at portMem
  rcases portMem with rfl | rfl | rfl | rfl <;> exact ⟨hx, hy⟩

private theorem sparseCoordinate_two_block (block offset : Nat)
    (hoffset : offset < 2) :
    sparseCoordinate (2 * block + offset) =
      8 * block + sparseCoordinate offset := by
  have cases : offset = 0 ∨ offset = 1 := by omega
  rcases cases with rfl | rfl
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega

private theorem sparsePort_two_block (blockX blockY : Nat) (port : Port)
    (hx : port.x < 2) (hy : port.y < 2) :
    sparsePort (translatePort port (2 * blockX) (2 * blockY)) =
      translatePort (sparsePort port) (8 * blockX) (8 * blockY) := by
  rcases port with ⟨x, y, side⟩
  simp only [sparsePort, translatePort]
  rw [sparseCoordinate_two_block blockX x hx,
    sparseCoordinate_two_block blockY y hy]

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

private theorem localCycleSource_onCycle :
    OnCycle 1 3 1 3 cycleSource := by
  change OnCycle 1 3 1 3 ⟨4, 3, .west⟩
  apply OnCycle.southWest <;> decide

private theorem value_succ_block (level : Nat) (root : Node)
    (blockX blockY : Nat) (port : Port)
    (hx : port.x < 8) (hy : port.y < 8) :
    value (shadeGrid root (level + 1))
        (translatePort port (8 * blockX) (8 * blockY)) =
      value (shadeGrid (supertileNodeGrid level root blockX blockY) 1)
        port := by
  rcases port with ⟨x, y, side⟩
  have stateEq := shadeGrid_succ_block level root blockX blockY x y hx hy
  cases side <;> exact congrArg _ stateEq

private theorem value_succ_sparse (level : Nat) (root : Node) (port : Port) :
    value (shadeGrid root (level + 1)) (sparsePort port) =
      value (shadeGrid root level) port := by
  rcases port with ⟨x, y, side⟩
  have stateEq := shadeGrid_succ_sparse level root x y
  cases side <;> exact congrArg _ stateEq

private theorem localGrid_eq (node : Node) (parent : Index)
    (parentEq : node.data.parent = parent) :
    indexGrid node 1 = fineGrid parent := by
  rw [indexGrid, supertileIndexGrid_eq_iterateRefine]
  simp [fineGrid, coarseGrid, parentEq]

private theorem sourceOnCell (blockX blockY : Nat) :
    OnCycle
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3)
      (translatePort cycleSource (8 * blockX) (8 * blockY)) := by
  have sourceEq :
      translatePort cycleSource (8 * blockX) (8 * blockY) =
        ⟨8 * blockX + 4, 8 * blockY + 3, .west⟩ := by
    simp [translatePort, cycleSource, quarterWest, quarterSouth]
  have southEq : quarterSouth (4 * blockY + 1) = 8 * blockY + 3 := by
    simp [quarterSouth]
    omega
  rw [sourceEq]
  simpa only [southEq] using
    (OnCycle.southWest
      (west := 4 * blockX + 1) (east := 4 * blockX + 3)
      (south := 4 * blockY + 1) (north := 4 * blockY + 3)
      (8 * blockX + 4)
      (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega))

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
  induction depth generalizing states target with
  | zero =>
      have targetMem : target ∈ portsIn 8 8 :=
        mem_portsIn (by simp [scale] at targetEast ⊢; omega)
          (by simp [scale] at targetNorth ⊢; omega)
      have targetWest' : 2 ≤ target.x := by simpa [scale] using targetWest
      have targetEast' : target.x < 6 := by simpa [scale] using targetEast
      have targetSouth' : 2 ≤ target.y := by simpa [scale] using targetSouth
      have targetNorth' : target.y < 6 := by simpa [scale] using targetNorth
      have localPresent : portPresent (fineGrid 0) target = true := by
        have comparison := portPresent_two_block coarse 0 0 target
          (by omega) (by omega)
        rw [coarseRoot] at comparison
        simpa [actualGrid, translatePort] using comparison.trans targetPresent
      rcases base_exists_boundedPath targetMem targetWest' targetEast'
          targetSouth' targetNorth' localPresent with
        ⟨parity, localPath⟩
      have actualPath := boundedPath_two_block coarse 0 0 localPath
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
        simp [scale, pow_succ, Nat.mul_comm]
      have coarseShaded : CycleShade coarseStates
          (scale depth) (3 * scale depth)
          (scale depth) (3 * scale depth) .light := by
        apply RedShadeGraphCoarsening.cycleShade validFine
          (rootCycle depth coarse)
        simpa [scaleSucc, Nat.mul_assoc] using shaded
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
      have scalePos : 0 < scale depth := pow_pos (by decide) _
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
      have blockXBound : blockX < 4 ^ (depth + 1) := by
        rw [show 4 ^ (depth + 1) = 4 * scale depth by
          simp [scale, pow_succ, Nat.mul_comm]]
        omega
      have blockYBound : blockY < 4 ^ (depth + 1) := by
        rw [show 4 ^ (depth + 1) = 4 * scale depth by
          simp [scale, pow_succ, Nat.mul_comm]]
        omega
      let node := supertileNodeGrid (depth + 1) root blockX blockY
      have rootEq : coarse 0 0 = root.data.parent :=
        coarseRoot.trans rootParent.symm
      have parentEq : node.data.parent = oldGrid blockX blockY := by
        change supertileIndexGrid (depth + 1) root blockX blockY = _
        simpa [oldGrid, actualGrid] using
          (supertileIndexGrid_eq_coarse (depth + 1) root coarse rootEq
            blockXBound blockYBound)
      have canonicalValid := validRectangle 1 node
      have localIndexEq : indexGrid node 1 = fineGrid (oldGrid blockX blockY) :=
        localGrid_eq node (oldGrid blockX blockY) parentEq
      rw [localIndexEq] at canonicalValid
      have canonicalRelation :=
        boundedPath_soundOnRectangle canonicalValid localPath
      have canonicalTarget := value_succ_block (depth + 1) root
        blockX blockY localTarget localTargetX localTargetY
      rw [targetEq] at canonicalTarget
      have finish
          (sourceValues :
            value states (translatePort source (8 * blockX) (8 * blockY)) =
              value (shadeGrid node 1) source) :
          value states target = value (shadeGrid root (depth + 2)) target := by
        have actualRelation := actualPath.sound valid
        have actualRelation' : Related parity
            (value (shadeGrid node 1) source) (value states target) := by
          simpa [sourceValues] using actualRelation
        have targetRelation : Related parity
            (value (shadeGrid node 1) source)
            (value (shadeGrid root (depth + 2)) target) := by
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
        have bridge := rootDescendantBridge (depth + 1) coarse
          blockX blockY blockXBound blockYBound
        have actualSource :
            value states
                (translatePort cycleSource (8 * blockX) (8 * blockY)) =
              some .light := by
          exact value_eq_of_evenCycleBridge valid (rootCycle (depth + 1) coarse)
            shaded cellCycle bridge (sourceOnCell blockX blockY)
        have canonicalSource := cycleSource_light node
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
        have oldAgreement := ih coarseStates oldGlobal coarseValid coarseShaded
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
              value (shadeGrid root (depth + 1)) oldGlobal :=
          refinedEq.trans (coarseValue.symm.trans oldAgreement)
        have canonicalSparse := value_succ_sparse (depth + 1) root oldGlobal
        have sourceGlobalEq :
            sparsePort oldGlobal =
              translatePort (sparsePort old) (8 * blockX) (8 * blockY) :=
          sparsePort_two_block blockX blockY old oldBounds.1 oldBounds.2
        have canonicalBlock := value_succ_block (depth + 1) root
          blockX blockY (sparsePort old)
          (sources_inBounds (oldGrid blockX blockY) (sparsePort old) (by
            simp [sources, inheritedSources, oldMem, oldLocalPresent])).1
          (sources_inBounds (oldGrid blockX blockY) (sparsePort old) (by
            simp [sources, inheritedSources, oldMem, oldLocalPresent])).2
        rw [← sourceGlobalEq] at canonicalBlock
        have sourceValues :
            value states
                (translatePort (sparsePort old) (8 * blockX) (8 * blockY)) =
              value (shadeGrid node 1) (sparsePort old) := by
          rw [← sourceGlobalEq]
          exact actualToPrevious.trans
            (canonicalSparse.symm.trans canonicalBlock)
        exact finish sourceValues

end CanonicalShadeComparison
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
