/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeGeometry
import LeanWang.Robinson.Closed104.OrientedRedBoardTranslations
import LeanWang.Robinson.Closed104.RedShadeCycleBridgeComposition
import LeanWang.Robinson.Closed104.ShadedFreeGrid

/-! Phase-independent local lemmas for canonical shade comparison. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalShadeComparisonCore

open OrientedRedCycles RedCycles RedShades RedShadePaths RedShadeCycles
  RedShadeGraph RedShadeGraphBoards RedShadeGraphColoring
  RedShadeGraphLocalCoverage RedShadeGraphRefinement
  RedShadeGraphBoundedPath RedShadeGraphTranslation
  RedShadeCycleConnectivity RedShadeCycleBridgeComposition
  OrientedRedBoardTranslations RefinementTranslation
  Signals.FreeCellLocal ShadedSubstitution
  CanonicalShadeGeometry Figure16

theorem Related.right_unique
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

theorem mem_portsIn {width height : Nat} {port : Port}
    (hx : port.x < width) (hy : port.y < height) :
    port ∈ portsIn width height := by
  rcases port with ⟨x, y, side⟩
  simp only [portsIn, List.mem_flatMap, List.mem_range]
  refine ⟨y, hy, x, hx, ?_⟩
  cases side <;> simp

theorem bounds_of_mem_portsIn {width height : Nat} {port : Port}
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

theorem sparseCoordinate_two_block (block offset : Nat)
    (hoffset : offset < 2) :
    sparseCoordinate (2 * block + offset) =
      8 * block + sparseCoordinate offset := by
  have cases : offset = 0 ∨ offset = 1 := by omega
  rcases cases with rfl | rfl
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
  · simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega

theorem sparsePort_two_block (blockX blockY : Nat) (port : Port)
    (hx : port.x < 2) (hy : port.y < 2) :
    sparsePort (translatePort port (2 * blockX) (2 * blockY)) =
      translatePort (sparsePort port) (8 * blockX) (8 * blockY) := by
  rcases port with ⟨x, y, side⟩
  simp only [sparsePort, translatePort]
  rw [sparseCoordinate_two_block blockX x hx,
    sparseCoordinate_two_block blockY y hy]

theorem localCycleSource_onCycle :
    OnCycle 1 3 1 3 cycleSource := by
  change OnCycle 1 3 1 3 ⟨4, 3, .west⟩
  apply OnCycle.southWest <;> decide

theorem localGrid_eq (node : Node) (parent : Index)
    (parentEq : node.data.parent = parent) :
    CanonicalEvenFreeLines.indexGrid node 1 = fineGrid parent := by
  rw [CanonicalEvenFreeLines.indexGrid,
    supertileIndexGrid_eq_iterateRefine]
  subst parent
  rfl

theorem sourceOnCell (blockX blockY : Nat) :
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

/-- A bridge of either parity transports a uniform shade to every port on its
target cycle. -/
theorem related_of_cycleBridge
    {grid : Nat → Nat → Index}
    {states : Nat → Nat → RedShades.State}
    {firstWest firstEast firstSouth firstNorth : Nat}
    {secondWest secondEast secondSouth secondNorth : Nat}
    {shade : RedShades.Shade} {target : Port} {parity : Bool}
    (valid : ValidShadeGrid grid states)
    (firstCycle : CycleOn grid
      firstWest firstEast firstSouth firstNorth)
    (firstShaded : CycleShade states
      firstWest firstEast firstSouth firstNorth shade)
    (secondCycle : CycleOn grid
      secondWest secondEast secondSouth secondNorth)
    (bridge : CycleBridge grid
      firstWest firstEast firstSouth firstNorth
      secondWest secondEast secondSouth secondNorth parity)
    (targetOn : OnCycle
      secondWest secondEast secondSouth secondNorth target) :
    Related parity (some shade) (value states target) := by
  rcases bridge with ⟨firstPort, secondPort, firstOn, secondOn, path⟩
  have firstValue := firstOn.value_eq firstCycle firstShaded valid
  have targetValue : value states secondPort = value states target :=
    (onCycle_connected secondCycle secondOn targetOn).sound valid
  simpa only [firstValue, targetValue] using path.sound valid

/-- A canonical supertile and the corresponding refined coarse grid have the
same component geometry throughout the supertile's finite extent. -/
theorem componentAt_supertile_eq_coarse
    (level : Nat) (root : Node) (coarse : Nat → Nat → Index)
    (rootEq : coarse 0 0 = root.data.parent) (x y : Nat)
    (xBound : x < 2 * 4 ^ level) (yBound : y < 2 * 4 ^ level) :
    componentAt (supertileIndexGrid level root) x y =
      componentAt (iterateRefine (2 * level) coarse) x y := by
  have halfXBound : x / 2 < 4 ^ level := by omega
  have halfYBound : y / 2 < 4 ^ level := by omega
  simp only [componentAt]
  rw [supertileIndexGrid_eq_coarse level root coarse rootEq
    halfXBound halfYBound]

/-- A complete canonical shade phase: recursive shade comparison together
with the finite canonical geometry used to transfer free lines. -/
structure RefinementComparison where
  scale : Nat → Nat
  actualGrid : Nat → Nat → Nat → Index
  canonicalGrid : Nat → Nat → Nat → Index
  canonicalStates : Nat → Nat → Nat → RedShades.State
  localStates : Nat → Nat → Nat → Nat → Nat → RedShades.State
  extent : Nat → Nat
  scaleSucc : ∀ depth, scale (depth + 1) = 4 * scale depth
  gridSucc : ∀ depth,
    iterateRefine 2 (actualGrid depth) = actualGrid (depth + 1)
  rootCycle : ∀ depth, CycleOn (actualGrid depth)
      (scale depth) (3 * scale depth) (scale depth) (3 * scale depth)
  base : ∀ states,
      ValidShadeGrid (actualGrid 0) states →
      CycleShade states (scale 0) (3 * scale 0)
        (scale 0) (3 * scale 0) .light →
      ∀ target,
        2 * scale 0 ≤ target.x → target.x < 6 * scale 0 →
        2 * scale 0 ≤ target.y → target.y < 6 * scale 0 →
        portPresent (actualGrid 0) target = true →
        value states target = value (canonicalStates 0) target
  localValid : ∀ depth blockX blockY,
      scale depth ≤ blockX → blockX < 3 * scale depth →
      scale depth ≤ blockY → blockY < 3 * scale depth →
      ValidShadeRectangle (fineGrid (actualGrid depth blockX blockY))
        (localStates depth blockX blockY) 8 8
  canonicalBlock : ∀ depth blockX blockY port,
      port.x < 8 → port.y < 8 →
      value (canonicalStates (depth + 1))
          (translatePort port (8 * blockX) (8 * blockY)) =
        value (localStates depth blockX blockY) port
  canonicalSparse : ∀ depth port,
      value (canonicalStates (depth + 1)) (sparsePort port) =
        value (canonicalStates depth) port
  cycleSourceAgreement : ∀ depth states blockX blockY,
      ValidShadeGrid (actualGrid (depth + 1)) states →
      CycleShade states
        (scale (depth + 1)) (3 * scale (depth + 1))
        (scale (depth + 1)) (3 * scale (depth + 1)) .light →
      scale depth ≤ blockX → blockX < 3 * scale depth →
      scale depth ≤ blockY → blockY < 3 * scale depth →
      CycleOn (actualGrid (depth + 1))
        (4 * blockX + 1) (4 * blockX + 3)
        (4 * blockY + 1) (4 * blockY + 3) →
      value states (translatePort cycleSource (8 * blockX) (8 * blockY)) =
        value (localStates depth blockX blockY) cycleSource
  canonicalValid : ∀ depth,
    ValidShadeRectangle (canonicalGrid depth) (canonicalStates depth)
      (extent depth) (extent depth)
  extentLarge : ∀ depth, 8 * scale depth ≤ extent depth
  componentEq : ∀ depth x y,
    x < 8 * scale depth → y < 8 * scale depth →
      componentAt (canonicalGrid depth) x y =
        componentAt (actualGrid depth) x y

/-- Common two-level coarsening induction for the even and odd canonical
shade phases. -/
theorem present_value_eq_of_refinement (comparison : RefinementComparison) :
    ∀ depth states,
      ValidShadeGrid (comparison.actualGrid depth) states →
      CycleShade states
        (comparison.scale depth) (3 * comparison.scale depth)
        (comparison.scale depth) (3 * comparison.scale depth) .light →
      ∀ target,
        2 * comparison.scale depth ≤ target.x →
        target.x < 6 * comparison.scale depth →
        2 * comparison.scale depth ≤ target.y →
        target.y < 6 * comparison.scale depth →
        portPresent (comparison.actualGrid depth) target = true →
        value states target = value (comparison.canonicalStates depth) target := by
  rcases comparison with ⟨scale, actualGrid, canonicalGrid, canonicalStates,
    localStates, extent, scaleSucc, gridSucc, rootCycle, base, localValid,
    canonicalBlock, canonicalSparse, cycleSourceAgreement, canonicalValid,
    extentLarge, componentEq⟩
  dsimp only at *
  intro depth states valid shaded target targetWest targetEast
    targetSouth targetNorth targetPresent
  induction depth generalizing states target with
  | zero =>
      exact base states valid shaded target targetWest targetEast
        targetSouth targetNorth targetPresent
  | succ depth ih =>
      let oldGrid := actualGrid depth
      let newGrid := actualGrid (depth + 1)
      have gridEq : iterateRefine 2 oldGrid = newGrid := by
        exact gridSucc depth
      have validFine : ValidShadeGrid (iterateRefine 2 oldGrid) states := by
        rw [gridEq]
        exact valid
      let coarseStates := RedShadeGraphCoarsening.stateGrid validFine
      have coarseValid : ValidShadeGrid oldGrid coarseStates :=
        RedShadeGraphCoarsening.valid validFine
      have coarseShaded : CycleShade coarseStates
          (scale depth) (3 * scale depth)
          (scale depth) (3 * scale depth) .light := by
        apply RedShadeGraphCoarsening.cycleShade validFine (rootCycle depth)
        convert shaded using 1 <;> rw [scaleSucc depth] <;> omega
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
      have blockXLower : scale depth ≤ blockX := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        rw [scaleSucc depth] at targetWest
        omega
      have blockXUpper : blockX < 3 * scale depth := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2
        rw [scaleSucc depth] at targetEast
        omega
      have blockYLower : scale depth ≤ blockY := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        rw [scaleSucc depth] at targetSouth
        omega
      have blockYUpper : blockY < 3 * scale depth := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2
        rw [scaleSucc depth] at targetNorth
        omega
      have canonicalValid := localValid depth blockX blockY
        blockXLower blockXUpper blockYLower blockYUpper
      have canonicalRelation :=
        boundedPath_soundOnRectangle canonicalValid localPath
      have canonicalTarget := canonicalBlock depth blockX blockY localTarget
        localTargetX localTargetY
      rw [targetEq] at canonicalTarget
      have finish
          (sourceValues :
            value states (translatePort source (8 * blockX) (8 * blockY)) =
              value (localStates depth blockX blockY) source) :
          value states target = value (canonicalStates (depth + 1)) target := by
        have actualRelation := actualPath.sound valid
        have actualRelation' : Related parity
            (value (localStates depth blockX blockY) source)
            (value states target) := by
          simpa [sourceValues] using actualRelation
        have targetRelation : Related parity
            (value (localStates depth blockX blockY) source)
            (value (canonicalStates (depth + 1)) target) := by
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
        exact finish (cycleSourceAgreement depth states blockX blockY
          valid shaded blockXLower blockXUpper blockYLower blockYUpper
          cellCycle)
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
              value (canonicalStates depth) oldGlobal :=
          refinedEq.trans (coarseValue.symm.trans oldAgreement)
        have canonicalSparseValue := canonicalSparse depth oldGlobal
        have sourceGlobalEq :
            sparsePort oldGlobal =
              translatePort (sparsePort old) (8 * blockX) (8 * blockY) :=
          sparsePort_two_block blockX blockY old oldBounds.1 oldBounds.2
        have canonicalBlockValue := canonicalBlock depth blockX blockY
          (sparsePort old)
          (sources_inBounds (oldGrid blockX blockY) (sparsePort old)
            sourceMem).1
          (sources_inBounds (oldGrid blockX blockY) (sparsePort old)
            sourceMem).2
        rw [← sourceGlobalEq] at canonicalBlockValue
        have sourceValues :
            value states
                (translatePort (sparsePort old) (8 * blockX) (8 * blockY)) =
              value (localStates depth blockX blockY) (sparsePort old) := by
          rw [← sourceGlobalEq]
          exact actualToPrevious.trans
            (canonicalSparseValue.symm.trans canonicalBlockValue)
        exact finish sourceValues

/-- Phase-specific inputs needed after agreement has been proved on live ports. -/
structure PhaseComparison
    (actualGrid canonicalGrid : Nat → Nat → Index)
    (actualStates canonicalStates : Nat → Nat → RedShades.State)
    (scale extent : Nat) : Prop where
  actualValid : ValidShadeGrid actualGrid actualStates
  canonicalValid : ValidShadeRectangle canonicalGrid canonicalStates extent extent
  extent_large : 8 * scale ≤ extent
  component_eq : ∀ x y, x < 8 * scale → y < 8 * scale →
    componentAt canonicalGrid x y = componentAt actualGrid x y
  present_value_eq : ∀ port,
    2 * scale ≤ port.x → port.x < 6 * scale →
    2 * scale ≤ port.y → port.y < 6 * scale →
    portPresent actualGrid port = true →
    value actualStates port = value canonicalStates port

/-- Instantiate the complete finite phase comparison supplied by a canonical
refinement specification. -/
def RefinementComparison.phaseComparison
    (comparison : RefinementComparison) (depth : Nat)
    (states : Nat → Nat → RedShades.State)
    (valid : ValidShadeGrid (comparison.actualGrid depth) states)
    (shaded : CycleShade states
      (comparison.scale depth) (3 * comparison.scale depth)
      (comparison.scale depth) (3 * comparison.scale depth) .light) :
    PhaseComparison (comparison.actualGrid depth)
      (comparison.canonicalGrid depth) states
      (comparison.canonicalStates depth) (comparison.scale depth)
      (comparison.extent depth) where
  actualValid := valid
  canonicalValid := comparison.canonicalValid depth
  extent_large := comparison.extentLarge depth
  component_eq := comparison.componentEq depth
  present_value_eq := present_value_eq_of_refinement comparison depth states
    valid shaded

namespace PhaseComparison

/-- Common component geometry determines which ports are present. -/
theorem portPresent_eq
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (port : Port) (portEast : port.x < 8 * scale)
    (portNorth : port.y < 8 * scale) :
    portPresent canonicalGrid port = portPresent actualGrid port := by
  rcases port with ⟨x, y, side⟩
  cases side <;> simp only [portPresent] <;>
    rw [comparison.component_eq x y portEast portNorth]

/-- Agreement on live ports extends to absent ports through common geometry. -/
theorem value_eq
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (target : Port)
    (targetWest : 2 * scale ≤ target.x)
    (targetEast : target.x < 6 * scale)
    (targetSouth : 2 * scale ≤ target.y)
    (targetNorth : target.y < 6 * scale) :
    value actualStates target = value canonicalStates target := by
  by_cases present : portPresent actualGrid target = true
  · exact comparison.present_value_eq target targetWest targetEast
      targetSouth targetNorth present
  · have canonicalBounds : PortInBounds target extent extent := by
      have extentLarge := comparison.extent_large
      constructor <;> omega
    have actualSome :=
      RedShadeGraphCoarsening.value_isSome_eq_portPresent
        comparison.actualValid target
    have canonicalSome :=
      RedShadeGraphColoring.value_isSome_eq_portPresent
        comparison.canonicalValid target canonicalBounds
    rw [comparison.portPresent_eq target (by omega) (by omega)] at canonicalSome
    have absent : portPresent actualGrid target = false :=
      Bool.eq_false_of_not_eq_true present
    rw [absent] at actualSome canonicalSome
    cases actualValue : value actualStates target <;>
      cases canonicalValue : value canonicalStates target <;>
      simp_all

/-- Portwise phase agreement determines the complete quarter state. -/
theorem state_eq
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent x y : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (xWest : 2 * scale ≤ x) (xEast : x < 6 * scale)
    (ySouth : 2 * scale ≤ y) (yNorth : y < 6 * scale) :
    actualStates x y = canonicalStates x y := by
  have west := comparison.value_eq ⟨x, y, .west⟩
    xWest xEast ySouth yNorth
  have east := comparison.value_eq ⟨x, y, .east⟩
    xWest xEast ySouth yNorth
  have south := comparison.value_eq ⟨x, y, .south⟩
    xWest xEast ySouth yNorth
  have north := comparison.value_eq ⟨x, y, .north⟩
    xWest xEast ySouth yNorth
  rcases actualEq : actualStates x y with
    ⟨actualWest, actualEast, actualSouth, actualNorth⟩
  rcases canonicalEq : canonicalStates x y with
    ⟨canonicalWest, canonicalEast, canonicalSouth, canonicalNorth⟩
  simp only [value, actualEq, canonicalEq] at west east south north
  subst canonicalWest
  subst canonicalEast
  subst canonicalSouth
  subst canonicalNorth
  rfl

/-- The two coordinate directions in which a free line can run. -/
inductive FreeAxis where
  | row
  | column

namespace FreeAxis

/-- The grid point on a line at a given transverse coordinate. -/
def point : FreeAxis → Nat → Nat → Nat × Nat
  | .row, line, transverse => (transverse, line)
  | .column, line, transverse => (line, transverse)

/-- The absence of the light border transverse to a line. -/
def Clear : FreeAxis → Thick → Quadrant → RedShades.State → Prop
  | .row, component, quadrant, state =>
      ShadedSignals.selectedVerticalFor component quadrant state = none
  | .column, component, quadrant, state =>
      ShadedSignals.selectedHorizontalFor component quadrant state = none

/-- Axis-neutral form of a free row or column. -/
def IsFreeLine (axis : FreeAxis) (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (first last line : Nat) : Prop :=
  ∀ transverse, quarterWest first < transverse →
    transverse < quarterEast last →
    let location := axis.point line transverse
    axis.Clear
      (componentAt indexGrid location.1 location.2)
      (quadrantAt location.1 location.2)
      (shadeGrid location.1 location.2)

end FreeAxis

/-- Transfer a canonical free line through one phase comparison. -/
theorem isFreeLine
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent line : Nat} (axis : FreeAxis)
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (canonicalFree : axis.IsFreeLine
      canonicalGrid canonicalStates scale (3 * scale) line)
    (lineLower : 2 * scale ≤ line) (lineUpper : line < 6 * scale) :
    axis.IsFreeLine actualGrid actualStates scale (3 * scale) line := by
  intro transverse lower upper
  let location := axis.point line transverse
  have locationBounds :
      2 * scale ≤ location.1 ∧ location.1 < 6 * scale ∧
      2 * scale ≤ location.2 ∧ location.2 < 6 * scale := by
    cases axis <;> simp [location, FreeAxis.point] <;>
      unfold quarterWest at lower <;> unfold quarterEast at upper <;> omega
  rcases locationBounds with ⟨xLower, xUpper, yLower, yUpper⟩
  have stateAgreement := comparison.state_eq xLower xUpper yLower yUpper
  have componentAgreement := comparison.component_eq location.1 location.2
    (by omega) (by omega)
  change axis.Clear
    (componentAt actualGrid location.1 location.2)
    (quadrantAt location.1 location.2)
    (actualStates location.1 location.2)
  rw [← componentAgreement, stateAgreement]
  exact canonicalFree transverse lower upper

/-- Transfer every member of a canonical family of free lines. -/
theorem isFreeLine_of_mem
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (axis : FreeAxis) (coordinates : List Nat)
    (bounds : ∀ {line}, line ∈ coordinates →
      quarterSouth scale < line ∧ line < quarterNorth (3 * scale))
    (canonicalFree : ∀ {line}, line ∈ coordinates →
      axis.IsFreeLine canonicalGrid canonicalStates scale (3 * scale) line)
    {line : Nat} (lineMem : line ∈ coordinates) :
    axis.IsFreeLine actualGrid actualStates scale (3 * scale) line := by
  have lineBounds := bounds lineMem
  apply comparison.isFreeLine axis (canonicalFree lineMem)
  · unfold quarterSouth at lineBounds
    omega
  · unfold quarterNorth at lineBounds
    omega

/-- A family of coordinates that are free in both directions. -/
structure FreeCoordinateFamily
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (scale : Nat) (coordinates : List Nat) : Prop where
  freeRow : ∀ {line}, line ∈ coordinates →
    FreeAxis.row.IsFreeLine indexGrid shadeGrid scale (3 * scale) line
  freeColumn : ∀ {line}, line ∈ coordinates →
    FreeAxis.column.IsFreeLine indexGrid shadeGrid scale (3 * scale) line

/-- An ordered indexing of a finite coordinate family inside one red board. -/
structure OrderedCoordinates (scale size : Nat) (coordinates : List Nat) where
  coord : Fin size → Nat
  mem_coord : ∀ i, coord i ∈ coordinates
  strictMono : StrictMono coord
  bounds : ∀ i,
    quarterSouth scale < coord i ∧ coord i < quarterNorth (3 * scale)

/-- Interpret one ordered coordinate family simultaneously as free rows and
columns. -/
def FreeCoordinateFamily.toFreeGrid
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {scale size : Nat} {coordinateList : List Nat}
    (family : FreeCoordinateFamily indexGrid shadeGrid scale coordinateList)
    (coordinates : OrderedCoordinates scale size coordinateList) :
    ShadedFreeGrid.FreeGrid indexGrid shadeGrid
      scale (3 * scale) scale (3 * scale) size where
  columnAt := coordinates.coord
  rowAt := coordinates.coord
  column_strictMono := fun {_ _} h => coordinates.strictMono h
  row_strictMono := fun {_ _} h => coordinates.strictMono h
  column_west := fun i => (coordinates.bounds i).1
  column_east := fun i => (coordinates.bounds i).2
  row_south := fun i => (coordinates.bounds i).1
  row_north := fun i => (coordinates.bounds i).2
  freeColumn := fun i => family.freeColumn (coordinates.mem_coord i)
  freeRow := fun i => family.freeRow (coordinates.mem_coord i)

/-- Transfer a canonical family of free rows and columns through one phase
comparison. -/
theorem freeCoordinateFamily
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (coordinates : List Nat)
    (bounds : ∀ {line}, line ∈ coordinates →
      quarterSouth scale < line ∧ line < quarterNorth (3 * scale))
    (canonicalFree : ∀ axis : FreeAxis, ∀ {line}, line ∈ coordinates →
      axis.IsFreeLine canonicalGrid canonicalStates scale (3 * scale) line) :
    FreeCoordinateFamily actualGrid actualStates scale coordinates where
  freeRow lineMem := comparison.isFreeLine_of_mem FreeAxis.row coordinates bounds
    (canonicalFree FreeAxis.row) lineMem
  freeColumn lineMem := comparison.isFreeLine_of_mem FreeAxis.column coordinates bounds
    (canonicalFree FreeAxis.column) lineMem

end PhaseComparison

end CanonicalShadeComparisonCore
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
