/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeGeometry
import LeanWang.Robinson.Closed104.RedShadeCycleBridgeComposition

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
  RefinementTranslation Signals.FreeCellLocal ShadedSubstitution
  CanonicalShadeGeometry

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

/-- An even cycle bridge transports a uniform shade unchanged. -/
theorem value_eq_of_evenCycleBridge
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

/-- An odd cycle bridge transports a uniform shade to its opposite. -/
theorem value_eq_of_oddCycleBridge
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
    (bridge : RedShadeCycleCrossingPaths.OddCycleBridge grid
      firstWest firstEast firstSouth firstNorth
      secondWest secondEast secondSouth secondNorth)
    (targetOn : OnCycle
      secondWest secondEast secondSouth secondNorth target) :
    value states target = some shade.opposite := by
  rcases bridge with ⟨firstPort, secondPort, firstOn, secondOn, path⟩
  have firstValue := firstOn.value_eq firstCycle firstShaded valid
  have secondValue := end_eq_opposite_of_odd_path valid path firstValue
  have around := onCycle_connected secondCycle secondOn targetOn
  have aroundEq : value states secondPort = value states target :=
    around.sound valid
  exact aroundEq.symm.trans secondValue

/-- Phase-specific inputs needed after agreement has been proved on live ports. -/
structure PhaseComparison
    (actualGrid canonicalGrid : Nat → Nat → Index)
    (actualStates canonicalStates : Nat → Nat → RedShades.State)
    (scale extent : Nat) : Prop where
  actualValid : ValidShadeGrid actualGrid actualStates
  canonicalValid : ValidShadeRectangle canonicalGrid canonicalStates extent extent
  extent_large : 8 * scale ≤ extent
  portPresent_eq : ∀ port, port.x < 8 * scale → port.y < 8 * scale →
    portPresent canonicalGrid port = portPresent actualGrid port
  present_value_eq : ∀ port,
    2 * scale ≤ port.x → port.x < 6 * scale →
    2 * scale ≤ port.y → port.y < 6 * scale →
    portPresent actualGrid port = true →
    value actualStates port = value canonicalStates port

namespace PhaseComparison

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

/-- Transfer a canonical free row through one phase comparison. -/
theorem isFreeRow
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent row : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (componentEq : ∀ x y, x < 8 * scale → y < 8 * scale →
      componentAt canonicalGrid x y = componentAt actualGrid x y)
    (canonicalFree : ShadedPlaneSignalGrid.IsFreeRow
      canonicalGrid canonicalStates scale (3 * scale) row)
    (rowSouth : 2 * scale ≤ row) (rowNorth : row < 6 * scale) :
    ShadedPlaneSignalGrid.IsFreeRow
      actualGrid actualStates scale (3 * scale) row := by
  intro quarterX westBound eastBound
  have xWest : 2 * scale ≤ quarterX := by
    unfold quarterWest at westBound
    omega
  have xEast : quarterX < 6 * scale := by
    unfold quarterEast at eastBound
    omega
  have stateAgreement := comparison.state_eq
    xWest xEast rowSouth rowNorth
  have componentAgreement := componentEq quarterX row (by omega) (by omega)
  rw [← componentAgreement, stateAgreement]
  exact canonicalFree quarterX westBound eastBound

/-- Transfer a canonical free column through one phase comparison. -/
theorem isFreeColumn
    {actualGrid canonicalGrid : Nat → Nat → Index}
    {actualStates canonicalStates : Nat → Nat → RedShades.State}
    {scale extent column : Nat}
    (comparison : PhaseComparison actualGrid canonicalGrid
      actualStates canonicalStates scale extent)
    (componentEq : ∀ x y, x < 8 * scale → y < 8 * scale →
      componentAt canonicalGrid x y = componentAt actualGrid x y)
    (canonicalFree : ShadedPlaneSignalGrid.IsFreeColumn
      canonicalGrid canonicalStates scale (3 * scale) column)
    (columnWest : 2 * scale ≤ column)
    (columnEast : column < 6 * scale) :
    ShadedPlaneSignalGrid.IsFreeColumn
      actualGrid actualStates scale (3 * scale) column := by
  intro quarterY southBound northBound
  have ySouth : 2 * scale ≤ quarterY := by
    unfold quarterSouth at southBound
    omega
  have yNorth : quarterY < 6 * scale := by
    unfold quarterNorth at northBound
    omega
  have stateAgreement := comparison.state_eq
    columnWest columnEast ySouth yNorth
  have componentAgreement := componentEq column quarterY (by omega) (by omega)
  rw [← componentAgreement, stateAgreement]
  exact canonicalFree quarterY southBound northBound

end PhaseComparison

end CanonicalShadeComparisonCore
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
