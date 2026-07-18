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
  RedShadeGraphLocalCoverage RedShadeGraphRefinement RedShadeGraphTranslation
  RedShadeCycleConnectivity RedShadeCycleBridgeComposition
  RefinementTranslation ShadedSubstitution CanonicalShadeGeometry

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

end CanonicalShadeComparisonCore
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
