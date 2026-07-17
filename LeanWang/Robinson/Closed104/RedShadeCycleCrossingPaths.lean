/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphBoards
import LeanWang.Robinson.Closed104.TranslatedRedShadeCrossings

/-!
# Odd graph paths between crossing Robinson cycles

The shade-comparison lemmas for crossing boards use the local crossing rule.
This module retains the stronger graph witness: an odd path whose endpoints
lie on the two cycle sides.  These bridges can be concatenated through a
nested board hierarchy.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycleCrossingPaths

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards

/-- An explicit odd path from one oriented cycle to another. -/
def OddCycleBridge
    (grid : Nat → Nat → Index)
    (firstWest firstEast firstSouth firstNorth : Nat)
    (secondWest secondEast secondSouth secondNorth : Nat) : Prop :=
  ∃ firstPort secondPort,
    OnCycle firstWest firstEast firstSouth firstNorth firstPort ∧
      OnCycle secondWest secondEast secondSouth secondNorth secondPort ∧
      Path grid firstPort secondPort true

/-- The north side of the small cycle crosses the west side of the large one. -/
theorem north_crosses_west
    {grid : Nat → Nat → Index}
    {largeWest largeEast largeSouth largeNorth : Nat}
    {smallWest smallEast smallSouth smallNorth : Nat}
    (large : CycleOn grid largeWest largeEast largeSouth largeNorth)
    (small : CycleOn grid smallWest smallEast smallSouth smallNorth)
    (hsmallWest : smallWest < largeWest)
    (hsmallEast : largeWest < smallEast)
    (hlargeSouth : largeSouth < smallNorth)
    (hlargeNorth : smallNorth < largeNorth) :
    OddCycleBridge grid largeWest largeEast largeSouth largeNorth
      smallWest smallEast smallSouth smallNorth := by
  let x := quarterWest largeWest
  let y := quarterNorth smallNorth
  have horizontal := CycleOn.north_path small (qx := x) (by
    dsimp [x]
    unfold quarterWest
    omega) (by
    dsimp [x]
    unfold quarterWest quarterEast
    omega)
  have vertical := CycleOn.west_path large (qy := y) (by
    dsimp [y]
    unfold quarterSouth quarterNorth
    omega) (by
    dsimp [y]
    unfold quarterNorth
    omega)
  refine ⟨⟨x, y, .south⟩, ⟨x, y, .west⟩, OnCycle.westSouth y (by
      dsimp [y]
      unfold quarterSouth quarterNorth
      omega) (by
      dsimp [y]
      unfold quarterNorth
      omega), OnCycle.northWest x (by
      dsimp [x]
      unfold quarterWest
      omega) (by
      dsimp [x]
      unfold quarterWest quarterEast
      omega), Path.ofLink (Link.symm (Link.crossing x y horizontal vertical))⟩

/-- The north side of the small cycle crosses the east side of the large one. -/
theorem north_crosses_east
    {grid : Nat → Nat → Index}
    {largeWest largeEast largeSouth largeNorth : Nat}
    {smallWest smallEast smallSouth smallNorth : Nat}
    (large : CycleOn grid largeWest largeEast largeSouth largeNorth)
    (small : CycleOn grid smallWest smallEast smallSouth smallNorth)
    (hsmallWest : smallWest < largeEast)
    (hsmallEast : largeEast < smallEast)
    (hlargeSouth : largeSouth < smallNorth)
    (hlargeNorth : smallNorth < largeNorth) :
    OddCycleBridge grid largeWest largeEast largeSouth largeNorth
      smallWest smallEast smallSouth smallNorth := by
  let x := quarterEast largeEast
  let y := quarterNorth smallNorth
  have horizontal := CycleOn.north_path small (qx := x) (by
    dsimp [x]
    unfold quarterWest quarterEast
    omega) (by
    dsimp [x]
    unfold quarterEast
    omega)
  have vertical := CycleOn.east_path large (qy := y) (by
    dsimp [y]
    unfold quarterSouth quarterNorth
    omega) (by
    dsimp [y]
    unfold quarterNorth
    omega)
  refine ⟨⟨x, y, .south⟩, ⟨x, y, .west⟩, OnCycle.eastSouth y (by
      dsimp [y]
      unfold quarterSouth quarterNorth
      omega) (by
      dsimp [y]
      unfold quarterNorth
      omega), OnCycle.northWest x (by
      dsimp [x]
      unfold quarterWest quarterEast
      omega) (by
      dsimp [x]
      unfold quarterEast
      omega), Path.ofLink (Link.symm (Link.crossing x y horizontal vertical))⟩

/-- The south side of the small cycle crosses the west side of the large one. -/
theorem south_crosses_west
    {grid : Nat → Nat → Index}
    {largeWest largeEast largeSouth largeNorth : Nat}
    {smallWest smallEast smallSouth smallNorth : Nat}
    (large : CycleOn grid largeWest largeEast largeSouth largeNorth)
    (small : CycleOn grid smallWest smallEast smallSouth smallNorth)
    (hsmallWest : smallWest < largeWest)
    (hsmallEast : largeWest < smallEast)
    (hlargeSouth : largeSouth < smallSouth)
    (hlargeNorth : smallSouth < largeNorth) :
    OddCycleBridge grid largeWest largeEast largeSouth largeNorth
      smallWest smallEast smallSouth smallNorth := by
  let x := quarterWest largeWest
  let y := quarterSouth smallSouth
  have horizontal := CycleOn.south_path small (qx := x) (by
    dsimp [x]
    unfold quarterWest
    omega) (by
    dsimp [x]
    unfold quarterWest quarterEast
    omega)
  have vertical := CycleOn.west_path large (qy := y) (by
    dsimp [y]
    unfold quarterSouth
    omega) (by
    dsimp [y]
    unfold quarterSouth quarterNorth
    omega)
  refine ⟨⟨x, y, .south⟩, ⟨x, y, .west⟩, OnCycle.westSouth y (by
      dsimp [y]
      unfold quarterSouth
      omega) (by
      dsimp [y]
      unfold quarterSouth quarterNorth
      omega), OnCycle.southWest x (by
      dsimp [x]
      unfold quarterWest
      omega) (by
      dsimp [x]
      unfold quarterWest quarterEast
      omega), Path.ofLink (Link.symm (Link.crossing x y horizontal vertical))⟩

/-- The south side of the small cycle crosses the east side of the large one. -/
theorem south_crosses_east
    {grid : Nat → Nat → Index}
    {largeWest largeEast largeSouth largeNorth : Nat}
    {smallWest smallEast smallSouth smallNorth : Nat}
    (large : CycleOn grid largeWest largeEast largeSouth largeNorth)
    (small : CycleOn grid smallWest smallEast smallSouth smallNorth)
    (hsmallWest : smallWest < largeEast)
    (hsmallEast : largeEast < smallEast)
    (hlargeSouth : largeSouth < smallSouth)
    (hlargeNorth : smallSouth < largeNorth) :
    OddCycleBridge grid largeWest largeEast largeSouth largeNorth
      smallWest smallEast smallSouth smallNorth := by
  let x := quarterEast largeEast
  let y := quarterSouth smallSouth
  have horizontal := CycleOn.south_path small (qx := x) (by
    dsimp [x]
    unfold quarterWest quarterEast
    omega) (by
    dsimp [x]
    unfold quarterEast
    omega)
  have vertical := CycleOn.east_path large (qy := y) (by
    dsimp [y]
    unfold quarterSouth
    omega) (by
    dsimp [y]
    unfold quarterSouth quarterNorth
    omega)
  refine ⟨⟨x, y, .south⟩, ⟨x, y, .west⟩, OnCycle.eastSouth y (by
      dsimp [y]
      unfold quarterSouth
      omega) (by
      dsimp [y]
      unfold quarterSouth quarterNorth
      omega), OnCycle.southWest x (by
      dsimp [x]
      unfold quarterWest quarterEast
      omega) (by
      dsimp [x]
      unfold quarterEast
      omega), Path.ofLink (Link.symm (Link.crossing x y horizontal vertical))⟩

end RedShadeCycleCrossingPaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
