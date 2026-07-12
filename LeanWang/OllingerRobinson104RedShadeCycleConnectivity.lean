/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeCycleCrossingPaths
import LeanWang.OllingerRobinson104RedShadeGraphRefinement

/-!
# Even connectivity along an oriented red cycle

Every strict cycle-side port is connected with even crossing parity to the
inward east port of the southwest corner.  Hence any two ports on one cycle
are joined by an even path.  This lets odd bridges between nested cycles be
concatenated without changing their accumulated parity.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycleConnectivity

open OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards
  RedShadeGraphRefinement Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem horizontalWestPath
    (grid : Nat → Nat → Index) (y start : Nat) :
    ∀ distance,
      (∀ i, i < distance → RedShades.hasHorizontal
        (componentAt grid (start + i) y) (quadrantAt (start + i) y) = true) →
      Path grid ⟨start, y, .west⟩ ⟨start + distance, y, .west⟩ false
  | 0, _ => by simpa using (Path.refl (indexGrid := grid) ⟨start, y, .west⟩)
  | distance + 1, paths => by
      have prior := horizontalWestPath grid y start distance
        (fun i hi => paths i (by omega))
      have horizontal := Path.ofLink
        (Link.horizontal (start + distance) y (paths distance (by omega)))
      have matching : Path grid
          ⟨start + distance, y, .east⟩
          ⟨start + distance + 1, y, .west⟩ false := Path.ofLink
        (Link.horizontalMatch (start + distance) y)
      have step : Path grid ⟨start + distance, y, .west⟩
          ⟨start + (distance + 1), y, .west⟩ false := by
        simpa [Bool.false_xor, Nat.add_assoc] using Path.trans horizontal matching
      simpa [Bool.false_xor] using Path.trans prior step

theorem verticalSouthPath
    (grid : Nat → Nat → Index) (x start : Nat) :
    ∀ distance,
      (∀ i, i < distance → RedShades.hasVertical
        (componentAt grid x (start + i)) (quadrantAt x (start + i)) = true) →
      Path grid ⟨x, start, .south⟩ ⟨x, start + distance, .south⟩ false
  | 0, _ => by simpa using (Path.refl (indexGrid := grid) ⟨x, start, .south⟩)
  | distance + 1, paths => by
      have prior := verticalSouthPath grid x start distance
        (fun i hi => paths i (by omega))
      have vertical := Path.ofLink
        (Link.vertical x (start + distance) (paths distance (by omega)))
      have matching : Path grid
          ⟨x, start + distance, .north⟩
          ⟨x, start + distance + 1, .south⟩ false := Path.ofLink
        (Link.verticalMatch x (start + distance))
      have step : Path grid ⟨x, start + distance, .south⟩
          ⟨x, start + (distance + 1), .south⟩ false := by
        simpa [Bool.false_xor, Nat.add_assoc] using Path.trans vertical matching
      simpa [Bool.false_xor] using Path.trans prior step

theorem southwest_to_south
    {grid : Nat → Nat → Index} {west east south north x : Nat}
    (cycle : CycleOn grid west east south north)
    (hwest : quarterWest west < x) (heast : x < quarterEast east) :
    Path grid ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨x, quarterSouth south, .west⟩ false := by
  let first := quarterWest west + 1
  have hfirst : first ≤ x := by dsimp [first]; omega
  have initial : Path grid
      ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨quarterWest west + 1, quarterSouth south, .west⟩ false := Path.ofLink
    (Link.horizontalMatch (quarterWest west) (quarterSouth south))
  have lane := horizontalWestPath grid (quarterSouth south) first (x - first)
    (fun i hi => RedShadeCycles.CycleOn.south_path cycle (qx := first + i) (by
      dsimp [first]
      omega) (by
      dsimp [first]
      omega))
  have hend : first + (x - first) = x := by omega
  rw [hend] at lane
  simpa [Bool.false_xor, first] using Path.trans initial lane

theorem southwest_to_west
    {grid : Nat → Nat → Index} {west east south north y : Nat}
    (cycle : CycleOn grid west east south north)
    (hsouth : quarterSouth south < y) (hnorth : y < quarterNorth north) :
    Path grid ⟨quarterWest west, quarterSouth south, .north⟩
      ⟨quarterWest west, y, .south⟩ false := by
  let first := quarterSouth south + 1
  have hfirst : first ≤ y := by dsimp [first]; omega
  have initial : Path grid
      ⟨quarterWest west, quarterSouth south, .north⟩
      ⟨quarterWest west, quarterSouth south + 1, .south⟩ false := Path.ofLink
    (Link.verticalMatch (quarterWest west) (quarterSouth south))
  have lane := verticalSouthPath grid (quarterWest west) first (y - first)
    (fun i hi => RedShadeCycles.CycleOn.west_path cycle (qy := first + i) (by
      dsimp [first]
      omega) (by
      dsimp [first]
      omega))
  have hend : first + (y - first) = y := by omega
  rw [hend] at lane
  simpa [Bool.false_xor, first] using Path.trans initial lane

theorem southwest_to_east_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    Path grid ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨quarterEast east, quarterSouth south, .west⟩ false := by
  let first := quarterWest west + 1
  have hfirst : first ≤ quarterEast east := by
    have hboard := cycle.west_lt_east
    dsimp [first]
    unfold quarterWest quarterEast
    omega
  have initial : Path grid
      ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨quarterWest west + 1, quarterSouth south, .west⟩ false := Path.ofLink
    (Link.horizontalMatch (quarterWest west) (quarterSouth south))
  have lane := horizontalWestPath grid (quarterSouth south) first
    (quarterEast east - first) (fun i hi => RedShadeCycles.CycleOn.south_path cycle
      (qx := first + i) (by dsimp [first]; omega) (by dsimp [first]; omega))
  have hend : first + (quarterEast east - first) = quarterEast east := by omega
  rw [hend] at lane
  simpa [Bool.false_xor, first] using Path.trans initial lane

theorem southwest_to_northwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    Path grid ⟨quarterWest west, quarterSouth south, .north⟩
      ⟨quarterWest west, quarterNorth north, .south⟩ false := by
  let first := quarterSouth south + 1
  have hfirst : first ≤ quarterNorth north := by
    have hboard := cycle.south_lt_north
    dsimp [first]
    unfold quarterSouth quarterNorth
    omega
  have initial : Path grid
      ⟨quarterWest west, quarterSouth south, .north⟩
      ⟨quarterWest west, quarterSouth south + 1, .south⟩ false := Path.ofLink
    (Link.verticalMatch (quarterWest west) (quarterSouth south))
  have lane := verticalSouthPath grid (quarterWest west) first
    (quarterNorth north - first) (fun i hi => RedShadeCycles.CycleOn.west_path cycle
      (qy := first + i) (by dsimp [first]; omega) (by dsimp [first]; omega))
  have hend : first + (quarterNorth north - first) = quarterNorth north := by omega
  rw [hend] at lane
  simpa [Bool.false_xor, first] using Path.trans initial lane

theorem southwest_to_north
    {grid : Nat → Nat → Index} {west east south north x : Nat}
    (cycle : CycleOn grid west east south north)
    (hwest : quarterWest west < x) (heast : x < quarterEast east) :
    Path grid ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨x, quarterNorth north, .west⟩ false := by
  have corner : Path grid
      ⟨quarterWest west, quarterSouth south, .east⟩
      ⟨quarterWest west, quarterNorth north, .south⟩ false :=
    Path.trans
      (Path.ofLink (Link.eastNorth _ _
        (RedShadeCycles.CycleOn.southwest_corner cycle).1
        (RedShadeCycles.CycleOn.southwest_corner cycle).2))
      (southwest_to_northwest_corner cycle)
  have turn : Path grid
      ⟨quarterWest west, quarterNorth north, .south⟩
      ⟨quarterWest west, quarterNorth north, .east⟩ false :=
    Path.ofLink (Link.symm (Link.eastSouth _ _
      (RedShadeCycles.CycleOn.northwest_corner cycle).1
      (RedShadeCycles.CycleOn.northwest_corner cycle).2))
  let first := quarterWest west + 1
  have initial : Path grid
      ⟨quarterWest west, quarterNorth north, .east⟩
      ⟨quarterWest west + 1, quarterNorth north, .west⟩ false := Path.ofLink
    (Link.horizontalMatch (quarterWest west) (quarterNorth north))
  have lane := horizontalWestPath grid (quarterNorth north) first (x - first)
    (fun i hi => RedShadeCycles.CycleOn.north_path cycle (qx := first + i)
      (by dsimp [first]; omega) (by dsimp [first]; omega))
  have hend : first + (x - first) = x := by dsimp [first]; omega
  rw [hend] at lane
  exact Path.trans corner (Path.trans turn (Path.trans initial lane))

/-- Every strict side port connects evenly from the southwest inward edge. -/
theorem southwest_to_onCycle
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) {port : Port}
    (onCycle : OnCycle west east south north port) :
    Path grid ⟨quarterWest west, quarterSouth south, .east⟩ port false := by
  cases onCycle with
  | southWest x hwest heast => exact southwest_to_south cycle hwest heast
  | southEast x hwest heast =>
      exact Path.trans (southwest_to_south cycle hwest heast)
        (Path.ofLink (Link.horizontal x (quarterSouth south)
          (RedShadeCycles.CycleOn.south_path cycle hwest heast)))
  | westSouth y hsouth hnorth =>
      exact Path.trans
        (Path.ofLink (Link.eastNorth _ _
          (RedShadeCycles.CycleOn.southwest_corner cycle).1
          (RedShadeCycles.CycleOn.southwest_corner cycle).2))
        (southwest_to_west cycle hsouth hnorth)
  | westNorth y hsouth hnorth =>
      exact Path.trans (Path.trans
        (Path.ofLink (Link.eastNorth _ _
          (RedShadeCycles.CycleOn.southwest_corner cycle).1
          (RedShadeCycles.CycleOn.southwest_corner cycle).2))
        (southwest_to_west cycle hsouth hnorth))
        (Path.ofLink (Link.vertical (quarterWest west) y
          (RedShadeCycles.CycleOn.west_path cycle hsouth hnorth)))
  | eastSouth y hsouth hnorth =>
      have corner := Path.trans (southwest_to_east_corner cycle)
        (Path.ofLink (Link.westNorth _ _
          (RedShadeCycles.CycleOn.southeast_corner cycle).1
          (RedShadeCycles.CycleOn.southeast_corner cycle).2))
      let first := quarterSouth south + 1
      have initial : Path grid
          ⟨quarterEast east, quarterSouth south, .north⟩
          ⟨quarterEast east, quarterSouth south + 1, .south⟩ false := Path.ofLink
        (Link.verticalMatch (quarterEast east) (quarterSouth south))
      have lane := verticalSouthPath grid (quarterEast east) first (y - first)
        (fun i hi => RedShadeCycles.CycleOn.east_path cycle (qy := first + i)
          (by dsimp [first]; omega) (by dsimp [first]; omega))
      have hend : first + (y - first) = y := by dsimp [first]; omega
      rw [hend] at lane
      exact Path.trans corner (Path.trans initial lane)
  | eastNorth y hsouth hnorth =>
      have southPath : Path grid
          ⟨quarterWest west, quarterSouth south, .east⟩
          ⟨quarterEast east, y, .south⟩ false := by
        have corner := Path.trans (southwest_to_east_corner cycle)
          (Path.ofLink (Link.westNorth _ _
            (RedShadeCycles.CycleOn.southeast_corner cycle).1
            (RedShadeCycles.CycleOn.southeast_corner cycle).2))
        let first := quarterSouth south + 1
        have initial : Path grid
            ⟨quarterEast east, quarterSouth south, .north⟩
            ⟨quarterEast east, quarterSouth south + 1, .south⟩ false := Path.ofLink
          (Link.verticalMatch (quarterEast east) (quarterSouth south))
        have lane := verticalSouthPath grid (quarterEast east) first (y - first)
          (fun i hi => RedShadeCycles.CycleOn.east_path cycle (qy := first + i)
            (by dsimp [first]; omega) (by dsimp [first]; omega))
        have hend : first + (y - first) = y := by dsimp [first]; omega
        rw [hend] at lane
        exact Path.trans corner (Path.trans initial lane)
      exact Path.trans southPath (Path.ofLink
        (Link.vertical (quarterEast east) y
          (RedShadeCycles.CycleOn.east_path cycle hsouth hnorth)))
  | northWest x hwest heast =>
      exact southwest_to_north cycle hwest heast
  | northEast x hwest heast =>
      have westPath := southwest_to_north cycle hwest heast
      exact Path.trans westPath (Path.ofLink
        (Link.horizontal x (quarterNorth north)
          (RedShadeCycles.CycleOn.north_path cycle hwest heast)))

/-- Any two ports on one oriented cycle are connected with even parity. -/
theorem onCycle_connected
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : CycleOn grid west east south north) {first second : Port}
    (firstOnCycle : OnCycle west east south north first)
    (secondOnCycle : OnCycle west east south north second) :
    Path grid first second false := by
  have toFirst := southwest_to_onCycle cycle firstOnCycle
  have toSecond := southwest_to_onCycle cycle secondOnCycle
  simpa [Bool.false_xor] using
    Path.trans (path_symm toFirst) toSecond

end RedShadeCycleConnectivity
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
