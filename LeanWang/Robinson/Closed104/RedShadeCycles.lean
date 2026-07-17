/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedRedCycles
import LeanWang.Robinson.Closed104.RedShadePaths

/-!
Uniform red-wire shade on the canonical depth-two board.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeCycles

open RedCycles QuarterGeometry Signals.FreeCellLocal RedShadePaths

set_option maxRecDepth 20000

def fixedGrid (parent : Index) : Nat → Nat → Index :=
  iterateRefine 2 (fun _ _ => parent)

/-- Quarter-level red-path geometry of the universal depth-two board. -/
structure FixedGeometry (parent : Index) : Prop where
  southwestEast : RedShades.cornerEast
    (components (fixedGrid parent (3 / 2) (3 / 2))).2.1
      (quadrantAt 3 3) = true
  southwestNorth : RedShades.cornerNorth
    (components (fixedGrid parent (3 / 2) (3 / 2))).2.1
      (quadrantAt 3 3) = true
  southeastWest : RedShades.cornerWest
    (componentAt (fixedGrid parent) 6 3) (quadrantAt 6 3) = true
  southeastNorth : RedShades.cornerNorth
    (componentAt (fixedGrid parent) 6 3) (quadrantAt 6 3) = true
  northeastWest : RedShades.cornerWest
    (componentAt (fixedGrid parent) 6 6) (quadrantAt 6 6) = true
  northeastSouth : RedShades.cornerSouth
    (componentAt (fixedGrid parent) 6 6) (quadrantAt 6 6) = true
  northwestEast : RedShades.cornerEast
    (componentAt (fixedGrid parent) 3 6) (quadrantAt 3 6) = true
  northwestSouth : RedShades.cornerSouth
    (componentAt (fixedGrid parent) 3 6) (quadrantAt 3 6) = true
  south4 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 4 3) (quadrantAt 4 3) = true
  south5 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 5 3) (quadrantAt 5 3) = true
  north4 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 4 6) (quadrantAt 4 6) = true
  north5 : RedShades.hasHorizontal
    (componentAt (fixedGrid parent) 5 6) (quadrantAt 5 6) = true
  west4 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 3 4) (quadrantAt 3 4) = true
  west5 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 3 5) (quadrantAt 3 5) = true
  east4 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 6 4) (quadrantAt 6 4) = true
  east5 : RedShades.hasVertical
    (componentAt (fixedGrid parent) 6 5) (quadrantAt 6 5) = true

set_option linter.style.nativeDecide false in
theorem fixedGeometry (parent : Index) : FixedGeometry parent := by
  refine {
    southwestEast := ?_
    southwestNorth := ?_
    southeastWest := ?_
    southeastNorth := ?_
    northeastWest := ?_
    northeastSouth := ?_
    northwestEast := ?_
    northwestSouth := ?_
    south4 := ?_
    south5 := ?_
    north4 := ?_
    north5 := ?_
    west4 := ?_
    west5 := ?_
    east4 := ?_
    east5 := ?_
  }
  all_goals revert parent; native_decide

def quarterWest (west : Nat) : Nat := 2 * west + 1
def quarterEast (east : Nat) : Nat := 2 * east
def quarterSouth (south : Nat) : Nat := 2 * south + 1
def quarterNorth (north : Nat) : Nat := 2 * north

@[simp] theorem quadrantAt_quarterSouth_yBit (x south : Nat) :
    (quadrantAt x (quarterSouth south)).yBit = true := by
  cases hbit : (x % 2 == 1) <;>
    simp [quadrantAt, quarterSouth, Quadrant.ofBits, Quadrant.yBit, hbit]

@[simp] theorem quadrantAt_quarterNorth_yBit (x north : Nat) :
    (quadrantAt x (quarterNorth north)).yBit = false := by
  cases hbit : (x % 2 == 1) <;>
    simp [quadrantAt, quarterNorth, Quadrant.ofBits, Quadrant.yBit, hbit]

@[simp] theorem quadrantAt_quarterWest_xBit (west y : Nat) :
    (quadrantAt (quarterWest west) y).xBit = true := by
  cases hbit : (y % 2 == 1) <;>
    simp [quadrantAt, quarterWest, Quadrant.ofBits, Quadrant.xBit, hbit]

@[simp] theorem quadrantAt_quarterEast_xBit (east y : Nat) :
    (quadrantAt (quarterEast east) y).xBit = false := by
  cases hbit : (y % 2 == 1) <;>
    simp [quadrantAt, quarterEast, Quadrant.ofBits, Quadrant.xBit, hbit]

theorem CycleOn.southwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    RedShades.cornerEast
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) = true ∧
      RedShades.cornerNorth
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) = true := by
  have hcomponent :
      componentAt grid (quarterWest west) (quarterSouth south) = .b := by
    rw [componentAt]
    simp only [quarterWest, quarterSouth]
    have hdivX : (2 * west + 1) / 2 = west := by omega
    have hdivY : (2 * south + 1) / 2 = south := by omega
    rw [hdivX, hdivY, ← indexThick_eq]
    exact cycle.southwest
  rw [hcomponent]
  simp [quadrantAt, quarterWest, quarterSouth, Quadrant.ofBits,
    RedShades.cornerEast, RedShades.cornerNorth]

theorem CycleOn.southeast_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    RedShades.cornerWest
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) = true ∧
      RedShades.cornerNorth
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) = true := by
  have hcomponent :
      componentAt grid (quarterEast east) (quarterSouth south) = .c := by
    rw [componentAt]
    simp only [quarterEast, quarterSouth]
    have hdivX : (2 * east) / 2 = east := by omega
    have hdivY : (2 * south + 1) / 2 = south := by omega
    rw [hdivX, hdivY, ← indexThick_eq]
    exact cycle.southeast
  rw [hcomponent]
  simp [quadrantAt, quarterEast, quarterSouth, Quadrant.ofBits,
    RedShades.cornerWest, RedShades.cornerNorth]

theorem CycleOn.northeast_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    RedShades.cornerWest
        (componentAt grid (quarterEast east) (quarterNorth north))
        (quadrantAt (quarterEast east) (quarterNorth north)) = true ∧
      RedShades.cornerSouth
        (componentAt grid (quarterEast east) (quarterNorth north))
        (quadrantAt (quarterEast east) (quarterNorth north)) = true := by
  have hcomponent :
      componentAt grid (quarterEast east) (quarterNorth north) = .d := by
    rw [componentAt]
    simp only [quarterEast, quarterNorth]
    have hdivX : (2 * east) / 2 = east := by omega
    have hdivY : (2 * north) / 2 = north := by omega
    rw [hdivX, hdivY, ← indexThick_eq]
    exact cycle.northeast
  rw [hcomponent]
  simp [quadrantAt, quarterEast, quarterNorth, Quadrant.ofBits,
    RedShades.cornerWest, RedShades.cornerSouth]

theorem CycleOn.northwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    RedShades.cornerEast
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) = true ∧
      RedShades.cornerSouth
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) = true := by
  have hcomponent :
      componentAt grid (quarterWest west) (quarterNorth north) = .a := by
    rw [componentAt]
    simp only [quarterWest, quarterNorth]
    have hdivX : (2 * west + 1) / 2 = west := by omega
    have hdivY : (2 * north) / 2 = north := by omega
    rw [hdivX, hdivY, ← indexThick_eq]
    exact cycle.northwest
  rw [hcomponent]
  simp [quadrantAt, quarterWest, quarterNorth, Quadrant.ofBits,
    RedShades.cornerEast, RedShades.cornerSouth]

set_option maxHeartbeats 500000 in
-- Dependent quarter-grid arithmetic needs more elaboration than the default.
theorem CycleOn.south_path
    {grid : Nat → Nat → Index} {west east south north qx : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    RedShades.hasHorizontal
      (componentAt grid qx (quarterSouth south))
      (quadrantAt qx (quarterSouth south)) = true := by
  have hparentWest : west < qx / 2 := by
    unfold quarterWest at hwest
    omega
  have hparentEast : qx / 2 < east := by
    unfold quarterEast at heast
    omega
  have hline := cycle.southLane (qx / 2) hparentWest hparentEast
  rw [indexThick_eq] at hline
  unfold RedShades.hasHorizontal
  rw [quadrantAt_quarterSouth_yBit]
  simp only [redHorizontalAt]
  unfold componentAt
  have hdivY : quarterSouth south / 2 = south := by
    unfold quarterSouth
    omega
  rw [hdivY]
  exact hline

set_option maxHeartbeats 500000 in
-- Dependent quarter-grid arithmetic needs more elaboration than the default.
theorem CycleOn.north_path
    {grid : Nat → Nat → Index} {west east south north qx : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    RedShades.hasHorizontal
      (componentAt grid qx (quarterNorth north))
      (quadrantAt qx (quarterNorth north)) = true := by
  have hparentWest : west < qx / 2 := by
    unfold quarterWest at hwest
    omega
  have hparentEast : qx / 2 < east := by
    unfold quarterEast at heast
    omega
  have hline := cycle.northLane (qx / 2) hparentWest hparentEast
  rw [indexThick_eq] at hline
  unfold RedShades.hasHorizontal
  rw [quadrantAt_quarterNorth_yBit]
  simp only [redHorizontalAt]
  unfold componentAt
  have hdivY : quarterNorth north / 2 = north := by
    unfold quarterNorth
    omega
  rw [hdivY]
  exact hline

set_option maxHeartbeats 500000 in
-- Dependent quarter-grid arithmetic needs more elaboration than the default.
theorem CycleOn.west_path
    {grid : Nat → Nat → Index} {west east south north qy : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    RedShades.hasVertical
      (componentAt grid (quarterWest west) qy)
      (quadrantAt (quarterWest west) qy) = true := by
  have hparentSouth : south < qy / 2 := by
    unfold quarterSouth at hsouth
    omega
  have hparentNorth : qy / 2 < north := by
    unfold quarterNorth at hnorth
    omega
  have hline := cycle.westLane (qy / 2) hparentSouth hparentNorth
  rw [indexThick_eq] at hline
  unfold RedShades.hasVertical
  rw [quadrantAt_quarterWest_xBit]
  simp only [redVerticalAt]
  unfold componentAt
  have hdivX : quarterWest west / 2 = west := by
    unfold quarterWest
    omega
  rw [hdivX]
  exact hline

set_option maxHeartbeats 500000 in
-- Dependent quarter-grid arithmetic needs more elaboration than the default.
theorem CycleOn.east_path
    {grid : Nat → Nat → Index} {west east south north qy : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    RedShades.hasVertical
      (componentAt grid (quarterEast east) qy)
      (quadrantAt (quarterEast east) qy) = true := by
  have hparentSouth : south < qy / 2 := by
    unfold quarterSouth at hsouth
    omega
  have hparentNorth : qy / 2 < north := by
    unfold quarterNorth at hnorth
    omega
  have hline := cycle.eastLane (qy / 2) hparentSouth hparentNorth
  rw [indexThick_eq] at hline
  unfold RedShades.hasVertical
  rw [quadrantAt_quarterEast_xBit]
  simp only [redVerticalAt]
  unfold componentAt
  have hdivX : quarterEast east / 2 = east := by
    unfold quarterEast
    omega
  rw [hdivX]
  exact hline

/-- Uniform shade at the four inward quarter corners of an arbitrary board. -/
structure CycleShade (stateGrid : Nat → Nat → RedShades.State)
    (west east south north : Nat) (shade : RedShades.Shade) : Prop where
  southwest : (stateGrid (quarterWest west) (quarterSouth south)).east =
    some shade
  southeast : (stateGrid (quarterEast east) (quarterSouth south)).west =
    some shade
  northeast : (stateGrid (quarterEast east) (quarterNorth north)).west =
    some shade
  northwest : (stateGrid (quarterWest west) (quarterNorth north)).east =
    some shade

set_option maxHeartbeats 500000 in
-- The proof composes four dependent quarter-grid path calculations.
/-- A shade on one edge of any oriented board propagates to every corner. -/
theorem CycleOn.cycleShade
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) (shade : RedShades.Shade)
    (hshade :
      (stateGrid (quarterWest west) (quarterSouth south)).east = some shade) :
    CycleShade stateGrid west east south north shade := by
  have hquarterWestEast : quarterWest west < quarterEast east := by
    unfold quarterWest quarterEast
    have := cycle.west_lt_east
    omega
  have hquarterSouthNorth : quarterSouth south < quarterNorth north := by
    unfold quarterSouth quarterNorth
    have := cycle.south_lt_north
    omega
  have hsouth :
      (stateGrid (quarterWest west) (quarterSouth south)).east =
        (stateGrid (quarterEast east) (quarterSouth south)).west := by
    have hflow := horizontal_shade_across
      (fun qx => stateGrid qx (quarterSouth south))
      (quarterWest west) (quarterEast east - quarterWest west - 1)
      (fun i hi => valid.hmatch (quarterWest west + i) (quarterSouth south))
      (fun i hi => valid.horizontal_eq
        (quarterWest west + i + 1) (quarterSouth south)
        (CycleOn.south_path cycle (by omega) (by omega)))
    have hend : quarterWest west +
        (quarterEast east - quarterWest west - 1) + 1 = quarterEast east := by
      omega
    simpa only [hend] using hflow
  have hseNorth :
      (stateGrid (quarterEast east) (quarterSouth south)).north = some shade := by
    rw [← valid.west_north_corner_eq
      (quarterEast east) (quarterSouth south)
      (CycleOn.southeast_corner cycle).1 (CycleOn.southeast_corner cycle).2]
    exact hsouth.symm.trans hshade
  have heast :
      (stateGrid (quarterEast east) (quarterSouth south)).north =
        (stateGrid (quarterEast east) (quarterNorth north)).south := by
    have hflow := vertical_shade_across
      (fun qy => stateGrid (quarterEast east) qy)
      (quarterSouth south) (quarterNorth north - quarterSouth south - 1)
      (fun i hi => valid.vmatch (quarterEast east) (quarterSouth south + i))
      (fun i hi => valid.vertical_eq
        (quarterEast east) (quarterSouth south + i + 1)
        (CycleOn.east_path cycle (by omega) (by omega)))
    have hend : quarterSouth south +
        (quarterNorth north - quarterSouth south - 1) + 1 = quarterNorth north := by
      omega
    simpa only [hend] using hflow
  have hneWest :
      (stateGrid (quarterEast east) (quarterNorth north)).west = some shade := by
    rw [valid.west_south_corner_eq
      (quarterEast east) (quarterNorth north)
      (CycleOn.northeast_corner cycle).1 (CycleOn.northeast_corner cycle).2]
    exact heast.symm.trans hseNorth
  have hnorth :
      (stateGrid (quarterWest west) (quarterNorth north)).east =
        (stateGrid (quarterEast east) (quarterNorth north)).west := by
    have hflow := horizontal_shade_across
      (fun qx => stateGrid qx (quarterNorth north))
      (quarterWest west) (quarterEast east - quarterWest west - 1)
      (fun i hi => valid.hmatch (quarterWest west + i) (quarterNorth north))
      (fun i hi => valid.horizontal_eq
        (quarterWest west + i + 1) (quarterNorth north)
        (CycleOn.north_path cycle (by omega) (by omega)))
    have hend : quarterWest west +
        (quarterEast east - quarterWest west - 1) + 1 = quarterEast east := by
      omega
    simpa only [hend] using hflow
  exact {
    southwest := hshade
    southeast := hsouth.symm.trans hshade
    northeast := hneWest
    northwest := hnorth.trans hneWest
  }

set_option maxHeartbeats 500000 in
-- Selecting the corner edge elaborates the dependent quarter-grid coordinate.
/-- Every oriented red board has one uniform light/dark corner shade. -/
theorem CycleOn.exists_cycleShade
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) :
    ∃ shade, CycleShade stateGrid west east south north shade := by
  have heast : RedShades.hasEast
      (componentAt grid (quarterWest west) (quarterSouth south))
      (quadrantAt (quarterWest west) (quarterSouth south)) = true := by
    simp [RedShades.hasEast, (CycleOn.southwest_corner cycle).1]
  have hpresent := valid.east_present
    (quarterWest west) (quarterSouth south) heast
  rcases hshade :
      (stateGrid (quarterWest west) (quarterSouth south)).east with _ | shade
  · simp [hshade] at hpresent
  · exact ⟨shade, CycleOn.cycleShade cycle valid shade hshade⟩

set_option maxHeartbeats 500000 in
-- The proof propagates through a dependent prefix of the south quarter path.
theorem CycleShade.south_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qx : Nat}
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    (stateGrid qx (quarterSouth south)).west = some shade ∧
      (stateGrid qx (quarterSouth south)).east = some shade := by
  have hflow := horizontal_shade_across
    (fun x => stateGrid x (quarterSouth south)) (quarterWest west)
    (qx - quarterWest west - 1)
    (fun i hi => valid.hmatch (quarterWest west + i) (quarterSouth south))
    (fun i hi => valid.horizontal_eq
      (quarterWest west + i + 1) (quarterSouth south)
      (CycleOn.south_path cycle (by omega) (by omega)))
  have hend : quarterWest west + (qx - quarterWest west - 1) + 1 = qx := by
    omega
  rw [hend] at hflow
  have hwestShade := hflow.symm.trans shaded.southwest
  exact ⟨hwestShade,
    (valid.horizontal_eq qx (quarterSouth south)
      (CycleOn.south_path cycle hwest heast)).symm.trans hwestShade⟩

set_option maxHeartbeats 500000 in
-- The proof propagates through a dependent prefix of the north quarter path.
theorem CycleShade.north_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qx : Nat}
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    (stateGrid qx (quarterNorth north)).west = some shade ∧
      (stateGrid qx (quarterNorth north)).east = some shade := by
  have hflow := horizontal_shade_across
    (fun x => stateGrid x (quarterNorth north)) (quarterWest west)
    (qx - quarterWest west - 1)
    (fun i hi => valid.hmatch (quarterWest west + i) (quarterNorth north))
    (fun i hi => valid.horizontal_eq
      (quarterWest west + i + 1) (quarterNorth north)
      (CycleOn.north_path cycle (by omega) (by omega)))
  have hend : quarterWest west + (qx - quarterWest west - 1) + 1 = qx := by
    omega
  rw [hend] at hflow
  have hwestShade := hflow.symm.trans shaded.northwest
  exact ⟨hwestShade,
    (valid.horizontal_eq qx (quarterNorth north)
      (CycleOn.north_path cycle hwest heast)).symm.trans hwestShade⟩

set_option maxHeartbeats 500000 in
-- The proof propagates through a dependent prefix of the west quarter path.
theorem CycleShade.west_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qy : Nat}
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    (stateGrid (quarterWest west) qy).south = some shade ∧
      (stateGrid (quarterWest west) qy).north = some shade := by
  have hstart :
      (stateGrid (quarterWest west) (quarterSouth south)).north = some shade := by
    rw [← valid.east_north_corner_eq (quarterWest west) (quarterSouth south)
      (CycleOn.southwest_corner cycle).1 (CycleOn.southwest_corner cycle).2]
    exact shaded.southwest
  have hflow := vertical_shade_across
    (fun y => stateGrid (quarterWest west) y) (quarterSouth south)
    (qy - quarterSouth south - 1)
    (fun i hi => valid.vmatch (quarterWest west) (quarterSouth south + i))
    (fun i hi => valid.vertical_eq (quarterWest west)
      (quarterSouth south + i + 1)
      (CycleOn.west_path cycle (by omega) (by omega)))
  have hend : quarterSouth south + (qy - quarterSouth south - 1) + 1 = qy := by
    omega
  rw [hend] at hflow
  have hsouthShade := hflow.symm.trans hstart
  exact ⟨hsouthShade,
    (valid.vertical_eq (quarterWest west) qy
      (CycleOn.west_path cycle hsouth hnorth)).symm.trans hsouthShade⟩

set_option maxHeartbeats 500000 in
-- The proof propagates through a dependent prefix of the east quarter path.
theorem CycleShade.east_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qy : Nat}
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    (stateGrid (quarterEast east) qy).south = some shade ∧
      (stateGrid (quarterEast east) qy).north = some shade := by
  have hstart :
      (stateGrid (quarterEast east) (quarterSouth south)).north = some shade := by
    rw [← valid.west_north_corner_eq (quarterEast east) (quarterSouth south)
      (CycleOn.southeast_corner cycle).1 (CycleOn.southeast_corner cycle).2]
    exact shaded.southeast
  have hflow := vertical_shade_across
    (fun y => stateGrid (quarterEast east) y) (quarterSouth south)
    (qy - quarterSouth south - 1)
    (fun i hi => valid.vmatch (quarterEast east) (quarterSouth south + i))
    (fun i hi => valid.vertical_eq (quarterEast east)
      (quarterSouth south + i + 1)
      (CycleOn.east_path cycle (by omega) (by omega)))
  have hend : quarterSouth south + (qy - quarterSouth south - 1) + 1 = qy := by
    omega
  rw [hend] at hflow
  have hsouthShade := hflow.symm.trans hstart
  exact ⟨hsouthShade,
    (valid.vertical_eq (quarterEast east) qy
      (CycleOn.east_path cycle hsouth hnorth)).symm.trans hsouthShade⟩

/-- Corner shades carried by one canonical depth-two board. -/
structure FixedCycleShade (stateGrid : Nat → Nat → RedShades.State)
    (shade : RedShades.Shade) : Prop where
  southwest : (stateGrid 3 3).east = some shade
  southeast : (stateGrid 6 3).west = some shade
  northeast : (stateGrid 6 6).west = some shade
  northwest : (stateGrid 3 6).east = some shade

/-- A shade on one edge of the canonical board propagates to every corner. -/
theorem fixedCycleShade (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (fixedGrid parent) stateGrid)
    (shade : RedShades.Shade)
    (hshade : (stateGrid 3 3).east = some shade) :
    FixedCycleShade stateGrid shade := by
  have geometry := fixedGeometry parent
  exact (by
    refine ⟨hshade, ?_, ?_, ?_⟩
    · calc
        (stateGrid 6 3).west = (stateGrid 5 3).east :=
          (valid.hmatch 5 3).symm
        _ = (stateGrid 5 3).west :=
          (valid.horizontal_eq 5 3 geometry.south5).symm
        _ = (stateGrid 4 3).east := (valid.hmatch 4 3).symm
        _ = (stateGrid 4 3).west :=
          (valid.horizontal_eq 4 3 geometry.south4).symm
        _ = (stateGrid 3 3).east := (valid.hmatch 3 3).symm
        _ = some shade := hshade
    · have hseNorth : (stateGrid 6 3).north = some shade := by
        rw [← valid.west_north_corner_eq 6 3
          geometry.southeastWest geometry.southeastNorth]
        exact (by
          calc
            (stateGrid 6 3).west = (stateGrid 5 3).east :=
              (valid.hmatch 5 3).symm
            _ = (stateGrid 5 3).west :=
              (valid.horizontal_eq 5 3 geometry.south5).symm
            _ = (stateGrid 4 3).east := (valid.hmatch 4 3).symm
            _ = (stateGrid 4 3).west :=
              (valid.horizontal_eq 4 3 geometry.south4).symm
            _ = (stateGrid 3 3).east := (valid.hmatch 3 3).symm
            _ = some shade := hshade)
      calc
        (stateGrid 6 6).west = (stateGrid 6 6).south :=
          valid.west_south_corner_eq 6 6
            geometry.northeastWest geometry.northeastSouth
        _ = (stateGrid 6 5).north := (valid.vmatch 6 5).symm
        _ = (stateGrid 6 5).south :=
          (valid.vertical_eq 6 5 geometry.east5).symm
        _ = (stateGrid 6 4).north := (valid.vmatch 6 4).symm
        _ = (stateGrid 6 4).south :=
          (valid.vertical_eq 6 4 geometry.east4).symm
        _ = (stateGrid 6 3).north := (valid.vmatch 6 3).symm
        _ = some shade := hseNorth
    · have hneWest : (stateGrid 6 6).west = some shade := by
        calc
          (stateGrid 6 6).west = (stateGrid 6 6).south :=
            valid.west_south_corner_eq 6 6
              geometry.northeastWest geometry.northeastSouth
          _ = (stateGrid 6 5).north := (valid.vmatch 6 5).symm
          _ = (stateGrid 6 5).south :=
            (valid.vertical_eq 6 5 geometry.east5).symm
          _ = (stateGrid 6 4).north := (valid.vmatch 6 4).symm
          _ = (stateGrid 6 4).south :=
            (valid.vertical_eq 6 4 geometry.east4).symm
          _ = (stateGrid 6 3).north := (valid.vmatch 6 3).symm
          _ = (stateGrid 6 3).west :=
            (valid.west_north_corner_eq 6 3
              geometry.southeastWest geometry.southeastNorth).symm
          _ = (stateGrid 5 3).east := (valid.hmatch 5 3).symm
          _ = (stateGrid 5 3).west :=
            (valid.horizontal_eq 5 3 geometry.south5).symm
          _ = (stateGrid 4 3).east := (valid.hmatch 4 3).symm
          _ = (stateGrid 4 3).west :=
            (valid.horizontal_eq 4 3 geometry.south4).symm
          _ = (stateGrid 3 3).east := (valid.hmatch 3 3).symm
          _ = some shade := hshade
      calc
        (stateGrid 3 6).east = (stateGrid 4 6).west := valid.hmatch 3 6
        _ = (stateGrid 4 6).east :=
          valid.horizontal_eq 4 6 geometry.north4
        _ = (stateGrid 5 6).west := valid.hmatch 4 6
        _ = (stateGrid 5 6).east :=
          valid.horizontal_eq 5 6 geometry.north5
        _ = (stateGrid 6 6).west := valid.hmatch 5 6
        _ = some shade := hneWest
  )

end RedShadeCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
