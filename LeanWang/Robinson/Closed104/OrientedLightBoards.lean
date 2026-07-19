/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightSegments
import LeanWang.Robinson.Closed104.RedShadeCycles

/-!
# Directed boundary of a light Robinson board

A uniformly light `CycleOn` is a literal counterclockwise directed rectangle
in the quarter grid.  These lemmas expose that fact in the small physical
segment model.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightBoards

open OrientedRedCycles RedShadeCycles RedShadePaths
  OrientedLightSegments Signals.FreeCellLocal

set_option maxRecDepth 20000

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

theorem CycleShade.south_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {quarterX : Nat}
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    segmentAt indexGrid stateGrid quarterX (quarterSouth south) =
      some .east := by
  apply segment_eq_east_of_horizontal_edges
    (valid.allowed quarterX (quarterSouth south))
  · exact (shaded.south_at cycle valid hwest heast).1
  · exact (shaded.south_at cycle valid hwest heast).2
  · exact quadrantAt_quarterSouth_yBit quarterX south

theorem CycleShade.north_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {quarterX : Nat}
    (hwest : quarterWest west < quarterX)
    (heast : quarterX < quarterEast east) :
    segmentAt indexGrid stateGrid quarterX (quarterNorth north) =
      some .west := by
  apply segment_eq_west_of_horizontal_edges
    (valid.allowed quarterX (quarterNorth north))
  · exact (shaded.north_at cycle valid hwest heast).1
  · exact (shaded.north_at cycle valid hwest heast).2
  · exact quadrantAt_quarterNorth_yBit quarterX north

theorem CycleShade.west_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {quarterY : Nat}
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    segmentAt indexGrid stateGrid (quarterWest west) quarterY =
      some .south := by
  apply segment_eq_south_of_vertical_edges
    (valid.allowed (quarterWest west) quarterY)
  · exact (shaded.west_at cycle valid hsouth hnorth).1
  · exact (shaded.west_at cycle valid hsouth hnorth).2
  · exact quadrantAt_quarterWest_xBit west quarterY

theorem CycleShade.east_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {quarterY : Nat}
    (hsouth : quarterSouth south < quarterY)
    (hnorth : quarterY < quarterNorth north) :
    segmentAt indexGrid stateGrid (quarterEast east) quarterY =
      some .north := by
  apply segment_eq_north_of_vertical_edges
    (valid.allowed (quarterEast east) quarterY)
  · exact (shaded.east_at cycle valid hsouth hnorth).1
  · exact (shaded.east_at cycle valid hsouth hnorth).2
  · exact quadrantAt_quarterEast_xBit east quarterY

theorem CycleShade.southwest_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    segmentAt indexGrid stateGrid (quarterWest west) (quarterSouth south) =
      some .southEast := by
  let x := quarterWest west
  let y := quarterSouth south
  have heast : (stateGrid x y).east = some .light := shaded.southwest
  have hnorth : (stateGrid x y).north = some .light := by
    rw [← valid.east_north_corner_eq x y
      (CycleOn.southwest_corner cycle).1
      (CycleOn.southwest_corner cycle).2]
    exact heast
  apply segment_eq_southEast_of_turn_edges (valid.allowed x y) heast hnorth
  · simpa [x] using quadrantAt_quarterWest_xBit west y
  · simpa [y] using quadrantAt_quarterSouth_yBit x south

theorem CycleShade.southeast_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    segmentAt indexGrid stateGrid (quarterEast east) (quarterSouth south) =
      some .eastNorth := by
  let x := quarterEast east
  let y := quarterSouth south
  have hwest : (stateGrid x y).west = some .light := shaded.southeast
  have hnorth : (stateGrid x y).north = some .light := by
    rw [← valid.west_north_corner_eq x y
      (CycleOn.southeast_corner cycle).1
      (CycleOn.southeast_corner cycle).2]
    exact hwest
  apply segment_eq_eastNorth_of_turn_edges (valid.allowed x y) hwest hnorth
  · simpa [x] using quadrantAt_quarterEast_xBit east y
  · simpa [y] using quadrantAt_quarterSouth_yBit x south

theorem CycleShade.northeast_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    segmentAt indexGrid stateGrid (quarterEast east) (quarterNorth north) =
      some .northWest := by
  let x := quarterEast east
  let y := quarterNorth north
  have hwest : (stateGrid x y).west = some .light := shaded.northeast
  have hsouth : (stateGrid x y).south = some .light := by
    rw [← valid.west_south_corner_eq x y
      (CycleOn.northeast_corner cycle).1
      (CycleOn.northeast_corner cycle).2]
    exact hwest
  apply segment_eq_northWest_of_turn_edges (valid.allowed x y) hwest hsouth
  · simpa [x] using quadrantAt_quarterEast_xBit east y
  · simpa [y] using quadrantAt_quarterNorth_yBit x north

theorem CycleShade.northwest_segment
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    segmentAt indexGrid stateGrid (quarterWest west) (quarterNorth north) =
      some .westSouth := by
  let x := quarterWest west
  let y := quarterNorth north
  have heast : (stateGrid x y).east = some .light := shaded.northwest
  have hsouth : (stateGrid x y).south = some .light := by
    have hallowed := valid.allowed x y
    have heq := RedShades.east_south_corner_eq_of_allowed
      hallowed (CycleOn.northwest_corner cycle).1
        (CycleOn.northwest_corner cycle).2
    exact heq.symm.trans heast
  apply segment_eq_westSouth_of_turn_edges (valid.allowed x y) heast hsouth
  · simpa [x] using quadrantAt_quarterWest_xBit west y
  · simpa [y] using quadrantAt_quarterNorth_yBit x north

end OrientedLightBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
