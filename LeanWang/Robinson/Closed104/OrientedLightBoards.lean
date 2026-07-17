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

private theorem segment_eq_of_entry_exit
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {entry exit : Direction} {target : Segment}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hentry : Enters quadrant state entry = true)
    (hexit : Exits quadrant state exit = true)
    (unique : forall segment, segment.entry = entry ->
      segment.exit = exit -> segment = target) :
    segment? component quadrant state = some target := by
  rcases (enters_iff_segment _ _ _ _ allowed).1 hentry with
    ⟨segment, hsegment, segmentEntry⟩
  rcases (exits_iff_segment _ _ _ _ allowed).1 hexit with
    ⟨other, hother, segmentExit⟩
  have heq : segment = other :=
    Option.some.inj (hsegment.symm.trans hother)
  subst other
  simpa [unique segment segmentEntry segmentExit] using hsegment

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
  apply segment_eq_of_entry_exit (entry := .south) (exit := .east)
    (target := .southEast) (valid.allowed x y)
  · have hx : (quadrantAt x y).xBit = true := by
      simpa [x] using quadrantAt_quarterWest_xBit west y
    simp only [Enters, hnorth, hx, decide_true, Bool.true_and]
  · have hy : (quadrantAt x y).yBit = true := by
      simpa [y] using quadrantAt_quarterSouth_yBit x south
    simp only [Exits, heast, hy, decide_true, Bool.true_and]
  · intro segment hentry hexit
    cases segment <;> simp_all [Segment.entry, Segment.exit]

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
  apply segment_eq_of_entry_exit (entry := .east) (exit := .north)
    (target := .eastNorth) (valid.allowed x y)
  · have hy : (quadrantAt x y).yBit = true := by
      simpa [y] using quadrantAt_quarterSouth_yBit x south
    simp only [Enters, hwest, hy, decide_true, Bool.true_and]
  · have hx : (quadrantAt x y).xBit = false := by
      simpa [x] using quadrantAt_quarterEast_xBit east y
    simp only [Exits, hnorth, hx, decide_true, Bool.true_and]
  · intro segment hentry hexit
    cases segment <;> simp_all [Segment.entry, Segment.exit]

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
  apply segment_eq_of_entry_exit (entry := .north) (exit := .west)
    (target := .northWest) (valid.allowed x y)
  · have hx : (quadrantAt x y).xBit = false := by
      simpa [x] using quadrantAt_quarterEast_xBit east y
    simp only [Enters, hsouth, hx, decide_true, Bool.true_and]
  · have hy : (quadrantAt x y).yBit = false := by
      simpa [y] using quadrantAt_quarterNorth_yBit x north
    simp only [Exits, hwest, hy, decide_true, Bool.true_and]
  · intro segment hentry hexit
    cases segment <;> simp_all [Segment.entry, Segment.exit]

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
  apply segment_eq_of_entry_exit (entry := .west) (exit := .south)
    (target := .westSouth) (valid.allowed x y)
  · have hy : (quadrantAt x y).yBit = false := by
      simpa [y] using quadrantAt_quarterNorth_yBit x north
    simp only [Enters, heast, hy, decide_true, Bool.true_and]
  · have hx : (quadrantAt x y).xBit = true := by
      simpa [x] using quadrantAt_quarterWest_xBit west y
    simp only [Exits, hsouth, hx, decide_true, Bool.true_and]
  · intro segment hentry hexit
    cases segment <;> simp_all [Segment.entry, Segment.exit]

end OrientedLightBoards
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
