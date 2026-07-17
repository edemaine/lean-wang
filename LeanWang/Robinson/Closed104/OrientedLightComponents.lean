/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightBoards

/-!
# Light-wire components inside a Robinson board

The exact counterclockwise board boundary traps every directed light segment.
This file packages the boundary argument in the form needed to turn local
segment continuation into finite components.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightComponents

open OrientedRedCycles RedShadeCycles RedShadePaths
  OrientedLightSegments OrientedLightBoards Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A quarter-grid coordinate in the closed rectangle bounded by a board. -/
structure InBoard (west east south north x y : Nat) : Prop where
  west_le : quarterWest west <= x
  le_east : x <= quarterEast east
  south_le : quarterSouth south <= y
  le_north : y <= quarterNorth north

/-- There is room to advance one grid edge in a direction while staying in
the closed board rectangle. -/
def CanAdvance (west east south north x y : Nat) : Direction -> Prop
  | .east => x < quarterEast east
  | .north => y < quarterNorth north
  | .west => quarterWest west < x
  | .south => quarterSouth south < y

/-- There is room to follow an incoming direction backwards by one grid edge
while staying in the closed board rectangle. -/
def CanRetreat (west east south north x y : Nat) : Direction -> Prop
  | .east => quarterWest west < x
  | .north => quarterSouth south < y
  | .west => x < quarterEast east
  | .south => y < quarterNorth north

private theorem segment_eq_of_values {value : Option Segment}
    {first second : Segment}
    (hfirst : value = some first) (hsecond : value = some second) :
    first = second := by
  exact Option.some.inj (hfirst.symm.trans hsecond)

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north x y : Nat}
  {segment : Segment}

theorem CycleShade.exit_east_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .east) :
    x < quarterEast east := by
  by_contra hx
  have hx' : x = quarterEast east := by
    have hle := inside.le_east
    omega
  subst x
  rcases eq_or_lt_of_le inside.south_le with hbottom | habove
  · subst y
    have hshape := OrientedLightBoards.CycleShade.southeast_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.exit] at hexit
  · rcases eq_or_lt_of_le inside.le_north with htop | hbelow
    · subst y
      have hshape := OrientedLightBoards.CycleShade.northeast_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit
    · have hshape := OrientedLightBoards.CycleShade.east_segment shaded cycle valid habove hbelow
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit

theorem CycleShade.exit_north_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .north) :
    y < quarterNorth north := by
  by_contra hy
  have hy' : y = quarterNorth north := by
    have hle := inside.le_north
    omega
  subst y
  rcases eq_or_lt_of_le inside.west_le with hleft | hright
  · subst x
    have hshape := OrientedLightBoards.CycleShade.northwest_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.exit] at hexit
  · rcases eq_or_lt_of_le inside.le_east with hrightEdge | hinside
    · subst x
      have hshape := OrientedLightBoards.CycleShade.northeast_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit
    · have hshape := OrientedLightBoards.CycleShade.north_segment shaded cycle valid hright hinside
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit

theorem CycleShade.exit_west_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .west) :
    quarterWest west < x := by
  by_contra hx
  have hx' : x = quarterWest west := by
    have hle := inside.west_le
    omega
  subst x
  rcases eq_or_lt_of_le inside.south_le with hbottom | habove
  · subst y
    have hshape := OrientedLightBoards.CycleShade.southwest_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.exit] at hexit
  · rcases eq_or_lt_of_le inside.le_north with htop | hbelow
    · subst y
      have hshape := OrientedLightBoards.CycleShade.northwest_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit
    · have hshape := OrientedLightBoards.CycleShade.west_segment shaded cycle valid habove hbelow
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit

theorem CycleShade.exit_south_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .south) :
    quarterSouth south < y := by
  by_contra hy
  have hy' : y = quarterSouth south := by
    have hle := inside.south_le
    omega
  subst y
  rcases eq_or_lt_of_le inside.west_le with hleft | hright
  · subst x
    have hshape := OrientedLightBoards.CycleShade.southwest_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.exit] at hexit
  · rcases eq_or_lt_of_le inside.le_east with hrightEdge | hinside
    · subst x
      have hshape := OrientedLightBoards.CycleShade.southeast_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit
    · have hshape := OrientedLightBoards.CycleShade.south_segment shaded cycle valid hright hinside
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.exit] at hexit

theorem CycleShade.entry_east_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hentry : segment.entry = .east) :
    quarterWest west < x := by
  by_contra hx
  have hx' : x = quarterWest west := by
    have hle := inside.west_le
    omega
  subst x
  rcases eq_or_lt_of_le inside.south_le with hbottom | habove
  · subst y
    have hshape := OrientedLightBoards.CycleShade.southwest_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.entry] at hentry
  · rcases eq_or_lt_of_le inside.le_north with htop | hbelow
    · subst y
      have hshape := OrientedLightBoards.CycleShade.northwest_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry
    · have hshape := OrientedLightBoards.CycleShade.west_segment shaded cycle valid habove hbelow
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry

theorem CycleShade.entry_north_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hentry : segment.entry = .north) :
    quarterSouth south < y := by
  by_contra hy
  have hy' : y = quarterSouth south := by
    have hle := inside.south_le
    omega
  subst y
  rcases eq_or_lt_of_le inside.west_le with hleft | hright
  · subst x
    have hshape := OrientedLightBoards.CycleShade.southwest_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.entry] at hentry
  · rcases eq_or_lt_of_le inside.le_east with hrightEdge | hinside
    · subst x
      have hshape := OrientedLightBoards.CycleShade.southeast_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry
    · have hshape := OrientedLightBoards.CycleShade.south_segment shaded cycle valid hright hinside
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry

theorem CycleShade.entry_west_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hentry : segment.entry = .west) :
    x < quarterEast east := by
  by_contra hx
  have hx' : x = quarterEast east := by
    have hle := inside.le_east
    omega
  subst x
  rcases eq_or_lt_of_le inside.south_le with hbottom | habove
  · subst y
    have hshape := OrientedLightBoards.CycleShade.southeast_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.entry] at hentry
  · rcases eq_or_lt_of_le inside.le_north with htop | hbelow
    · subst y
      have hshape := OrientedLightBoards.CycleShade.northeast_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry
    · have hshape := OrientedLightBoards.CycleShade.east_segment shaded cycle valid habove hbelow
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry

theorem CycleShade.entry_south_lt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hentry : segment.entry = .south) :
    y < quarterNorth north := by
  by_contra hy
  have hy' : y = quarterNorth north := by
    have hle := inside.le_north
    omega
  subst y
  rcases eq_or_lt_of_le inside.west_le with hleft | hright
  · subst x
    have hshape := OrientedLightBoards.CycleShade.northwest_segment shaded cycle valid
    have := segment_eq_of_values hsegment hshape
    subst segment
    simp [Segment.entry] at hentry
  · rcases eq_or_lt_of_le inside.le_east with hrightEdge | hinside
    · subst x
      have hshape := OrientedLightBoards.CycleShade.northeast_segment shaded cycle valid
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry
    · have hshape := OrientedLightBoards.CycleShade.north_segment shaded cycle valid hright hinside
      have := segment_eq_of_values hsegment hshape
      subst segment
      simp [Segment.entry] at hentry

theorem CycleShade.canAdvance
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment) :
    CanAdvance west east south north x y segment.exit := by
  cases hexit : segment.exit with
  | east => exact CycleShade.exit_east_lt shaded cycle valid inside hsegment hexit
  | north => exact CycleShade.exit_north_lt shaded cycle valid inside hsegment hexit
  | west => exact CycleShade.exit_west_lt shaded cycle valid inside hsegment hexit
  | south => exact CycleShade.exit_south_lt shaded cycle valid inside hsegment hexit

theorem CycleShade.canRetreat
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (inside : InBoard west east south north x y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment) :
    CanRetreat west east south north x y segment.entry := by
  cases hentry : segment.entry with
  | east => exact CycleShade.entry_east_lt shaded cycle valid inside hsegment hentry
  | north => exact CycleShade.entry_north_lt shaded cycle valid inside hsegment hentry
  | west => exact CycleShade.entry_west_lt shaded cycle valid inside hsegment hentry
  | south => exact CycleShade.entry_south_lt shaded cycle valid inside hsegment hentry

end OrientedLightComponents
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
