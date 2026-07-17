/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightComponents

/-!
# Finite orbits of directed light wires

Inside a light board, advancing through a segment and retreating through its
successor are inverse operations.  Empty cells are fixed.  Thus the physical
light-wire components form the cycles of one finite permutation.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightOrbits

open OrientedRedCycles RedShadeCycles RedShadePaths
  OrientedLightSegments OrientedLightBoards OrientedLightComponents
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Quarter-grid coordinates in the closed board rectangle.  The `Fin`
coordinates supply the upper bounds, while the subtype stores the lower
bounds. -/
abbrev BoardPoint (west east south north : Nat) :=
  {point : Prod (Fin (quarterEast east + 1)) (Fin (quarterNorth north + 1)) //
    quarterWest west <= point.1.val /\ quarterSouth south <= point.2.val}

namespace BoardPoint

def x {west east south north : Nat}
    (point : BoardPoint west east south north) : Nat :=
  point.1.1.val

def y {west east south north : Nat}
    (point : BoardPoint west east south north) : Nat :=
  point.1.2.val

def mk {west east south north x y : Nat}
    (hwest : quarterWest west <= x) (heast : x <= quarterEast east)
    (hsouth : quarterSouth south <= y) (hnorth : y <= quarterNorth north) :
    BoardPoint west east south north :=
  ⟨(⟨x, Nat.lt_succ_of_le heast⟩, ⟨y, Nat.lt_succ_of_le hnorth⟩),
    hwest, hsouth⟩

@[simp] theorem x_mk {west east south north x y : Nat}
    (hwest : quarterWest west <= x) (heast : x <= quarterEast east)
    (hsouth : quarterSouth south <= y) (hnorth : y <= quarterNorth north) :
    (mk hwest heast hsouth hnorth :
      BoardPoint west east south north).x = x := rfl

@[simp] theorem y_mk {west east south north x y : Nat}
    (hwest : quarterWest west <= x) (heast : x <= quarterEast east)
    (hsouth : quarterSouth south <= y) (hnorth : y <= quarterNorth north) :
    (mk hwest heast hsouth hnorth :
      BoardPoint west east south north).y = y := rfl

theorem inBoard {west east south north : Nat}
    (point : BoardPoint west east south north) :
    InBoard west east south north point.x point.y := by
  refine ⟨point.2.1, ?_, point.2.2, ?_⟩
  · change point.1.1.val <= quarterEast east
    exact Nat.le_of_lt_succ point.1.1.isLt
  · change point.1.2.val <= quarterNorth north
    exact Nat.le_of_lt_succ point.1.2.isLt

@[ext] theorem ext {west east south north : Nat}
    {first second : BoardPoint west east south north}
    (hx : first.x = second.x) (hy : first.y = second.y) :
    first = second := by
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hx
  · exact Fin.ext hy

end BoardPoint

/-- Move one grid edge in the outgoing direction. -/
def advance {west east south north : Nat}
    (point : BoardPoint west east south north) (direction : Direction)
    (canMove : CanAdvance west east south north point.x point.y direction) :
    BoardPoint west east south north :=
  match direction with
  | .east => BoardPoint.mk (x := point.x + 1) (y := point.y) (by
      have hwest : quarterWest west <= point.x := point.2.1
      omega) (by
      simp only [CanAdvance] at canMove
      omega) point.2.2 point.inBoard.le_north
  | .north => BoardPoint.mk (x := point.x) (y := point.y + 1)
      point.2.1 point.inBoard.le_east (by
        have hsouth : quarterSouth south <= point.y := point.2.2
        omega) (by
        simp only [CanAdvance] at canMove
        omega)
  | .west => BoardPoint.mk (x := point.x - 1) (y := point.y) (by
      simp only [CanAdvance] at canMove
      omega) (by
      have := point.inBoard.le_east
      omega) point.2.2 point.inBoard.le_north
  | .south => BoardPoint.mk (x := point.x) (y := point.y - 1)
      point.2.1 point.inBoard.le_east (by
        simp only [CanAdvance] at canMove
        omega) (by
        have := point.inBoard.le_north
        omega)

/-- Move one grid edge backwards along an incoming direction. -/
def retreat {west east south north : Nat}
    (point : BoardPoint west east south north) (direction : Direction)
    (canMove : CanRetreat west east south north point.x point.y direction) :
    BoardPoint west east south north :=
  match direction with
  | .east => BoardPoint.mk (x := point.x - 1) (y := point.y) (by
      simp only [CanRetreat] at canMove
      omega) (by
      have := point.inBoard.le_east
      omega) point.2.2 point.inBoard.le_north
  | .north => BoardPoint.mk (x := point.x) (y := point.y - 1)
      point.2.1 point.inBoard.le_east (by
        simp only [CanRetreat] at canMove
        omega) (by
        have := point.inBoard.le_north
        omega)
  | .west => BoardPoint.mk (x := point.x + 1) (y := point.y) (by
      have hwest : quarterWest west <= point.x := point.2.1
      omega) (by
      simp only [CanRetreat] at canMove
      omega) point.2.2 point.inBoard.le_north
  | .south => BoardPoint.mk (x := point.x) (y := point.y + 1)
      point.2.1 point.inBoard.le_east (by
        have hsouth : quarterSouth south <= point.y := point.2.2
        omega) (by
        simp only [CanRetreat] at canMove
        omega)

@[simp] theorem advance_east_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .east) :
    (advance point .east canMove).x = point.x + 1 := rfl

@[simp] theorem advance_east_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .east) :
    (advance point .east canMove).y = point.y := rfl

@[simp] theorem advance_north_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .north) :
    (advance point .north canMove).x = point.x := rfl

@[simp] theorem advance_north_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .north) :
    (advance point .north canMove).y = point.y + 1 := rfl

@[simp] theorem advance_west_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .west) :
    (advance point .west canMove).x = point.x - 1 := rfl

@[simp] theorem advance_west_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .west) :
    (advance point .west canMove).y = point.y := rfl

@[simp] theorem advance_south_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .south) :
    (advance point .south canMove).x = point.x := rfl

@[simp] theorem advance_south_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanAdvance west east south north point.x point.y .south) :
    (advance point .south canMove).y = point.y - 1 := rfl

@[simp] theorem retreat_east_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .east) :
    (retreat point .east canMove).x = point.x - 1 := rfl

@[simp] theorem retreat_east_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .east) :
    (retreat point .east canMove).y = point.y := rfl

@[simp] theorem retreat_north_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .north) :
    (retreat point .north canMove).x = point.x := rfl

@[simp] theorem retreat_north_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .north) :
    (retreat point .north canMove).y = point.y - 1 := rfl

@[simp] theorem retreat_west_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .west) :
    (retreat point .west canMove).x = point.x + 1 := rfl

@[simp] theorem retreat_west_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .west) :
    (retreat point .west canMove).y = point.y := rfl

@[simp] theorem retreat_south_x {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .south) :
    (retreat point .south canMove).x = point.x := rfl

@[simp] theorem retreat_south_y {west east south north : Nat}
    (point : BoardPoint west east south north)
    (canMove : CanRetreat west east south north point.x point.y .south) :
    (retreat point .south canMove).y = point.y + 1 := rfl

theorem retreat_advance {west east south north : Nat}
    (point : BoardPoint west east south north) (direction : Direction)
    (canAdvance : CanAdvance west east south north point.x point.y direction)
    (canRetreat : CanRetreat west east south north
      (advance point direction canAdvance).x
      (advance point direction canAdvance).y direction) :
    retreat (advance point direction canAdvance) direction canRetreat = point := by
  cases direction with
  | east =>
      apply BoardPoint.ext
      · simp only [retreat_east_x, advance_east_x]
        omega
      · simp only [retreat_east_y, advance_east_y]
  | north =>
      apply BoardPoint.ext
      · simp only [retreat_north_x, advance_north_x]
      · simp only [retreat_north_y, advance_north_y]
        omega
  | west =>
      apply BoardPoint.ext
      · simp only [retreat_west_x, advance_west_x]
        simp only [CanAdvance] at canAdvance
        omega
      · simp only [retreat_west_y, advance_west_y]
  | south =>
      apply BoardPoint.ext
      · simp only [retreat_south_x, advance_south_x]
      · simp only [retreat_south_y, advance_south_y]
        simp only [CanAdvance] at canAdvance
        omega

theorem advance_retreat {west east south north : Nat}
    (point : BoardPoint west east south north) (direction : Direction)
    (canRetreat : CanRetreat west east south north point.x point.y direction)
    (canAdvance : CanAdvance west east south north
      (retreat point direction canRetreat).x
      (retreat point direction canRetreat).y direction) :
    advance (retreat point direction canRetreat) direction canAdvance = point := by
  cases direction with
  | east =>
      apply BoardPoint.ext
      · simp only [advance_east_x, retreat_east_x]
        simp only [CanRetreat] at canRetreat
        omega
      · simp only [advance_east_y, retreat_east_y]
  | north =>
      apply BoardPoint.ext
      · simp only [advance_north_x, retreat_north_x]
      · simp only [advance_north_y, retreat_north_y]
        simp only [CanRetreat] at canRetreat
        omega
  | west =>
      apply BoardPoint.ext
      · simp only [advance_west_x, retreat_west_x]
        omega
      · simp only [advance_west_y, retreat_west_y]
  | south =>
      apply BoardPoint.ext
      · simp only [advance_south_x, retreat_south_x]
      · simp only [advance_south_y, retreat_south_y]
        omega

def segmentAtPoint (indexGrid : Nat -> Nat -> Index)
    (stateGrid : Nat -> Nat -> RedShades.State)
    {west east south north : Nat}
    (point : BoardPoint west east south north) : Option Segment :=
  segmentAt indexGrid stateGrid point.x point.y

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

private theorem segmentAt_advance_direction
    (valid : ValidShadeGrid indexGrid stateGrid)
    {point : BoardPoint west east south north} {segment : Segment}
    {direction : Direction}
    (hsegment : segmentAtPoint indexGrid stateGrid point = some segment)
    (hexit : segment.exit = direction)
    (canMove : CanAdvance west east south north point.x point.y direction) :
    exists nextSegment,
      segmentAtPoint indexGrid stateGrid
          (advance point direction canMove) = some nextSegment /\
        nextSegment.entry = direction := by
  cases direction with
  | east =>
      simpa only [segmentAtPoint, advance_east_x, advance_east_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_east valid hsegment hexit
  | north =>
      simpa only [segmentAtPoint, advance_north_x, advance_north_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_north valid hsegment hexit
  | west =>
      have hx : 0 < point.x := by
        have hwest := point.inBoard.west_le
        simp [quarterWest] at hwest
        omega
      simpa only [segmentAtPoint, advance_west_x, advance_west_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_west valid hx hsegment hexit
  | south =>
      have hy : 0 < point.y := by
        have hsouth := point.inBoard.south_le
        simp [quarterSouth] at hsouth
        omega
      simpa only [segmentAtPoint, advance_south_x, advance_south_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_south valid hy hsegment hexit

theorem ValidShadeGrid.segmentAtPoint_advance
    (valid : ValidShadeGrid indexGrid stateGrid)
    {point : BoardPoint west east south north} {segment : Segment}
    (hsegment : segmentAtPoint indexGrid stateGrid point = some segment)
    (canMove : CanAdvance west east south north point.x point.y segment.exit) :
    exists nextSegment,
      segmentAtPoint indexGrid stateGrid
          (advance point segment.exit canMove) = some nextSegment /\
        nextSegment.entry = segment.exit :=
  segmentAt_advance_direction valid hsegment rfl canMove

private theorem segmentAt_retreat_direction
    (valid : ValidShadeGrid indexGrid stateGrid)
    {point : BoardPoint west east south north} {segment : Segment}
    {direction : Direction}
    (hsegment : segmentAtPoint indexGrid stateGrid point = some segment)
    (hentry : segment.entry = direction)
    (canMove : CanRetreat west east south north point.x point.y direction) :
    exists previousSegment,
      segmentAtPoint indexGrid stateGrid
          (retreat point direction canMove) = some previousSegment /\
        previousSegment.exit = direction := by
  cases direction with
  | east =>
      have hx : 0 < point.x := by
        have hwest := point.inBoard.west_le
        simp [quarterWest] at hwest
        omega
      simpa only [segmentAtPoint, retreat_east_x, retreat_east_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_predecessor_east valid hx hsegment hentry
  | north =>
      have hy : 0 < point.y := by
        have hsouth := point.inBoard.south_le
        simp [quarterSouth] at hsouth
        omega
      simpa only [segmentAtPoint, retreat_north_x, retreat_north_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_predecessor_north valid hy hsegment hentry
  | west =>
      simpa only [segmentAtPoint, retreat_west_x, retreat_west_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_predecessor_west valid hsegment hentry
  | south =>
      simpa only [segmentAtPoint, retreat_south_x, retreat_south_y] using
        OrientedLightSegments.ValidShadeGrid.segmentAt_predecessor_south valid hsegment hentry

theorem ValidShadeGrid.segmentAtPoint_retreat
    (valid : ValidShadeGrid indexGrid stateGrid)
    {point : BoardPoint west east south north} {segment : Segment}
    (hsegment : segmentAtPoint indexGrid stateGrid point = some segment)
    (canMove : CanRetreat west east south north point.x point.y segment.entry) :
    exists previousSegment,
      segmentAtPoint indexGrid stateGrid
          (retreat point segment.entry canMove) = some previousSegment /\
        previousSegment.exit = segment.entry :=
  segmentAt_retreat_direction valid hsegment rfl canMove

end OrientedLightOrbits
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
