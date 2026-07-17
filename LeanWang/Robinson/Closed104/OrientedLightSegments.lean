/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignals
import LeanWang.Robinson.Closed104.RedShadePaths

/-!
# Directed light-red segments

The light part of an allowed shaded quarter tile is either absent, a straight
segment, or one of four left turns.  This small physical model deliberately
forgets the parity-changing crossing links used by the refinement search
graph: at a red crossing, exactly one of the two wires is light.

The finite local audit below is the only construction-specific input.  Its
grid lemmas say that matching shade edges continue a directed segment into
the neighboring quarter tile.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightSegments

open Figure16 RedCycles RedShadePaths Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Direction of travel with the square interior on the left. -/
inductive Direction where
  | east
  | north
  | west
  | south
deriving DecidableEq, Repr

namespace Direction

/-- A counterclockwise quarter turn. -/
def left : Direction -> Direction
  | .east => .north
  | .north => .west
  | .west => .south
  | .south => .east

@[simp] theorem left_left_left_left (direction : Direction) :
    direction.left.left.left.left = direction := by
  cases direction <;> rfl

end Direction

/-- The eight possible nonempty light-wire shapes in an allowed quarter. -/
inductive Segment where
  | east
  | north
  | west
  | south
  | southEast
  | eastNorth
  | northWest
  | westSouth
deriving DecidableEq, Repr

namespace Segment

def entry : Segment -> Direction
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south
  | .southEast => .south
  | .eastNorth => .east
  | .northWest => .north
  | .westSouth => .west

def exit : Segment -> Direction
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south
  | .southEast => .east
  | .eastNorth => .north
  | .northWest => .west
  | .westSouth => .south

/-- Every local segment goes straight or turns left. -/
theorem exit_eq_entry_or_left (segment : Segment) :
    segment.exit = segment.entry ∨
      segment.exit = segment.entry.left := by
  cases segment <;> simp [entry, exit, Direction.left]

end Segment

/-- Read the directed light segment from the two selected border values. -/
def segment? (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) : Option Segment :=
  match ShadedSignals.selectedVerticalFor component quadrant state,
      ShadedSignals.selectedHorizontalFor component quadrant state with
  | none, none => none
  | none, some .north => some .east
  | some .west, none => some .north
  | none, some .south => some .west
  | some .east, none => some .south
  | some .east, some .north => some .southEast
  | some .west, some .north => some .eastNorth
  | some .west, some .south => some .northWest
  | some .east, some .south => some .westSouth

/-- Local edge data saying that a light segment enters in this direction. -/
def Enters (quadrant : Quadrant) (state : RedShades.State) : Direction -> Bool
  | .east => decide (state.west = some .light) && decide (quadrant.yBit = true)
  | .north => decide (state.south = some .light) && decide (quadrant.xBit = false)
  | .west => decide (state.east = some .light) && decide (quadrant.yBit = false)
  | .south => decide (state.north = some .light) && decide (quadrant.xBit = true)

/-- Local edge data saying that a light segment exits in this direction. -/
def Exits (quadrant : Quadrant) (state : RedShades.State) : Direction -> Bool
  | .east => decide (state.east = some .light) && decide (quadrant.yBit = true)
  | .north => decide (state.north = some .light) && decide (quadrant.xBit = false)
  | .west => decide (state.west = some .light) && decide (quadrant.yBit = false)
  | .south => decide (state.south = some .light) && decide (quadrant.xBit = true)

private theorem thick_mem_all (component : Thick) : component ∈ Thick.all := by
  cases component <;> decide

private def directionAll : List Direction :=
  [.east, .north, .west, .south]

private theorem direction_mem_all (direction : Direction) :
    direction ∈ directionAll := by
  cases direction <;> decide

private def segmentAll : List Segment :=
  [.east, .north, .west, .south,
    .southEast, .eastNorth, .northWest, .westSouth]

private theorem segment_mem_all (segment : Segment) : segment ∈ segmentAll := by
  cases segment <;> decide

local instance : Fintype Thick := Fintype.ofList Thick.all thick_mem_all
local instance : Fintype Quadrant := Fintype.ofList Quadrant.all Quadrant.mem_all
local instance : Fintype RedShades.State :=
  Fintype.ofList RedShades.State.all RedShades.State.mem_all
local instance : Fintype Direction := Fintype.ofList directionAll direction_mem_all
local instance : Fintype Segment := Fintype.ofList segmentAll segment_mem_all

private def entersCheck (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) (direction : Direction) : Bool :=
  !RedShades.allowedFor component quadrant state ||
    Enters quadrant state direction ==
      segmentAll.any fun segment =>
        decide (segment? component quadrant state = some segment) &&
          decide (segment.entry = direction)

private def exitsCheck (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) (direction : Direction) : Bool :=
  !RedShades.allowedFor component quadrant state ||
    Exits quadrant state direction ==
      segmentAll.any fun segment =>
        decide (segment? component quadrant state = some segment) &&
          decide (segment.exit = direction)

private def allEntersValid : Bool :=
  Thick.all.all fun component =>
    Quadrant.all.all fun quadrant =>
      RedShades.State.all.all fun state =>
        directionAll.all fun direction =>
          entersCheck component quadrant state direction

private def allExitsValid : Bool :=
  Thick.all.all fun component =>
    Quadrant.all.all fun quadrant =>
      RedShades.State.all.all fun state =>
        directionAll.all fun direction =>
          exitsCheck component quadrant state direction

set_option linter.style.nativeDecide false in
private theorem allEntersValid_eq_true : allEntersValid = true := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem allExitsValid_eq_true : allExitsValid = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Finite local certificate: an incoming light edge determines exactly the
directed segment that uses it. -/
theorem enters_iff_segment
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (direction : Direction)
    (allowed : RedShades.allowedFor component quadrant state = true) :
    Iff (Enters quadrant state direction = true)
      (Exists fun segment => And
        (segment? component quadrant state = some segment)
        (segment.entry = direction)) := by
  have hcomponent := List.all_eq_true.1 allEntersValid_eq_true
    component (thick_mem_all component)
  have hquadrant := List.all_eq_true.1 hcomponent
    quadrant (Quadrant.mem_all quadrant)
  have hstate := List.all_eq_true.1 hquadrant
    state (RedShades.State.mem_all state)
  have hdirection := List.all_eq_true.1 hstate
    direction (direction_mem_all direction)
  simp only [entersCheck, allowed, Bool.not_true, Bool.false_or,
    beq_iff_eq] at hdirection
  constructor
  · intro hentry
    have hany : (segmentAll.any fun segment =>
        decide (segment? component quadrant state = some segment) &&
          decide (segment.entry = direction)) = true := by
      rw [← hdirection]
      exact hentry
    rcases List.any_eq_true.1 hany with ⟨segment, _, hsegment⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsegment
    exact ⟨segment, hsegment⟩
  · rintro ⟨segment, hsegment, hentry⟩
    rw [hdirection]
    apply List.any_eq_true.2
    exact ⟨segment, segment_mem_all segment, by simp [hsegment, hentry]⟩

set_option linter.style.nativeDecide false in
/-- Finite local certificate: an outgoing light edge determines exactly the
directed segment that uses it. -/
theorem exits_iff_segment
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (direction : Direction)
    (allowed : RedShades.allowedFor component quadrant state = true) :
    Iff (Exits quadrant state direction = true)
      (Exists fun segment => And
        (segment? component quadrant state = some segment)
        (segment.exit = direction)) := by
  have hcomponent := List.all_eq_true.1 allExitsValid_eq_true
    component (thick_mem_all component)
  have hquadrant := List.all_eq_true.1 hcomponent
    quadrant (Quadrant.mem_all quadrant)
  have hstate := List.all_eq_true.1 hquadrant
    state (RedShades.State.mem_all state)
  have hdirection := List.all_eq_true.1 hstate
    direction (direction_mem_all direction)
  simp only [exitsCheck, allowed, Bool.not_true, Bool.false_or,
    beq_iff_eq] at hdirection
  constructor
  · intro hexit
    have hany : (segmentAll.any fun segment =>
        decide (segment? component quadrant state = some segment) &&
          decide (segment.exit = direction)) = true := by
      rw [← hdirection]
      exact hexit
    rcases List.any_eq_true.1 hany with ⟨segment, _, hsegment⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsegment
    exact ⟨segment, hsegment⟩
  · rintro ⟨segment, hsegment, hexit⟩
    rw [hdirection]
    apply List.any_eq_true.2
    exact ⟨segment, segment_mem_all segment, by simp [hsegment, hexit]⟩

theorem selectedHorizontal_eq_north_of_exit_east
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    {segment : Segment}
    (hsegment : segment? component quadrant state = some segment)
    (hexit : segment.exit = .east) :
    ShadedSignals.selectedHorizontalFor component quadrant state =
      some .north := by
  revert component quadrant state segment
  native_decide

theorem selectedHorizontal_eq_south_of_exit_west
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    {segment : Segment}
    (hsegment : segment? component quadrant state = some segment)
    (hexit : segment.exit = .west) :
    ShadedSignals.selectedHorizontalFor component quadrant state =
      some .south := by
  revert component quadrant state segment
  native_decide

theorem selectedVertical_eq_west_of_exit_north
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    {segment : Segment}
    (hsegment : segment? component quadrant state = some segment)
    (hexit : segment.exit = .north) :
    ShadedSignals.selectedVerticalFor component quadrant state =
      some .west := by
  revert component quadrant state segment
  native_decide

theorem selectedVertical_eq_east_of_exit_south
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    {segment : Segment}
    (hsegment : segment? component quadrant state = some segment)
    (hexit : segment.exit = .south) :
    ShadedSignals.selectedVerticalFor component quadrant state =
      some .east := by
  revert component quadrant state segment
  native_decide

@[simp] theorem quadrantAt_xBit (x y : Nat) :
    (quadrantAt x y).xBit = (x % 2 == 1) := by
  cases hx : (x % 2 == 1) <;> cases hy : (y % 2 == 1) <;>
    simp [quadrantAt, hx, hy, Quadrant.ofBits, Quadrant.xBit]

@[simp] theorem quadrantAt_yBit (x y : Nat) :
    (quadrantAt x y).yBit = (y % 2 == 1) := by
  cases hx : (x % 2 == 1) <;> cases hy : (y % 2 == 1) <;>
    simp [quadrantAt, hx, hy, Quadrant.ofBits, Quadrant.yBit]

/-- Directed segment at an absolute quarter-grid coordinate. -/
def segmentAt (indexGrid : Nat -> Nat -> Index)
    (stateGrid : Nat -> Nat -> RedShades.State) (x y : Nat) : Option Segment :=
  segment? (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y)

theorem ValidShadeGrid.segmentAt_east
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x y : Nat} {segment : Segment}
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .east) :
    ∃ next, segmentAt indexGrid stateGrid (x + 1) y = some next ∧
      next.entry = .east := by
  have hexits : Exits (quadrantAt x y) (stateGrid x y) .east = true :=
    (exits_iff_segment _ _ _ _ (valid.allowed x y)).2
      ⟨segment, hsegment, hexit⟩
  simp only [Exits, Bool.and_eq_true, decide_eq_true_eq] at hexits
  have henters : Enters (quadrantAt (x + 1) y) (stateGrid (x + 1) y) .east = true := by
    simp only [Enters, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · exact (valid.hmatch x y).symm.trans hexits.1
    · simpa only [quadrantAt_yBit] using hexits.2
  exact (enters_iff_segment _ _ _ _ (valid.allowed (x + 1) y)).1 henters

theorem ValidShadeGrid.segmentAt_north
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x y : Nat} {segment : Segment}
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .north) :
    ∃ next, segmentAt indexGrid stateGrid x (y + 1) = some next ∧
      next.entry = .north := by
  have hexits : Exits (quadrantAt x y) (stateGrid x y) .north = true :=
    (exits_iff_segment _ _ _ _ (valid.allowed x y)).2
      ⟨segment, hsegment, hexit⟩
  simp only [Exits, Bool.and_eq_true, decide_eq_true_eq] at hexits
  have henters : Enters (quadrantAt x (y + 1)) (stateGrid x (y + 1)) .north = true := by
    simp only [Enters, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · exact (valid.vmatch x y).symm.trans hexits.1
    · simpa only [quadrantAt_xBit] using hexits.2
  exact (enters_iff_segment _ _ _ _ (valid.allowed x (y + 1))).1 henters

theorem ValidShadeGrid.segmentAt_west
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x y : Nat} {segment : Segment}
    (hx : 0 < x)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .west) :
    ∃ next, segmentAt indexGrid stateGrid (x - 1) y = some next ∧
      next.entry = .west := by
  have hexits : Exits (quadrantAt x y) (stateGrid x y) .west = true :=
    (exits_iff_segment _ _ _ _ (valid.allowed x y)).2
      ⟨segment, hsegment, hexit⟩
  simp only [Exits, Bool.and_eq_true, decide_eq_true_eq] at hexits
  have hmatch := valid.hmatch (x - 1) y
  have hx' : x - 1 + 1 = x := by omega
  rw [hx'] at hmatch
  have henters : Enters (quadrantAt (x - 1) y) (stateGrid (x - 1) y) .west = true := by
    simp only [Enters, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · exact hmatch.trans hexits.1
    · simpa only [quadrantAt_yBit] using hexits.2
  exact (enters_iff_segment _ _ _ _ (valid.allowed (x - 1) y)).1 henters

theorem ValidShadeGrid.segmentAt_south
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x y : Nat} {segment : Segment}
    (hy : 0 < y)
    (hsegment : segmentAt indexGrid stateGrid x y = some segment)
    (hexit : segment.exit = .south) :
    ∃ next, segmentAt indexGrid stateGrid x (y - 1) = some next ∧
      next.entry = .south := by
  have hexits : Exits (quadrantAt x y) (stateGrid x y) .south = true :=
    (exits_iff_segment _ _ _ _ (valid.allowed x y)).2
      ⟨segment, hsegment, hexit⟩
  simp only [Exits, Bool.and_eq_true, decide_eq_true_eq] at hexits
  have hmatch := valid.vmatch x (y - 1)
  have hy' : y - 1 + 1 = y := by omega
  rw [hy'] at hmatch
  have henters : Enters (quadrantAt x (y - 1)) (stateGrid x (y - 1)) .south = true := by
    simp only [Enters, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · exact hmatch.trans hexits.1
    · simpa only [quadrantAt_xBit] using hexits.2
  exact (enters_iff_segment _ _ _ _ (valid.allowed x (y - 1))).1 henters

end OrientedLightSegments
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
