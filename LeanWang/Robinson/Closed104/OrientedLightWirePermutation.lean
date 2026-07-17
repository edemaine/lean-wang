/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightOrbits

/-!
# The light-wire permutation

An occupied wire point records both its board coordinate and its unique local
segment.  Continuation and predecessor continuation define inverse maps on
this finite type, so each physical light-wire component is literally a cycle
of a finite permutation.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightWirePermutation

open OrientedRedCycles RedShadeCycles RedShadePaths
  OrientedLightSegments OrientedLightBoards OrientedLightComponents
  OrientedLightOrbits Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- An occupied light-wire coordinate and the segment occupying it. -/
abbrev WirePoint (indexGrid : Nat -> Nat -> Index)
    (stateGrid : Nat -> Nat -> RedShades.State)
    (west east south north : Nat) :=
  {entry : Prod (BoardPoint west east south north) Segment //
    segmentAtPoint indexGrid stateGrid entry.1 = some entry.2}

namespace WirePoint

def point {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    {west east south north : Nat}
    (wire : WirePoint indexGrid stateGrid west east south north) :
    BoardPoint west east south north :=
  wire.1.1

def segment {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    {west east south north : Nat}
    (wire : WirePoint indexGrid stateGrid west east south north) : Segment :=
  wire.1.2

theorem hsegment {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    {west east south north : Nat}
    (wire : WirePoint indexGrid stateGrid west east south north) :
    segmentAtPoint indexGrid stateGrid wire.point = some wire.segment :=
  wire.2

@[ext] theorem ext {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    {west east south north : Nat}
    {first second : WirePoint indexGrid stateGrid west east south north}
    (hpoint : first.point = second.point) : first = second := by
  apply Subtype.ext
  apply Prod.ext
  · exact hpoint
  · have hfirst := first.hsegment
    have hsecond := second.hsegment
    rw [hpoint] at hfirst
    exact Option.some.inj (hfirst.symm.trans hsecond)

end WirePoint

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

private def canAdvance
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    CanAdvance west east south north wire.point.x wire.point.y
      wire.segment.exit :=
  OrientedLightComponents.CycleShade.canAdvance shaded cycle valid
    wire.point.inBoard wire.hsegment

private theorem continued
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north)
    (canMove : CanAdvance west east south north wire.point.x wire.point.y
      wire.segment.exit) :
    exists nextSegment,
      segmentAtPoint indexGrid stateGrid
          (advance wire.point wire.segment.exit canMove) = some nextSegment /\
        nextSegment.entry = wire.segment.exit :=
  OrientedLightOrbits.ValidShadeGrid.segmentAtPoint_advance
    valid wire.hsegment canMove

/-- Follow the outgoing edge of an occupied light-wire point. -/
def next
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    WirePoint indexGrid stateGrid west east south north :=
  let canMove := canAdvance shaded cycle valid wire
  let hcontinued := continued valid wire canMove
  let nextSegment := Classical.choose hcontinued
  ⟨(advance wire.point wire.segment.exit canMove, nextSegment),
    (Classical.choose_spec hcontinued).1⟩

@[simp] theorem next_point
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    (next shaded cycle valid wire).point =
      advance wire.point wire.segment.exit
        (canAdvance shaded cycle valid wire) := rfl

theorem next_entry
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    (next shaded cycle valid wire).segment.entry = wire.segment.exit := by
  exact (Classical.choose_spec
    (continued valid wire (canAdvance shaded cycle valid wire))).2

private def canRetreat
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    CanRetreat west east south north wire.point.x wire.point.y
      wire.segment.entry :=
  OrientedLightComponents.CycleShade.canRetreat shaded cycle valid
    wire.point.inBoard wire.hsegment

private theorem preceded
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north)
    (canMove : CanRetreat west east south north wire.point.x wire.point.y
      wire.segment.entry) :
    exists previousSegment,
      segmentAtPoint indexGrid stateGrid
          (retreat wire.point wire.segment.entry canMove) =
        some previousSegment /\
      previousSegment.exit = wire.segment.entry :=
  OrientedLightOrbits.ValidShadeGrid.segmentAtPoint_retreat
    valid wire.hsegment canMove

/-- Follow the incoming edge of an occupied light-wire point backwards. -/
def previous
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    WirePoint indexGrid stateGrid west east south north :=
  let canMove := canRetreat shaded cycle valid wire
  let hpreceded := preceded valid wire canMove
  let previousSegment := Classical.choose hpreceded
  ⟨(retreat wire.point wire.segment.entry canMove, previousSegment),
    (Classical.choose_spec hpreceded).1⟩

@[simp] theorem previous_point
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    (previous shaded cycle valid wire).point =
      retreat wire.point wire.segment.entry
        (canRetreat shaded cycle valid wire) := rfl

theorem previous_exit
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    (previous shaded cycle valid wire).segment.exit = wire.segment.entry := by
  exact (Classical.choose_spec
    (preceded valid wire (canRetreat shaded cycle valid wire))).2

theorem previous_next
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    previous shaded cycle valid (next shaded cycle valid wire) = wire := by
  apply WirePoint.ext
  have canRetreatNext : CanRetreat west east south north
      (advance wire.point wire.segment.exit
        (canAdvance shaded cycle valid wire)).x
      (advance wire.point wire.segment.exit
        (canAdvance shaded cycle valid wire)).y wire.segment.exit := by
    simpa only [next_point, next_entry] using
      canRetreat shaded cycle valid (next shaded cycle valid wire)
  simpa only [previous_point, next_point, next_entry] using
    retreat_advance wire.point wire.segment.exit
      (canAdvance shaded cycle valid wire) canRetreatNext

theorem next_previous
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    next shaded cycle valid (previous shaded cycle valid wire) = wire := by
  apply WirePoint.ext
  have canAdvancePrevious : CanAdvance west east south north
      (retreat wire.point wire.segment.entry
        (canRetreat shaded cycle valid wire)).x
      (retreat wire.point wire.segment.entry
        (canRetreat shaded cycle valid wire)).y wire.segment.entry := by
    simpa only [previous_point, previous_exit] using
      canAdvance shaded cycle valid (previous shaded cycle valid wire)
  simpa only [next_point, previous_point, previous_exit] using
    advance_retreat wire.point wire.segment.entry
      (canRetreat shaded cycle valid wire) canAdvancePrevious

/-- The finite permutation whose cycles are the physical light-wire
components inside the board. -/
def permutation
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    Equiv.Perm (WirePoint indexGrid stateGrid west east south north) where
  toFun := next shaded cycle valid
  invFun := previous shaded cycle valid
  left_inv := previous_next shaded cycle valid
  right_inv := next_previous shaded cycle valid

end OrientedLightWirePermutation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
