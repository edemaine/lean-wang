/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightWirePermutation

/-!
# Closed cycles of light wires

The light-wire permutation acts on a finite type.  Consequently every wire
point lies on a positive-period closed orbit.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightCycles

open OrientedRedCycles RedShadeCycles RedShadePaths
  OrientedLightSegments OrientedLightComponents OrientedLightOrbits
  OrientedLightWirePermutation Signals.FreeCellLocal

set_option maxRecDepth 20000

private def segmentAll : List Segment :=
  [.east, .north, .west, .south,
    .southEast, .eastNorth, .northWest, .westSouth]

private theorem segment_mem_all (segment : Segment) : segment ∈ segmentAll := by
  cases segment <;> decide

local instance : Fintype Segment :=
  Fintype.ofList segmentAll segment_mem_all

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

theorem next_ne_self
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    next shaded cycle valid wire ≠ wire := by
  intro heq
  have hpoint := congrArg WirePoint.point heq
  rw [next_point] at hpoint
  cases hexit : wire.segment.exit with
  | east =>
      have hx := congrArg BoardPoint.x hpoint
      simp only [hexit, advance_east_x] at hx
      omega
  | north =>
      have hy := congrArg BoardPoint.y hpoint
      simp only [hexit, advance_north_y] at hy
      omega
  | west =>
      have hmove := OrientedLightComponents.CycleShade.canAdvance
        shaded cycle valid wire.point.inBoard wire.hsegment
      simp only [hexit, CanAdvance] at hmove
      have hx := congrArg BoardPoint.x hpoint
      simp only [hexit, advance_west_x] at hx
      omega
  | south =>
      have hmove := OrientedLightComponents.CycleShade.canAdvance
        shaded cycle valid wire.point.inBoard wire.hsegment
      simp only [hexit, CanAdvance] at hmove
      have hy := congrArg BoardPoint.y hpoint
      simp only [hexit, advance_south_y] at hy
      omega

/-- Every occupied light-wire point belongs to a positive-period closed orbit. -/
theorem exists_positive_period
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    (wire : WirePoint indexGrid stateGrid west east south north) :
    exists period : Nat, 0 < period /\
      (permutation shaded cycle valid ^ period) wire = wire := by
  let perm := permutation shaded cycle valid
  refine ⟨orderOf perm, orderOf_pos perm, ?_⟩
  have hperiod := congrArg (fun sigma : Equiv.Perm
      (WirePoint indexGrid stateGrid west east south north) => sigma wire)
    (pow_orderOf_eq_one perm)
  change (perm ^ orderOf perm) wire = wire at hperiod
  simpa only [perm] using hperiod

end OrientedLightCycles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
