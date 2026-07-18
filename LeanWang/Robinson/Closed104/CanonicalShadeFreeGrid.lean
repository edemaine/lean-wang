/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeComparison
import LeanWang.Robinson.Closed104.ShadedFreeGrid

/-!
# Free grids from canonical shade comparison

The direct base-four coordinate family is packaged as the `FreeGrid` expected
by the routed-signal argument.  No graph-path recurrence appears here: shade
comparison has already transferred each canonical free line to the arbitrary
valid assignment.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalShadeFreeGrid

open OrientedRedCycles RedShadePaths RedShadeCycles RedShadeGraph
  CanonicalFreeLineCoordinates CanonicalShadeComparison
  ShadedFreeGrid ShadedSubstitution

set_option maxRecDepth 20000

def coordinateAt (depth : Nat) (index : Fin (depth + 1)) : Nat :=
  CanonicalFreeLineCoordinates.coordinateAt depth
    (Fin.cast (coordinates_length depth).symm index)

theorem coordinateAt_mem (depth : Nat) (index : Fin (depth + 1)) :
    coordinateAt depth index ∈ coordinates depth :=
  CanonicalFreeLineCoordinates.coordinateAt_mem depth _

theorem coordinateAt_strictMono (depth : Nat)
    {first second : Fin (depth + 1)} (hlt : first < second) :
    coordinateAt depth first < coordinateAt depth second := by
  apply CanonicalFreeLineCoordinates.coordinateAt_strictMono depth
  simpa [Fin.cast] using hlt

@[simp] theorem coordinateAt_zero (depth : Nat) :
    coordinateAt depth (0 : Fin (depth + 1)) = 4 * 4 ^ depth + 1 := by
  unfold coordinateAt
  apply CanonicalFreeLineCoordinates.coordinateAt_zero

theorem coordinateAt_bounds (depth : Nat) (index : Fin (depth + 1)) :
    quarterSouth (scale depth) < coordinateAt depth index ∧
      coordinateAt depth index < quarterNorth (3 * scale depth) := by
  simpa [coordinateAt, scale] using
    (CanonicalFreeLineCoordinates.coordinateAt_bounds depth
      (Fin.cast (coordinates_length depth).symm index))

/-- The canonical coordinate family interpreted in an arbitrary valid
light-root shade assignment. -/
def freeGrid (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State) (root : Node)
    (coarseRoot : coarse 0 0 = 0) (rootParent : root.data.parent = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light) :
    FreeGrid (actualGrid depth coarse) states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) (depth + 1) where
  columnAt := coordinateAt depth
  rowAt := coordinateAt depth
  column_strictMono := coordinateAt_strictMono depth
  row_strictMono := coordinateAt_strictMono depth
  column_west := fun index => (coordinateAt_bounds depth index).1
  column_east := fun index => (coordinateAt_bounds depth index).2
  row_south := fun index => (coordinateAt_bounds depth index).1
  row_north := fun index => (coordinateAt_bounds depth index).2
  freeColumn := fun index => coordinate_isFreeColumn depth coarse states root
    coarseRoot rootParent valid shaded (coordinateAt_mem depth index)
  freeRow := fun index => coordinate_isFreeRow depth coarse states root
    coarseRoot rootParent valid shaded (coordinateAt_mem depth index)

end CanonicalShadeFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
