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
  CanonicalShadeComparisonCore
  ShadedFreeGrid ShadedSubstitution

set_option maxRecDepth 20000

abbrev coordinateAt (depth : Nat) (index : Fin (depth + 1)) : Nat :=
  CanonicalFreeLineCoordinates.coordinateAt depth
    (Fin.cast (coordinates_length depth).symm index)

@[simp] theorem coordinateAt_zero (depth : Nat) :
    coordinateAt depth (0 : Fin (depth + 1)) = 4 * 4 ^ depth + 1 := by
  unfold coordinateAt
  apply CanonicalFreeLineCoordinates.coordinateAt_zero

private def orderedCoordinates (depth : Nat) :
    PhaseComparison.OrderedCoordinates (scale depth) (depth + 1)
      (coordinates depth) where
  coord := coordinateAt depth
  mem_coord := fun index => CanonicalFreeLineCoordinates.coordinateAt_mem depth _
  strictMono := by
    intro first second hlt
    apply CanonicalFreeLineCoordinates.coordinateAt_strictMono depth
    simpa [Fin.cast] using hlt
  bounds := by
    intro index
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
      (scale depth) (3 * scale depth) (depth + 1) :=
  (freeCoordinates depth coarse states root coarseRoot rootParent
    valid shaded).toFreeGrid (orderedCoordinates depth)

end CanonicalShadeFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
