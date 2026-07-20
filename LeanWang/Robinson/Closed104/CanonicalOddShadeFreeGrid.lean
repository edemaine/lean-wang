/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeComparison
import LeanWang.Robinson.Closed104.ShadedFreeGrid

/-! Free grids obtained from the canonical odd shade comparison. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeFreeGrid

open RedShadeCycles RedShadeGraph RedShadePaths CanonicalOddFreeLineCoordinates
  CanonicalOddShadeComparison CanonicalShadeComparisonCore ShadedFreeGrid

abbrev coordinateAt (depth : Nat) (index : Fin (depth + 1)) : Nat :=
  CanonicalOddFreeLineCoordinates.coordinateAt depth
    (Fin.cast (coordinates_length depth).symm index)

@[simp] theorem coordinateAt_zero (depth : Nat) :
    coordinateAt depth (0 : Fin (depth + 1)) = 8 * 4 ^ depth + 1 := by
  unfold coordinateAt
  apply CanonicalOddFreeLineCoordinates.coordinateAt_zero

private def orderedCoordinates (depth : Nat) :
    PhaseComparison.OrderedCoordinates (scale depth) (depth + 1)
      (coordinates depth) where
  coord := coordinateAt depth
  mem_coord := fun index => CanonicalOddFreeLineCoordinates.coordinateAt_mem depth _
  strictMono := by
    intro first second hlt
    apply CanonicalOddFreeLineCoordinates.coordinateAt_strictMono depth
    simpa [Fin.cast] using hlt
  bounds := by
    intro index
    have bounds := CanonicalOddFreeLineCoordinates.coordinateAt_bounds depth
      (Fin.cast (coordinates_length depth).symm index)
    simpa only [coordinateAt, scale,
      show 3 * (2 * 4 ^ depth) = 6 * 4 ^ depth by omega] using bounds

/-- The canonical odd coordinate family interpreted in an arbitrary valid
light-root shade assignment. -/
def freeGrid (depth : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid depth coarse) states)
    (shaded : CycleShade states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) .light) :
    FreeGrid (actualGrid depth coarse) states
      (scale depth) (3 * scale depth)
      (scale depth) (3 * scale depth) (depth + 1) :=
  (freeCoordinates depth coarse states coarseRoot valid shaded)
    |>.toFreeGrid (orderedCoordinates depth)

end CanonicalOddShadeFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
