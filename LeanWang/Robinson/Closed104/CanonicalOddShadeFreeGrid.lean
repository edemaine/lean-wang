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
  CanonicalOddShadeComparison ShadedFreeGrid

def coordinateAt (depth : Nat) (index : Fin (depth + 1)) : Nat :=
  CanonicalOddFreeLineCoordinates.coordinateAt depth
    (Fin.cast (coordinates_length depth).symm index)

theorem coordinateAt_mem (depth : Nat) (index : Fin (depth + 1)) :
    coordinateAt depth index ∈ coordinates depth :=
  CanonicalOddFreeLineCoordinates.coordinateAt_mem depth _

theorem coordinateAt_strictMono (depth : Nat)
    {first second : Fin (depth + 1)} (hlt : first < second) :
    coordinateAt depth first < coordinateAt depth second := by
  apply CanonicalOddFreeLineCoordinates.coordinateAt_strictMono depth
  simpa [Fin.cast] using hlt

@[simp] theorem coordinateAt_zero (depth : Nat) :
    coordinateAt depth (0 : Fin (depth + 1)) = 8 * 4 ^ depth + 1 := by
  unfold coordinateAt
  apply CanonicalOddFreeLineCoordinates.coordinateAt_zero

theorem coordinateAt_bounds (depth : Nat) (index : Fin (depth + 1)) :
    quarterSouth (scale depth) < coordinateAt depth index ∧
      coordinateAt depth index < quarterNorth (3 * scale depth) := by
  have bounds := CanonicalOddFreeLineCoordinates.coordinateAt_bounds depth
    (Fin.cast (coordinates_length depth).symm index)
  have eastScale : 3 * scale depth = 6 * 4 ^ depth := by
    unfold scale
    omega
  rw [eastScale]
  exact bounds

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
      (scale depth) (3 * scale depth) (depth + 1) where
  columnAt := coordinateAt depth
  rowAt := coordinateAt depth
  column_strictMono := coordinateAt_strictMono depth
  row_strictMono := coordinateAt_strictMono depth
  column_west := fun index => (coordinateAt_bounds depth index).1
  column_east := fun index => (coordinateAt_bounds depth index).2
  row_south := fun index => (coordinateAt_bounds depth index).1
  row_north := fun index => (coordinateAt_bounds depth index).2
  freeColumn := fun index => coordinate_isFreeColumn depth coarse states
    coarseRoot valid shaded (coordinateAt_mem depth index)
  freeRow := fun index => coordinate_isFreeRow depth coarse states
    coarseRoot valid shaded (coordinateAt_mem depth index)

end CanonicalOddShadeFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
