/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeFreeGrid
import LeanWang.Robinson.Closed104.ShadedMarkedFreeGrid

/-!
# Marked free grids from canonical shade comparison

The first direct canonical coordinate is the persistent northeast marker.
Together with `CanonicalShadeFreeGrid.freeGrid`, this supplies the marked
witness required by the routed payload argument without the sparse graph-path
recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalShadeMarkedFreeGrid

open RedCycles RedShadePaths RedShadeCycles Signals.FreeCellLocal
  CanonicalShadeComparison CanonicalShadeFreeGrid ShadedSubstitution
  CanonicalShadeComparisonCore.PhaseComparison
  SparseFreeLinePlaneMarkedGrid

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
private theorem baseMarker_constant :
    (iterateRefine 4 (fun _ _ => (0 : Index)) 8 8,
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  native_decide

private theorem markerIndex (extra : Nat)
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0) :
    (actualGrid (extra + 1) coarse
        (2 * 4 ^ (extra + 1)) (2 * 4 ^ (extra + 1)),
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  have base := markerAt_of_root coarse coarseRoot 8 (by decide) baseMarker_constant
  have propagated := markerAt_iterateRefine coarse 8 extra base
  have depthEq : 2 * (extra + 1) + 2 = 2 * extra + 4 := by omega
  have coordinateEq : 2 * 4 ^ (extra + 1) = 8 * 4 ^ extra := by
    rw [pow_succ]
    omega
  simpa only [actualGrid, depthEq, coordinateEq] using propagated

/-- The direct canonical free grid, with its first crossing certified as the
routed lower-left marker. -/
def markedFreeGrid (size : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State) (root : Node)
    (coarseRoot : coarse 0 0 = 0) (rootParent : root.data.parent = 0)
    (valid : ValidShadeGrid (actualGrid (size + 1) coarse) states)
    (shaded : CycleShade states
      (scale (size + 1)) (3 * scale (size + 1))
      (scale (size + 1)) (3 * scale (size + 1)) .light) :
    MarkedFreeGrid (actualGrid (size + 1) coarse) states
      (scale (size + 1)) (3 * scale (size + 1))
      (scale (size + 1)) (3 * scale (size + 1)) (size + 2) where
  grid := freeGrid (size + 1) coarse states root coarseRoot rootParent
    valid shaded
  positive := by omega
  lowerLeftMarker := by
    simp only [freeGrid, FreeCoordinateFamily.toFreeGrid]
    change
      (actualGrid (size + 1) coarse
          (coordinateAt (size + 1) 0 / 2)
          (coordinateAt (size + 1) 0 / 2),
        quadrantAt (coordinateAt (size + 1) 0)
          (coordinateAt (size + 1) 0)) ∈ ShadedSignals.markerQuarters
    rw [coordinateAt_zero]
    have half : (4 * 4 ^ (size + 1) + 1) / 2 =
        2 * 4 ^ (size + 1) := by omega
    have quadrant : quadrantAt (4 * 4 ^ (size + 1) + 1)
        (4 * 4 ^ (size + 1) + 1) = Quadrant.northeast := by
      rw [show 4 * 4 ^ (size + 1) + 1 =
          2 * (2 * 4 ^ (size + 1)) + 1 by omega]
      simp [quadrantAt, Quadrant.ofBits]
    rw [half, quadrant]
    exact markerIndex size coarse coarseRoot

end CanonicalShadeMarkedFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
