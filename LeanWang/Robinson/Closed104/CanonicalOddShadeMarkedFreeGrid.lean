/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeFreeGrid
import LeanWang.Robinson.Closed104.ShadedMarkedFreeGrid

/-! Marked free grids from the canonical odd shade comparison. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeMarkedFreeGrid

open RedCycles RedShadePaths RedShadeCycles Signals.FreeCellLocal
  CanonicalOddShadeComparison
  CanonicalOddShadeFreeGrid CanonicalShadeComparisonCore.PhaseComparison
  SparseFreeLinePlaneMarkedGrid

set_option linter.style.nativeDecide false in
private theorem baseMarker_constant :
    (iterateRefine 4 (fun _ _ => (0 : Index)) 4 4,
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  native_decide

private theorem markerIndex (depth : Nat)
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0) :
    (actualGrid depth coarse (4 * 4 ^ depth) (4 * 4 ^ depth),
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  have base := markerAt_of_root coarse coarseRoot 4 (by decide) baseMarker_constant
  simpa [actualGrid] using markerAt_iterateRefine coarse 4 depth base

/-- The direct canonical odd free grid with its first crossing marked. -/
def markedFreeGrid (size : Nat) (coarse : Nat → Nat → Index)
    (states : Nat → Nat → RedShades.State)
    (coarseRoot : coarse 0 0 = 0)
    (valid : ValidShadeGrid (actualGrid size coarse) states)
    (shaded : CycleShade states
      (scale size) (3 * scale size)
      (scale size) (3 * scale size) .light) :
    MarkedFreeGrid (actualGrid size coarse) states
      (scale size) (3 * scale size)
      (scale size) (3 * scale size) (size + 1) where
  grid := freeGrid size coarse states coarseRoot valid shaded
  positive := by omega
  lowerLeftMarker := by
    simp only [freeGrid, FreeCoordinateFamily.toFreeGrid]
    change
      (actualGrid size coarse
          (coordinateAt size 0 / 2) (coordinateAt size 0 / 2),
        quadrantAt (coordinateAt size 0) (coordinateAt size 0)) ∈
          ShadedSignals.markerQuarters
    rw [coordinateAt_zero]
    have half : (8 * 4 ^ size + 1) / 2 = 4 * 4 ^ size := by omega
    have quadrant : quadrantAt (8 * 4 ^ size + 1)
        (8 * 4 ^ size + 1) = Quadrant.northeast := by
      rw [show 8 * 4 ^ size + 1 = 2 * (4 * 4 ^ size) + 1 by omega]
      simp [quadrantAt, Quadrant.ofBits]
    rw [half, quadrant]
    exact markerIndex size coarse coarseRoot

end CanonicalOddShadeMarkedFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
