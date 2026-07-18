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

open RedCycles RedShadePaths RedShadeCycles RedShadeGraphRefinement RefinementTranslation
  Signals.FreeCellLocal CanonicalOddShadeComparison
  CanonicalOddShadeFreeGrid SparseFreeLinePlaneMarkedGrid

set_option linter.style.nativeDecide false in
private theorem marker_refines (index : Index)
    (marker : (index, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters) :
    (southwestChild (southwestChild index), Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  revert index
  native_decide

set_option linter.style.nativeDecide false in
private theorem baseMarker_constant :
    (iterateRefine 4 (fun _ _ => (0 : Index)) 4 4,
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  native_decide

private theorem baseMarker (coarse : Nat → Nat → Index)
    (coarseRoot : coarse 0 0 = 0) :
    (actualGrid 0 coarse 4 4, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  have localized := iterateRefine_shift_eq_constant 4 coarse 0 0 4 4
    (by norm_num) (by norm_num)
  have shiftZero : shiftGrid coarse 0 0 = coarse := by
    funext x y
    simp [shiftGrid]
  rw [shiftZero] at localized
  change (iterateRefine 4 coarse 4 4, Quadrant.northeast) ∈
    ShadedSignals.markerQuarters
  rw [localized, coarseRoot]
  exact baseMarker_constant

private theorem actualGrid_succ (depth : Nat)
    (coarse : Nat → Nat → Index) :
    actualGrid (depth + 1) coarse = iterateRefine 2 (actualGrid depth coarse) := by
  unfold actualGrid
  rw [PlaneRedBoards.iterateRefine_add]
  congr 1
  omega

private theorem markerIndex (depth : Nat)
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0) :
    (actualGrid depth coarse (4 * 4 ^ depth) (4 * 4 ^ depth),
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  induction depth with
  | zero => simpa using baseMarker coarse coarseRoot
  | succ depth ih =>
      rw [actualGrid_succ]
      change
        (refineIndexGrid (refineIndexGrid (actualGrid depth coarse))
            (4 * 4 ^ (depth + 1)) (4 * 4 ^ (depth + 1)),
          Quadrant.northeast) ∈ ShadedSignals.markerQuarters
      rw [show 4 * 4 ^ (depth + 1) =
          2 * (2 * (4 * 4 ^ depth)) by
        rw [pow_succ]
        omega]
      simp only [refineIndexGrid_even_even]
      exact marker_refines _ ih

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
    dsimp [freeGrid]
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
