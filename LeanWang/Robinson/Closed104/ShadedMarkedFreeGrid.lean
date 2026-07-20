/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeGrid
import LeanWang.Robinson.Closed104.ShadedSignalRoutingScaffold
import LeanWang.Robinson.Closed104.RedCycleExpansion
import LeanWang.Robinson.Closed104.RefinementTranslation

/-! A free grid whose lower-left crossing carries the routed marker. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneMarkedGrid

open RedCycles RedShadeCycles RefinementTranslation ShadedFreeGrid
  Signals.FreeCellLocal

structure MarkedFreeGrid
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north size : Nat) where
  grid : FreeGrid indexGrid shadeGrid west east south north size
  positive : 0 < size
  lowerLeftMarker :
    (indexGrid (grid.columnAt ⟨0, positive⟩ / 2)
        (grid.rowAt ⟨0, positive⟩ / 2),
      quadrantAt (grid.columnAt ⟨0, positive⟩)
        (grid.rowAt ⟨0, positive⟩)) ∈
      ShadedSignals.markerQuarters

set_option linter.style.nativeDecide false in
theorem marker_refines (index : Index)
    (marker : (index, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters) :
    (southwestChild (southwestChild index), Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  revert index
  native_decide

/-- Localize a constant-grid marker certificate at the root of an arbitrary
coarse grid. -/
theorem markerAt_of_root
    (coarse : Nat → Nat → Index) (coarseRoot : coarse 0 0 = 0)
    (coordinate : Nat) (coordinate_lt : coordinate < 16)
    (constantMarker :
      (iterateRefine 4 (fun _ _ => (0 : Index)) coordinate coordinate,
        Quadrant.northeast) ∈ ShadedSignals.markerQuarters) :
    (iterateRefine 4 coarse coordinate coordinate,
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  have localized := iterateRefine_shift_eq_constant 4 coarse 0 0
    coordinate coordinate coordinate_lt coordinate_lt
  have shiftZero : shiftGrid coarse 0 0 = coarse := by
    funext x y
    simp [shiftGrid]
  rw [shiftZero] at localized
  rw [localized, coarseRoot]
  exact constantMarker

/-- A marker surviving two southwest refinements propagates along any
base-four coordinate ray. -/
theorem markerAt_iterateRefine
    (coarse : Nat → Nat → Index) (base depth : Nat)
    (baseMarker :
      (iterateRefine 4 coarse base base, Quadrant.northeast) ∈
        ShadedSignals.markerQuarters) :
    (iterateRefine (2 * depth + 4) coarse
        (base * 4 ^ depth) (base * 4 ^ depth),
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  induction depth with
  | zero => simpa using baseMarker
  | succ depth ih =>
      rw [show 2 * (depth + 1) + 4 = 2 + (2 * depth + 4) by omega,
        ← PlaneRedBoards.iterateRefine_add]
      change
        (refineIndexGrid (refineIndexGrid
            (iterateRefine (2 * depth + 4) coarse))
          (base * 4 ^ (depth + 1)) (base * 4 ^ (depth + 1)),
          Quadrant.northeast) ∈ ShadedSignals.markerQuarters
      rw [show base * 4 ^ (depth + 1) =
          2 * (2 * (base * 4 ^ depth)) by
        rw [pow_succ]
        calc
          base * (4 ^ depth * 4) = 4 * (base * 4 ^ depth) := by ac_rfl
          _ = 2 * (2 * (base * 4 ^ depth)) := by omega]
      simp only [refineIndexGrid_even_even]
      exact marker_refines _ ih

end SparseFreeLinePlaneMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
