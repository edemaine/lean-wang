/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSignalRoutingScaffold
import LeanWang.OllingerRobinson104SparseFreeLinePlaneLocalStep

/-!
# The retained sparse-pivot marker

The first retained free row and column meet in a northeast quarter.  At the
even base its corrected index is one of `0, 1, 2, 3`; the same finite set is
closed under the two southwest-child refinements used at later depths.  The
odd base has the identical local property.  This gives both light-cycle
branches one honest marker without prepending an additional free line.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePivotMarker

open RedCycles RedShadeGraphRefinement RefinementTranslation
  ShadedFreeLineRecurrence SparseFreeLineOffsets SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem odd_pivot_coordinate (depth : Nat) :
    lineCoordinate .odd depth (pivot depth) = 8 * 4 ^ depth + 1 := by
  simp [pivot, BorderCoverageOffsets.lineCoordinate_odd]
  omega

set_option linter.style.nativeDecide false in
theorem markerNortheast_refines (index : Index)
    (hmarker : (index, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters) :
    (southwestChild (southwestChild index), Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  revert index
  native_decide

set_option linter.style.nativeDecide false in
theorem evenBaseMarkerQuarter_constant (parent : Index) :
    (ShadedFreeLineGraphBase.localGrid parent 8 8, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  revert parent
  native_decide

theorem evenBaseMarkerQuarter (grid : Nat → Nat → Index) :
    (refinedGrid .even 1 grid 8 8, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  have hlocal := iterateRefine_shift_eq_constant 4 grid 0 0 8 8
    (by norm_num) (by norm_num)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  unfold refinedGrid
  simp only [refinementDepth, Phase.extra]
  rw [hlocal]
  simpa [ShadedFreeLineGraphBase.localGrid] using
    evenBaseMarkerQuarter_constant (grid 0 0)

theorem evenPivotMarkerIndex (extra : Nat) (grid : Nat → Nat → Index) :
    (refinedGrid .even (extra + 1) grid
        (2 * 4 ^ (extra + 1)) (2 * 4 ^ (extra + 1)),
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  induction extra with
  | zero => simpa using evenBaseMarkerQuarter grid
  | succ extra ih =>
      rw [show extra + 1 + 1 = (extra + 1) + 1 by omega,
        SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      change
        (refineIndexGrid (refineIndexGrid (refinedGrid .even (extra + 1) grid))
            (2 * 4 ^ (extra + 2)) (2 * 4 ^ (extra + 2)),
          Quadrant.northeast) ∈ ShadedSignals.markerQuarters
      rw [show 2 * 4 ^ (extra + 2) =
          2 * (2 * (2 * 4 ^ (extra + 1))) by
        rw [pow_succ]
        omega]
      simp only [refineIndexGrid_even_even]
      exact markerNortheast_refines _ ih

theorem evenPivotMarkerQuarter (extra : Nat) (grid : Nat → Nat → Index) :
    let coordinate := lineCoordinate .even (extra + 1) (pivot (extra + 1))
    (refinedGrid .even (extra + 1) grid
        (coordinate / 2) (coordinate / 2),
      quadrantAt coordinate coordinate) ∈ ShadedSignals.markerQuarters := by
  dsimp only
  rw [even_pivot_coordinate]
  have hhalf : (4 * 4 ^ (extra + 1) + 1) / 2 =
      2 * 4 ^ (extra + 1) := by omega
  have hquadrant : quadrantAt (4 * 4 ^ (extra + 1) + 1)
      (4 * 4 ^ (extra + 1) + 1) = Quadrant.northeast := by
    rw [show 4 * 4 ^ (extra + 1) + 1 =
        2 * (2 * 4 ^ (extra + 1)) + 1 by omega]
    simp [quadrantAt, Quadrant.ofBits]
  rw [hhalf, hquadrant]
  exact evenPivotMarkerIndex extra grid

set_option linter.style.nativeDecide false in
theorem oddBaseMarkerQuarter_constant (parent : Index) :
    (ShadedFreeLineOddBase.localGrid parent 4 4, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  revert parent
  native_decide

theorem oddBaseMarkerQuarter (grid : Nat → Nat → Index) :
    (refinedGrid .odd 0 grid 4 4, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  have hlocal := iterateRefine_shift_eq_constant 3 grid 0 0 4 4
    (by norm_num) (by norm_num)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  unfold refinedGrid
  simp only [refinementDepth, Phase.extra]
  rw [hlocal]
  simpa [ShadedFreeLineOddBase.localGrid] using
    oddBaseMarkerQuarter_constant (grid 0 0)

theorem oddPivotMarkerIndex (depth : Nat) (grid : Nat → Nat → Index) :
    (refinedGrid .odd depth grid
        (4 * 4 ^ depth) (4 * 4 ^ depth), Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  induction depth with
  | zero => simpa using oddBaseMarkerQuarter grid
  | succ depth ih =>
      rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      change
        (refineIndexGrid (refineIndexGrid (refinedGrid .odd depth grid))
            (4 * 4 ^ (depth + 1)) (4 * 4 ^ (depth + 1)),
          Quadrant.northeast) ∈ ShadedSignals.markerQuarters
      rw [show 4 * 4 ^ (depth + 1) =
          2 * (2 * (4 * 4 ^ depth)) by
        rw [pow_succ]
        omega]
      simp only [refineIndexGrid_even_even]
      exact markerNortheast_refines _ ih

theorem oddPivotMarkerQuarter (depth : Nat) (grid : Nat → Nat → Index) :
    let coordinate := lineCoordinate .odd depth (pivot depth)
    (refinedGrid .odd depth grid (coordinate / 2) (coordinate / 2),
      quadrantAt coordinate coordinate) ∈ ShadedSignals.markerQuarters := by
  dsimp only
  rw [odd_pivot_coordinate]
  have hhalf : (8 * 4 ^ depth + 1) / 2 = 4 * 4 ^ depth := by omega
  have hquadrant : quadrantAt (8 * 4 ^ depth + 1)
      (8 * 4 ^ depth + 1) = Quadrant.northeast := by
    rw [show 8 * 4 ^ depth + 1 = 2 * (4 * 4 ^ depth) + 1 by omega]
    simp [quadrantAt, Quadrant.ofBits]
  rw [hhalf, hquadrant]
  exact oddPivotMarkerIndex depth grid

end SparseFreeLinePivotMarker
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
