/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignalRoutingScaffold
import LeanWang.Robinson.Closed104.SparseFreeLinePlaneLocalStep

/-!
# The retained sparse-pivot marker

The first retained free row and column meet in a northeast quarter.  Choosing
a coarse occurrence of corrected index `0` makes both finite bases index `0`,
and index `0` is fixed by the southwest-child refinements used at later depths.
This gives both light-cycle branches one canonical marker without prepending
an additional free line.
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
theorem evenBaseMarkerQuarter_constant :
    (ShadedFreeLineGraphBase.localGrid 0 8 8, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  native_decide

theorem evenBaseMarkerQuarter (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0) :
    (refinedGrid .even 1 grid 8 8, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  have hlocal := iterateRefine_shift_eq_constant 4 grid 0 0 8 8
    (by norm_num) (by norm_num)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  unfold refinedGrid
  simp only [refinementDepth, Phase.extra]
  rw [hlocal, root]
  exact evenBaseMarkerQuarter_constant

theorem evenPivotMarkerIndex (extra : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0) :
    (refinedGrid .even (extra + 1) grid
        (2 * 4 ^ (extra + 1)) (2 * 4 ^ (extra + 1)),
      Quadrant.northeast) ∈ ShadedSignals.markerQuarters := by
  induction extra with
  | zero => simpa using evenBaseMarkerQuarter grid root
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

theorem evenPivotMarkerQuarter (extra : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0) :
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
  exact evenPivotMarkerIndex extra grid root

set_option linter.style.nativeDecide false in
theorem oddBaseMarkerQuarter_constant :
    (ShadedFreeLineOddBase.localGrid 0 4 4, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  native_decide

theorem oddBaseMarkerQuarter (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0) :
    (refinedGrid .odd 0 grid 4 4, Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  have hlocal := iterateRefine_shift_eq_constant 3 grid 0 0 4 4
    (by norm_num) (by norm_num)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  unfold refinedGrid
  simp only [refinementDepth, Phase.extra]
  rw [hlocal, root]
  exact oddBaseMarkerQuarter_constant

theorem oddPivotMarkerIndex (depth : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0) :
    (refinedGrid .odd depth grid
        (4 * 4 ^ depth) (4 * 4 ^ depth), Quadrant.northeast) ∈
      ShadedSignals.markerQuarters := by
  induction depth with
  | zero => simpa using oddBaseMarkerQuarter grid root
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

theorem oddPivotMarkerQuarter (depth : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0) :
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
  exact oddPivotMarkerIndex depth grid root

end SparseFreeLinePivotMarker
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
