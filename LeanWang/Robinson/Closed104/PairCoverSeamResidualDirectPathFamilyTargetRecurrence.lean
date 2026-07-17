/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathSearch
import LeanWang.Robinson.Closed104.RefinedCoordinateProjection

/-! Arithmetic transport for same-family residual targets. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetRecurrence

open RedShadeGraphRefinement PairCoverSeamPathSearch RefinedCoordinateProjection

theorem strictBetween_of_coarseCoordinates
    {first second value fine target : Nat}
    (firstEq : coarseCoordinate fine = first)
    (targetEq : coarseCoordinate target = value)
    (between : StrictBetween first second value) :
    StrictBetween fine (sparseCoordinate second) target := by
  have fineBounds := coarseCoordinate_spec fine
  have targetBounds := coarseCoordinate_spec target
  rw [firstEq] at fineBounds
  rw [targetEq] at targetBounds
  rcases between with between | between
  · left
    have nextFirst : first + 1 ≤ value := by omega
    have nextValue : value + 1 ≤ second := by omega
    exact ⟨fineBounds.2.trans_le
        ((sparseCoordinate_mono nextFirst).trans targetBounds.1),
      targetBounds.2.trans_le (sparseCoordinate_mono nextValue)⟩
  · right
    have nextValue : value + 1 ≤ first := by omega
    have nextSecond : second + 1 ≤ value := by omega
    exact ⟨(sparseCoordinate_strictMono (Nat.lt_succ_self second)).trans_le
        ((sparseCoordinate_mono nextSecond).trans targetBounds.1),
      targetBounds.2.trans_le
        ((sparseCoordinate_mono nextValue).trans fineBounds.1)⟩


/-- Strict betweenness lifts when the query, boundary, and target are all
arbitrary points of their respective coarse intervals. -/
theorem strictBetween_of_threeCoarseCoordinates
    {first second value fineFirst fineSecond fineValue : Nat}
    (firstEq : coarseCoordinate fineFirst = first)
    (secondEq : coarseCoordinate fineSecond = second)
    (valueEq : coarseCoordinate fineValue = value)
    (between : StrictBetween first second value) :
    StrictBetween fineFirst fineSecond fineValue := by
  have firstBounds := coarseCoordinate_spec fineFirst
  have secondBounds := coarseCoordinate_spec fineSecond
  have valueBounds := coarseCoordinate_spec fineValue
  rw [firstEq] at firstBounds
  rw [secondEq] at secondBounds
  rw [valueEq] at valueBounds
  rcases between with between | between
  · left
    have nextFirst : first + 1 ≤ value := by omega
    have nextValue : value + 1 ≤ second := by omega
    exact ⟨firstBounds.2.trans_le
        ((sparseCoordinate_mono nextFirst).trans valueBounds.1),
      valueBounds.2.trans_le
        ((sparseCoordinate_mono nextValue).trans secondBounds.1)⟩
  · right
    have nextSecond : second + 1 ≤ value := by omega
    have nextValue : value + 1 ≤ first := by omega
    exact ⟨secondBounds.2.trans_le
        ((sparseCoordinate_mono nextSecond).trans valueBounds.1),
      valueBounds.2.trans_le
        ((sparseCoordinate_mono nextValue).trans firstBounds.1)⟩

end PairCoverSeamResidualDirectPathFamilyTargetRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
