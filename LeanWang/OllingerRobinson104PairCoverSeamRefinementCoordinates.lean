/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamArithmetic
import LeanWang.OllingerRobinson104RefinedCoordinateProjection

/-!
# Coordinate projection for recursive pair-cover seams

Two substitutions multiply every board and recursive-child coordinate by
four.  Consequently, strict membership in a coarse child interval lifts to
strict membership in the corresponding fine interval.  This is the arithmetic
fact needed to project a noncontained seam query to the preceding hierarchy
level.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamRefinementCoordinates

open RedShadeCycles RedShadeGraphRefinement ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence PairCoverSeamArithmetic
  RefinedCoordinateProjection

theorem successorWest_succ (phase : Phase) (depth parent : Nat) :
    successorWest phase (depth + 1) parent =
      4 * successorWest phase depth parent := by
  simp only [successorWest, two_pow_refinementDepth_succ, west_succ]
  ring

theorem successorEast_succ (phase : Phase) (depth parent : Nat) :
    successorEast phase (depth + 1) parent =
      4 * successorEast phase depth parent := by
  simp only [successorEast, two_pow_refinementDepth_succ, east_succ]
  ring

/-- Fine successor-board bounds project into the previous successor board.
The lower bound is weak because the first newly created sparse interval is
still strictly inside the fine board. -/
theorem coarse_successor_bounds_of_fine_bounds
    {phase : Phase} {depth parent coordinate : Nat}
    (hlower : quarterWest (successorWest phase (depth + 1) parent) < coordinate)
    (hupper : coordinate < quarterEast
      (successorEast phase (depth + 1) parent)) :
    quarterWest (successorWest phase depth parent) ≤
        coarseCoordinate coordinate ∧
      coarseCoordinate coordinate <
        quarterEast (successorEast phase depth parent) := by
  rw [successorWest_succ] at hlower
  rw [successorEast_succ] at hupper
  exact coarse_board_bounds_of_fine_bounds hlower hupper

/-- Fine successor-collar bounds project to the previous successor collar.
Unlike the board-interior form above, the collar includes its lower edge. -/
theorem coarse_successor_bounds_of_fine_weak_bounds
    {phase : Phase} {depth parent coordinate : Nat}
    (hlower : quarterWest (successorWest phase (depth + 1) parent) ≤ coordinate)
    (hupper : coordinate < quarterEast
      (successorEast phase (depth + 1) parent)) :
    quarterWest (successorWest phase depth parent) ≤
        coarseCoordinate coordinate ∧
      coarseCoordinate coordinate <
        quarterEast (successorEast phase depth parent) := by
  rcases hlower.eq_or_lt with rfl | hlower
  · rw [successorWest_succ] at hupper ⊢
    rw [successorEast_succ] at hupper
    have hcoarse :
        coarseCoordinate (quarterWest (4 * successorWest phase depth parent)) =
          quarterWest (successorWest phase depth parent) := by
      have hmod :
          (2 * (4 * successorWest phase depth parent) + 1) % 8 = 1 := by
        omega
      have hdiv :
          (2 * (4 * successorWest phase depth parent) + 1) / 8 =
            successorWest phase depth parent := by
        omega
      unfold coarseCoordinate quarterWest
      rw [hmod]
      norm_num [hdiv]
    rw [hcoarse]
    simp only [quarterWest, quarterEast] at hupper ⊢
    omega
  · exact coarse_successor_bounds_of_fine_bounds hlower hupper

/-- A previous-level successor-board interior lifts to the corresponding fine
successor-board interior. -/
theorem fine_successor_bounds_of_coarse_bounds
    {phase : Phase} {depth parent coordinate : Nat}
    (hlower : quarterWest (successorWest phase depth parent) <
      coarseCoordinate coordinate)
    (hupper : coarseCoordinate coordinate <
      quarterEast (successorEast phase depth parent)) :
    quarterWest (successorWest phase (depth + 1) parent) < coordinate ∧
      coordinate < quarterEast
        (successorEast phase (depth + 1) parent) := by
  rw [successorWest_succ, successorEast_succ]
  exact fine_board_bounds_of_coarse_bounds hlower hupper

/-- The only failure of strict lower-bound projection is the first newly
created sparse interval immediately inside the fine board. -/
theorem coarse_successor_bounds_or_lower
    {phase : Phase} {depth parent coordinate : Nat}
    (hlower : quarterWest (successorWest phase (depth + 1) parent) < coordinate)
    (hupper : coordinate < quarterEast
      (successorEast phase (depth + 1) parent)) :
    coarseCoordinate coordinate =
        quarterWest (successorWest phase depth parent) ∨
      (quarterWest (successorWest phase depth parent) <
          coarseCoordinate coordinate ∧
        coarseCoordinate coordinate <
          quarterEast (successorEast phase depth parent)) := by
  have bounds := coarse_successor_bounds_of_fine_bounds hlower hupper
  omega

theorem absoluteChildWest_succ
    (phase : Phase) (depth parent : Nat) (side : Fin 2) :
    2 ^ refinementDepth phase (depth + 1) * absoluteChildBlock parent side +
        west phase (depth + 1) =
      4 * (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
        west phase depth) := by
  rw [two_pow_refinementDepth_succ, west_succ]
  ring

theorem absoluteChildEast_succ
    (phase : Phase) (depth parent : Nat) (side : Fin 2) :
    2 ^ refinementDepth phase (depth + 1) * absoluteChildBlock parent side +
        east phase (depth + 1) =
      4 * (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
        east phase depth) := by
  rw [two_pow_refinementDepth_succ, east_succ]
  ring

/-- A coordinate strictly inside a coarse child interval has every point of
its selected sparse interval strictly inside the corresponding fine child. -/
theorem inAbsoluteChildInterval_of_coarseCoordinate
    {phase : Phase} {depth parent : Nat} {side : Fin 2} {coordinate : Nat}
    (inside : InAbsoluteChildInterval phase depth parent side
      (coarseCoordinate coordinate)) :
    InAbsoluteChildInterval phase (depth + 1) parent side coordinate := by
  rcases inside with ⟨hlower, hupper⟩
  have bounds := sparse_bounds_of_coarse_bounds hlower hupper
  constructor
  · rw [absoluteChildWest_succ, ← sparseCoordinate_quarterWest]
    exact bounds.1
  · rw [absoluteChildEast_succ, ← sparseCoordinate_quarterEast]
    exact bounds.2

theorem inSomeAbsoluteChild_of_coarseCoordinate
    {phase : Phase} {depth parent coordinate : Nat}
    (inside : InSomeAbsoluteChild phase depth parent
      (coarseCoordinate coordinate)) :
    InSomeAbsoluteChild phase (depth + 1) parent coordinate := by
  rcases inside with ⟨side, inside⟩
  exact ⟨side, inAbsoluteChildInterval_of_coarseCoordinate inside⟩

theorem inSameAbsoluteChild_of_coarseCoordinate
    {phase : Phase} {depth parent first second : Nat}
    (inside : InSameAbsoluteChild phase depth parent
      (coarseCoordinate first) (coarseCoordinate second)) :
    InSameAbsoluteChild phase (depth + 1) parent first second := by
  rcases inside with ⟨side, firstInside, secondInside⟩
  exact ⟨side, inAbsoluteChildInterval_of_coarseCoordinate firstInside,
    inAbsoluteChildInterval_of_coarseCoordinate secondInside⟩

/-- Failure to fit in one fine recursive child projects to failure to fit in
one coarse recursive child. -/
theorem notFitsContainedVerticalChild_coarseCoordinate
    {phase : Phase} {depth parentX parentY column row boundary : Nat}
    (notFits : ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary) :
    ¬FitsContainedVerticalChild phase depth parentX parentY
      (coarseCoordinate column) (coarseCoordinate row)
      (coarseCoordinate boundary) := by
  rw [fitsContainedVerticalChild_iff_regions] at notFits ⊢
  rintro ⟨columnInside, rowBoundaryInside⟩
  exact notFits ⟨
    inSomeAbsoluteChild_of_coarseCoordinate columnInside,
    inSameAbsoluteChild_of_coarseCoordinate rowBoundaryInside⟩

/-- Horizontal dual of `notFitsContainedVerticalChild_coarseCoordinate`. -/
theorem notFitsContainedHorizontalChild_coarseCoordinate
    {phase : Phase} {depth parentX parentY column row boundary : Nat}
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary) :
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      (coarseCoordinate column) (coarseCoordinate row)
      (coarseCoordinate boundary) := by
  rw [fitsContainedHorizontalChild_iff_regions] at notFits ⊢
  rintro ⟨columnBoundaryInside, rowInside⟩
  exact notFits ⟨
    inSameAbsoluteChild_of_coarseCoordinate columnBoundaryInside,
    inSomeAbsoluteChild_of_coarseCoordinate rowInside⟩

end PairCoverSeamRefinementCoordinates
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
