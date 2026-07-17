/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import LeanWang.Robinson.Closed104.PairCoverSeamChecks
import LeanWang.Robinson.Closed104.ShadedObstructionPairCoverRecurrence

/-!
# Finite arithmetic for pair-cover seams

One hierarchy successor contains four recursive child boards.  This module
normalizes the unbounded block coordinates in the recurrence interface to the
two choices in each axis.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamArithmetic

open RedCycles RedShadeCycles RedShadePaths RedShadeGraphRefinement
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  Signals.FreeCellLocal

/-- The refinement block width is four times the current board scale. -/
theorem two_pow_refinementDepth_eq_four_mul_west
    (phase : Phase) (depth : Nat) :
    2 ^ refinementDepth phase depth = 4 * west phase depth := by
  cases phase <;>
    simp [refinementDepth, Phase.extra, west, scale, Phase.factor,
      pow_add, pow_mul] <;> ring

theorem west_pos (phase : Phase) (depth : Nat) : 0 < west phase depth := by
  cases phase <;> simp [west, scale, Phase.factor]

theorem two_pow_refinementDepth_succ (phase : Phase) (depth : Nat) :
    2 ^ refinementDepth phase (depth + 1) =
      4 * 2 ^ refinementDepth phase depth := by
  rw [two_pow_refinementDepth_eq_four_mul_west,
    two_pow_refinementDepth_eq_four_mul_west, west_succ]

theorem absolute_child_block_eq
    {phase : Phase} {depth parent child : Nat}
    (outerLower : quarterWest
      (2 ^ refinementDepth phase (depth + 1) * parent + west phase (depth + 1)) ≤
        quarterWest
          (2 ^ refinementDepth phase depth * child + west phase depth))
    (outerUpper : quarterEast
        (2 ^ refinementDepth phase depth * child + east phase depth) ≤
      quarterEast
        (2 ^ refinementDepth phase (depth + 1) * parent + east phase (depth + 1))) :
    child = 4 * parent + 1 ∨ child = 4 * parent + 2 := by
  have hpow := two_pow_refinementDepth_eq_four_mul_west phase depth
  have hpowSucc := two_pow_refinementDepth_succ phase depth
  have hwestSucc := west_succ phase depth
  have heast : east phase depth = 3 * west phase depth := rfl
  have heastSucc : east phase (depth + 1) = 4 * east phase depth :=
    east_succ phase depth
  have hwest := west_pos phase depth
  simp only [quarterWest, quarterEast, hpow, hpowSucc,
    hwestSucc, heast, heastSucc] at outerLower outerUpper
  have hlower : 4 * parent + 1 ≤ child := by
    by_contra h
    have : child ≤ 4 * parent := by omega
    nlinarith
  have hupper : child ≤ 4 * parent + 2 := by
    by_contra h
    have : 4 * parent + 3 ≤ child := by omega
    nlinarith
  omega

theorem absolute_child_contained
    (phase : Phase) (depth parent : Nat) (side : Fin 2) :
    quarterWest
      (2 ^ refinementDepth phase (depth + 1) * parent + west phase (depth + 1)) ≤
        quarterWest
          (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
            west phase depth) ∧
      quarterEast
          (2 ^ refinementDepth phase depth * absoluteChildBlock parent side +
            east phase depth) ≤
        quarterEast
          (2 ^ refinementDepth phase (depth + 1) * parent +
            east phase (depth + 1)) := by
  have hpow := two_pow_refinementDepth_eq_four_mul_west phase depth
  have hpowSucc := two_pow_refinementDepth_succ phase depth
  have hwestSucc := west_succ phase depth
  have heast : east phase depth = 3 * west phase depth := rfl
  have heastSucc : east phase (depth + 1) = 4 * east phase depth :=
    east_succ phase depth
  have hwest := west_pos phase depth
  fin_cases side <;>
    simp only [absoluteChildBlock, childBlock,
      quarterWest, quarterEast, hpow, hpowSucc, hwestSucc,
      heast, heastSucc] <;>
    constructor <;> nlinarith

theorem exists_side_of_absolute_child_block_eq
    {parent child : Nat}
    (hchild : child = 4 * parent + 1 ∨ child = 4 * parent + 2) :
    ∃ side : Fin 2, child = absoluteChildBlock parent side := by
  rcases hchild with hchild | hchild
  · exact ⟨⟨0, by decide⟩, by simpa [absoluteChildBlock, childBlock] using hchild⟩
  · exact ⟨⟨1, by decide⟩, by simpa [absoluteChildBlock, childBlock] using hchild⟩

theorem fitsContainedVerticalChild_iff
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    FitsContainedVerticalChild phase depth parentX parentY
      column row boundary ↔
      ∃ childX childY : Fin 2,
        InAbsoluteChildInterval phase depth parentX childX column ∧
        InAbsoluteChildInterval phase depth parentY childY row ∧
        InAbsoluteChildInterval phase depth parentY childY boundary := by
  constructor
  · rintro ⟨childX, childY, houterWest, houterEast,
      houterSouth, houterNorth, hcolumnWest, hcolumnEast,
      hrowSouth, hrowNorth, hboundarySouth, hboundaryNorth⟩
    rcases exists_side_of_absolute_child_block_eq
        (absolute_child_block_eq houterWest houterEast) with
      ⟨sideX, rfl⟩
    rcases exists_side_of_absolute_child_block_eq
        (absolute_child_block_eq houterSouth houterNorth) with
      ⟨sideY, rfl⟩
    exact ⟨sideX, sideY, ⟨hcolumnWest, hcolumnEast⟩,
      ⟨hrowSouth, hrowNorth⟩,
      ⟨hboundarySouth, hboundaryNorth⟩⟩
  · rintro ⟨childX, childY, hcolumn, hrow, hboundary⟩
    exact ⟨absoluteChildBlock parentX childX,
      absoluteChildBlock parentY childY,
      (absolute_child_contained phase depth parentX childX).1,
      (absolute_child_contained phase depth parentX childX).2,
      (absolute_child_contained phase depth parentY childY).1,
      (absolute_child_contained phase depth parentY childY).2,
      hcolumn.1, hcolumn.2, hrow.1, hrow.2,
      hboundary.1, hboundary.2⟩

theorem fitsContainedHorizontalChild_iff
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary ↔
      ∃ childX childY : Fin 2,
        InAbsoluteChildInterval phase depth parentX childX column ∧
        InAbsoluteChildInterval phase depth parentY childY row ∧
        InAbsoluteChildInterval phase depth parentX childX boundary := by
  constructor
  · rintro ⟨childX, childY, houterWest, houterEast,
      houterSouth, houterNorth, hcolumnWest, hcolumnEast,
      hrowSouth, hrowNorth, hboundaryWest, hboundaryEast⟩
    rcases exists_side_of_absolute_child_block_eq
        (absolute_child_block_eq houterWest houterEast) with
      ⟨sideX, rfl⟩
    rcases exists_side_of_absolute_child_block_eq
        (absolute_child_block_eq houterSouth houterNorth) with
      ⟨sideY, rfl⟩
    exact ⟨sideX, sideY, ⟨hcolumnWest, hcolumnEast⟩,
      ⟨hrowSouth, hrowNorth⟩,
      ⟨hboundaryWest, hboundaryEast⟩⟩
  · rintro ⟨childX, childY, hcolumn, hrow, hboundary⟩
    exact ⟨absoluteChildBlock parentX childX,
      absoluteChildBlock parentY childY,
      (absolute_child_contained phase depth parentX childX).1,
      (absolute_child_contained phase depth parentX childX).2,
      (absolute_child_contained phase depth parentY childY).1,
      (absolute_child_contained phase depth parentY childY).2,
      hcolumn.1, hcolumn.2, hrow.1, hrow.2,
      hboundary.1, hboundary.2⟩

theorem fitsContainedVerticalChild_iff_regions
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    FitsContainedVerticalChild phase depth parentX parentY
      column row boundary ↔
      InSomeAbsoluteChild phase depth parentX column ∧
        InSameAbsoluteChild phase depth parentY row boundary := by
  rw [fitsContainedVerticalChild_iff]
  constructor
  · rintro ⟨childX, childY, hcolumn, hrow, hboundary⟩
    exact ⟨⟨childX, hcolumn⟩, ⟨childY, hrow, hboundary⟩⟩
  · rintro ⟨⟨childX, hcolumn⟩, ⟨childY, hrow, hboundary⟩⟩
    exact ⟨childX, childY, hcolumn, hrow, hboundary⟩

theorem fitsContainedHorizontalChild_iff_regions
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary ↔
      InSameAbsoluteChild phase depth parentX column boundary ∧
        InSomeAbsoluteChild phase depth parentY row := by
  rw [fitsContainedHorizontalChild_iff]
  constructor
  · rintro ⟨childX, childY, hcolumn, hrow, hboundary⟩
    exact ⟨⟨childX, hcolumn, hboundary⟩, ⟨childY, hrow⟩⟩
  · rintro ⟨⟨childX, hcolumn, hboundary⟩, ⟨childY, hrow⟩⟩
    exact ⟨childX, childY, hcolumn, hrow, hboundary⟩

theorem inAbsoluteChildIntervalCheck_eq_true_iff
    (phase : Phase) (depth parent : Nat) (side : Fin 2) (coordinate : Nat) :
    inAbsoluteChildIntervalCheck phase depth parent side coordinate = true ↔
      InAbsoluteChildInterval phase depth parent side coordinate := by
  simp [inAbsoluteChildIntervalCheck, InAbsoluteChildInterval]

theorem inSomeAbsoluteChildCheck_eq_true_iff
    (phase : Phase) (depth parent coordinate : Nat) :
    inSomeAbsoluteChildCheck phase depth parent coordinate = true ↔
      InSomeAbsoluteChild phase depth parent coordinate := by
  simp [inSomeAbsoluteChildCheck, InSomeAbsoluteChild,
    Fin.exists_fin_two, inAbsoluteChildIntervalCheck_eq_true_iff]

theorem inSameAbsoluteChildCheck_eq_true_iff
    (phase : Phase) (depth parent first second : Nat) :
    inSameAbsoluteChildCheck phase depth parent first second = true ↔
      InSameAbsoluteChild phase depth parent first second := by
  simp [inSameAbsoluteChildCheck, InSameAbsoluteChild,
    Fin.exists_fin_two, inAbsoluteChildIntervalCheck_eq_true_iff]

theorem containedVerticalSeamCheck_eq_true_iff
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    containedVerticalSeamCheck phase depth parentX parentY
      column row boundary = true ↔
      ¬FitsContainedVerticalChild phase depth parentX parentY
        column row boundary := by
  rw [fitsContainedVerticalChild_iff_regions]
  constructor
  · intro hcheck ⟨hsome, hsame⟩
    have hsomeCheck := (inSomeAbsoluteChildCheck_eq_true_iff
      phase depth parentX column).2 hsome
    have hsameCheck := (inSameAbsoluteChildCheck_eq_true_iff
      phase depth parentY row boundary).2 hsame
    simp [containedVerticalSeamCheck, hsomeCheck, hsameCheck] at hcheck
  · intro hnot
    by_cases hsome : InSomeAbsoluteChild phase depth parentX column
    · have hnotSame : ¬InSameAbsoluteChild phase depth parentY row boundary :=
        fun hsame => hnot ⟨hsome, hsame⟩
      have hsomeCheck := (inSomeAbsoluteChildCheck_eq_true_iff
        phase depth parentX column).2 hsome
      have hsameCheck : inSameAbsoluteChildCheck phase depth parentY
          row boundary = false := by
        cases hcheck : inSameAbsoluteChildCheck phase depth parentY row boundary
        · rfl
        · exact (hnotSame ((inSameAbsoluteChildCheck_eq_true_iff
            phase depth parentY row boundary).1 hcheck)).elim
      simp [containedVerticalSeamCheck, hsomeCheck, hsameCheck]
    · have hsomeCheck : inSomeAbsoluteChildCheck phase depth parentX
          column = false := by
        cases hcheck : inSomeAbsoluteChildCheck phase depth parentX column
        · rfl
        · exact (hsome ((inSomeAbsoluteChildCheck_eq_true_iff
            phase depth parentX column).1 hcheck)).elim
      simp [containedVerticalSeamCheck, hsomeCheck]

theorem containedHorizontalSeamCheck_eq_true_iff
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    containedHorizontalSeamCheck phase depth parentX parentY
      column row boundary = true ↔
      ¬FitsContainedHorizontalChild phase depth parentX parentY
        column row boundary := by
  rw [fitsContainedHorizontalChild_iff_regions]
  constructor
  · intro hcheck ⟨hsame, hsome⟩
    have hsameCheck := (inSameAbsoluteChildCheck_eq_true_iff
      phase depth parentX column boundary).2 hsame
    have hsomeCheck := (inSomeAbsoluteChildCheck_eq_true_iff
      phase depth parentY row).2 hsome
    simp [containedHorizontalSeamCheck, hsameCheck, hsomeCheck] at hcheck
  · intro hnot
    by_cases hsame : InSameAbsoluteChild phase depth parentX column boundary
    · have hnotSome : ¬InSomeAbsoluteChild phase depth parentY row :=
        fun hsome => hnot ⟨hsame, hsome⟩
      have hsameCheck := (inSameAbsoluteChildCheck_eq_true_iff
        phase depth parentX column boundary).2 hsame
      have hsomeCheck : inSomeAbsoluteChildCheck phase depth parentY row = false := by
        cases hcheck : inSomeAbsoluteChildCheck phase depth parentY row
        · rfl
        · exact (hnotSome ((inSomeAbsoluteChildCheck_eq_true_iff
            phase depth parentY row).1 hcheck)).elim
      simp [containedHorizontalSeamCheck, hsameCheck, hsomeCheck]
    · have hsameCheck : inSameAbsoluteChildCheck phase depth parentX
          column boundary = false := by
        cases hcheck : inSameAbsoluteChildCheck phase depth parentX column boundary
        · rfl
        · exact (hsame ((inSameAbsoluteChildCheck_eq_true_iff
            phase depth parentX column boundary).1 hcheck)).elim
      simp [containedHorizontalSeamCheck, hsameCheck]

/- The central-board recurrence below is superseded by the contained all-block
invariant above.  It is retained temporarily for source history but excluded
from elaboration. -/
/-
theorem fitting_block_eq_child
    {phase : Phase} {depth block coordinate : Nat}
    (globalLower : quarterWest (4 * west phase depth) < coordinate)
    (globalUpper : coordinate < quarterEast (4 * east phase depth))
    (localLower : quarterWest
      (2 ^ refinementDepth phase depth * block + west phase depth) < coordinate)
    (localUpper : coordinate < quarterEast
      (2 ^ refinementDepth phase depth * block + east phase depth)) :
    block = 1 ∨ block = 2 := by
  have hpow := two_pow_refinementDepth_eq_four_mul_west phase depth
  have hwest := west_pos phase depth
  have heast : east phase depth = 3 * west phase depth := rfl
  simp only [quarterWest, quarterEast, hpow, heast] at
    globalLower globalUpper localLower localUpper
  have hblockLower : 1 ≤ block := by
    by_contra h
    have : block = 0 := by omega
    subst block
    omega
  have hblockUpper : block ≤ 2 := by
    by_contra h
    have : 3 ≤ block := by omega
    nlinarith
  omega

theorem contained_child_block_eq_child
    {phase : Phase} {depth block : Nat}
    (outerLower : quarterWest (4 * west phase depth) ≤ quarterWest
      (2 ^ refinementDepth phase depth * block + west phase depth))
    (outerUpper : quarterEast
      (2 ^ refinementDepth phase depth * block + east phase depth) ≤
        quarterEast (4 * east phase depth)) :
    block = 1 ∨ block = 2 := by
  have hpow := two_pow_refinementDepth_eq_four_mul_west phase depth
  have hwest := west_pos phase depth
  have heast : east phase depth = 3 * west phase depth := rfl
  simp only [quarterWest, quarterEast, hpow, heast] at outerLower outerUpper
  have hblockLower : 1 ≤ block := by
    by_contra h
    have : block = 0 := by omega
    subst block
    omega
  have hblockUpper : block ≤ 2 := by
    by_contra h
    have : 3 ≤ block := by omega
    nlinarith
  omega

theorem child_contained (phase : Phase) (depth : Nat) (side : Fin 2) :
    quarterWest (4 * west phase depth) ≤ quarterWest
        (2 ^ refinementDepth phase depth * childBlock side + west phase depth) ∧
      quarterEast
        (2 ^ refinementDepth phase depth * childBlock side + east phase depth) ≤
          quarterEast (4 * east phase depth) := by
  have hpow := two_pow_refinementDepth_eq_four_mul_west phase depth
  have hwest := west_pos phase depth
  have heast : east phase depth = 3 * west phase depth := rfl
  fin_cases side <;>
    simp [childBlock, quarterWest, quarterEast, hpow, heast] <;> omega

theorem fitsVerticalChild_iff
    (phase : Phase) (depth column row boundary : Nat)
    (hrowSouthGlobal : quarterSouth (4 * west phase depth) < row)
    (hrowNorthGlobal : row < quarterNorth (4 * east phase depth)) :
    FitsVerticalChild phase depth column row boundary ↔
      ∃ blockX blockY : Fin 2,
        InChildInterval phase depth blockX column ∧
        InChildInterval phase depth blockY row ∧
        InChildInterval phase depth blockY boundary := by
  constructor
  · rintro ⟨blockX, blockY, houterWest, houterEast,
      hcolumnWest, hcolumnEast, hrowSouth, hrowNorth,
      hboundarySouth, hboundaryNorth⟩
    rcases contained_child_block_eq_child houterWest houterEast with
      rfl | rfl
    all_goals
      rcases fitting_block_eq_child
        (coordinate := row) hrowSouthGlobal hrowNorthGlobal
        hrowSouth hrowNorth with rfl | rfl
    all_goals
      first
      | exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundarySouth, hboundaryNorth⟩⟩
      | exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundarySouth, hboundaryNorth⟩⟩
      | exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundarySouth, hboundaryNorth⟩⟩
      | exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundarySouth, hboundaryNorth⟩⟩
  · rintro ⟨blockX, blockY, hcolumn, hrow, hboundary⟩
    exact ⟨childBlock blockX, childBlock blockY,
      (child_contained phase depth blockX).1,
      (child_contained phase depth blockX).2,
      hcolumn.1, hcolumn.2, hrow.1, hrow.2,
      hboundary.1, hboundary.2⟩

theorem fitsHorizontalChild_iff
    (phase : Phase) (depth column row boundary : Nat)
    (hcolumnWestGlobal : quarterWest (4 * west phase depth) < column)
    (hcolumnEastGlobal : column < quarterEast (4 * east phase depth)) :
    FitsHorizontalChild phase depth column row boundary ↔
      ∃ blockX blockY : Fin 2,
        InChildInterval phase depth blockX column ∧
        InChildInterval phase depth blockY row ∧
        InChildInterval phase depth blockX boundary := by
  constructor
  · rintro ⟨blockX, blockY, houterSouth, houterNorth,
      hcolumnWest, hcolumnEast, hrowSouth, hrowNorth,
      hboundaryWest, hboundaryEast⟩
    rcases fitting_block_eq_child
      (coordinate := column) hcolumnWestGlobal hcolumnEastGlobal
      hcolumnWest hcolumnEast with rfl | rfl
    all_goals
      rcases contained_child_block_eq_child houterSouth houterNorth with rfl | rfl
    all_goals
      first
      | exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundaryWest, hboundaryEast⟩⟩
      | exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundaryWest, hboundaryEast⟩⟩
      | exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundaryWest, hboundaryEast⟩⟩
      | exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩,
          ⟨hcolumnWest, hcolumnEast⟩,
          ⟨hrowSouth, hrowNorth⟩,
          ⟨hboundaryWest, hboundaryEast⟩⟩
  · rintro ⟨blockX, blockY, hcolumn, hrow, hboundary⟩
    exact ⟨childBlock blockX, childBlock blockY,
      (child_contained phase depth blockY).1,
      (child_contained phase depth blockY).2,
      hcolumn.1, hcolumn.2, hrow.1, hrow.2,
      hboundary.1, hboundary.2⟩

theorem fitsVerticalChild_iff_regions
    (phase : Phase) (depth column row boundary : Nat)
    (hrowSouthGlobal : quarterSouth (4 * west phase depth) < row)
    (hrowNorthGlobal : row < quarterNorth (4 * east phase depth)) :
    FitsVerticalChild phase depth column row boundary ↔
      InSomeChild phase depth column ∧
        InSameChild phase depth row boundary := by
  rw [fitsVerticalChild_iff phase depth column row boundary
    hrowSouthGlobal hrowNorthGlobal]
  constructor
  · rintro ⟨blockX, blockY, hcolumn, hrow, hboundary⟩
    exact ⟨⟨blockX, hcolumn⟩, ⟨blockY, hrow, hboundary⟩⟩
  · rintro ⟨⟨blockX, hcolumn⟩, ⟨blockY, hrow, hboundary⟩⟩
    exact ⟨blockX, blockY, hcolumn, hrow, hboundary⟩

theorem fitsHorizontalChild_iff_regions
    (phase : Phase) (depth column row boundary : Nat)
    (hcolumnWestGlobal : quarterWest (4 * west phase depth) < column)
    (hcolumnEastGlobal : column < quarterEast (4 * east phase depth)) :
    FitsHorizontalChild phase depth column row boundary ↔
      InSameChild phase depth column boundary ∧
        InSomeChild phase depth row := by
  rw [fitsHorizontalChild_iff phase depth column row boundary
    hcolumnWestGlobal hcolumnEastGlobal]
  constructor
  · rintro ⟨blockX, blockY, hcolumn, hrow, hboundary⟩
    exact ⟨⟨blockX, hcolumn, hboundary⟩, ⟨blockY, hrow⟩⟩
  · rintro ⟨⟨blockX, hcolumn, hboundary⟩, ⟨blockY, hrow⟩⟩
    exact ⟨blockX, blockY, hcolumn, hrow, hboundary⟩

theorem not_fitsVerticalChild_iff_regions
    (phase : Phase) (depth column row boundary : Nat)
    (hrowSouthGlobal : quarterSouth (4 * west phase depth) < row)
    (hrowNorthGlobal : row < quarterNorth (4 * east phase depth)) :
    ¬FitsVerticalChild phase depth column row boundary ↔
      ¬InSomeChild phase depth column ∨
        ¬InSameChild phase depth row boundary := by
  rw [fitsVerticalChild_iff_regions phase depth column row boundary
    hrowSouthGlobal hrowNorthGlobal]
  tauto

theorem not_fitsHorizontalChild_iff_regions
    (phase : Phase) (depth column row boundary : Nat)
    (hcolumnWestGlobal : quarterWest (4 * west phase depth) < column)
    (hcolumnEastGlobal : column < quarterEast (4 * east phase depth)) :
    ¬FitsHorizontalChild phase depth column row boundary ↔
      ¬InSameChild phase depth column boundary ∨
        ¬InSomeChild phase depth row := by
  rw [fitsHorizontalChild_iff_regions phase depth column row boundary
    hcolumnWestGlobal hcolumnEastGlobal]
  tauto

/-- Executable classification of a vertical query as a seam case. -/
def verticalSeamCheck (phase : Phase) (depth column row boundary : Nat) : Bool :=
  decide (¬InSomeChild phase depth column ∨
    ¬InSameChild phase depth row boundary)

/-- Executable classification of a horizontal query as a seam case. -/
def horizontalSeamCheck (phase : Phase) (depth column row boundary : Nat) : Bool :=
  decide (¬InSameChild phase depth column boundary ∨
    ¬InSomeChild phase depth row)

theorem verticalSeamCheck_eq_true_iff
    (phase : Phase) (depth column row boundary : Nat)
    (hrowSouthGlobal : quarterSouth (4 * west phase depth) < row)
    (hrowNorthGlobal : row < quarterNorth (4 * east phase depth)) :
    verticalSeamCheck phase depth column row boundary = true ↔
      ¬FitsVerticalChild phase depth column row boundary := by
  rw [verticalSeamCheck, decide_eq_true_eq,
    not_fitsVerticalChild_iff_regions phase depth column row boundary
      hrowSouthGlobal hrowNorthGlobal]

theorem horizontalSeamCheck_eq_true_iff
    (phase : Phase) (depth column row boundary : Nat)
    (hcolumnWestGlobal : quarterWest (4 * west phase depth) < column)
    (hcolumnEastGlobal : column < quarterEast (4 * east phase depth)) :
    horizontalSeamCheck phase depth column row boundary = true ↔
      ¬FitsHorizontalChild phase depth column row boundary := by
  rw [horizontalSeamCheck, decide_eq_true_eq,
    not_fitsHorizontalChild_iff_regions phase depth column row boundary
      hcolumnWestGlobal hcolumnEastGlobal]

/-- The four scale-independent seam families left after recursive child
covers: transverse-outside and longitudinally-separated, in both
orientations. -/
structure RegionSeamCover : Prop where
  verticalOutside : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    quarterWest (4 * west phase depth) < column →
    column < quarterEast (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < row →
    row < quarterNorth (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < boundary →
    boundary < quarterNorth (4 * east phase depth) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    ¬InSomeChild phase depth column →
    VerticalGeometryWitness phase depth
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      column row boundary
  verticalSeparated : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    quarterWest (4 * west phase depth) < column →
    column < quarterEast (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < row →
    row < quarterNorth (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < boundary →
    boundary < quarterNorth (4 * east phase depth) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    ¬InSameChild phase depth row boundary →
    VerticalGeometryWitness phase depth
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      column row boundary
  horizontalSeparated : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    quarterWest (4 * west phase depth) < column →
    column < quarterEast (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < row →
    row < quarterNorth (4 * east phase depth) →
    quarterWest (4 * west phase depth) < boundary →
    boundary < quarterEast (4 * east phase depth) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    ¬InSameChild phase depth column boundary →
    HorizontalGeometryWitness phase depth
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      column row boundary
  horizontalOutside : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ChildCovers phase depth grid shadeGrid →
    quarterWest (4 * west phase depth) < column →
    column < quarterEast (4 * east phase depth) →
    quarterSouth (4 * west phase depth) < row →
    row < quarterNorth (4 * east phase depth) →
    quarterWest (4 * west phase depth) < boundary →
    boundary < quarterEast (4 * east phase depth) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    ¬InSomeChild phase depth row →
    HorizontalGeometryWitness phase depth
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      column row boundary

theorem seamCover_of_regionSeamCover (regions : RegionSeamCover) :
    SeamCover := by
  constructor
  · intro phase depth grid shadeGrid column row boundary valid children
      hwest heast hsouth hnorth hboundarySouth hboundaryNorth hselected hnotFit
    rcases (not_fitsVerticalChild_iff_regions phase depth column row boundary
      hsouth hnorth).1 hnotFit with houtside | hseparated
    · exact regions.verticalOutside phase depth grid shadeGrid valid children
        hwest heast hsouth hnorth hboundarySouth hboundaryNorth hselected houtside
    · exact regions.verticalSeparated phase depth grid shadeGrid valid children
        hwest heast hsouth hnorth hboundarySouth hboundaryNorth hselected hseparated
  · intro phase depth grid shadeGrid column row boundary valid children
      hwest heast hsouth hnorth hboundaryWest hboundaryEast hselected hnotFit
    rcases (not_fitsHorizontalChild_iff_regions phase depth column row boundary
      hwest heast).1 hnotFit with hseparated | houtside
    · exact regions.horizontalSeparated phase depth grid shadeGrid valid children
        hwest heast hsouth hnorth hboundaryWest hboundaryEast hselected hseparated
    · exact regions.horizontalOutside phase depth grid shadeGrid valid children
        hwest heast hsouth hnorth hboundaryWest hboundaryEast hselected houtside

/-- The four normalized seam families are the sole remaining recurrence
obligation. -/
theorem step_of_regionSeamCover (regions : RegionSeamCover) : Step :=
  step_of_childLift
    (childLift_of_seamCover (seamCover_of_regionSeamCover regions))

theorem forcesRoutedFixedCornerSquares_of_regionSeamCover
    (regions : RegionSeamCover) :
    ShadedRoutedScaffoldForward.ForcesRoutedFixedCornerSquares
      ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_step (step_of_regionSeamCover regions)
-/

end PairCoverSeamArithmetic
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
