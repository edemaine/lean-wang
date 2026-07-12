/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionPairCoverRecurrence

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

open RedShadeCycles ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence

/-- The refinement block width is four times the current board scale. -/
theorem two_pow_refinementDepth_eq_four_mul_west
    (phase : Phase) (depth : Nat) :
    2 ^ refinementDepth phase depth = 4 * west phase depth := by
  cases phase <;>
    simp [refinementDepth, Phase.extra, west, scale, Phase.factor,
      pow_add, pow_mul] <;> ring

/-- The southwest/northeast child selector as an ordinary block index. -/
def childBlock (side : Fin 2) : Nat := side.val + 1

/-- Strict membership in one recursive child's quarter-coordinate interval. -/
def InChildInterval (phase : Phase) (depth : Nat)
    (side : Fin 2) (coordinate : Nat) : Prop :=
  quarterWest
      (2 ^ refinementDepth phase depth * childBlock side + west phase depth) <
      coordinate ∧
    coordinate < quarterEast
      (2 ^ refinementDepth phase depth * childBlock side + east phase depth)

def InSomeChild (phase : Phase) (depth coordinate : Nat) : Prop :=
  ∃ side : Fin 2, InChildInterval phase depth side coordinate

def InSameChild (phase : Phase) (depth first second : Nat) : Prop :=
  ∃ side : Fin 2,
    InChildInterval phase depth side first ∧
      InChildInterval phase depth side second

theorem west_pos (phase : Phase) (depth : Nat) : 0 < west phase depth := by
  cases phase <;> simp [west, scale, Phase.factor]

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

end PairCoverSeamArithmetic
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
