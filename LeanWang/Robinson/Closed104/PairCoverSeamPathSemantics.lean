/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamChecks
import LeanWang.Robinson.Closed104.PairCoverSeamPathSearch
import LeanWang.Robinson.Closed104.BorderGeometry
import LeanWang.Robinson.Closed104.ShadedFreeLineCoordinates
import LeanWang.Robinson.Closed104.PairCoverSeamArithmetic
import LeanWang.Robinson.Closed104.RedShadeGraphTranslation
import LeanWang.Robinson.Closed104.RedShadeGraphWeightedReachBounded

/-!
# Seam-path certificate semantics

Logical seam-path predicates, finite parent coordinates, and canonical-parent
transport shared by both the committed component certificates and the optional
exhaustive base-search audit.  This module performs no exhaustive search.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathBaseAudit

open RedCycles RedShadeCycles RedShadeGraph
  ShadedFreeLineRecurrence
  PairCoverSeamArithmetic
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  Signals.FreeCellLocal BorderGeometry

set_option maxRecDepth 20000

def fineGrid (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  iterateRefine 2 (iterateRefine (refinementDepth phase depth) grid)

def coordinates (phase : Phase) (depth : Nat) : List Nat :=
  (List.range (quarterNorth (successorEast phase depth 0))).filter fun value =>
    quarterSouth (successorWest phase depth 0) < value

def searchSize (phase : Phase) (depth : Nat) : Nat :=
  2 ^ (refinementDepth phase depth + 3)

def verticalQueries (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (coords : List Nat)
    (column boundary : Nat) : List Nat :=
  let interior := Signals.horizontalInterior?
    (componentAt grid column boundary) (quadrantAt column boundary)
  coords.filter fun row =>
    (((decide (row < boundary) && decide (interior = some .south)) ||
      (decide (boundary < row) && decide (interior = some .north))) &&
      containedVerticalSeamCheck phase depth 0 0 column row boundary)

def horizontalQueries (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (coords : List Nat)
    (row boundary : Nat) : List Nat :=
  let interior := Signals.verticalInterior?
    (componentAt grid boundary row) (quadrantAt boundary row)
  coords.filter fun column =>
    (((decide (column < boundary) && decide (interior = some .west)) ||
      (decide (boundary < column) && decide (interior = some .east))) &&
      containedHorizontalSeamCheck phase depth 0 0 column row boundary)

structure ParentPaths (phase : Phase) (depth : Nat) (parent : Index) : Prop where
  vertical :
    let grid := fineGrid phase depth (fun _ _ => parent)
    let coords := coordinates phase depth
    ∀ {column boundary row : Nat}, column ∈ coords → boundary ∈ coords →
      row ∈ verticalQueries phase depth grid coords column boundary →
      VerticalSeamPath grid (successorWest phase depth 0)
        (successorEast phase depth 0) column row boundary
  horizontal :
    let grid := fineGrid phase depth (fun _ _ => parent)
    let coords := coordinates phase depth
    ∀ {boundary row column : Nat}, boundary ∈ coords → row ∈ coords →
      column ∈ horizontalQueries phase depth grid coords row boundary →
      HorizontalSeamPath grid (successorWest phase depth 0)
        (successorEast phase depth 0) row column boundary

def Paths (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent : Index, ParentPaths phase depth parent

theorem horizontalPort_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (x y : Nat) :
    horizontalPort first x y = horizontalPort second x y := by
  simp only [horizontalPort, same x y]

theorem verticalPort_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    (x y : Nat) :
    verticalPort first x y = verticalPort second x y := by
  simp only [verticalPort, same x y]

theorem verticalSeamPath_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    {west east column row boundary : Nat}
    (path : VerticalSeamPath first west east column row boundary) :
    VerticalSeamPath second west east column row boundary := by
  rcases path with path | path
  · left
    rcases path with ⟨targetX, hwest, heast, hinterior, path⟩
    refine ⟨targetX, hwest, heast, ?_, ?_⟩
    · simpa [same targetX row] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [horizontalPort_congr_of_sameComponents same,
        verticalPort_congr_of_sameComponents same] using transported
  · right
    rcases path with ⟨targetY, hbetween, hinterior, path⟩
    refine ⟨targetY, hbetween, ?_, ?_⟩
    · simpa [same column targetY] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [horizontalPort_congr_of_sameComponents same] using transported

theorem horizontalSeamPath_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    {south north row column boundary : Nat}
    (path : HorizontalSeamPath first south north row column boundary) :
    HorizontalSeamPath second south north row column boundary := by
  rcases path with path | path
  · left
    rcases path with ⟨targetY, hsouth, hnorth, hinterior, path⟩
    refine ⟨targetY, hsouth, hnorth, ?_, ?_⟩
    · simpa [same column targetY] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [verticalPort_congr_of_sameComponents same,
        horizontalPort_congr_of_sameComponents same] using transported
  · right
    rcases path with ⟨targetX, hbetween, hinterior, path⟩
    refine ⟨targetX, hbetween, ?_, ?_⟩
    · simpa [same targetX row] using hinterior
    · have transported := path_congr_of_sameComponents same path
      simpa only [verticalPort_congr_of_sameComponents same] using transported

theorem sameComponents_fineGrid_canonicalIndex
    (phase : Phase) (depth : Nat) (parent : Index) :
    SameComponents
      (fineGrid phase depth
        (fun _ _ => BorderSubstitution.canonicalIndex parent))
      (fineGrid phase depth (fun _ _ => parent)) := by
  change SameComponents
    (iterateRefine 2 (iterateRefine (refinementDepth phase depth)
      (fun _ _ => BorderSubstitution.canonicalIndex parent)))
    (iterateRefine 2 (iterateRefine (refinementDepth phase depth)
      (fun _ _ => parent)))
  rw [PlaneRedBoards.iterateRefine_add,
    PlaneRedBoards.iterateRefine_add]
  have same := sameComponents_iterateRefine_canonicalizeGrid
    (2 + refinementDepth phase depth) (fun _ _ => parent)
  have gridEquality : (fun _ _ => BorderSubstitution.canonicalIndex parent) =
      BorderSubstitution.canonicalizeGrid (fun _ _ => parent) := by
    funext x y
    rfl
  rw [gridEquality]
  exact same

theorem ParentPaths.of_canonicalIndex
    {phase : Phase} {depth : Nat} {parent : Index}
    (canonical : ParentPaths phase depth
      (BorderSubstitution.canonicalIndex parent)) :
    ParentPaths phase depth parent := by
  let canonicalGrid := fineGrid phase depth
    (fun _ _ => BorderSubstitution.canonicalIndex parent)
  let grid := fineGrid phase depth (fun _ _ => parent)
  have same : SameComponents canonicalGrid grid := by
    simpa [canonicalGrid, grid] using
      (sameComponents_fineGrid_canonicalIndex phase depth parent)
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    have canonicalRow : row ∈ verticalQueries phase depth canonicalGrid
        (coordinates phase depth) column boundary := by
      simp only [verticalQueries, List.mem_filter] at hrow ⊢
      refine ⟨hrow.1, ?_⟩
      simpa [same column boundary] using hrow.2
    have path := canonical.vertical hcolumn hboundary canonicalRow
    exact verticalSeamPath_congr_of_sameComponents same path
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    have canonicalColumn : column ∈ horizontalQueries phase depth canonicalGrid
        (coordinates phase depth) row boundary := by
      simp only [horizontalQueries, List.mem_filter] at hcolumn ⊢
      refine ⟨hcolumn.1, ?_⟩
      simpa [same boundary row] using hcolumn.2
    have path := canonical.horizontal hboundary hrow canonicalColumn
    exact horizontalSeamPath_congr_of_sameComponents same path

def canonicalParents : List Index :=
  BorderSubstitution.states.map BorderSubstitution.representative

abbrev Chunk := Fin 14

def parentChunk (chunk : Chunk) : List Index :=
  (canonicalParents.drop (4 * chunk.val)).take 4

set_option linter.style.nativeDecide false in
theorem canonicalParents_eq_chunks :
    canonicalParents = (List.finRange 14).flatMap parentChunk := by
  native_decide

def CanonicalPaths (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent ∈ canonicalParents, ParentPaths phase depth parent

theorem CanonicalPaths.paths {phase : Phase} {depth : Nat}
    (canonical : CanonicalPaths phase depth) : Paths phase depth := by
  intro parent
  apply ParentPaths.of_canonicalIndex
  apply canonical
  exact List.mem_map.2
    ⟨BorderSubstitution.indexState parent,
      BorderSubstitution.indexState_mem_states parent, rfl⟩

end PairCoverSeamPathBaseAudit

namespace PairCoverSeamPathBoundedBase

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness BorderGeometry
  PairCoverSeamShadePaths PairCoverSeamPathSearch
  PairCoverSeamPathBaseAudit PairCoverSeamArithmetic
  ShadedFreeLineRecurrence Signals.FreeCellLocal

set_option maxRecDepth 20000

def BoundedVerticalSeamPath (grid : Nat → Nat → Index) (size : Nat)
    (west east column row boundary : Nat) : Prop :=
  (∃ targetX,
    quarterWest west < targetX ∧ targetX < quarterEast east ∧
    Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
    BoundedPath grid size size (horizontalPort grid column boundary)
      (verticalPort grid targetX row) false) ∨
  (∃ targetY, StrictBetween row boundary targetY ∧
    Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
    BoundedPath grid size size (horizontalPort grid column boundary)
      (horizontalPort grid column targetY) false)

def BoundedHorizontalSeamPath (grid : Nat → Nat → Index) (size : Nat)
    (south north row column boundary : Nat) : Prop :=
  (∃ targetY,
    quarterSouth south < targetY ∧ targetY < quarterNorth north ∧
    Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
    BoundedPath grid size size (verticalPort grid boundary row)
      (horizontalPort grid column targetY) false) ∨
  (∃ targetX, StrictBetween column boundary targetX ∧
    Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
    BoundedPath grid size size (verticalPort grid boundary row)
      (verticalPort grid targetX row) false)

theorem boundedVerticalSeamPath_of_target
    {grid : Nat → Nat → Index} {size west east column row boundary : Nat}
    {finish : Port}
    (path : BoundedPath grid size size
      (horizontalPort grid column boundary) finish false)
    (target : verticalSeamTarget grid west east
      column row boundary finish = true) :
    BoundedVerticalSeamPath grid size west east column row boundary := by
  simp only [verticalSeamTarget, Bool.or_eq_true] at target
  rcases target with hvertical | hbetween
  · simp only [verticalTarget, Bool.and_eq_true, decide_eq_true_eq] at hvertical
    left
    refine ⟨finish.x, hvertical.1.1.1.1, hvertical.1.1.1.2,
      Option.isSome_iff_ne_none.mp hvertical.2, ?_⟩
    rw [← hvertical.1.2]
    exact path
  · simp only [horizontalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hbetween
    right
    refine ⟨finish.y, hbetween.1.1.1,
      Option.isSome_iff_ne_none.mp hbetween.2, ?_⟩
    rw [← hbetween.1.2]
    exact path

theorem boundedHorizontalSeamPath_of_target
    {grid : Nat → Nat → Index} {size south north row column boundary : Nat}
    {finish : Port}
    (path : BoundedPath grid size size
      (verticalPort grid boundary row) finish false)
    (target : horizontalSeamTarget grid south north
      row column boundary finish = true) :
    BoundedHorizontalSeamPath grid size south north row column boundary := by
  simp only [horizontalSeamTarget, Bool.or_eq_true] at target
  rcases target with hhorizontal | hbetween
  · simp only [horizontalTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hhorizontal
    left
    refine ⟨finish.y, hhorizontal.1.1.1.1, hhorizontal.1.1.1.2,
      Option.isSome_iff_ne_none.mp hhorizontal.2, ?_⟩
    rw [← hhorizontal.1.2]
    exact path
  · simp only [verticalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at hbetween
    right
    refine ⟨finish.x, hbetween.1.1.1,
      Option.isSome_iff_ne_none.mp hbetween.2, ?_⟩
    rw [← hbetween.1.2]
    exact path

theorem coordinate_lt_searchSize {phase : Phase} {depth coordinate : Nat}
    (hcoordinate : coordinate ∈ coordinates phase depth) :
    coordinate < searchSize phase depth := by
  simp only [coordinates, List.mem_filter, List.mem_range] at hcoordinate
  have hpow := two_pow_refinementDepth_eq_four_mul_west phase depth
  have hwest := west_pos phase depth
  have heast : east phase depth = 3 * west phase depth := rfl
  have heastSucc : east phase (depth + 1) = 4 * east phase depth :=
    east_succ phase depth
  have hupper : quarterNorth (successorEast phase depth 0) ≤
      searchSize phase depth := by
    simp only [successorEast, Nat.mul_zero, Nat.zero_add, searchSize,
      quarterNorth, pow_add, hpow, heastSucc, heast]
    nlinarith
  exact hcoordinate.1.trans_le hupper

structure BoundedParentPaths (phase : Phase) (depth : Nat)
    (parent : Index) : Prop where
  vertical :
    let grid := fineGrid phase depth (fun _ _ => parent)
    let coords := coordinates phase depth
    ∀ {column boundary row : Nat}, column ∈ coords → boundary ∈ coords →
      row ∈ verticalQueries phase depth grid coords column boundary →
      BoundedVerticalSeamPath grid (searchSize phase depth)
        (successorWest phase depth 0) (successorEast phase depth 0)
        column row boundary
  horizontal :
    let grid := fineGrid phase depth (fun _ _ => parent)
    let coords := coordinates phase depth
    ∀ {boundary row column : Nat}, boundary ∈ coords → row ∈ coords →
      column ∈ horizontalQueries phase depth grid coords row boundary →
      BoundedHorizontalSeamPath grid (searchSize phase depth)
        (successorWest phase depth 0) (successorEast phase depth 0)
        row column boundary

def BoundedPaths (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent : Index, BoundedParentPaths phase depth parent

private theorem boundedPath_congr_of_sameComponents
    {first second : Nat → Nat → Index} (same : SameComponents first second)
    {size : Nat} {start finish : Port} {parity : Bool}
    (path : BoundedPath first size size start finish parity) :
    BoundedPath second size size start finish parity :=
  RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
    (fun x y _ _ => same x y) path

set_option maxHeartbeats 1000000 in
-- Dependent endpoint transport across both disjunctive path families is costly.
theorem BoundedParentPaths.of_canonicalIndex
    {phase : Phase} {depth : Nat} {parent : Index}
    (canonical : BoundedParentPaths phase depth
      (BorderSubstitution.canonicalIndex parent)) :
    BoundedParentPaths phase depth parent := by
  have same : SameComponents
      (fineGrid phase depth
        (fun _ _ => BorderSubstitution.canonicalIndex parent))
      (fineGrid phase depth (fun _ _ => parent)) :=
    sameComponents_fineGrid_canonicalIndex phase depth parent
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    have canonicalRow : row ∈ verticalQueries phase depth
        (fineGrid phase depth
          (fun _ _ => BorderSubstitution.canonicalIndex parent))
        (coordinates phase depth) column boundary := by
      simp only [verticalQueries, List.mem_filter] at hrow ⊢
      refine ⟨hrow.1, ?_⟩
      rw [same column boundary]
      exact hrow.2
    rcases canonical.vertical hcolumn hboundary canonicalRow with path | path
    · left
      rcases path with ⟨targetX, hwest, heast, hinterior, path⟩
      refine ⟨targetX, hwest, heast, ?_, ?_⟩
      · rw [← same targetX row]
        exact hinterior
      · have hsource := horizontalPort_congr_of_sameComponents same column boundary
        have htarget := verticalPort_congr_of_sameComponents same targetX row
        simpa only [hsource, htarget] using
          (boundedPath_congr_of_sameComponents same path)
    · right
      rcases path with ⟨targetY, hbetween, hinterior, path⟩
      refine ⟨targetY, hbetween, ?_, ?_⟩
      · rw [← same column targetY]
        exact hinterior
      · have hsource := horizontalPort_congr_of_sameComponents same column boundary
        have htarget := horizontalPort_congr_of_sameComponents same column targetY
        simpa only [hsource, htarget] using
          (boundedPath_congr_of_sameComponents same path)
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    have canonicalColumn : column ∈ horizontalQueries phase depth
        (fineGrid phase depth
          (fun _ _ => BorderSubstitution.canonicalIndex parent))
        (coordinates phase depth) row boundary := by
      simp only [horizontalQueries, List.mem_filter] at hcolumn ⊢
      refine ⟨hcolumn.1, ?_⟩
      rw [same boundary row]
      exact hcolumn.2
    rcases canonical.horizontal hboundary hrow canonicalColumn with path | path
    · left
      rcases path with ⟨targetY, hsouth, hnorth, hinterior, path⟩
      refine ⟨targetY, hsouth, hnorth, ?_, ?_⟩
      · rw [← same column targetY]
        exact hinterior
      · have hsource := verticalPort_congr_of_sameComponents same boundary row
        have htarget := horizontalPort_congr_of_sameComponents same column targetY
        simpa only [hsource, htarget] using
          (boundedPath_congr_of_sameComponents same path)
    · right
      rcases path with ⟨targetX, hbetween, hinterior, path⟩
      refine ⟨targetX, hbetween, ?_, ?_⟩
      · rw [← same targetX row]
        exact hinterior
      · have hsource := verticalPort_congr_of_sameComponents same boundary row
        have htarget := verticalPort_congr_of_sameComponents same targetX row
        simpa only [hsource, htarget] using
          (boundedPath_congr_of_sameComponents same path)

def BoundedCanonicalPaths (phase : Phase) (depth : Nat) : Prop :=
  ∀ parent ∈ canonicalParents, BoundedParentPaths phase depth parent

theorem BoundedCanonicalPaths.paths {phase : Phase} {depth : Nat}
    (canonical : BoundedCanonicalPaths phase depth) : BoundedPaths phase depth := by
  intro parent
  apply BoundedParentPaths.of_canonicalIndex
  apply canonical
  exact List.mem_map.2
    ⟨BorderSubstitution.indexState parent,
      BorderSubstitution.indexState_mem_states parent, rfl⟩

end PairCoverSeamPathBoundedBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
