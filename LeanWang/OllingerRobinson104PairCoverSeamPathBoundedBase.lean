/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamPathBaseAudit
import LeanWang.OllingerRobinson104PairCoverSeamPathBoundedSearch
import LeanWang.OllingerRobinson104PairCoverSeamArithmetic
import LeanWang.OllingerRobinson104RedShadeGraphTranslation

/-!
# Bounded semantics of the seam base certificates

Successful cached Boolean checks imply seam paths whose intermediate ports all
remain in the searched parent block.  The bounded statement can consequently
be transported from a canonical parent representative and later into an
arbitrary coarse-grid block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathBoundedBase

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness BorderGeometry
  PairCoverSeamShadePaths PairCoverSeamPathSearch
  PairCoverSeamPathBoundedSearch PairCoverSeamPathBaseAudit
  PairCoverSeamArithmetic ShadedFreeLineRecurrence Signals.FreeCellLocal

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

private theorem boundedVerticalSeamPath_of_target
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

private theorem boundedHorizontalSeamPath_of_target
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

theorem verticalReachSeamCheck_bounded_sound_of_paths
    {grid : Nat → Nat → Index} {size west east column row boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      BoundedPath grid size size (horizontalPort grid column boundary)
        node.current node.parity)
    (checked : verticalReachSeamCheck grid west east
      column row boundary found = true) :
    BoundedVerticalSeamPath grid size west east column row boundary := by
  simp only [verticalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : BoundedPath grid size size
      (horizontalPort grid column boundary) node.current false := by
    simpa [nodeParity] using paths node hnode
  exact boundedVerticalSeamPath_of_target pathFalse htarget

theorem horizontalReachSeamCheck_bounded_sound_of_paths
    {grid : Nat → Nat → Index} {size south north row column boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      BoundedPath grid size size (verticalPort grid boundary row)
        node.current node.parity)
    (checked : horizontalReachSeamCheck grid south north
      row column boundary found = true) :
    BoundedHorizontalSeamPath grid size south north row column boundary := by
  simp only [horizontalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have pathFalse : BoundedPath grid size size
      (verticalPort grid boundary row) node.current false := by
    simpa [nodeParity] using paths node hnode
  exact boundedHorizontalSeamPath_of_target pathFalse htarget

theorem verticalQueriesCheck_bounded_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel west east column boundary row : Nat}
    {queries : List Nat} (hrow : row ∈ queries)
    (startBound : PortInBounds (horizontalPort grid column boundary) size size)
    (checked : verticalQueriesCheck grid size fuel fallbackFuel
      west east column boundary queries = true) :
    BoundedVerticalSeamPath grid size west east column row boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hrow
  | cons first rest =>
      subst queries
      simp only [verticalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have rowChecked := checked row hrow
      simp only [Bool.or_eq_true] at rowChecked
      rcases rowChecked with hfound | hfallback
      · exact verticalReachSeamCheck_bounded_sound_of_paths
          (fun _ hnode => verticalReachCover_node_bounded_sound startBound hnode)
          hfound
      · let missing := (first :: rest).filter fun query =>
          !verticalReachSeamCheck grid west east column query boundary
            (verticalReachCover grid size size fuel
              west east column boundary (first :: rest))
        change verticalReachSeamCheck grid west east column row boundary
          (match missing with
            | [] => []
            | _ => verticalReachCover grid size size fallbackFuel
                west east column boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, verticalReachSeamCheck] at hfallback
        | cons query queries =>
            apply verticalReachSeamCheck_bounded_sound_of_paths
              (fun _ hnode => verticalReachCover_node_bounded_sound startBound hnode)
            simpa [hmissing] using hfallback

theorem horizontalQueriesCheck_bounded_sound
    {grid : Nat → Nat → Index}
    {size fuel fallbackFuel south north row boundary column : Nat}
    {queries : List Nat} (hcolumn : column ∈ queries)
    (startBound : PortInBounds (verticalPort grid boundary row) size size)
    (checked : horizontalQueriesCheck grid size fuel fallbackFuel
      south north row boundary queries = true) :
    BoundedHorizontalSeamPath grid size south north row column boundary := by
  cases hqueries : queries with
  | nil => simp [hqueries] at hcolumn
  | cons first rest =>
      subst queries
      simp only [horizontalQueriesCheck] at checked
      simp only [List.all_eq_true] at checked
      have columnChecked := checked column hcolumn
      simp only [Bool.or_eq_true] at columnChecked
      rcases columnChecked with hfound | hfallback
      · exact horizontalReachSeamCheck_bounded_sound_of_paths
          (fun _ hnode => horizontalReachCover_node_bounded_sound startBound hnode)
          hfound
      · let missing := (first :: rest).filter fun query =>
          !horizontalReachSeamCheck grid south north row query boundary
            (horizontalReachCover grid size size fuel
              south north row boundary (first :: rest))
        change horizontalReachSeamCheck grid south north row column boundary
          (match missing with
            | [] => []
            | _ => horizontalReachCover grid size size fallbackFuel
                south north row boundary missing) = true at hfallback
        cases hmissing : missing with
        | nil => simp [hmissing, horizontalReachSeamCheck] at hfallback
        | cons query queries =>
            apply horizontalReachSeamCheck_bounded_sound_of_paths
              (fun _ hnode => horizontalReachCover_node_bounded_sound startBound hnode)
            simpa [hmissing] using hfallback

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

private theorem horizontalPort_inBounds
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {column boundary : Nat}
    (hcolumn : column ∈ coordinates phase depth)
    (hboundary : boundary ∈ coordinates phase depth) :
    PortInBounds (horizontalPort grid column boundary)
      (searchSize phase depth) (searchSize phase depth) := by
  have hx := coordinate_lt_searchSize hcolumn
  have hy := coordinate_lt_searchSize hboundary
  unfold horizontalPort
  split <;> exact ⟨hx, hy⟩

private theorem verticalPort_inBounds
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {boundary row : Nat}
    (hboundary : boundary ∈ coordinates phase depth)
    (hrow : row ∈ coordinates phase depth) :
    PortInBounds (verticalPort grid boundary row)
      (searchSize phase depth) (searchSize phase depth) := by
  have hx := coordinate_lt_searchSize hboundary
  have hy := coordinate_lt_searchSize hrow
  unfold verticalPort
  split <;> exact ⟨hx, hy⟩

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

theorem checkParent_bounded_sound
    {phase : Phase} {depth : Nat} {parent : Index}
    (checked : checkParent phase depth parent = true) :
    BoundedParentPaths phase depth parent := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at checked
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    exact verticalQueriesCheck_bounded_sound hrow
      (horizontalPort_inBounds hcolumn hboundary)
      (checked.1 column hcolumn boundary hboundary)
  · dsimp only
    intro boundary row column hboundary hrow hcolumn
    exact horizontalQueriesCheck_bounded_sound hcolumn
      (verticalPort_inBounds hboundary hrow)
      (checked.2 boundary hboundary row hrow)

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

theorem ChunkChecks.boundedPaths {phase : Phase} {depth : Nat}
    (checked : ChunkChecks phase depth) : BoundedPaths phase depth := by
  apply BoundedCanonicalPaths.paths
  intro parent hparent
  rw [canonicalParents_eq_chunks] at hparent
  simp only [List.mem_flatMap] at hparent
  rcases hparent with ⟨chunk, _, hparent⟩
  apply checkParent_bounded_sound
  have chunkChecked := checked chunk
  simp only [checkChunk, List.all_eq_true] at chunkChecked
  exact chunkChecked parent hparent

end PairCoverSeamPathBoundedBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
