/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditChunks
import LeanWang.OllingerRobinson104PairCoverSeamPathBoundedSearch

/-! Proposition-level soundness for adjacent created-boundary seam checks. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedAdjacentAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness PairCoverSeamPathSearch
  PairCoverSeamPathBoundedSearch PairCoverSeamShadePaths
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def RectangularVerticalSeamPath (grid : Nat → Nat → Index)
    (width height west east column row boundary : Nat) : Prop :=
  (∃ targetX,
    quarterWest west < targetX ∧ targetX < quarterEast east ∧
    Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
    BoundedPath grid width height (horizontalPort grid column boundary)
      (verticalPort grid targetX row) false) ∨
  (∃ targetY, StrictBetween row boundary targetY ∧
    Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
    BoundedPath grid width height (horizontalPort grid column boundary)
      (horizontalPort grid column targetY) false)

def RectangularHorizontalSeamPath (grid : Nat → Nat → Index)
    (width height south north row column boundary : Nat) : Prop :=
  (∃ targetY,
    quarterSouth south < targetY ∧ targetY < quarterNorth north ∧
    Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none ∧
    BoundedPath grid width height (verticalPort grid boundary row)
      (horizontalPort grid column targetY) false) ∨
  (∃ targetX, StrictBetween column boundary targetX ∧
    Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none ∧
    BoundedPath grid width height (verticalPort grid boundary row)
      (verticalPort grid targetX row) false)

theorem verticalReachSeamCheck_rectangular_sound
    {grid : Nat → Nat → Index} {width height west east column row boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      BoundedPath grid width height (horizontalPort grid column boundary)
        node.current node.parity)
    (checked : verticalReachSeamCheck grid west east
      column row boundary found = true) :
    RectangularVerticalSeamPath grid width height west east
      column row boundary := by
  simp only [verticalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have path : BoundedPath grid width height
      (horizontalPort grid column boundary) node.current false := by
    simpa [nodeParity] using paths node hnode
  simp only [verticalSeamTarget, Bool.or_eq_true] at htarget
  rcases htarget with htarget | htarget
  · simp only [verticalTarget, Bool.and_eq_true,
      decide_eq_true_eq] at htarget
    left
    refine ⟨node.current.x, htarget.1.1.1.1, htarget.1.1.1.2,
      Option.isSome_iff_ne_none.mp htarget.2, ?_⟩
    rw [← htarget.1.2]
    exact path
  · simp only [horizontalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at htarget
    right
    refine ⟨node.current.y, htarget.1.1.1,
      Option.isSome_iff_ne_none.mp htarget.2, ?_⟩
    rw [← htarget.1.2]
    exact path

theorem horizontalReachSeamCheck_rectangular_sound
    {grid : Nat → Nat → Index}
    {width height south north row column boundary : Nat}
    {found : List ReachNode}
    (paths : ∀ node ∈ found,
      BoundedPath grid width height (verticalPort grid boundary row)
        node.current node.parity)
    (checked : horizontalReachSeamCheck grid south north
      row column boundary found = true) :
    RectangularHorizontalSeamPath grid width height south north
      row column boundary := by
  simp only [horizontalReachSeamCheck, List.any_eq_true,
    Bool.and_eq_true] at checked
  rcases checked with ⟨node, hnode, hparity, htarget⟩
  have nodeParity : node.parity = false :=
    Bool.eq_false_of_not_eq_true' hparity
  have path : BoundedPath grid width height
      (verticalPort grid boundary row) node.current false := by
    simpa [nodeParity] using paths node hnode
  simp only [horizontalSeamTarget, Bool.or_eq_true] at htarget
  rcases htarget with htarget | htarget
  · simp only [horizontalTarget, Bool.and_eq_true,
      decide_eq_true_eq] at htarget
    left
    refine ⟨node.current.y, htarget.1.1.1.1, htarget.1.1.1.2,
      Option.isSome_iff_ne_none.mp htarget.2, ?_⟩
    rw [← htarget.1.2]
    exact path
  · simp only [verticalBetweenTarget, Bool.and_eq_true,
      decide_eq_true_eq] at htarget
    right
    refine ⟨node.current.x, htarget.1.1.1,
      Option.isSome_iff_ne_none.mp htarget.2, ?_⟩
    rw [← htarget.1.2]
    exact path

structure VerticalPairPaths (pair : PairState) : Prop where
  lower : ∀ {column boundary : Nat}, column ∈ List.range 8 →
    boundary ∈ createdCoordinates →
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (verticalGrid pair)) column boundary)
      (quadrantAt column boundary) = some .north →
    RectangularVerticalSeamPath
      (iterateRefine 2 (verticalGrid pair)) 8 16 0 4 column 8 boundary
  upper : ∀ {column boundary : Nat}, column ∈ List.range 8 →
    boundary ∈ createdCoordinates →
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (verticalGrid pair)) column (8 + boundary))
      (quadrantAt column (8 + boundary)) = some .south →
    RectangularVerticalSeamPath
      (iterateRefine 2 (verticalGrid pair)) 8 16 0 4
      column 7 (8 + boundary)

structure HorizontalPairPaths (pair : PairState) : Prop where
  left : ∀ {row boundary : Nat}, row ∈ List.range 8 →
    boundary ∈ createdCoordinates →
    Signals.verticalInterior?
      (componentAt (iterateRefine 2 (horizontalGrid pair)) boundary row)
      (quadrantAt boundary row) = some .east →
    RectangularHorizontalSeamPath
      (iterateRefine 2 (horizontalGrid pair)) 16 8 0 4 row 8 boundary
  right : ∀ {row boundary : Nat}, row ∈ List.range 8 →
    boundary ∈ createdCoordinates →
    Signals.verticalInterior?
      (componentAt (iterateRefine 2 (horizontalGrid pair)) (8 + boundary) row)
      (quadrantAt (8 + boundary) row) = some .west →
    RectangularHorizontalSeamPath
      (iterateRefine 2 (horizontalGrid pair)) 16 8 0 4
      row 7 (8 + boundary)

set_option maxHeartbeats 1000000 in
-- Unfolding both rectangular searches through the nested finite checks is costly.
theorem verticalPairPaths {pair : PairState} (hpair : pair ∈ verticalPairs) :
    VerticalPairPaths pair := by
  have checked := (List.all_eq_true.mp vertical_complete) pair hpair
  simp only [checkVerticalPair, List.all_eq_true] at checked
  constructor
  · intro column boundary hcolumn hboundary hinterior
    have entry := checked column hcolumn boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have lower := entry.1
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at lower
    apply verticalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply verticalReachCover_node_bounded_sound
      · simp only [PortInBounds, horizontalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact lower
  · intro column boundary hcolumn hboundary hinterior
    have entry := checked column hcolumn boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have upper := entry.2
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at upper
    apply verticalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply verticalReachCover_node_bounded_sound
      · simp only [PortInBounds, horizontalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact upper

set_option maxHeartbeats 1000000 in
-- Horizontal dual of the nested rectangular-search elaboration above.
theorem horizontalPairPaths {pair : PairState} (hpair : pair ∈ horizontalPairs) :
    HorizontalPairPaths pair := by
  have checked := (List.all_eq_true.mp horizontal_complete) pair hpair
  simp only [checkHorizontalPair, List.all_eq_true] at checked
  constructor
  · intro row boundary hrow hboundary hinterior
    have entry := checked row hrow boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have left := entry.1
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at left
    apply horizontalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply horizontalReachCover_node_bounded_sound
      · simp only [PortInBounds, verticalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact left
  · intro row boundary hrow hboundary hinterior
    have entry := checked row hrow boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have right := entry.2
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at right
    apply horizontalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply horizontalReachCover_node_bounded_sound
      · simp only [PortInBounds, verticalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact right

end PairCoverSeamCreatedAdjacentAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
