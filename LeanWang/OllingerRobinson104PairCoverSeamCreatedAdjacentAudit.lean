/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAuditDefs
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


end PairCoverSeamCreatedAdjacentAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
