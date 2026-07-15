/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentAudit
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentFullAuditChunks

/-! Proposition-level soundness for the full adjacent-macrocell audit. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedAdjacentFullAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness PairCoverSeamPathSearch
  PairCoverSeamPathBoundedSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedAdjacentAudit Signals.FreeCellLocal

set_option maxRecDepth 20000

structure VerticalPairPaths (pair : PairState) : Prop where
  lower : ∀ {column boundary row : Nat}, column ∈ List.range 8 →
    boundary ∈ createdCoordinates → row ∈ upperQueries →
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (verticalGrid pair)) column boundary)
      (quadrantAt column boundary) = some .north →
    RectangularVerticalSeamPath
      (iterateRefine 2 (verticalGrid pair)) 8 16 0 4
      column row boundary
  upper : ∀ {column boundary row : Nat}, column ∈ List.range 8 →
    boundary ∈ createdCoordinates → row ∈ lowerQueries →
    Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (verticalGrid pair)) column (8 + boundary))
      (quadrantAt column (8 + boundary)) = some .south →
    RectangularVerticalSeamPath
      (iterateRefine 2 (verticalGrid pair)) 8 16 0 4
      column row (8 + boundary)

structure HorizontalPairPaths (pair : PairState) : Prop where
  left : ∀ {row boundary column : Nat}, row ∈ List.range 8 →
    boundary ∈ createdCoordinates → column ∈ rightQueries →
    Signals.verticalInterior?
      (componentAt (iterateRefine 2 (horizontalGrid pair)) boundary row)
      (quadrantAt boundary row) = some .east →
    RectangularHorizontalSeamPath
      (iterateRefine 2 (horizontalGrid pair)) 16 8 0 4
      row column boundary
  right : ∀ {row boundary column : Nat}, row ∈ List.range 8 →
    boundary ∈ createdCoordinates → column ∈ leftQueries →
    Signals.verticalInterior?
      (componentAt (iterateRefine 2 (horizontalGrid pair)) (8 + boundary) row)
      (quadrantAt (8 + boundary) row) = some .west →
    RectangularHorizontalSeamPath
      (iterateRefine 2 (horizontalGrid pair)) 16 8 0 4
      row column (8 + boundary)

set_option maxHeartbeats 1000000 in
-- Unfolding the nested finite checks requires a larger elaboration budget.
theorem verticalPairPaths {pair : PairState}
    (hpair : pair ∈ PairCoverSeamCreatedAdjacentAudit.verticalPairs) :
    VerticalPairPaths pair := by
  have checked := (List.all_eq_true.mp vertical_complete) pair hpair
  simp only [checkVerticalPair, List.all_eq_true] at checked
  constructor
  · intro column boundary row hcolumn hboundary hrow hinterior
    have entry := checked column hcolumn boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have lower := entry.1
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at lower
    have lower := List.all_eq_true.mp lower
    apply verticalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply verticalReachCover_node_bounded_sound
      · simp only [PortInBounds, horizontalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact lower row hrow
  · intro column boundary row hcolumn hboundary hrow hinterior
    have entry := checked column hcolumn boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have upper := entry.2
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at upper
    have upper := List.all_eq_true.mp upper
    apply verticalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply verticalReachCover_node_bounded_sound
      · simp only [PortInBounds, horizontalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact upper row hrow

set_option maxHeartbeats 1000000 in
-- Horizontal dual of the nested finite-check soundness proof above.
theorem horizontalPairPaths {pair : PairState}
    (hpair : pair ∈ PairCoverSeamCreatedAdjacentAudit.horizontalPairs) :
    HorizontalPairPaths pair := by
  have checked := (List.all_eq_true.mp horizontal_complete) pair hpair
  simp only [checkHorizontalPair, List.all_eq_true] at checked
  constructor
  · intro row boundary column hrow hboundary hcolumn hinterior
    have entry := checked row hrow boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have left := entry.1
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at left
    have left := List.all_eq_true.mp left
    apply horizontalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply horizontalReachCover_node_bounded_sound
      · simp only [PortInBounds, verticalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact left column hcolumn
  · intro row boundary column hrow hboundary hcolumn hinterior
    have entry := checked row hrow boundary hboundary
    simp only [Bool.and_eq_true] at entry
    have right := entry.2
    simp only [hinterior, decide_true, Bool.not_true, Bool.false_or] at right
    have right := List.all_eq_true.mp right
    apply horizontalReachSeamCheck_rectangular_sound
    · intro node hnode
      apply horizontalReachCover_node_bounded_sound
      · simp only [PortInBounds, verticalPort]
        split <;> simp_all [List.mem_range, createdCoordinates] <;> omega
      · exact hnode
    · exact right column hcolumn

end PairCoverSeamCreatedAdjacentFullAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
