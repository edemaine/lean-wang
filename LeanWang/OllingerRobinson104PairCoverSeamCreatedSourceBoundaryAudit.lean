/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedSourceBoundaryAuditCheck
import LeanWang.OllingerRobinson104PairCoverSeamPathQuerySearch

/-! Proposition-level soundness for the created source-boundary audit. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedSourceBoundaryAudit

open RedShadeGraphSearchSoundness RedShadeGraphRefinement
  PairCoverSeamCreatedSourceBoundaryAuditCheck PairCoverSeamPathBoundedBase
  PairCoverSeamShadePaths Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- The finite checker supplies equality-query paths inside every depth-two
parent macrocell. -/
structure ParentPaths (parent : Index) : Prop where
  vertical :
    let grid := fineGrid parent
    ∀ {column boundary : Nat},
      column ∈ PairCoverSeamCreatedLocalAuditCheck.coordinates →
      boundary ∈ PairCoverSeamCreatedLocalAuditCheck.coordinates →
      PairCoverSeamCreatedLocalAuditCheck.isCreated boundary = true →
      Signals.horizontalInterior?
        (componentAt grid column boundary) (quadrantAt column boundary) =
          some .north →
      BoundedVerticalSeamPath grid 8 0 4 column boundary boundary
  horizontal :
    let grid := fineGrid parent
    ∀ {row boundary : Nat},
      row ∈ PairCoverSeamCreatedLocalAuditCheck.coordinates →
      boundary ∈ PairCoverSeamCreatedLocalAuditCheck.coordinates →
      PairCoverSeamCreatedLocalAuditCheck.isCreated boundary = true →
      Signals.verticalInterior?
        (componentAt grid boundary row) (quadrantAt boundary row) =
          some .east →
      BoundedHorizontalSeamPath grid 8 0 4 row boundary boundary

theorem parentPaths (parent : Index) : ParentPaths parent := by
  have checked := (List.all_eq_true.mp complete) parent (by simp)
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨verticalChecked, horizontalChecked⟩
  constructor
  · dsimp only
    intro column boundary hcolumn hboundary hcreated hnorth
    have queryMember : boundary ∈ verticalQueries
        (fineGrid parent) column boundary := by
      simp only [verticalQueries, List.mem_filter]
      exact ⟨hboundary, by simp [hcreated, hnorth]⟩
    apply verticalQueriesCheck_bounded_sound queryMember
    · simp only [PortInBounds, horizontalPort]
      split <;> simp_all [PairCoverSeamCreatedLocalAuditCheck.coordinates]
    · simp only [checkVerticalParent, List.all_eq_true] at verticalChecked
      exact verticalChecked column hcolumn boundary hboundary
  · dsimp only
    intro row boundary hrow hboundary hcreated heast
    have queryMember : boundary ∈ horizontalQueries
        (fineGrid parent) row boundary := by
      simp only [horizontalQueries, List.mem_filter]
      exact ⟨hboundary, by simp [hcreated, heast]⟩
    apply horizontalQueriesCheck_bounded_sound queryMember
    · simp only [PortInBounds, verticalPort]
      split <;> simp_all [PairCoverSeamCreatedLocalAuditCheck.coordinates]
    · simp only [checkHorizontalParent, List.all_eq_true] at horizontalChecked
      exact horizontalChecked row hrow boundary hboundary

end PairCoverSeamCreatedSourceBoundaryAudit
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
