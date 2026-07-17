/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedLocalAuditCheck
import LeanWang.Robinson.Closed104.PairCoverSeamPathQuerySearch

/-! Proposition-level soundness for the local created-coordinate seam audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedLocalAudit

open RedShadeGraphSearchSoundness RedShadeGraphRefinement
  PairCoverSeamShadePaths PairCoverSeamPathBoundedBase
  PairCoverSeamCreatedLocalAuditCheck

set_option maxRecDepth 20000

/-- The checked local paths retain their macrocell bounds so they can later be
translated into an arbitrary refined grid. -/
structure ParentPaths (parent : Index) : Prop where
  vertical :
    let grid := RedShadeGraphRefinement.fineGrid parent
    ∀ {column boundary row : Nat},
      column ∈ coordinates → boundary ∈ coordinates →
      row ∈ verticalQueries grid column boundary →
      BoundedVerticalSeamPath grid 8 0 4 column row boundary
  horizontal :
    let grid := RedShadeGraphRefinement.fineGrid parent
    ∀ {row boundary column : Nat},
      row ∈ coordinates → boundary ∈ coordinates →
      column ∈ horizontalQueries grid row boundary →
      BoundedHorizontalSeamPath grid 8 0 4 row column boundary

theorem parentPaths (parent : Index) : ParentPaths parent := by
  have checked := (List.all_eq_true.mp complete) parent (by simp)
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨verticalChecked, horizontalChecked⟩
  constructor
  · dsimp only
    intro column boundary row hcolumn hboundary hrow
    apply verticalQueriesCheck_bounded_sound hrow
    · simp only [PortInBounds, horizontalPort]
      split <;> simp_all [coordinates]
    · simp only [checkVerticalParent, List.all_eq_true] at verticalChecked
      exact verticalChecked column hcolumn boundary hboundary
  · dsimp only
    intro row boundary column hrow hboundary hcolumn
    apply horizontalQueriesCheck_bounded_sound hcolumn
    · simp only [PortInBounds, verticalPort]
      split <;> simp_all [coordinates]
    · simp only [checkHorizontalParent, List.all_eq_true] at horizontalChecked
      exact horizontalChecked row hrow boundary hboundary

end PairCoverSeamCreatedLocalAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
