/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBaseAudit

/-!
# Project the nearest-boundary audit to an arbitrary parent

The expensive native check is cached once over the 56 border states.  These
lemmas expose its coverage and nearest-boundary conclusions for the canonical
representative of any corrected tile type and either outer-board shade.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryBaseComplete

open BorderSubstitution ShadedObstructionGeometryBaseAudit

private theorem canonical_mem_representatives (parent : Index) :
    canonicalIndex parent ∈ states.map representative := by
  exact List.mem_map.2
    ⟨indexState parent, indexState_mem_states parent, rfl⟩

private theorem checked_canonical (parent : Index) :
    let canonical := canonicalIndex parent
    let visited := reachedBitmap (ShadedFreeLineGraphBase.nodes canonical)
    coverageFor canonical visited = true ∧
      completeFor canonical visited false = true ∧
      completeFor canonical visited true = true := by
  have checked := complete_eq_true
  unfold complete at checked
  have hall := List.all_eq_true.mp checked
  have hcanonical := hall (canonicalIndex parent)
    (canonical_mem_representatives parent)
  simp only [Bool.and_eq_true] at hcanonical
  exact ⟨hcanonical.1.1, hcanonical.1.2, hcanonical.2⟩

theorem coverageFor_canonical_eq_true (parent : Index) :
    coverageFor (canonicalIndex parent)
      (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent))) = true :=
  (checked_canonical parent).1

theorem completeFor_canonical_eq_true (parent : Index) (parentLight : Bool) :
    completeFor (canonicalIndex parent)
      (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
      parentLight = true := by
  cases parentLight
  · exact (checked_canonical parent).2.1
  · exact (checked_canonical parent).2.2

theorem vertical_case (parent : Index) (parentLight : Bool)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hfreeRow : freeRow (canonicalIndex parent)
      (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
      parentLight row = true)
    (hnotFreeColumn : freeColumn (canonicalIndex parent)
      (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
      parentLight column = false) :
    selectedHorizontal (canonicalIndex parent)
        (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
        parentLight column row = true ∨
      upperWitness (canonicalIndex parent)
        (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
        parentLight column row = true ∨
      lowerWitness (canonicalIndex parent)
        (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
        parentLight column row = true := by
  have checked := completeFor_canonical_eq_true parent parentLight
  simp only [completeFor, List.all_eq_true] at checked
  have crossing := checked column hcolumn row hrow
  rw [Bool.and_eq_true] at crossing
  have vertical := crossing.1
  simp only [hfreeRow, hnotFreeColumn, Bool.not_true, Bool.not_false,
    Bool.false_or, Bool.true_or, Bool.or_eq_true] at vertical
  rcases vertical with (hselected | hupper) | hlower
  · exact Or.inl hselected
  · exact Or.inr (Or.inl hupper)
  · exact Or.inr (Or.inr hlower)

theorem horizontal_case (parent : Index) (parentLight : Bool)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hfreeColumn : freeColumn (canonicalIndex parent)
      (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
      parentLight column = true)
    (hnotFreeRow : freeRow (canonicalIndex parent)
      (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
      parentLight row = false) :
    selectedVertical (canonicalIndex parent)
        (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
        parentLight column row = true ∨
      rightWitness (canonicalIndex parent)
        (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
        parentLight column row = true ∨
      leftWitness (canonicalIndex parent)
        (reachedBitmap (ShadedFreeLineGraphBase.nodes (canonicalIndex parent)))
        parentLight column row = true := by
  have checked := completeFor_canonical_eq_true parent parentLight
  simp only [completeFor, List.all_eq_true] at checked
  have crossing := checked column hcolumn row hrow
  rw [Bool.and_eq_true] at crossing
  have horizontal := crossing.2
  simp only [hfreeColumn, hnotFreeRow, Bool.not_true, Bool.not_false,
    Bool.false_or, Bool.true_or, Bool.or_eq_true] at horizontal
  rcases horizontal with (hselected | hright) | hleft
  · exact Or.inl hselected
  · exact Or.inr (Or.inl hright)
  · exact Or.inr (Or.inr hleft)

end ShadedObstructionGeometryBaseComplete
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
