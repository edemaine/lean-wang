/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryOddBaseAudit

/-!
# Project the odd obstruction audit to one parent

The expensive native theorem is cached in the imported module.  These lemmas
extract its coverage and nearest-boundary conclusions for an arbitrary parent
and either possible board shade.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryOddBaseComplete

open ShadedObstructionGeometryOddBaseAudit

private theorem checked (parent : Index) :
    let visited := reachedBitmap (ShadedFreeLineOddBase.nodes parent)
    coverageFor parent visited = true ∧
      completeFor parent visited false = true ∧
      completeFor parent visited true = true := by
  have hcomplete := complete_eq_true
  unfold complete at hcomplete
  have hall := List.all_eq_true.mp hcomplete
  have hparent := hall (parent, ShadedFreeLineOddBase.nodes parent)
    (List.mem_map.2 ⟨parent, List.mem_finRange parent, rfl⟩)
  simp only [Bool.and_eq_true] at hparent
  exact ⟨hparent.1.1, hparent.1.2, hparent.2⟩

theorem coverageFor_eq_true (parent : Index) :
    coverageFor parent
      (reachedBitmap (ShadedFreeLineOddBase.nodes parent)) = true :=
  (checked parent).1

theorem completeFor_eq_true (parent : Index) (parentLight : Bool) :
    completeFor parent
      (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
      parentLight = true := by
  cases parentLight
  · exact (checked parent).2.1
  · exact (checked parent).2.2

theorem vertical_case (parent : Index) (parentLight : Bool)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hfreeRow : freeRow parent
      (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
      parentLight row = true)
    (hnotFreeColumn : freeColumn parent
      (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
      parentLight column = false) :
    selectedHorizontal parent
        (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
        parentLight column row = true ∨
      upperWitness parent
        (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
        parentLight column row = true ∨
      lowerWitness parent
        (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
        parentLight column row = true := by
  have hcomplete := completeFor_eq_true parent parentLight
  simp only [completeFor, List.all_eq_true] at hcomplete
  have crossing := hcomplete column hcolumn row hrow
  rw [Bool.and_eq_true] at crossing
  have vertical := crossing.1
  simp only [hfreeRow, hnotFreeColumn, Bool.not_true,
    Bool.false_or, Bool.or_eq_true] at vertical
  rcases vertical with (hselected | hupper) | hlower
  · exact Or.inl hselected
  · exact Or.inr (Or.inl hupper)
  · exact Or.inr (Or.inr hlower)

theorem horizontal_case (parent : Index) (parentLight : Bool)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hfreeColumn : freeColumn parent
      (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
      parentLight column = true)
    (hnotFreeRow : freeRow parent
      (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
      parentLight row = false) :
    selectedVertical parent
        (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
        parentLight column row = true ∨
      rightWitness parent
        (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
        parentLight column row = true ∨
      leftWitness parent
        (reachedBitmap (ShadedFreeLineOddBase.nodes parent))
        parentLight column row = true := by
  have hcomplete := completeFor_eq_true parent parentLight
  simp only [completeFor, List.all_eq_true] at hcomplete
  have crossing := hcomplete column hcolumn row hrow
  rw [Bool.and_eq_true] at crossing
  have horizontal := crossing.2
  simp only [hfreeColumn, hnotFreeRow, Bool.not_true,
    Bool.false_or, Bool.or_eq_true] at horizontal
  rcases horizontal with (hselected | hright) | hleft
  · exact Or.inl hselected
  · exact Or.inr (Or.inl hright)
  · exact Or.inr (Or.inr hleft)

end ShadedObstructionGeometryOddBaseComplete
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
