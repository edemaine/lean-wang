/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104Primitivity

/-!
Occurrence consequences of primitivity inside an arbitrary desubstitution tower.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace HierarchyRecurrence

open Desubstitution ParentPlane Hierarchy Primitivity

private theorem exists_fine_occurrence_of_mem_children
    {fine : IndexPlane} {origin parentCoord : Int × Int}
    {middle target : Index}
    (hparent : IsParentAt fine origin middle parentCoord)
    (hchild : target ∈ children middle) :
    ∃ fineCoord : Int × Int, fine fineCoord = target := by
  rw [children_eq_childrenAt] at hchild
  simp only [childrenAt, List.mem_cons, List.not_mem_nil, or_false] at hchild
  rcases hchild with hchild | hchild | hchild | hchild
  · subst target
    exact ⟨blockOrigin origin parentCoord, hparent.1.symm⟩
  · subst target
    exact ⟨shift (blockOrigin origin parentCoord) 1 0, hparent.2.1.symm⟩
  · subst target
    exact ⟨shift (blockOrigin origin parentCoord) 0 1, hparent.2.2.1.symm⟩
  · subst target
    exact ⟨shift (blockOrigin origin parentCoord) 1 1, hparent.2.2.2.symm⟩

/-- A finite descendant type occurs at an actual coordinate of the fine plane. -/
theorem exists_occurrence_of_mem_descendants
    {base : ValidPlane} (tower : Tower base) :
    ∀ (depth baseLevel : Nat) (coarseCoord : Int × Int) (target : Index),
      target ∈ descendants depth
        ((tower.plane (baseLevel + depth)).tiling coarseCoord) →
      ∃ fineCoord : Int × Int,
        (tower.plane baseLevel).tiling fineCoord = target := by
  intro depth
  induction depth with
  | zero =>
      intro baseLevel coarseCoord target htarget
      have htarget' : target =
          (tower.plane baseLevel).tiling coarseCoord := by
        rw [Nat.add_zero] at htarget
        exact mem_descendants_zero.1 htarget
      exact ⟨coarseCoord, htarget'.symm⟩
  | succ depth ih =>
      intro baseLevel coarseCoord target htarget
      have hindex : baseLevel + (depth + 1) = (baseLevel + 1) + depth := by
        omega
      rw [hindex] at htarget
      rcases mem_descendants_succ.1 htarget with
        ⟨middle, hmiddle, hchild⟩
      obtain ⟨middleCoord, hmiddleCoord⟩ :=
        ih (baseLevel + 1) coarseCoord middle hmiddle
      have hparent := tower.children baseLevel middleCoord
      rw [hmiddleCoord] at hparent
      exact exists_fine_occurrence_of_mem_children hparent hchild

/-- Every tile type occurs below every depth-five coarse tile in the tower. -/
theorem every_type_occurs
    {base : ValidPlane} (tower : Tower base)
    (baseLevel : Nat) (coarseCoord : Int × Int) (target : Index) :
    ∃ fineCoord : Int × Int,
      (tower.plane baseLevel).tiling fineCoord = target := by
  exact exists_occurrence_of_mem_descendants tower 5 baseLevel coarseCoord target
    (mem_descendants_five _ target)

/-- In particular, every corrected tile type occurs in the original plane. -/
theorem every_type_occurs_in_base
    {base : ValidPlane} (tower : Tower base) (target : Index) :
    ∃ coord : Int × Int, base.tiling coord = target := by
  obtain ⟨coord, hcoord⟩ := every_type_occurs tower 0 (0, 0) target
  rw [tower.zero] at hcoord
  exact ⟨coord, hcoord⟩

end HierarchyRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
