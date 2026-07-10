/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedBoards

/-!
Embed substitution grids at their actual coordinates in a hierarchy tower.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace HierarchyEmbedding

open Desubstitution LocalRecognizability ParentPlane Hierarchy RedCycles

set_option maxRecDepth 20000

theorem IsParentAt.child_eq
    {fine : IndexPlane} {origin parentCoord : Int × Int} {parent : Index}
    (hparent : IsParentAt fine origin parent parentCoord) (i j : Fin 2) :
    childBlock parent i j =
      fine (shift (blockOrigin origin parentCoord) i.val j.val) := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  have hj : j.val = 0 ∨ j.val = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hi' : i = offset0 := Fin.ext hi
    have hj' : j = offset0 := Fin.ext hj
    simpa only [hi', hj', offset0, offset1, shift, add_zero,
      Nat.cast_zero] using hparent.1
  · have hi' : i = offset0 := Fin.ext hi
    have hj' : j = offset1 := Fin.ext hj
    simpa only [hi', hj', offset0, offset1, Nat.cast_zero,
      Nat.cast_one] using hparent.2.2.1
  · have hi' : i = offset1 := Fin.ext hi
    have hj' : j = offset0 := Fin.ext hj
    simpa only [hi', hj', offset0, offset1, Nat.cast_zero,
      Nat.cast_one] using hparent.2.1
  · have hi' : i = offset1 := Fin.ext hi
    have hj' : j = offset1 := Fin.ext hj
    simpa only [hi', hj', offset0, offset1, Nat.cast_one] using hparent.2.2.2

private theorem natCast_two_div_add_mod (coordinate : Nat) :
    (coordinate : Int) =
      2 * (coordinate / 2 : Nat) + (coordinate % 2 : Nat) := by
  have hcast : (coordinate : Int) =
      (coordinate % 2 : Nat) + 2 * (coordinate / 2 : Nat) := by
    exact_mod_cast (Nat.mod_add_div coordinate 2).symm
  omega

theorem childCoordinate (origin parentCoord : Int × Int) (x y : Nat) :
    shift (blockOrigin origin parentCoord) x y =
      shift
        (blockOrigin origin
          (shift parentCoord (x / 2 : Nat) (y / 2 : Nat)))
        (x % 2 : Nat) (y % 2 : Nat) := by
  have hx := natCast_two_div_add_mod x
  have hy := natCast_two_div_add_mod y
  apply Prod.ext <;> simp [blockOrigin, shift] <;> omega

/-- Restrict an integer plane to the first-quadrant grid at an arbitrary origin. -/
def natGridAt (plane : IndexPlane) (origin : Int × Int) : Nat → Nat → Index :=
  fun x y => plane (shift origin x y)

/-- One recognized parent step is exactly simultaneous grid refinement. -/
theorem natGridAt_refines
    {fine coarse : IndexPlane} {origin : Int × Int}
    (hparent : ∀ k, IsParentAt fine origin (coarse k) k)
    (coarseOrigin : Int × Int) :
    natGridAt fine (blockOrigin origin coarseOrigin) =
      refineIndexGrid (natGridAt coarse coarseOrigin) := by
  funext x y
  let parentCoord := shift coarseOrigin (x / 2 : Nat) (y / 2 : Nat)
  let i := parityOffset x
  let j := parityOffset y
  have hchild := IsParentAt.child_eq (hparent parentCoord) i j
  calc
    fine (shift (blockOrigin origin coarseOrigin) x y) =
        fine (shift (blockOrigin origin parentCoord)
          (x % 2 : Nat) (y % 2 : Nat)) := by
      exact congrArg fine (childCoordinate origin coarseOrigin x y)
    _ = childBlock (coarse parentCoord) i j := by
      simpa only [i, j, parityOffset] using hchild.symm
    _ = refineIndexGrid (natGridAt coarse coarseOrigin) x y := by
      rfl

/-- Consecutive levels of a hierarchy satisfy the concrete grid refinement equation. -/
theorem Tower.natGridAt_refines
    {base : ValidPlane} (tower : Tower base)
    (level : Nat) (coarseOrigin : Int × Int) :
    natGridAt (tower.plane level).tiling
        (blockOrigin (tower.origin level) coarseOrigin) =
      refineIndexGrid
        (natGridAt (tower.plane (level + 1)).tiling coarseOrigin) :=
  HierarchyEmbedding.natGridAt_refines (tower.children level) coarseOrigin

end HierarchyEmbedding
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
