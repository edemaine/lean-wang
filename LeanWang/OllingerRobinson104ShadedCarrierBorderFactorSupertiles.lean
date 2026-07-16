/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedCarrierBorderFactorCertificate
import LeanWang.OllingerRobinson104ShadedSubstitutionPlane

/-!
# The selected-border factor on substitution supertiles

The stable sixteen-state factor follows the same base-four recursion as the
decorated substitution.  Its visible patch is exactly the four horizontal and
four vertical selected borders in the corresponding `2 x 2` quarter block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderFactorSupertiles

open Signals.FreeCellLocal ShadedSubstitution ShadedSubstitutionPlane
open ShadedCarrierBorderFactor

def horizontalOutput (classId x y : Nat) : Option Bool :=
  (classPatch classId)[x + 2 * y]?.getD none

def verticalOutput (classId x y : Nat) : Option Bool :=
  (classPatch classId)[4 + x + 2 * y]?.getD none

theorem horizontalOutput_classOf (node : Node) (x y : Nat)
    (hx : x < 2) (hy : y < 2) :
    horizontalOutput (classOf node) x y =
      ShadedSignalRectangle.horizontalInteriorCode
        (ShadedSignals.selectedVerticalFor
          (componentAt (fun _ _ => node.data.parent) x y)
          (quadrantAt x y) (node.data.block.at x y)) := by
  rw [horizontalOutput, ← patch_eq node]
  have xCases : x = 0 ∨ x = 1 := by omega
  have yCases : y = 0 ∨ y = 1 := by omega
  rcases xCases with rfl | rfl <;> rcases yCases with rfl | rfl <;>
    simp [patchData, List.range_succ, componentAt, quadrantAt, ShadeBlock.at]

theorem verticalOutput_classOf (node : Node) (x y : Nat)
    (hx : x < 2) (hy : y < 2) :
    verticalOutput (classOf node) x y =
      ShadedSignalRectangle.verticalInteriorCode
        (ShadedSignals.selectedHorizontalFor
          (componentAt (fun _ _ => node.data.parent) x y)
          (quadrantAt x y) (node.data.block.at x y)) := by
  rw [verticalOutput, ← patch_eq node]
  have xCases : x = 0 ∨ x = 1 := by omega
  have yCases : y = 0 ∨ y = 1 := by omega
  rcases xCases with rfl | rfl <;> rcases yCases with rfl | rfl <;>
    simp [patchData, List.range_succ, componentAt, quadrantAt, ShadeBlock.at]

/-- The finite factor generated below a root class. -/
def generatedClass : Nat → Nat → Nat → Nat → Nat
  | 0, rootClass, _, _ => rootClass
  | level + 1, rootClass, x, y =>
      childClass (generatedClass level rootClass (x / 4) (y / 4))
        (childPosition x y)

theorem classOf_supertileNodeGrid (level : Nat) (root : Node) (x y : Nat) :
    classOf (supertileNodeGrid level root x y) =
      generatedClass level (classOf root) x y := by
  induction level generalizing x y with
  | zero => rfl
  | succ level inductionHypothesis =>
      change classOf
          ((supertileNodeGrid level root (x / 4) (y / 4)).child
            (childPosition x y)) = _
      rw [child_class, inductionHypothesis]
      rfl

theorem classOf_seed_supertileNodeGrid (level x y : Nat) :
    classOf (supertileNodeGrid level seedNode x y) =
      generatedClass level 15 x y := by
  rw [classOf_supertileNodeGrid, seed_class]

theorem rowInterior_eq_horizontalOutput
    (level : Nat) (root : Node) (x y : Nat) :
    rowInterior level root x y =
      horizontalOutput
        (classOf (supertileNodeGrid level root (x / 2) (y / 2)))
        (x % 2) (y % 2) := by
  have output := horizontalOutput_classOf
    (supertileNodeGrid level root (x / 2) (y / 2))
    (x % 2) (y % 2) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))
  simpa [rowInterior, ShadedSignalRectangle.horizontalInterior,
    componentAt, supertileIndexGrid, supertileShadeGrid,
    supertileBlockGrid, quadrantAt, Nat.mod_mod] using output.symm

theorem columnInterior_eq_verticalOutput
    (level : Nat) (root : Node) (x y : Nat) :
    columnInterior level root x y =
      verticalOutput
        (classOf (supertileNodeGrid level root (x / 2) (y / 2)))
        (x % 2) (y % 2) := by
  have output := verticalOutput_classOf
    (supertileNodeGrid level root (x / 2) (y / 2))
    (x % 2) (y % 2) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))
  simpa [columnInterior, ShadedSignalRectangle.verticalInterior,
    componentAt, supertileIndexGrid, supertileShadeGrid,
    supertileBlockGrid, quadrantAt, Nat.mod_mod] using output.symm

end ShadedCarrierBorderFactorSupertiles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
