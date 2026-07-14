/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSubstitutionCertificate

/-!
# Recursive supertiles from the finite-state shade certificate

Reachability makes the selected substitution total: every node has one child
at each of the sixteen positions.  This module packages those children as a
typed operation and iterates the resulting `4 x 4` substitution.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitution

open RedShadeGraphRefinement

set_option maxRecDepth 20000

/-- A decorated substitution state certified reachable from the selected seed. -/
abbrev Node := { node : Nat // node ∈ reachable }

namespace Node

/-- Decoded tile, shade block, and selected expansion of a reachable node. -/
def data (node : Node) : DecoratedData :=
  Classical.choose (modelData_exists_of_mem node.property)

@[simp]
theorem modelData_data (node : Node) : modelData node = some node.data :=
  Classical.choose_spec (modelData_exists_of_mem node.property)

/-- The certified child in one position of the selected `4 x 4` expansion. -/
def child (node : Node) (position : Fin 16) : Node :=
  ⟨Classical.choose
      (modelChild_exists_of_mem node.property position.isLt),
    (Classical.choose_spec
      (modelChild_exists_of_mem node.property position.isLt)).2⟩

@[simp]
theorem childNode_child (node : Node) (position : Fin 16) :
    childNode node position = some (node.child position) :=
  (Classical.choose_spec
    (modelChild_exists_of_mem node.property position.isLt)).1

theorem child_spec (node : Node) (position : Fin 16) :
    (node.child position).data.parent =
        fineGrid node.data.parent (position % 4) (position / 4) ∧
      node.data.expansion[position]? =
        some (node.child position).data.block := by
  rcases modelChild_spec_of_mem node.property position.isLt with
    ⟨data, child, childData, block, hdata, hchild, hchildData, hblock,
      _, hparent, hchildBlock⟩
  have dataEq : data = node.data :=
    Option.some.inj (hdata.symm.trans (modelData_data node))
  subst data
  have childEq : child = node.child position :=
    Option.some.inj (hchild.symm.trans (childNode_child node position))
  subst child
  have childDataEq : childData = (node.child position).data :=
    Option.some.inj
      (hchildData.symm.trans (modelData_data (node.child position)))
  subst childData
  subst block
  exact ⟨hparent, hblock⟩

theorem child_parent (node : Node) (position : Fin 16) :
    (node.child position).data.parent =
      fineGrid node.data.parent (position % 4) (position / 4) :=
  (child_spec node position).1

theorem child_block (node : Node) (position : Fin 16) :
    node.data.expansion[position]? = some (node.child position).data.block :=
  (child_spec node position).2

end Node

/-- Position in a `4 x 4` child block, encoded in south-to-north row order. -/
def childPosition (x y : Nat) : Fin 16 :=
  ⟨x % 4 + 4 * (y % 4), by
    have hx := Nat.mod_lt x (by decide : 0 < 4)
    have hy := Nat.mod_lt y (by decide : 0 < 4)
    omega⟩

/-- Simultaneously replace every node in a grid by its certified child block. -/
def refineNodeGrid (grid : Nat → Nat → Node) : Nat → Nat → Node :=
  fun x y => (grid (x / 4) (y / 4)).child (childPosition x y)

/-- Iterate the certified two-substitution step. -/
def iterateNodeRefine : Nat → (Nat → Nat → Node) → Nat → Nat → Node
  | 0, grid => grid
  | level + 1, grid => refineNodeGrid (iterateNodeRefine level grid)

/-- The depth-`level` decorated supertile below one reachable root. -/
def supertileNodeGrid (level : Nat) (root : Node) : Nat → Nat → Node :=
  iterateNodeRefine level (fun _ _ => root)

def supertileIndexGrid (level : Nat) (root : Node) : Nat → Nat → Index :=
  fun x y => (supertileNodeGrid level root x y).data.parent

def supertileBlockGrid (level : Nat) (root : Node) : Nat → Nat → ShadeBlock :=
  fun x y => (supertileNodeGrid level root x y).data.block

/-- Flatten each corrected-tile shade block into its four quarter states. -/
def supertileShadeGrid (level : Nat) (root : Node) :
    Nat → Nat → RedShades.State := fun x y =>
  (supertileBlockGrid level root (x / 2) (y / 2)).at (x % 2) (y % 2)

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
