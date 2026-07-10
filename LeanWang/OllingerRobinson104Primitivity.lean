/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104Hierarchy

/-!
Finite primitivity certificate for the corrected Ollinger substitution.

After five substitutions, the descendants of every parent contain all 104 tile
types. This supplies the uniform recurrence needed to find board patterns in an
arbitrary desubstitution hierarchy, independently of its chosen coarse tiles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Primitivity

/-- Four immediate substitution children, in southwest-first order. -/
def childrenAt (parent : Index) : List Index :=
  [childBlock parent ⟨0, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨0, by decide⟩,
    childBlock parent ⟨0, by decide⟩ ⟨1, by decide⟩,
    childBlock parent ⟨1, by decide⟩ ⟨1, by decide⟩]

/-- The finite transition table, computed once by the native certificate. -/
def childrenTable : List (List Index) :=
  (List.finRange 104).map childrenAt

def children (parent : Index) : List Index :=
  childrenTable.getD parent.val []

def allChildrenTableCorrectBool : Bool :=
  (List.finRange 104).all fun parent =>
    decide (children parent = childrenAt parent)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allChildrenTableCorrectBool_eq_true :
    allChildrenTableCorrectBool = true := by
  native_decide

theorem children_eq_childrenAt (parent : Index) :
    children parent = childrenAt parent := by
  have hparent := List.all_eq_true.1 allChildrenTableCorrectBool_eq_true
    parent (List.mem_finRange parent)
  exact of_decide_eq_true hparent

/-- Set-like list of tile types reached after exactly `level` substitutions. -/
def descendants : Nat → Index → List Index
  | 0, parent => [parent]
  | level + 1, parent =>
      ((descendants level parent).flatMap children).eraseDups

@[simp]
theorem mem_descendants_zero {parent target : Index} :
    target ∈ descendants 0 parent ↔ target = parent := by
  simp [descendants]

theorem mem_descendants_succ {level : Nat} {parent target : Index} :
    target ∈ descendants (level + 1) parent ↔
      ∃ middle ∈ descendants level parent, target ∈ children middle := by
  simp [descendants]

/-- Executable universal primitivity check at substitution depth five. -/
def allReachAllAtFiveBool : Bool :=
  (List.finRange 104).all fun parent =>
    decide ((descendants 5 parent).toFinset = Finset.univ)

set_option linter.style.nativeDecide false in
set_option maxRecDepth 20000 in
theorem allReachAllAtFiveBool_eq_true : allReachAllAtFiveBool = true := by
  native_decide

/-- Every tile type occurs below every parent after five substitutions. -/
theorem mem_descendants_five (parent target : Index) :
    target ∈ descendants 5 parent := by
  have hparent := List.all_eq_true.1 allReachAllAtFiveBool_eq_true
    parent (List.mem_finRange parent)
  have hall : (descendants 5 parent).toFinset = Finset.univ :=
    of_decide_eq_true hparent
  have htarget : target ∈ (descendants 5 parent).toFinset := by
    rw [hall]
    exact Finset.mem_univ target
  simpa using htarget

/-- In particular, the fifth descendant set is the full corrected alphabet. -/
theorem descendants_five_toFinset (parent : Index) :
    (descendants 5 parent).toFinset = Finset.univ := by
  ext target
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_descendants_five parent target

end Primitivity
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
