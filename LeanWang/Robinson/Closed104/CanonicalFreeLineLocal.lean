/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineCertificate
import LeanWang.Robinson.Closed104.ShadedSubstitutionSupertiles

/-! Semantic wrappers for the canonical local free-line audit. -/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalFreeLineLocal

open Signals.FreeCellLocal ShadedSubstitution
open CanonicalFreeLine

def selectedVertical (node : Node) (x y : Nat) :
    Option Signals.HorizontalInterior :=
  ShadedSignals.selectedVerticalFor (components node.data.parent).2.1
    (quadrantAt x y) (flipShade (node.data.block.at (x % 2) (y % 2)))

def selectedHorizontal (node : Node) (x y : Nat) :
    Option Signals.VerticalInterior :=
  ShadedSignals.selectedHorizontalFor (components node.data.parent).2.1
    (quadrantAt x y) (flipShade (node.data.block.at (x % 2) (y % 2)))

def fineNode (node : Node) (x y : Nat) : Node :=
  node.child (childPosition (x / 2) (y / 2))

def fineSelectedVertical (node : Node) (x y : Nat) :
    Option Signals.HorizontalInterior :=
  selectedVertical (fineNode node x y) x y

def fineSelectedHorizontal (node : Node) (x y : Nat) :
    Option Signals.VerticalInterior :=
  selectedHorizontal (fineNode node x y) x y

def RowClear (node : Node) (y : Nat) : Prop :=
  ∀ x, x < 2 → selectedVertical node x y = none

def ColumnClear (node : Node) (x : Nat) : Prop :=
  ∀ y, y < 2 → selectedHorizontal node x y = none

def FineRowClear (node : Node) (y : Nat) : Prop :=
  ∀ x, x < 8 → fineSelectedVertical node x y = none

def FineColumnClear (node : Node) (x : Nat) : Prop :=
  ∀ y, y < 8 → fineSelectedHorizontal node x y = none

def WestStripClear (node : Node) (y : Nat) : Prop :=
  ∀ x, 2 ≤ x → x < 8 → fineSelectedVertical node x y = none

def SouthStripClear (node : Node) (x : Nat) : Prop :=
  ∀ y, 2 ≤ y → y < 8 → fineSelectedHorizontal node x y = none

@[simp] theorem selectedVertical?_val (node : Node) (x y : Nat) :
    selectedVertical? node.val x y = selectedVertical node x y := by
  simp [selectedVertical?, selectedVertical, Node.modelData_data]

@[simp] theorem selectedHorizontal?_val (node : Node) (x y : Nat) :
    selectedHorizontal? node.val x y = selectedHorizontal node x y := by
  simp [selectedHorizontal?, selectedHorizontal, Node.modelData_data]

@[simp] theorem clearVertical_val (node : Node) (x y : Nat) :
    clearVertical node.val x y = true ↔ selectedVertical node x y = none := by
  simp [clearVertical, Node.modelData_data]

@[simp] theorem clearHorizontal_val (node : Node) (x y : Nat) :
    clearHorizontal node.val x y = true ↔ selectedHorizontal node x y = none := by
  simp [clearHorizontal, Node.modelData_data]

@[simp] theorem fineNode?_val (node : Node) (x y : Nat) :
    fineNode? node.val x y = some (fineNode node x y).val := by
  unfold CanonicalFreeLine.fineNode? fineNode
  change childNode node.val (childPosition (x / 2) (y / 2)).val = _
  rw [Node.childNode_child]
  simp

@[simp] theorem fineClearVertical_val (node : Node) (x y : Nat) :
    fineClearVertical node.val x y = true ↔
      fineSelectedVertical node x y = none := by
  simp [fineClearVertical, fineSelectedVertical]

@[simp] theorem fineClearHorizontal_val (node : Node) (x y : Nat) :
    fineClearHorizontal node.val x y = true ↔
      fineSelectedHorizontal node x y = none := by
  simp [fineClearHorizontal, fineSelectedHorizontal]

@[simp] theorem rowClear_val (node : Node) (y : Nat) :
    rowClear node.val y = true ↔ RowClear node y := by
  simp [rowClear, RowClear, List.all_eq_true]

@[simp] theorem columnClear_val (node : Node) (x : Nat) :
    columnClear node.val x = true ↔ ColumnClear node x := by
  simp [columnClear, ColumnClear, List.all_eq_true]

@[simp] theorem fineRowClear_val (node : Node) (y : Nat) :
    fineRowClear node.val y = true ↔ FineRowClear node y := by
  simp [fineRowClear, FineRowClear, List.all_eq_true]

@[simp] theorem fineColumnClear_val (node : Node) (x : Nat) :
    fineColumnClear node.val x = true ↔ FineColumnClear node x := by
  simp [fineColumnClear, FineColumnClear, List.all_eq_true]

@[simp] theorem westStripClear_val (node : Node) (y : Nat) :
    westStripClear node.val y = true ↔ WestStripClear node y := by
  constructor
  · intro checked x hxLower hxUpper
    have all := List.all_eq_true.1 checked (x - 2) (by
      simp only [List.mem_range]
      omega)
    rw [show x - 2 + 2 = x by omega] at all
    exact (fineClearVertical_val node x y).1 all
  · intro clear
    apply List.all_eq_true.2
    intro dx hdx
    simp only [List.mem_range] at hdx
    exact (fineClearVertical_val node (dx + 2) y).2
      (clear (dx + 2) (by omega) (by omega))

@[simp] theorem southStripClear_val (node : Node) (x : Nat) :
    southStripClear node.val x = true ↔ SouthStripClear node x := by
  constructor
  · intro checked y hyLower hyUpper
    have all := List.all_eq_true.1 checked (y - 2) (by
      simp only [List.mem_range]
      omega)
    rw [show y - 2 + 2 = y by omega] at all
    exact (fineClearHorizontal_val node x y).1 all
  · intro clear
    apply List.all_eq_true.2
    intro dy hdy
    simp only [List.mem_range] at hdy
    exact (fineClearHorizontal_val node x (dy + 2)).2
      (clear (dy + 2) (by omega) (by omega))

theorem row_zero_refines (node : Node) (clear : RowClear node 0) :
    FineRowClear node 0 := by
  exact (fineRowClear_val node 0).1
    (CanonicalFreeLine.row_zero_refines node.property
      ((rowClear_val node 0).2 clear))

theorem row_one_refines (node : Node) (clear : RowClear node 1) :
    FineRowClear node 1 ∧ FineRowClear node 2 := by
  have refined := CanonicalFreeLine.row_one_refines node.property
    ((rowClear_val node 1).2 clear)
  exact ⟨(fineRowClear_val node 1).1 refined.1,
    (fineRowClear_val node 2).1 refined.2⟩

theorem column_zero_refines (node : Node) (clear : ColumnClear node 0) :
    FineColumnClear node 0 := by
  exact (fineColumnClear_val node 0).1
    (CanonicalFreeLine.column_zero_refines node.property
      ((columnClear_val node 0).2 clear))

theorem column_one_refines (node : Node) (clear : ColumnClear node 1) :
    FineColumnClear node 1 ∧ FineColumnClear node 2 := by
  have refined := CanonicalFreeLine.column_one_refines node.property
    ((columnClear_val node 1).2 clear)
  exact ⟨(fineColumnClear_val node 1).1 refined.1,
    (fineColumnClear_val node 2).1 refined.2⟩

theorem west_strips_clear (node : Node) :
    WestStripClear node 0 ∧ WestStripClear node 1 ∧
      WestStripClear node 2 := by
  have clear := CanonicalFreeLine.west_strips_clear node.property
  exact ⟨(westStripClear_val node 0).1 clear.1,
    (westStripClear_val node 1).1 clear.2.1,
    (westStripClear_val node 2).1 clear.2.2⟩

theorem south_strips_clear (node : Node) :
    SouthStripClear node 0 ∧ SouthStripClear node 1 ∧
      SouthStripClear node 2 := by
  have clear := CanonicalFreeLine.south_strips_clear node.property
  exact ⟨(southStripClear_val node 0).1 clear.1,
    (southStripClear_val node 1).1 clear.2.1,
    (southStripClear_val node 2).1 clear.2.2⟩

def baseNode (node : Node) : Node :=
  node.child ⟨10, by decide⟩

@[simp] theorem evenBaseNode?_val (node : Node) :
    evenBaseNode? node.val = some (baseNode node).val := by
  unfold evenBaseNode? baseNode
  change childNode node.val (10 : Fin 16) = _
  rw [Node.childNode_child]
  simp

theorem baseNode_clear (node : Node) :
    RowClear (baseNode node) 1 ∧ ColumnClear (baseNode node) 1 := by
  have checked := evenBaseValid_of_mem node.property
  rw [evenBaseValid, evenBaseNode?_val] at checked
  simp only [Bool.and_eq_true] at checked
  exact ⟨(rowClear_val (baseNode node) 1).1 checked.1,
    (columnClear_val (baseNode node) 1).1 checked.2⟩

end CanonicalFreeLineLocal
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
