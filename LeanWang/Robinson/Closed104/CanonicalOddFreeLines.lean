/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddFreeLineCertificate
import LeanWang.Robinson.Closed104.CanonicalOddFreeLineCoordinates
import LeanWang.Robinson.Closed104.ShadedLightBoardFreeLines
import LeanWang.Robinson.Closed104.ShadedSubstitutionSupertiles

/-!
# Canonical free lines in odd-depth supertiles

The deterministic raw shade substitution has a finite two-parity invariant.
Clear interior nodes propagate through child rows or columns `0`, `1`, and
`3`; a separate boundary class accounts for the strict lower board boundary.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddFreeLines

open RedShadeCycles Signals.FreeCellLocal ShadedSubstitution
open CanonicalFreeLine CanonicalOddFreeLineData
  CanonicalOddFreeLineCertificate CanonicalOddFreeLineCoordinates

set_option maxRecDepth 20000

def indexGrid (level : Nat) : Nat → Nat → Index :=
  supertileIndexGrid level seedNode

def shadeGrid (level : Nat) : Nat → Nat → RedShades.State :=
  supertileShadeGrid level seedNode

def selectedVertical (node : Node) (x y : Nat) :
    Option Signals.HorizontalInterior :=
  ShadedSignals.selectedVerticalFor (components node.data.parent).2.1
    (quadrantAt x y) (node.data.block.at (x % 2) (y % 2))

def selectedHorizontal (node : Node) (x y : Nat) :
    Option Signals.VerticalInterior :=
  ShadedSignals.selectedHorizontalFor (components node.data.parent).2.1
    (quadrantAt x y) (node.data.block.at (x % 2) (y % 2))

def selectedVerticalAt (level x y : Nat) :
    Option Signals.HorizontalInterior :=
  ShadedSignals.selectedVerticalFor (componentAt (indexGrid level) x y)
    (quadrantAt x y) (shadeGrid level x y)

def selectedHorizontalAt (level x y : Nat) :
    Option Signals.VerticalInterior :=
  ShadedSignals.selectedHorizontalFor (componentAt (indexGrid level) x y)
    (quadrantAt x y) (shadeGrid level x y)

theorem selectedVerticalAt_eq_local (level x y : Nat) :
    selectedVerticalAt level x y =
      selectedVertical (supertileNodeGrid level seedNode (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  simp [selectedVerticalAt, selectedVertical, indexGrid, shadeGrid,
    componentAt, supertileIndexGrid, supertileShadeGrid,
    supertileBlockGrid, quadrantAt]

theorem selectedHorizontalAt_eq_local (level x y : Nat) :
    selectedHorizontalAt level x y =
      selectedHorizontal (supertileNodeGrid level seedNode (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  simp [selectedHorizontalAt, selectedHorizontal, indexGrid, shadeGrid,
    componentAt, supertileIndexGrid, supertileShadeGrid,
    supertileBlockGrid, quadrantAt]

@[simp] theorem rawSelectedVertical?_val (node : Node) (x y : Nat) :
    rawSelectedVertical? node.val x y = selectedVertical node x y := by
  simp [rawSelectedVertical?, selectedVertical, Node.modelData_data]

@[simp] theorem rawSelectedHorizontal?_val (node : Node) (x y : Nat) :
    rawSelectedHorizontal? node.val x y = selectedHorizontal node x y := by
  simp [rawSelectedHorizontal?, selectedHorizontal, Node.modelData_data]

private theorem row_clear_of_check (node : Node)
    (checked : rawRowClear node.val 1 = true) (x : Nat) (hx : x < 2) :
    selectedVertical node x 1 = none := by
  have atX := List.all_eq_true.1 checked x (by simpa using hx)
  simp only [rawClearVertical, Node.modelData_data, Option.isSome_some,
    Bool.true_and, beq_iff_eq, rawSelectedVertical?_val] at atX
  exact atX

private theorem column_clear_of_check (node : Node)
    (checked : rawColumnClear node.val 1 = true) (y : Nat) (hy : y < 2) :
    selectedHorizontal node 1 y = none := by
  have atY := List.all_eq_true.1 checked y (by simpa using hy)
  simp only [rawClearHorizontal, Node.modelData_data, Option.isSome_some,
    Bool.true_and, beq_iff_eq, rawSelectedHorizontal?_val] at atY
  exact atY

def nodeAt (depth x y : Nat) : Node :=
  supertileNodeGrid (depth + 2) seedNode x y

theorem nodeAt_succ (depth x y : Nat) :
    nodeAt (depth + 1) x y =
      (nodeAt depth (x / 4) (y / 4)).child (childPosition x y) := by
  rfl

private theorem childAt?_val (node : Node) (childX childY : Nat)
    (hx : childX < 4) (hy : childY < 4) :
    childAt? node.val childX childY =
      some (node.child (childPosition childX childY)).val := by
  unfold CanonicalOddFreeLineData.childAt?
  have positionEq : childX + 4 * childY = childPosition childX childY := by
    simp [childPosition, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rw [positionEq, Node.childNode_child]
  simp

set_option maxHeartbeats 1000000 in
-- Normalizing two certified `Node.child` witnesses unfolds their choice proofs.
private theorem seedNodeAt?_eq (x y : Nat) :
    seedNodeAt? x y = some (nodeAt 0 x y).val := by
  let firstPosition := childPosition (x / 4) (y / 4)
  let secondPosition := childPosition x y
  have firstPositionMod :
      childPosition (x / 4 % 4) (y / 4 % 4) = firstPosition := by
    apply Fin.ext
    simp [firstPosition, childPosition]
  have secondPositionMod : childPosition (x % 4) (y % 4) = secondPosition := by
    apply Fin.ext
    simp [secondPosition, childPosition]
  unfold seedNodeAt? CanonicalOddFreeLineData.seed
  unfold CanonicalFreeLine.levelTwoNode?
  change (childAt? seedNode.val (x / 4 % 4) (y / 4 % 4) >>= fun first =>
    childAt? first (x % 4) (y % 4)) = some (nodeAt 0 x y).val
  apply Option.bind_eq_some_iff.mpr
  refine ⟨(seedNode.child firstPosition).val, ?_, ?_⟩
  · rw [← firstPositionMod]
    exact childAt?_val seedNode (x / 4 % 4) (y / 4 % 4)
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  · rw [childAt?_val (seedNode.child firstPosition) (x % 4) (y % 4)
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
      secondPositionMod]
    apply congrArg some
    unfold nodeAt supertileNodeGrid
    simp only [iterateNodeRefine, refineNodeGrid]
    rfl

def RowInterior (depth offset : Nat) (members : List Nat) : Prop :=
  ∀ x, 2 * 4 ^ depth < x → x < 6 * 4 ^ depth →
    (nodeAt depth x (2 * 4 ^ depth + offset)).val ∈ members

def RowBoundary (depth offset : Nat) (members : List Nat) : Prop :=
  (nodeAt depth (2 * 4 ^ depth) (2 * 4 ^ depth + offset)).val ∈ members

def ColumnInterior (depth offset : Nat) (members : List Nat) : Prop :=
  ∀ y, 2 * 4 ^ depth < y → y < 6 * 4 ^ depth →
    (nodeAt depth (2 * 4 ^ depth + offset) y).val ∈ members

def ColumnBoundary (depth offset : Nat) (members : List Nat) : Prop :=
  (nodeAt depth (2 * 4 ^ depth + offset) (2 * 4 ^ depth)).val ∈ members

def RowClassified (depth offset : Nat) : Prop :=
  if offset % 2 = 0 then
    RowInterior depth offset rowEven ∧
      RowBoundary depth offset rowBoundaryEven
  else
    RowInterior depth offset rowOdd ∧
      RowBoundary depth offset rowBoundaryOdd

def ColumnClassified (depth offset : Nat) : Prop :=
  if offset % 2 = 0 then
    ColumnInterior depth offset columnEven ∧
      ColumnBoundary depth offset columnBoundaryEven
  else
    ColumnInterior depth offset columnOdd ∧
      ColumnBoundary depth offset columnBoundaryOdd

private theorem row_step {depth old child localY : Nat}
    {oldInterior oldBoundary newInterior newBoundary : List Nat}
    (oldClassified : RowInterior depth old oldInterior ∧
      RowBoundary depth old oldBoundary)
    (childEq : child = 4 * old + localY) (localYBound : localY < 4)
    (interiorChild : ∀ (node : Node) (localX : Nat),
      node.val ∈ oldInterior → localX < 4 →
        (node.child (childPosition localX localY)).val ∈ newInterior)
    (boundaryChild : ∀ node : Node, node.val ∈ oldBoundary →
      (node.child (childPosition 0 localY)).val ∈ newBoundary)
    (boundaryEnters : ∀ (node : Node) (localX : Nat),
      node.val ∈ oldBoundary → 0 < localX → localX < 4 →
        (node.child (childPosition localX localY)).val ∈ newInterior) :
    RowInterior (depth + 1) child newInterior ∧
      RowBoundary (depth + 1) child newBoundary := by
  constructor
  · intro x hxLower hxUpper
    let parentX := x / 4
    let localX := x % 4
    have localXBound : localX < 4 := Nat.mod_lt _ (by decide)
    have xEq : x = 4 * parentX + localX := by
      dsimp [parentX, localX]
      omega
    have parentLower : 2 * 4 ^ depth ≤ parentX := by
      simp only [pow_succ] at hxLower
      omega
    have parentUpper : parentX < 6 * 4 ^ depth := by
      simp only [pow_succ] at hxUpper
      omega
    have rowDiv : (2 * 4 ^ (depth + 1) + child) / 4 =
        2 * 4 ^ depth + old := by
      rw [childEq, pow_succ]
      omega
    have rowMod : (2 * 4 ^ (depth + 1) + child) % 4 = localY := by
      rw [childEq, pow_succ]
      omega
    rw [nodeAt_succ, rowDiv]
    have positionEq : childPosition x (2 * 4 ^ (depth + 1) + child) =
        childPosition localX localY := by
      apply Fin.ext
      simp [childPosition, localX, rowMod,
        Nat.mod_eq_of_lt localYBound]
    rw [positionEq]
    by_cases boundary : parentX = 2 * 4 ^ depth
    · have localXPositive : 0 < localX := by
        rw [xEq, boundary] at hxLower
        simp only [pow_succ] at hxLower
        omega
      dsimp [parentX] at boundary
      apply boundaryEnters _ localX (by
        rw [boundary]
        exact oldClassified.2) localXPositive localXBound
    · exact interiorChild _ localX
        (oldClassified.1 parentX (by omega) parentUpper) localXBound
  · unfold RowBoundary at oldClassified ⊢
    have rowDiv : (2 * 4 ^ (depth + 1) + child) / 4 =
        2 * 4 ^ depth + old := by
      rw [childEq, pow_succ]
      omega
    have rowMod : (2 * 4 ^ (depth + 1) + child) % 4 = localY := by
      rw [childEq, pow_succ]
      omega
    rw [nodeAt_succ]
    have xDiv : (2 * 4 ^ (depth + 1)) / 4 = 2 * 4 ^ depth := by
      rw [pow_succ]
      omega
    have xMod : (2 * 4 ^ (depth + 1)) % 4 = 0 := by
      rw [pow_succ]
      omega
    rw [xDiv, rowDiv]
    have positionEq : childPosition (2 * 4 ^ (depth + 1))
        (2 * 4 ^ (depth + 1) + child) = childPosition 0 localY := by
      apply Fin.ext
      simp [childPosition, xMod, rowMod,
        Nat.mod_eq_of_lt localYBound]
    rw [positionEq]
    exact boundaryChild _ oldClassified.2

private theorem column_step {depth old child localX : Nat}
    {oldInterior oldBoundary newInterior newBoundary : List Nat}
    (oldClassified : ColumnInterior depth old oldInterior ∧
      ColumnBoundary depth old oldBoundary)
    (childEq : child = 4 * old + localX) (localXBound : localX < 4)
    (interiorChild : ∀ (node : Node) (localY : Nat),
      node.val ∈ oldInterior → localY < 4 →
        (node.child (childPosition localX localY)).val ∈ newInterior)
    (boundaryChild : ∀ node : Node, node.val ∈ oldBoundary →
      (node.child (childPosition localX 0)).val ∈ newBoundary)
    (boundaryEnters : ∀ (node : Node) (localY : Nat),
      node.val ∈ oldBoundary → 0 < localY → localY < 4 →
        (node.child (childPosition localX localY)).val ∈ newInterior) :
    ColumnInterior (depth + 1) child newInterior ∧
      ColumnBoundary (depth + 1) child newBoundary := by
  constructor
  · intro y hyLower hyUpper
    let parentY := y / 4
    let localY := y % 4
    have localYBound : localY < 4 := Nat.mod_lt _ (by decide)
    have yEq : y = 4 * parentY + localY := by
      dsimp [parentY, localY]
      omega
    have parentLower : 2 * 4 ^ depth ≤ parentY := by
      simp only [pow_succ] at hyLower
      omega
    have parentUpper : parentY < 6 * 4 ^ depth := by
      simp only [pow_succ] at hyUpper
      omega
    have columnDiv : (2 * 4 ^ (depth + 1) + child) / 4 =
        2 * 4 ^ depth + old := by
      rw [childEq, pow_succ]
      omega
    have columnMod : (2 * 4 ^ (depth + 1) + child) % 4 = localX := by
      rw [childEq, pow_succ]
      omega
    rw [nodeAt_succ, columnDiv]
    have positionEq : childPosition (2 * 4 ^ (depth + 1) + child) y =
        childPosition localX localY := by
      apply Fin.ext
      simp [childPosition, localY, columnMod,
        Nat.mod_eq_of_lt localXBound]
    rw [positionEq]
    by_cases boundary : parentY = 2 * 4 ^ depth
    · have localYPositive : 0 < localY := by
        rw [yEq, boundary] at hyLower
        simp only [pow_succ] at hyLower
        omega
      dsimp [parentY] at boundary
      apply boundaryEnters _ localY (by
        rw [boundary]
        exact oldClassified.2) localYPositive localYBound
    · exact interiorChild _ localY
        (oldClassified.1 parentY (by omega) parentUpper) localYBound
  · unfold ColumnBoundary at oldClassified ⊢
    have columnDiv : (2 * 4 ^ (depth + 1) + child) / 4 =
        2 * 4 ^ depth + old := by
      rw [childEq, pow_succ]
      omega
    have columnMod : (2 * 4 ^ (depth + 1) + child) % 4 = localX := by
      rw [childEq, pow_succ]
      omega
    rw [nodeAt_succ]
    have yDiv : (2 * 4 ^ (depth + 1)) / 4 = 2 * 4 ^ depth := by
      rw [pow_succ]
      omega
    have yMod : (2 * 4 ^ (depth + 1)) % 4 = 0 := by
      rw [pow_succ]
      omega
    rw [columnDiv, yDiv]
    have positionEq : childPosition (2 * 4 ^ (depth + 1) + child)
        (2 * 4 ^ (depth + 1)) = childPosition localX 0 := by
      apply Fin.ext
      simp [childPosition, columnMod, yMod,
        Nat.mod_eq_of_lt localXBound]
    rw [positionEq]
    exact boundaryChild _ oldClassified.2

private theorem base_classified : RowClassified 0 2 ∧ ColumnClassified 0 2 := by
  have rowInterior : RowInterior 0 2 rowEven := by
    intro x hxLower hxUpper
    have checked := base_row_interior x (by omega) (by omega)
    rw [seedNodeAt?_eq x 4] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    convert checked using 1
    all_goals norm_num
  have rowBoundary : RowBoundary 0 2 rowBoundaryEven := by
    have checked := base_row_boundary
    rw [seedNodeAt?_eq 2 4] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    unfold RowBoundary
    convert checked using 1
    all_goals norm_num
  have columnInterior : ColumnInterior 0 2 columnEven := by
    intro y hyLower hyUpper
    have checked := base_column_interior y (by omega) (by omega)
    rw [seedNodeAt?_eq 4 y] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    convert checked using 1
    all_goals norm_num
  have columnBoundary : ColumnBoundary 0 2 columnBoundaryEven := by
    have checked := base_column_boundary
    rw [seedNodeAt?_eq 4 2] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    unfold ColumnBoundary
    convert checked using 1
    all_goals norm_num
  simpa [RowClassified, ColumnClassified] using
    And.intro (And.intro rowInterior rowBoundary)
      (And.intro columnInterior columnBoundary)

set_option maxHeartbeats 1000000 in
-- The dependent parity split instantiates six list-indexed strip transitions.
private theorem classified_child {depth old child : Nat}
    (classified : RowClassified depth old ∧ ColumnClassified depth old)
    (hchild : child ∈ CanonicalOddFreeLineCoordinates.children old) :
    RowClassified (depth + 1) child ∧ ColumnClassified (depth + 1) child := by
  rcases mem_children_cases hchild with
    ⟨oldEven, rfl | rfl⟩ | ⟨oldOdd, rfl⟩
  · have oldRow : RowInterior depth old rowEven ∧
        RowBoundary depth old rowBoundaryEven := by
      have result := classified.1
      rw [RowClassified, if_pos oldEven] at result
      exact result
    have oldColumn : ColumnInterior depth old columnEven ∧
        ColumnBoundary depth old columnBoundaryEven := by
      have result := classified.2
      rw [ColumnClassified, if_pos oldEven] at result
      exact result
    have newEven : (4 * old) % 2 = 0 := by omega
    rw [RowClassified, ColumnClassified, if_pos newEven, if_pos newEven]
    constructor
    · apply row_step (depth := depth) (old := old) (child := 4 * old)
        (localY := 0) (oldInterior := rowEven)
        (oldBoundary := rowBoundaryEven) (newInterior := rowEven)
        (newBoundary := rowBoundaryEven) oldRow rfl (by decide)
      · intro node localX hnode hx
        apply rowEven_child_zero hnode hx
        exact childAt?_val node localX 0 hx (by decide)
      · intro node hnode
        apply rowBoundaryEven_child_zero hnode
        exact childAt?_val node 0 0 (by decide) (by decide)
      · intro node localX hnode hxLower hxUpper
        apply rowBoundaryEven_enters_zero hnode hxLower hxUpper
        exact childAt?_val node localX 0 hxUpper (by decide)
    · apply column_step (depth := depth) (old := old) (child := 4 * old)
        (localX := 0) (oldInterior := columnEven)
        (oldBoundary := columnBoundaryEven) (newInterior := columnEven)
        (newBoundary := columnBoundaryEven) oldColumn rfl (by decide)
      · intro node localY hnode hy
        apply columnEven_child_zero hnode hy
        exact childAt?_val node 0 localY (by decide) hy
      · intro node hnode
        apply columnBoundaryEven_child_zero hnode
        exact childAt?_val node 0 0 (by decide) (by decide)
      · intro node localY hnode hyLower hyUpper
        apply columnBoundaryEven_enters_zero hnode hyLower hyUpper
        exact childAt?_val node 0 localY (by decide) hyUpper
  · have oldRow : RowInterior depth old rowEven ∧
        RowBoundary depth old rowBoundaryEven := by
      have result := classified.1
      rw [RowClassified, if_pos oldEven] at result
      exact result
    have oldColumn : ColumnInterior depth old columnEven ∧
        ColumnBoundary depth old columnBoundaryEven := by
      have result := classified.2
      rw [ColumnClassified, if_pos oldEven] at result
      exact result
    have newOdd : (4 * old + 1) % 2 = 1 := by omega
    have newNotEven : (4 * old + 1) % 2 ≠ 0 := by omega
    rw [RowClassified, ColumnClassified, if_neg newNotEven,
      if_neg newNotEven]
    constructor
    · apply row_step (depth := depth) (old := old) (child := 4 * old + 1)
        (localY := 1) (oldInterior := rowEven)
        (oldBoundary := rowBoundaryEven) (newInterior := rowOdd)
        (newBoundary := rowBoundaryOdd) oldRow rfl (by decide)
      · intro node localX hnode hx
        apply rowEven_child_one hnode hx
        exact childAt?_val node localX 1 hx (by decide)
      · intro node hnode
        apply rowBoundaryEven_child_one hnode
        exact childAt?_val node 0 1 (by decide) (by decide)
      · intro node localX hnode hxLower hxUpper
        apply rowBoundaryEven_enters_one hnode hxLower hxUpper
        exact childAt?_val node localX 1 hxUpper (by decide)
    · apply column_step (depth := depth) (old := old) (child := 4 * old + 1)
        (localX := 1) (oldInterior := columnEven)
        (oldBoundary := columnBoundaryEven) (newInterior := columnOdd)
        (newBoundary := columnBoundaryOdd) oldColumn rfl (by decide)
      · intro node localY hnode hy
        apply columnEven_child_one hnode hy
        exact childAt?_val node 1 localY (by decide) hy
      · intro node hnode
        apply columnBoundaryEven_child_one hnode
        exact childAt?_val node 1 0 (by decide) (by decide)
      · intro node localY hnode hyLower hyUpper
        apply columnBoundaryEven_enters_one hnode hyLower hyUpper
        exact childAt?_val node 1 localY (by decide) hyUpper
  · have oldRow : RowInterior depth old rowOdd ∧
        RowBoundary depth old rowBoundaryOdd := by
      have oldNotEven : old % 2 ≠ 0 := by omega
      have result := classified.1
      rw [RowClassified, if_neg oldNotEven] at result
      exact result
    have oldColumn : ColumnInterior depth old columnOdd ∧
        ColumnBoundary depth old columnBoundaryOdd := by
      have oldNotEven : old % 2 ≠ 0 := by omega
      have result := classified.2
      rw [ColumnClassified, if_neg oldNotEven] at result
      exact result
    have newOdd : (4 * old + 3) % 2 = 1 := by omega
    have newNotEven : (4 * old + 3) % 2 ≠ 0 := by omega
    rw [RowClassified, ColumnClassified, if_neg newNotEven,
      if_neg newNotEven]
    constructor
    · apply row_step (depth := depth) (old := old) (child := 4 * old + 3)
        (localY := 3) (oldInterior := rowOdd)
        (oldBoundary := rowBoundaryOdd) (newInterior := rowOdd)
        (newBoundary := rowBoundaryOdd) oldRow rfl (by decide)
      · intro node localX hnode hx
        apply rowOdd_child_three hnode hx
        exact childAt?_val node localX 3 hx (by decide)
      · intro node hnode
        apply rowBoundaryOdd_child_three hnode
        exact childAt?_val node 0 3 (by decide) (by decide)
      · intro node localX hnode hxLower hxUpper
        apply rowBoundaryOdd_enters_three hnode hxLower hxUpper
        exact childAt?_val node localX 3 hxUpper (by decide)
    · apply column_step (depth := depth) (old := old) (child := 4 * old + 3)
        (localX := 3) (oldInterior := columnOdd)
        (oldBoundary := columnBoundaryOdd) (newInterior := columnOdd)
        (newBoundary := columnBoundaryOdd) oldColumn rfl (by decide)
      · intro node localY hnode hy
        apply columnOdd_child_three hnode hy
        exact childAt?_val node 3 localY (by decide) hy
      · intro node hnode
        apply columnBoundaryOdd_child_three hnode
        exact childAt?_val node 3 0 (by decide) (by decide)
      · intro node localY hnode hyLower hyUpper
        apply columnBoundaryOdd_enters_three hnode hyLower hyUpper
        exact childAt?_val node 3 localY (by decide) hyUpper

theorem offset_classified (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) :
    RowClassified depth offset ∧ ColumnClassified depth offset := by
  induction depth generalizing offset with
  | zero =>
      simp only [offsets_zero, List.mem_singleton] at hoffset
      subst offset
      exact base_classified
  | succ depth ih =>
      rw [offsets_succ, List.mem_flatMap] at hoffset
      rcases hoffset with ⟨old, hold, hchild⟩
      exact classified_child (ih hold) hchild

@[irreducible] def FreeRowAt (depth row : Nat) : Prop :=
  ∀ x, quarterWest (2 * 4 ^ depth) < x →
    x < quarterEast (6 * 4 ^ depth) →
      selectedVerticalAt (depth + 2) x row = none

@[irreducible] def FreeColumnAt (depth column : Nat) : Prop :=
  ∀ y, quarterSouth (2 * 4 ^ depth) < y →
    y < quarterNorth (6 * 4 ^ depth) →
      selectedHorizontalAt (depth + 2) column y = none

theorem coordinate_free_lines (depth : Nat) {coordinateValue : Nat}
    (hcoordinate : coordinateValue ∈ coordinates depth) :
    FreeRowAt depth coordinateValue ∧ FreeColumnAt depth coordinateValue := by
  rw [mem_coordinates_iff] at hcoordinate
  rcases hcoordinate with ⟨offset, hoffset, rfl⟩
  have classified := offset_classified depth hoffset
  have rowNode (x : Nat) (hxLower : quarterWest (2 * 4 ^ depth) < x)
      (hxUpper : x < quarterEast (6 * 4 ^ depth)) :
      (nodeAt depth (x / 2) (2 * 4 ^ depth + offset)).val ∈
        (if offset % 2 = 0 then rowEven else rowOdd) := by
    have nodeLower : 2 * 4 ^ depth < x / 2 := by
      simp only [quarterWest] at hxLower
      omega
    have nodeUpper : x / 2 < 6 * 4 ^ depth := by
      simp only [quarterEast] at hxUpper
      omega
    by_cases heven : offset % 2 = 0
    · have rowClass : RowInterior depth offset rowEven := by
        have rowClassified := classified.1
        rw [RowClassified, if_pos heven] at rowClassified
        exact rowClassified.1
      rw [if_pos heven]
      exact rowClass _ nodeLower nodeUpper
    · have rowClass : RowInterior depth offset rowOdd := by
        have rowClassified := classified.1
        rw [RowClassified, if_neg heven] at rowClassified
        exact rowClassified.1
      rw [if_neg heven]
      exact rowClass _ nodeLower nodeUpper
  have columnNode (y : Nat) (hyLower : quarterSouth (2 * 4 ^ depth) < y)
      (hyUpper : y < quarterNorth (6 * 4 ^ depth)) :
      (nodeAt depth (2 * 4 ^ depth + offset) (y / 2)).val ∈
        (if offset % 2 = 0 then columnEven else columnOdd) := by
    have nodeLower : 2 * 4 ^ depth < y / 2 := by
      simp only [quarterSouth] at hyLower
      omega
    have nodeUpper : y / 2 < 6 * 4 ^ depth := by
      simp only [quarterNorth] at hyUpper
      omega
    by_cases heven : offset % 2 = 0
    · have columnClass : ColumnInterior depth offset columnEven := by
        have columnClassified := classified.2
        rw [ColumnClassified, if_pos heven] at columnClassified
        exact columnClassified.1
      rw [if_pos heven]
      exact columnClass _ nodeLower nodeUpper
    · have columnClass : ColumnInterior depth offset columnOdd := by
        have columnClassified := classified.2
        rw [ColumnClassified, if_neg heven] at columnClassified
        exact columnClassified.1
      rw [if_neg heven]
      exact columnClass _ nodeLower nodeUpper
  constructor
  · unfold FreeRowAt
    intro x hxLower hxUpper
    have rowHalf : coordinate depth offset / 2 = 2 * 4 ^ depth + offset := by
      simp [coordinate]
      omega
    have rowMod : coordinate depth offset % 2 = 1 := by
      unfold coordinate
      omega
    rw [selectedVerticalAt_eq_local, rowHalf, rowMod]
    have nodeMem := rowNode x hxLower hxUpper
    by_cases heven : offset % 2 = 0
    · rw [if_pos heven] at nodeMem
      exact row_clear_of_check _ (rowEven_clear nodeMem)
        (x % 2) (Nat.mod_lt _ (by decide))
    · rw [if_neg heven] at nodeMem
      exact row_clear_of_check _ (rowOdd_clear nodeMem)
        (x % 2) (Nat.mod_lt _ (by decide))
  · unfold FreeColumnAt
    intro y hyLower hyUpper
    have columnHalf : coordinate depth offset / 2 =
        2 * 4 ^ depth + offset := by
      simp [coordinate]
      omega
    have columnMod : coordinate depth offset % 2 = 1 := by
      unfold coordinate
      omega
    rw [selectedHorizontalAt_eq_local, columnHalf, columnMod]
    have nodeMem := columnNode y hyLower hyUpper
    by_cases heven : offset % 2 = 0
    · rw [if_pos heven] at nodeMem
      exact column_clear_of_check _ (columnEven_clear nodeMem)
        (y % 2) (Nat.mod_lt _ (by decide))
    · rw [if_neg heven] at nodeMem
      exact column_clear_of_check _ (columnOdd_clear nodeMem)
        (y % 2) (Nat.mod_lt _ (by decide))

theorem freeRowAt_iff_isFreeRow (depth row : Nat) :
    FreeRowAt depth row ↔
      ShadedPlaneSignalGrid.IsFreeRow (indexGrid (depth + 2))
        (shadeGrid (depth + 2)) (2 * 4 ^ depth) (6 * 4 ^ depth) row := by
  unfold FreeRowAt ShadedPlaneSignalGrid.IsFreeRow selectedVerticalAt
  rfl

theorem freeColumnAt_iff_isFreeColumn (depth column : Nat) :
    FreeColumnAt depth column ↔
      ShadedPlaneSignalGrid.IsFreeColumn (indexGrid (depth + 2))
        (shadeGrid (depth + 2)) (2 * 4 ^ depth) (6 * 4 ^ depth) column := by
  unfold FreeColumnAt ShadedPlaneSignalGrid.IsFreeColumn selectedHorizontalAt
  rfl

theorem coordinate_isFreeRow (depth : Nat) {row : Nat}
    (hrow : row ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeRow (indexGrid (depth + 2))
      (shadeGrid (depth + 2)) (2 * 4 ^ depth) (6 * 4 ^ depth) row :=
  (freeRowAt_iff_isFreeRow depth row).1 (coordinate_free_lines depth hrow).1

theorem coordinate_isFreeColumn (depth : Nat) {column : Nat}
    (hcolumn : column ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeColumn (indexGrid (depth + 2))
      (shadeGrid (depth + 2)) (2 * 4 ^ depth) (6 * 4 ^ depth) column :=
  (freeColumnAt_iff_isFreeColumn depth column).1
    (coordinate_free_lines depth hcolumn).2

end CanonicalOddFreeLines
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
