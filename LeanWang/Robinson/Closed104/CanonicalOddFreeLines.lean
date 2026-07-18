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
theorem seedNodeAt?_eq (x y : Nat) :
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

private def orientedPoint : StripAxis → Nat → Nat → Nat × Nat
  | .row, along, fixed => (along, fixed)
  | .column, along, fixed => (fixed, along)

private def stripNode (axis : StripAxis) (depth offset along : Nat) : Node :=
  let point := orientedPoint axis along (2 * 4 ^ depth + offset)
  nodeAt depth point.1 point.2

private def stripChildPosition (axis : StripAxis)
    (along fixed : Nat) : Fin 16 :=
  let point := orientedPoint axis along fixed
  childPosition point.1 point.2

private theorem childAtAxis?_val (axis : StripAxis) (node : Node)
    (along fixed : Nat) (alongBound : along < 4) (fixedBound : fixed < 4) :
    childAtAxis? axis node.val along fixed =
      some (node.child (stripChildPosition axis along fixed)).val := by
  cases axis with
  | row =>
      simpa [childAtAxis?, stripChildPosition, orientedPoint] using
        childAt?_val node along fixed alongBound fixedBound
  | column =>
      simpa [childAtAxis?, stripChildPosition, orientedPoint] using
        childAt?_val node fixed along fixedBound alongBound

private def StripInterior (axis : StripAxis)
    (depth offset : Nat) (members : List Nat) : Prop :=
  ∀ along, 2 * 4 ^ depth < along → along < 6 * 4 ^ depth →
    (stripNode axis depth offset along).val ∈ members

private def StripBoundary (axis : StripAxis)
    (depth offset : Nat) (members : List Nat) : Prop :=
  (stripNode axis depth offset (2 * 4 ^ depth)).val ∈ members

abbrev RowInterior := StripInterior .row
abbrev RowBoundary := StripBoundary .row
abbrev ColumnInterior := StripInterior .column
abbrev ColumnBoundary := StripBoundary .column

private def StripClassified (axis : StripAxis) (depth offset : Nat) : Prop :=
  if offset % 2 = 0 then
    StripInterior axis depth offset (interiorClass axis .even) ∧
      StripBoundary axis depth offset (boundaryClass axis .even)
  else
    StripInterior axis depth offset (interiorClass axis .odd) ∧
      StripBoundary axis depth offset (boundaryClass axis .odd)

abbrev RowClassified := StripClassified .row
abbrev ColumnClassified := StripClassified .column

private theorem stripNode_succ (axis : StripAxis)
    {depth old child localFixed : Nat}
    (childEq : child = 4 * old + localFixed)
    (localFixedBound : localFixed < 4) (along : Nat) :
    stripNode axis (depth + 1) child along =
      (stripNode axis depth old (along / 4)).child
        (stripChildPosition axis (along % 4) localFixed) := by
  have fixedDiv : (2 * 4 ^ (depth + 1) + child) / 4 =
      2 * 4 ^ depth + old := by
    rw [childEq, pow_succ]
    omega
  have fixedMod : (2 * 4 ^ (depth + 1) + child) % 4 = localFixed := by
    rw [childEq, pow_succ]
    omega
  have alongModBound : along % 4 < 4 := Nat.mod_lt _ (by decide)
  cases axis with
  | row =>
      unfold stripNode orientedPoint stripChildPosition
      rw [nodeAt_succ, fixedDiv]
      congr 1
      apply Fin.ext
      simp [orientedPoint, childPosition, fixedMod,
        Nat.mod_eq_of_lt localFixedBound,
        Nat.mod_eq_of_lt alongModBound]
  | column =>
      unfold stripNode orientedPoint stripChildPosition
      rw [nodeAt_succ, fixedDiv]
      congr 1
      apply Fin.ext
      simp [orientedPoint, childPosition, fixedMod,
        Nat.mod_eq_of_lt localFixedBound,
        Nat.mod_eq_of_lt alongModBound]

private theorem strip_step {axis : StripAxis}
    {depth old child localFixed : Nat}
    {oldInterior oldBoundary newInterior newBoundary : List Nat}
    (oldClassified : StripInterior axis depth old oldInterior ∧
      StripBoundary axis depth old oldBoundary)
    (childEq : child = 4 * old + localFixed)
    (localFixedBound : localFixed < 4)
    (interiorChild : ∀ (node : Node) (localAlong : Nat),
      node.val ∈ oldInterior → localAlong < 4 →
        (node.child
          (stripChildPosition axis localAlong localFixed)).val ∈ newInterior)
    (boundaryChild : ∀ node : Node, node.val ∈ oldBoundary →
      (node.child (stripChildPosition axis 0 localFixed)).val ∈ newBoundary)
    (boundaryEnters : ∀ (node : Node) (localAlong : Nat),
      node.val ∈ oldBoundary → 0 < localAlong → localAlong < 4 →
        (node.child
          (stripChildPosition axis localAlong localFixed)).val ∈ newInterior) :
    StripInterior axis (depth + 1) child newInterior ∧
      StripBoundary axis (depth + 1) child newBoundary := by
  constructor
  · intro along alongLower alongUpper
    let parentAlong := along / 4
    let localAlong := along % 4
    have localAlongBound : localAlong < 4 := Nat.mod_lt _ (by decide)
    have alongEq : along = 4 * parentAlong + localAlong := by
      dsimp [parentAlong, localAlong]
      omega
    have parentLower : 2 * 4 ^ depth ≤ parentAlong := by
      simp only [pow_succ] at alongLower
      omega
    have parentUpper : parentAlong < 6 * 4 ^ depth := by
      simp only [pow_succ] at alongUpper
      omega
    rw [stripNode_succ axis childEq localFixedBound]
    by_cases boundary : parentAlong = 2 * 4 ^ depth
    · have localAlongPositive : 0 < localAlong := by
        rw [alongEq, boundary] at alongLower
        simp only [pow_succ] at alongLower
        omega
      dsimp [parentAlong] at boundary
      apply boundaryEnters _ localAlong (by
        rw [boundary]
        exact oldClassified.2) localAlongPositive localAlongBound
    · exact interiorChild _ localAlong
        (oldClassified.1 parentAlong (by omega) parentUpper) localAlongBound
  · unfold StripBoundary at oldClassified ⊢
    rw [stripNode_succ axis childEq localFixedBound]
    have alongDiv : (2 * 4 ^ (depth + 1)) / 4 = 2 * 4 ^ depth := by
      rw [pow_succ]
      omega
    have alongMod : (2 * 4 ^ (depth + 1)) % 4 = 0 := by
      rw [pow_succ]
      omega
    rw [alongDiv, alongMod]
    exact boundaryChild _ oldClassified.2

private theorem strip_transition {axis : StripAxis}
    {depth old child : Nat} (transition : StripTransition)
    (transitionMem : transition ∈ stripTransitions)
    (oldClassified :
      StripInterior axis depth old (interiorClass axis transition.source) ∧
        StripBoundary axis depth old (boundaryClass axis transition.source))
    (childEq : child = 4 * old + transition.localFixed) :
    StripInterior axis (depth + 1) child
        (interiorClass axis transition.target) ∧
      StripBoundary axis (depth + 1) child
        (boundaryClass axis transition.target) := by
  apply strip_step oldClassified childEq transition.localFixed.isLt
  · intro node localAlong hnode localAlongBound
    exact interior_child transitionMem hnode localAlongBound
      (childAtAxis?_val axis node localAlong transition.localFixed
        localAlongBound transition.localFixed.isLt)
  · intro node hnode
    exact boundary_child transitionMem hnode
      (childAtAxis?_val axis node 0 transition.localFixed
        (by decide) transition.localFixed.isLt)
  · intro node localAlong hnode localAlongPositive localAlongBound
    exact boundary_enters transitionMem hnode localAlongPositive localAlongBound
      (childAtAxis?_val axis node localAlong transition.localFixed
        localAlongBound transition.localFixed.isLt)

private theorem base_classified : RowClassified 0 2 ∧ ColumnClassified 0 2 := by
  have rowInterior : RowInterior 0 2 rowEven := by
    intro x hxLower hxUpper
    have checked := base_row_interior x (by omega) (by omega)
    rw [seedNodeAt?_eq x 4] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    change (nodeAt 0 x 4).val ∈ rowEven
    exact checked
  have rowBoundary : RowBoundary 0 2 rowBoundaryEven := by
    have checked := base_row_boundary
    rw [seedNodeAt?_eq 2 4] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    change (nodeAt 0 2 4).val ∈ rowBoundaryEven
    exact checked
  have columnInterior : ColumnInterior 0 2 columnEven := by
    intro y hyLower hyUpper
    have checked := base_column_interior y (by omega) (by omega)
    rw [seedNodeAt?_eq 4 y] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    change (nodeAt 0 4 y).val ∈ columnEven
    exact checked
  have columnBoundary : ColumnBoundary 0 2 columnBoundaryEven := by
    have checked := base_column_boundary
    rw [seedNodeAt?_eq 4 2] at checked
    simp only [optionIn, Option.any_some, decide_eq_true_eq] at checked
    change (nodeAt 0 4 2).val ∈ columnBoundaryEven
    exact checked
  simpa [StripClassified, interiorClass, boundaryClass] using
    And.intro (And.intro rowInterior rowBoundary)
      (And.intro columnInterior columnBoundary)

set_option maxHeartbeats 1000000 in
-- The parity split selects one of the three checked strip transitions.
private theorem classified_child {depth old child : Nat}
    (classified : RowClassified depth old ∧ ColumnClassified depth old)
    (hchild : child ∈ CanonicalOddFreeLineCoordinates.children old) :
    RowClassified (depth + 1) child ∧ ColumnClassified (depth + 1) child := by
  rcases mem_children_cases hchild with
    ⟨oldEven, rfl | rfl⟩ | ⟨oldOdd, rfl⟩
  · have oldRow : RowInterior depth old rowEven ∧
        RowBoundary depth old rowBoundaryEven := by
      have result := classified.1
      simp only [StripClassified, if_pos oldEven, interiorClass,
        boundaryClass] at result
      exact result
    have oldColumn : ColumnInterior depth old columnEven ∧
        ColumnBoundary depth old columnBoundaryEven := by
      have result := classified.2
      simp only [StripClassified, if_pos oldEven, interiorClass,
        boundaryClass] at result
      exact result
    have newEven : (4 * old) % 2 = 0 := by omega
    simp only [StripClassified, if_pos newEven, interiorClass, boundaryClass]
    constructor
    · simpa [evenZeroTransition, interiorClass, boundaryClass] using
        strip_transition (axis := .row) evenZeroTransition
          (by simp [stripTransitions]) oldRow rfl
    · simpa [evenZeroTransition, interiorClass, boundaryClass] using
        strip_transition (axis := .column) evenZeroTransition
          (by simp [stripTransitions]) oldColumn rfl
  · have oldRow : RowInterior depth old rowEven ∧
        RowBoundary depth old rowBoundaryEven := by
      have result := classified.1
      simp only [StripClassified, if_pos oldEven, interiorClass,
        boundaryClass] at result
      exact result
    have oldColumn : ColumnInterior depth old columnEven ∧
        ColumnBoundary depth old columnBoundaryEven := by
      have result := classified.2
      simp only [StripClassified, if_pos oldEven, interiorClass,
        boundaryClass] at result
      exact result
    have newNotEven : (4 * old + 1) % 2 ≠ 0 := by omega
    simp only [StripClassified, if_neg newNotEven, interiorClass, boundaryClass]
    constructor
    · simpa [evenOneTransition, interiorClass, boundaryClass] using
        strip_transition (axis := .row) evenOneTransition
          (by simp [stripTransitions]) oldRow rfl
    · simpa [evenOneTransition, interiorClass, boundaryClass] using
        strip_transition (axis := .column) evenOneTransition
          (by simp [stripTransitions]) oldColumn rfl
  · have oldRow : RowInterior depth old rowOdd ∧
        RowBoundary depth old rowBoundaryOdd := by
      have oldNotEven : old % 2 ≠ 0 := by omega
      have result := classified.1
      simp only [StripClassified, if_neg oldNotEven, interiorClass,
        boundaryClass] at result
      exact result
    have oldColumn : ColumnInterior depth old columnOdd ∧
        ColumnBoundary depth old columnBoundaryOdd := by
      have oldNotEven : old % 2 ≠ 0 := by omega
      have result := classified.2
      simp only [StripClassified, if_neg oldNotEven, interiorClass,
        boundaryClass] at result
      exact result
    have newNotEven : (4 * old + 3) % 2 ≠ 0 := by omega
    simp only [StripClassified, if_neg newNotEven, interiorClass, boundaryClass]
    constructor
    · simpa [oddThreeTransition, interiorClass, boundaryClass] using
        strip_transition (axis := .row) oddThreeTransition
          (by simp [stripTransitions]) oldRow rfl
    · simpa [oddThreeTransition, interiorClass, boundaryClass] using
        strip_transition (axis := .column) oddThreeTransition
          (by simp [stripTransitions]) oldColumn rfl

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
        simp only [StripClassified, if_pos heven, interiorClass,
          boundaryClass] at rowClassified
        exact rowClassified.1
      rw [if_pos heven]
      exact rowClass _ nodeLower nodeUpper
    · have rowClass : RowInterior depth offset rowOdd := by
        have rowClassified := classified.1
        simp only [StripClassified, if_neg heven, interiorClass,
          boundaryClass] at rowClassified
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
        simp only [StripClassified, if_pos heven, interiorClass,
          boundaryClass] at columnClassified
        exact columnClassified.1
      rw [if_pos heven]
      exact columnClass _ nodeLower nodeUpper
    · have columnClass : ColumnInterior depth offset columnOdd := by
        have columnClassified := classified.2
        simp only [StripClassified, if_neg heven, interiorClass,
          boundaryClass] at columnClassified
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
