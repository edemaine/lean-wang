/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalFreeLineCoordinates
import LeanWang.Robinson.Closed104.CanonicalFreeLineLocal
import LeanWang.Robinson.Closed104.ShadedLightBoardFreeLines

/-!
# Canonical free lines in even-depth supertiles

The finite local audit propagates a line directly through the selected shade
substitution.  This is the semantic replacement for transporting explicit odd
graph paths through arbitrary border windows.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalEvenFreeLines

open RedShadeCycles Signals.FreeCellLocal ShadedSubstitution
open CanonicalFreeLine CanonicalFreeLineBranching
  CanonicalFreeLineCoordinates CanonicalFreeLineLocal

set_option maxRecDepth 20000

def indexGrid (root : Node) (level : Nat) : Nat → Nat → Index :=
  supertileIndexGrid level root

def shadeGrid (root : Node) (level : Nat) : Nat → Nat → RedShades.State :=
  fun x y => flipShade (supertileShadeGrid level root x y)

def selectedVerticalAt (root : Node) (level x y : Nat) :
    Option Signals.HorizontalInterior :=
  ShadedSignals.selectedVerticalFor
    (componentAt (indexGrid root level) x y) (quadrantAt x y)
    (shadeGrid root level x y)

def selectedHorizontalAt (root : Node) (level x y : Nat) :
    Option Signals.VerticalInterior :=
  ShadedSignals.selectedHorizontalFor
    (componentAt (indexGrid root level) x y) (quadrantAt x y)
    (shadeGrid root level x y)

theorem shadeGrid_one_eq_fineState (root : Node) (x y : Nat) :
    shadeGrid root 1 x y =
      flipShade ((fineNode root x y).data.block.at (x % 2) (y % 2)) := by
  rfl

theorem rootCycle_light (root : Node) :
    CycleShade (shadeGrid root 1) 1 3 1 3 .light := by
  have checked := evenRootCycleDark_of_mem root.property
  simp only [evenRootCycleDark, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨southwest, southeast⟩, northeast⟩, northwest⟩
  simp only [fineState?_val, Option.bind_some] at southwest southeast northeast northwest
  constructor
  · simp [quarterWest, quarterSouth, shadeGrid_one_eq_fineState, flipShade, southwest,
      RedShades.Shade.opposite]
  · simp [quarterEast, quarterSouth, shadeGrid_one_eq_fineState, flipShade, southeast,
      RedShades.Shade.opposite]
  · simp [quarterEast, quarterNorth, shadeGrid_one_eq_fineState, flipShade, northeast,
      RedShades.Shade.opposite]
  · simp [quarterWest, quarterNorth, shadeGrid_one_eq_fineState, flipShade, northwest,
      RedShades.Shade.opposite]

theorem selectedVerticalAt_eq_local (root : Node) (level x y : Nat) :
    selectedVerticalAt root level x y =
      CanonicalFreeLineLocal.selectedVertical
        (supertileNodeGrid level root (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  simp [selectedVerticalAt, indexGrid, shadeGrid,
    CanonicalFreeLineLocal.selectedVertical, componentAt,
    supertileIndexGrid, supertileShadeGrid, supertileBlockGrid,
    quadrantAt]

theorem selectedHorizontalAt_eq_local (root : Node) (level x y : Nat) :
    selectedHorizontalAt root level x y =
      CanonicalFreeLineLocal.selectedHorizontal
        (supertileNodeGrid level root (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  simp [selectedHorizontalAt, indexGrid, shadeGrid,
    CanonicalFreeLineLocal.selectedHorizontal, componentAt,
    supertileIndexGrid, supertileShadeGrid, supertileBlockGrid,
    quadrantAt]

private theorem supertileNodeGrid_succ_block (root : Node)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    supertileNodeGrid (level + 1) root
        ((8 * blockX + localX) / 2) ((8 * blockY + localY) / 2) =
      fineNode (supertileNodeGrid level root blockX blockY)
        localX localY := by
  have hxDiv : ((8 * blockX + localX) / 2) / 4 = blockX := by omega
  have hyDiv : ((8 * blockY + localY) / 2) / 4 = blockY := by omega
  have hxMod : ((8 * blockX + localX) / 2) % 4 = localX / 2 := by omega
  have hyMod : ((8 * blockY + localY) / 2) % 4 = localY / 2 := by omega
  have hxHalfMod : (localX / 2) % 4 = localX / 2 := by omega
  have hyHalfMod : (localY / 2) % 4 = localY / 2 := by omega
  simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, fineNode,
    childPosition, hxDiv, hyDiv, hxMod, hyMod, hxHalfMod, hyHalfMod]

theorem selectedVerticalAt_succ_block (root : Node)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    selectedVerticalAt root (level + 1)
        (8 * blockX + localX) (8 * blockY + localY) =
      fineSelectedVertical
        (supertileNodeGrid level root blockX blockY) localX localY := by
  rw [selectedVerticalAt_eq_local]
  rw [supertileNodeGrid_succ_block root level blockX blockY localX localY hx hy]
  unfold fineSelectedVertical CanonicalFreeLineLocal.selectedVertical
  have hxmod : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hymod : (8 * blockY + localY) % 2 = localY % 2 := by omega
  rw [hxmod, hymod]
  simp [quadrantAt]

theorem selectedHorizontalAt_succ_block
    (root : Node) (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    selectedHorizontalAt root (level + 1)
        (8 * blockX + localX) (8 * blockY + localY) =
      fineSelectedHorizontal
        (supertileNodeGrid level root blockX blockY) localX localY := by
  rw [selectedHorizontalAt_eq_local]
  rw [supertileNodeGrid_succ_block root level blockX blockY localX localY hx hy]
  unfold fineSelectedHorizontal CanonicalFreeLineLocal.selectedHorizontal
  have hxmod : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hymod : (8 * blockY + localY) % 2 = localY % 2 := by omega
  rw [hxmod, hymod]
  simp [quadrantAt]

@[irreducible] def FreeRowAt (root : Node) (depth row : Nat) : Prop :=
  ∀ x, quarterWest (4 ^ depth) < x →
    x < quarterEast (3 * 4 ^ depth) →
      selectedVerticalAt root (depth + 1) x row = none

@[irreducible] def FreeColumnAt (root : Node) (depth column : Nat) : Prop :=
  ∀ y, quarterSouth (4 ^ depth) < y →
    y < quarterNorth (3 * 4 ^ depth) →
      selectedHorizontalAt root (depth + 1) column y = none

theorem base_free_row (root : Node) : FreeRowAt root 0 5 := by
  unfold FreeRowAt
  simp only [pow_zero, Nat.mul_one]
  intro x hwest heast
  have hxDiv : x / 2 = 2 := by
    simp only [quarterWest, quarterEast] at hwest heast
    omega
  have clear := (baseNode_clear root).1
  rw [selectedVerticalAt_eq_local, hxDiv]
  have nodeEq : supertileNodeGrid 1 root 2 2 = baseNode root := by
    unfold baseNode
    simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, childPosition]
  rw [nodeEq]
  exact clear (x % 2) (Nat.mod_lt _ (by decide))

theorem base_free_column (root : Node) : FreeColumnAt root 0 5 := by
  unfold FreeColumnAt
  simp only [pow_zero, Nat.mul_one]
  intro y hsouth hnorth
  have hyDiv : y / 2 = 2 := by
    simp only [quarterSouth, quarterNorth] at hsouth hnorth
    omega
  have clear := (baseNode_clear root).2
  rw [selectedHorizontalAt_eq_local, hyDiv]
  have nodeEq : supertileNodeGrid 1 root 2 2 = baseNode root := by
    unfold baseNode
    simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, childPosition]
  rw [nodeEq]
  exact clear (y % 2) (Nat.mod_lt _ (by decide))

private inductive LineAxis where
  | row
  | column

private def linePoint : LineAxis → Nat → Nat → Nat × Nat
  | .row, along, fixed => (along, fixed)
  | .column, along, fixed => (fixed, along)

private def lineNode (axis : LineAxis) (root : Node)
    (level along fixed : Nat) : Node :=
  let point := linePoint axis (along / 2) (fixed / 2)
  supertileNodeGrid level root point.1 point.2

private def lineClearAt (axis : LineAxis) (root : Node)
    (level along fixed : Nat) : Prop :=
  match axis with
  | .row => selectedVerticalAt root level along fixed = none
  | .column => selectedHorizontalAt root level fixed along = none

private def localLineClear (axis : LineAxis) (node : Node)
    (along fixed : Nat) : Prop :=
  match axis with
  | .row => CanonicalFreeLineLocal.selectedVertical node along fixed = none
  | .column => CanonicalFreeLineLocal.selectedHorizontal node fixed along = none

private def fineLineClear (axis : LineAxis) (node : Node)
    (along fixed : Nat) : Prop :=
  match axis with
  | .row => fineSelectedVertical node along fixed = none
  | .column => fineSelectedHorizontal node fixed along = none

private def CoarseLineClear (axis : LineAxis) (node : Node)
    (fixed : Nat) : Prop :=
  ∀ along, along < 2 → localLineClear axis node along fixed

private def FineLineClear (axis : LineAxis) (node : Node)
    (fixed : Nat) : Prop :=
  ∀ along, along < 8 → fineLineClear axis node along fixed

private def BoundaryStripClear (axis : LineAxis) (node : Node)
    (fixed : Nat) : Prop :=
  ∀ along, 2 ≤ along → along < 8 → fineLineClear axis node along fixed

private def LineFree (axis : LineAxis) (root : Node)
    (depth fixed : Nat) : Prop :=
  ∀ along, 2 * 4 ^ depth + 1 < along →
    along < 2 * (3 * 4 ^ depth) →
      lineClearAt axis root (depth + 1) along fixed

private theorem lineClearAt_eq_local (axis : LineAxis) (root : Node)
    (level along fixed : Nat) :
    lineClearAt axis root level along fixed ↔
      localLineClear axis (lineNode axis root level along fixed)
        (along % 2) (fixed % 2) := by
  cases axis <;>
    simp [lineClearAt, localLineClear, lineNode, linePoint,
      selectedVerticalAt_eq_local, selectedHorizontalAt_eq_local]

private theorem lineClearAt_succ_block (axis : LineAxis) (root : Node)
    (level blockAlong blockFixed localAlong localFixed : Nat)
    (alongBound : localAlong < 8) (fixedBound : localFixed < 8) :
    lineClearAt axis root (level + 1)
        (8 * blockAlong + localAlong) (8 * blockFixed + localFixed) ↔
      fineLineClear axis
        (let point := linePoint axis blockAlong blockFixed;
          supertileNodeGrid level root point.1 point.2)
        localAlong localFixed := by
  cases axis with
  | row =>
      simp only [lineClearAt, linePoint, fineLineClear]
      rw [selectedVerticalAt_succ_block root level blockAlong blockFixed
        localAlong localFixed alongBound fixedBound]
  | column =>
      simp only [lineClearAt, linePoint, fineLineClear]
      rw [selectedHorizontalAt_succ_block root level blockFixed blockAlong
        localFixed localAlong fixedBound alongBound]

private theorem freeLine_refine {axis : LineAxis} {root : Node}
    {depth old child localFixed : Nat}
    (oldFree : LineFree axis root depth old)
    (childEq : child = 8 * (old / 2) + localFixed)
    (localFixedBound : localFixed < 8)
    (refines : ∀ node : Node,
      CoarseLineClear axis node (old % 2) →
        FineLineClear axis node localFixed)
    (boundaryClear : ∀ node : Node,
      BoundaryStripClear axis node localFixed) :
    LineFree axis root (depth + 1) child := by
  intro along lower upper
  let blockAlong := along / 8
  let localAlong := along % 8
  have localAlongBound : localAlong < 8 := Nat.mod_lt _ (by decide)
  have alongEq : along = 8 * blockAlong + localAlong := by
    dsimp [blockAlong, localAlong]
    omega
  have blockAlongLower : 4 ^ depth ≤ blockAlong := by
    simp only [pow_succ] at lower
    omega
  have blockAlongUpper : blockAlong < 3 * 4 ^ depth := by
    simp only [pow_succ] at upper
    omega
  rw [alongEq, childEq,
    lineClearAt_succ_block axis root (depth + 1) blockAlong (old / 2)
      localAlong localFixed localAlongBound localFixedBound]
  by_cases boundary : blockAlong = 4 ^ depth
  · apply boundaryClear
    · simp only [pow_succ] at lower
      omega
    · exact localAlongBound
  · have parentClear : CoarseLineClear axis
        (let point := linePoint axis blockAlong (old / 2);
          supertileNodeGrid (depth + 1) root point.1 point.2)
        (old % 2) := by
      intro oldLocal oldLocalBound
      let oldAlong := 2 * blockAlong + oldLocal
      have oldLower : 2 * 4 ^ depth + 1 < oldAlong := by
        dsimp [oldAlong]
        omega
      have oldUpper : oldAlong < 2 * (3 * 4 ^ depth) := by
        dsimp [oldAlong]
        omega
      have clear := oldFree oldAlong oldLower oldUpper
      have oldAlongDiv : oldAlong / 2 = blockAlong := by
        dsimp [oldAlong]
        omega
      have oldAlongMod : oldAlong % 2 = oldLocal := by
        dsimp [oldAlong]
        omega
      rw [lineClearAt_eq_local] at clear
      unfold lineNode at clear
      rw [oldAlongDiv, oldAlongMod] at clear
      exact clear
    exact (refines _ parentClear) localAlong localAlongBound

private theorem freeLine_child {axis : LineAxis} {root : Node}
    {depth oldOffset childOffset : Nat}
    (oldFree : LineFree axis root depth (coordinate depth oldOffset))
    (hchild : childOffset ∈ CanonicalFreeLineBranching.children oldOffset)
    (oddRefines : ∀ node : Node,
      CoarseLineClear axis node 1 →
        FineLineClear axis node 1 ∧ FineLineClear axis node 2)
    (evenRefines : ∀ node : Node,
      CoarseLineClear axis node 0 → FineLineClear axis node 0)
    (boundaryClears : ∀ node : Node,
      BoundaryStripClear axis node 0 ∧
        BoundaryStripClear axis node 1 ∧
          BoundaryStripClear axis node 2) :
    LineFree axis root (depth + 1) (coordinate (depth + 1) childOffset) := by
  rcases mem_children_cases hchild with
    ⟨even, rfl | rfl⟩ | ⟨odd, rfl⟩
  · apply freeLine_refine oldFree (localFixed := 1)
    · simp only [coordinate, pow_succ]
      omega
    · decide
    · intro node clear
      rw [show coordinate depth oldOffset % 2 = 1 by
        simp only [coordinate]
        omega] at clear
      exact (oddRefines node clear).1
    · exact fun node => (boundaryClears node).2.1
  · apply freeLine_refine oldFree (localFixed := 2)
    · simp only [coordinate, pow_succ]
      omega
    · decide
    · intro node clear
      rw [show coordinate depth oldOffset % 2 = 1 by
        simp only [coordinate]
        omega] at clear
      exact (oddRefines node clear).2
    · exact fun node => (boundaryClears node).2.2
  · apply freeLine_refine oldFree (localFixed := 0)
    · simp only [coordinate, pow_succ]
      omega
    · decide
    · intro node clear
      rw [show coordinate depth oldOffset % 2 = 0 by
        simp only [coordinate]
        omega] at clear
      exact evenRefines node clear
    · exact fun node => (boundaryClears node).1

private theorem freeRow_child {root : Node} {depth oldOffset childOffset : Nat}
    (oldFree : FreeRowAt root depth (coordinate depth oldOffset))
    (hchild : childOffset ∈ CanonicalFreeLineBranching.children oldOffset) :
    FreeRowAt root (depth + 1) (coordinate (depth + 1) childOffset) := by
  unfold FreeRowAt at oldFree ⊢
  change LineFree .row root depth (coordinate depth oldOffset) at oldFree
  change LineFree .row root (depth + 1) (coordinate (depth + 1) childOffset)
  apply freeLine_child oldFree hchild
  · intro node clear
    exact row_one_refines node clear
  · intro node clear
    exact row_zero_refines node clear
  · intro node
    exact west_strips_clear node

private theorem freeColumn_child {root : Node} {depth oldOffset childOffset : Nat}
    (oldFree : FreeColumnAt root depth (coordinate depth oldOffset))
    (hchild : childOffset ∈ CanonicalFreeLineBranching.children oldOffset) :
    FreeColumnAt root (depth + 1) (coordinate (depth + 1) childOffset) := by
  unfold FreeColumnAt at oldFree ⊢
  change LineFree .column root depth (coordinate depth oldOffset) at oldFree
  change LineFree .column root (depth + 1) (coordinate (depth + 1) childOffset)
  apply freeLine_child oldFree hchild
  · intro node clear
    exact column_one_refines node clear
  · intro node clear
    exact column_zero_refines node clear
  · intro node
    exact south_strips_clear node

theorem coordinate_free_lines (root : Node) (depth : Nat) {coordinate : Nat}
    (hcoordinate : coordinate ∈ coordinates depth) :
    FreeRowAt root depth coordinate ∧ FreeColumnAt root depth coordinate := by
  rw [mem_coordinates_iff] at hcoordinate
  rcases hcoordinate with ⟨offset, hoffset, rfl⟩
  induction depth generalizing offset with
  | zero =>
      simp only [offsets_zero, List.mem_singleton] at hoffset
      subst offset
      simpa [coordinate] using
        And.intro (base_free_row root) (base_free_column root)
  | succ depth ih =>
      rw [offsets_succ, List.mem_flatMap] at hoffset
      rcases hoffset with ⟨old, hold, hchild⟩
      exact ⟨freeRow_child (ih old hold).1 hchild,
        freeColumn_child (ih old hold).2 hchild⟩

theorem freeRowAt_iff_isFreeRow (root : Node) (depth row : Nat) :
    FreeRowAt root depth row ↔
      ShadedPlaneSignalGrid.IsFreeRow (indexGrid root (depth + 1))
        (shadeGrid root (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) row := by
  unfold FreeRowAt ShadedPlaneSignalGrid.IsFreeRow selectedVerticalAt
  rfl

theorem freeColumnAt_iff_isFreeColumn (root : Node) (depth column : Nat) :
    FreeColumnAt root depth column ↔
      ShadedPlaneSignalGrid.IsFreeColumn (indexGrid root (depth + 1))
        (shadeGrid root (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) column := by
  unfold FreeColumnAt ShadedPlaneSignalGrid.IsFreeColumn selectedHorizontalAt
  rfl

theorem coordinate_isFreeRow (root : Node) (depth : Nat) {row : Nat}
    (hrow : row ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeRow (indexGrid root (depth + 1))
      (shadeGrid root (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) row :=
  (freeRowAt_iff_isFreeRow root depth row).1
    (coordinate_free_lines root depth hrow).1

theorem coordinate_isFreeColumn (root : Node) (depth : Nat) {column : Nat}
    (hcolumn : column ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeColumn (indexGrid root (depth + 1))
      (shadeGrid root (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) column :=
  (freeColumnAt_iff_isFreeColumn root depth column).1
    (coordinate_free_lines root depth hcolumn).2

end CanonicalEvenFreeLines
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
