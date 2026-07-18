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
open CanonicalFreeLine CanonicalFreeLineCoordinates CanonicalFreeLineLocal

set_option maxRecDepth 20000

def indexGrid (level : Nat) : Nat → Nat → Index :=
  supertileIndexGrid level seedNode

def shadeGrid (level : Nat) : Nat → Nat → RedShades.State :=
  fun x y => flipShade (supertileShadeGrid level seedNode x y)

def selectedVerticalAt (level x y : Nat) :
    Option Signals.HorizontalInterior :=
  ShadedSignals.selectedVerticalFor
    (componentAt (indexGrid level) x y) (quadrantAt x y)
    (shadeGrid level x y)

def selectedHorizontalAt (level x y : Nat) :
    Option Signals.VerticalInterior :=
  ShadedSignals.selectedHorizontalFor
    (componentAt (indexGrid level) x y) (quadrantAt x y)
    (shadeGrid level x y)

theorem selectedVerticalAt_eq_local (level x y : Nat) :
    selectedVerticalAt level x y =
      CanonicalFreeLineLocal.selectedVertical
        (supertileNodeGrid level seedNode (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  simp [selectedVerticalAt, indexGrid, shadeGrid,
    CanonicalFreeLineLocal.selectedVertical, componentAt,
    supertileIndexGrid, supertileShadeGrid, supertileBlockGrid,
    quadrantAt]

theorem selectedHorizontalAt_eq_local (level x y : Nat) :
    selectedHorizontalAt level x y =
      CanonicalFreeLineLocal.selectedHorizontal
        (supertileNodeGrid level seedNode (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  simp [selectedHorizontalAt, indexGrid, shadeGrid,
    CanonicalFreeLineLocal.selectedHorizontal, componentAt,
    supertileIndexGrid, supertileShadeGrid, supertileBlockGrid,
    quadrantAt]

theorem selectedVerticalAt_succ_block (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    selectedVerticalAt (level + 1)
        (8 * blockX + localX) (8 * blockY + localY) =
      fineSelectedVertical
        (supertileNodeGrid level seedNode blockX blockY) localX localY := by
  rw [selectedVerticalAt_eq_local]
  have nodeEq :
      supertileNodeGrid (level + 1) seedNode
          ((8 * blockX + localX) / 2) ((8 * blockY + localY) / 2) =
        fineNode (supertileNodeGrid level seedNode blockX blockY)
          localX localY := by
    have hxDiv : ((8 * blockX + localX) / 2) / 4 = blockX := by omega
    have hyDiv : ((8 * blockY + localY) / 2) / 4 = blockY := by omega
    have hxMod : ((8 * blockX + localX) / 2) % 4 = localX / 2 := by omega
    have hyMod : ((8 * blockY + localY) / 2) % 4 = localY / 2 := by omega
    have hxHalfMod : (localX / 2) % 4 = localX / 2 := by omega
    have hyHalfMod : (localY / 2) % 4 = localY / 2 := by omega
    simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, fineNode,
      childPosition, hxDiv, hyDiv, hxMod, hyMod, hxHalfMod, hyHalfMod]
  rw [nodeEq]
  unfold fineSelectedVertical CanonicalFreeLineLocal.selectedVertical
  have hxmod : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hymod : (8 * blockY + localY) % 2 = localY % 2 := by omega
  rw [hxmod, hymod]
  simp [quadrantAt]

theorem selectedHorizontalAt_succ_block
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    selectedHorizontalAt (level + 1)
        (8 * blockX + localX) (8 * blockY + localY) =
      fineSelectedHorizontal
        (supertileNodeGrid level seedNode blockX blockY) localX localY := by
  rw [selectedHorizontalAt_eq_local]
  have nodeEq :
      supertileNodeGrid (level + 1) seedNode
          ((8 * blockX + localX) / 2) ((8 * blockY + localY) / 2) =
        fineNode (supertileNodeGrid level seedNode blockX blockY)
          localX localY := by
    have hxDiv : ((8 * blockX + localX) / 2) / 4 = blockX := by omega
    have hyDiv : ((8 * blockY + localY) / 2) / 4 = blockY := by omega
    have hxMod : ((8 * blockX + localX) / 2) % 4 = localX / 2 := by omega
    have hyMod : ((8 * blockY + localY) / 2) % 4 = localY / 2 := by omega
    have hxHalfMod : (localX / 2) % 4 = localX / 2 := by omega
    have hyHalfMod : (localY / 2) % 4 = localY / 2 := by omega
    simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, fineNode,
      childPosition, hxDiv, hyDiv, hxMod, hyMod, hxHalfMod, hyHalfMod]
  rw [nodeEq]
  unfold fineSelectedHorizontal CanonicalFreeLineLocal.selectedHorizontal
  have hxmod : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hymod : (8 * blockY + localY) % 2 = localY % 2 := by omega
  rw [hxmod, hymod]
  simp [quadrantAt]

@[irreducible] def FreeRowAt (depth row : Nat) : Prop :=
  ∀ x, quarterWest (4 ^ depth) < x →
    x < quarterEast (3 * 4 ^ depth) →
      selectedVerticalAt (depth + 1) x row = none

@[irreducible] def FreeColumnAt (depth column : Nat) : Prop :=
  ∀ y, quarterSouth (4 ^ depth) < y →
    y < quarterNorth (3 * 4 ^ depth) →
      selectedHorizontalAt (depth + 1) column y = none

theorem base_free_row : FreeRowAt 0 5 := by
  unfold FreeRowAt
  simp only [pow_zero, Nat.mul_one]
  intro x hwest heast
  have hxDiv : x / 2 = 2 := by
    simp only [quarterWest, quarterEast] at hwest heast
    omega
  have checkedAt : clearVertical evenBaseNodeId (x % 2) 1 = true := by
    apply List.all_eq_true.1 evenBaseRowClear_eq_true
    simp only [List.mem_range]
    exact Nat.mod_lt _ (by decide)
  have clearAt : clearVertical baseNode.val (x % 2) 1 = true := by
    simpa only [baseNode_val] using checkedAt
  rw [selectedVerticalAt_eq_local, hxDiv]
  have nodeEq : supertileNodeGrid 1 seedNode 2 2 = baseNode := by
    unfold baseNode
    simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, childPosition]
  rw [nodeEq]
  exact (clearVertical_val baseNode (x % 2) 1).1 clearAt

theorem base_free_column : FreeColumnAt 0 5 := by
  unfold FreeColumnAt
  simp only [pow_zero, Nat.mul_one]
  intro y hsouth hnorth
  have hyDiv : y / 2 = 2 := by
    simp only [quarterSouth, quarterNorth] at hsouth hnorth
    omega
  have checkedAt : clearHorizontal evenBaseNodeId 1 (y % 2) = true := by
    apply List.all_eq_true.1 evenBaseColumnClear_eq_true
    simp only [List.mem_range]
    exact Nat.mod_lt _ (by decide)
  have clearAt : clearHorizontal baseNode.val 1 (y % 2) = true := by
    simpa only [baseNode_val] using checkedAt
  rw [selectedHorizontalAt_eq_local, hyDiv]
  have nodeEq : supertileNodeGrid 1 seedNode 2 2 = baseNode := by
    unfold baseNode
    simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, childPosition]
  rw [nodeEq]
  exact (clearHorizontal_val baseNode 1 (y % 2)).1 clearAt

private theorem freeRow_refine {depth old child localY : Nat}
    (oldFree : FreeRowAt depth old)
    (child_eq : child = 8 * (old / 2) + localY)
    (localY_lt : localY < 8)
    (refines : ∀ node : Node,
      RowClear node (old % 2) → FineRowClear node localY)
    (westClear : ∀ node : Node, WestStripClear node localY) :
    FreeRowAt (depth + 1) child := by
  unfold FreeRowAt at oldFree ⊢
  intro x hwest heast
  let blockX := x / 8
  let localX := x % 8
  have localX_lt : localX < 8 := by
    exact Nat.mod_lt _ (by decide)
  have x_eq : x = 8 * blockX + localX := by
    dsimp [blockX, localX]
    omega
  have blockX_lower : 4 ^ depth ≤ blockX := by
    simp only [quarterWest, pow_succ] at hwest
    omega
  have blockX_upper : blockX < 3 * 4 ^ depth := by
    simp only [quarterEast, pow_succ] at heast
    omega
  rw [x_eq, child_eq,
    selectedVerticalAt_succ_block (depth + 1) blockX (old / 2)
      localX localY localX_lt localY_lt]
  by_cases boundary : blockX = 4 ^ depth
  · apply westClear
    · simp only [quarterWest, pow_succ] at hwest
      omega
    · exact localX_lt
  · have parentClear : RowClear
        (supertileNodeGrid (depth + 1) seedNode blockX (old / 2))
        (old % 2) := by
      intro oldLocal oldLocal_lt
      let oldX := 2 * blockX + oldLocal
      have oldWest : quarterWest (4 ^ depth) < oldX := by
        simp only [quarterWest]
        dsimp [oldX]
        omega
      have oldEast : oldX < quarterEast (3 * 4 ^ depth) := by
        simp only [quarterEast]
        dsimp [oldX]
        omega
      have clear := oldFree oldX oldWest oldEast
      have oldX_div : oldX / 2 = blockX := by
        dsimp [oldX]
        omega
      have oldX_mod : oldX % 2 = oldLocal := by
        dsimp [oldX]
        omega
      rw [selectedVerticalAt_eq_local, oldX_div, oldX_mod] at clear
      exact clear
    exact (refines _ parentClear) localX localX_lt

private theorem freeColumn_refine {depth old child localX : Nat}
    (oldFree : FreeColumnAt depth old)
    (child_eq : child = 8 * (old / 2) + localX)
    (localX_lt : localX < 8)
    (refines : ∀ node : Node,
      ColumnClear node (old % 2) → FineColumnClear node localX)
    (southClear : ∀ node : Node, SouthStripClear node localX) :
    FreeColumnAt (depth + 1) child := by
  unfold FreeColumnAt at oldFree ⊢
  intro y hsouth hnorth
  let blockY := y / 8
  let localY := y % 8
  have localY_lt : localY < 8 := by
    exact Nat.mod_lt _ (by decide)
  have y_eq : y = 8 * blockY + localY := by
    dsimp [blockY, localY]
    omega
  have blockY_lower : 4 ^ depth ≤ blockY := by
    simp only [quarterSouth, pow_succ] at hsouth
    omega
  have blockY_upper : blockY < 3 * 4 ^ depth := by
    simp only [quarterNorth, pow_succ] at hnorth
    omega
  rw [child_eq, y_eq,
    selectedHorizontalAt_succ_block (depth + 1) (old / 2) blockY
      localX localY localX_lt localY_lt]
  by_cases boundary : blockY = 4 ^ depth
  · apply southClear
    · simp only [quarterSouth, pow_succ] at hsouth
      omega
    · exact localY_lt
  · have parentClear : ColumnClear
        (supertileNodeGrid (depth + 1) seedNode (old / 2) blockY)
        (old % 2) := by
      intro oldLocal oldLocal_lt
      let oldY := 2 * blockY + oldLocal
      have oldSouth : quarterSouth (4 ^ depth) < oldY := by
        simp only [quarterSouth]
        dsimp [oldY]
        omega
      have oldNorth : oldY < quarterNorth (3 * 4 ^ depth) := by
        simp only [quarterNorth]
        dsimp [oldY]
        omega
      have clear := oldFree oldY oldSouth oldNorth
      have oldY_div : oldY / 2 = blockY := by
        dsimp [oldY]
        omega
      have oldY_mod : oldY % 2 = oldLocal := by
        dsimp [oldY]
        omega
      rw [selectedHorizontalAt_eq_local, oldY_div, oldY_mod] at clear
      exact clear
    exact (refines _ parentClear) localY localY_lt

theorem freeRow_child {depth old child : Nat}
    (oldFree : FreeRowAt depth old)
    (hchild : child ∈ CanonicalFreeLineCoordinates.children old) :
    FreeRowAt (depth + 1) child := by
  rcases mem_children_cases hchild with
    ⟨odd, rfl | rfl⟩ | ⟨even, rfl⟩
  · apply freeRow_refine oldFree (localY := 1)
    · omega
    · decide
    · intro node clear
      rw [odd] at clear
      exact (row_one_refines node clear).1
    · intro node
      exact (west_strips_clear node).2.1
  · apply freeRow_refine oldFree (localY := 2)
    · omega
    · decide
    · intro node clear
      rw [odd] at clear
      exact (row_one_refines node clear).2
    · intro node
      exact (west_strips_clear node).2.2
  · apply freeRow_refine oldFree (localY := 0)
    · omega
    · decide
    · intro node clear
      rw [even] at clear
      exact row_zero_refines node clear
    · intro node
      exact (west_strips_clear node).1

theorem freeColumn_child {depth old child : Nat}
    (oldFree : FreeColumnAt depth old)
    (hchild : child ∈ CanonicalFreeLineCoordinates.children old) :
    FreeColumnAt (depth + 1) child := by
  rcases mem_children_cases hchild with
    ⟨odd, rfl | rfl⟩ | ⟨even, rfl⟩
  · apply freeColumn_refine oldFree (localX := 1)
    · omega
    · decide
    · intro node clear
      rw [odd] at clear
      exact (column_one_refines node clear).1
    · intro node
      exact (south_strips_clear node).2.1
  · apply freeColumn_refine oldFree (localX := 2)
    · omega
    · decide
    · intro node clear
      rw [odd] at clear
      exact (column_one_refines node clear).2
    · intro node
      exact (south_strips_clear node).2.2
  · apply freeColumn_refine oldFree (localX := 0)
    · omega
    · decide
    · intro node clear
      rw [even] at clear
      exact column_zero_refines node clear
    · intro node
      exact (south_strips_clear node).1

theorem coordinate_free_lines (depth : Nat) {coordinate : Nat}
    (hcoordinate : coordinate ∈ coordinates depth) :
    FreeRowAt depth coordinate ∧ FreeColumnAt depth coordinate := by
  induction depth generalizing coordinate with
  | zero =>
      simp only [coordinates_zero, List.mem_singleton] at hcoordinate
      subst coordinate
      exact ⟨base_free_row, base_free_column⟩
  | succ depth ih =>
      rw [coordinates_succ, List.mem_flatMap] at hcoordinate
      rcases hcoordinate with ⟨old, hold, hchild⟩
      exact ⟨freeRow_child (ih hold).1 hchild,
        freeColumn_child (ih hold).2 hchild⟩

theorem freeRowAt_iff_isFreeRow (depth row : Nat) :
    FreeRowAt depth row ↔
      ShadedPlaneSignalGrid.IsFreeRow (indexGrid (depth + 1))
        (shadeGrid (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) row := by
  unfold FreeRowAt ShadedPlaneSignalGrid.IsFreeRow selectedVerticalAt
  rfl

theorem freeColumnAt_iff_isFreeColumn (depth column : Nat) :
    FreeColumnAt depth column ↔
      ShadedPlaneSignalGrid.IsFreeColumn (indexGrid (depth + 1))
        (shadeGrid (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) column := by
  unfold FreeColumnAt ShadedPlaneSignalGrid.IsFreeColumn selectedHorizontalAt
  rfl

theorem coordinate_isFreeRow (depth : Nat) {row : Nat}
    (hrow : row ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeRow (indexGrid (depth + 1))
      (shadeGrid (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) row :=
  (freeRowAt_iff_isFreeRow depth row).1 (coordinate_free_lines depth hrow).1

theorem coordinate_isFreeColumn (depth : Nat) {column : Nat}
    (hcolumn : column ∈ coordinates depth) :
    ShadedPlaneSignalGrid.IsFreeColumn (indexGrid (depth + 1))
      (shadeGrid (depth + 1)) (4 ^ depth) (3 * 4 ^ depth) column :=
  (freeColumnAt_iff_isFreeColumn depth column).1
    (coordinate_free_lines depth hcolumn).2

end CanonicalEvenFreeLines
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
