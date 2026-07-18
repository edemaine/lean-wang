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

theorem selectedVerticalAt_succ_block (root : Node)
    (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    selectedVerticalAt root (level + 1)
        (8 * blockX + localX) (8 * blockY + localY) =
      fineSelectedVertical
        (supertileNodeGrid level root blockX blockY) localX localY := by
  rw [selectedVerticalAt_eq_local]
  have nodeEq :
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
  rw [nodeEq]
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
  have nodeEq :
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
  rw [nodeEq]
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

private theorem freeRow_refine {root : Node} {depth old child localY : Nat}
    (oldFree : FreeRowAt root depth old)
    (child_eq : child = 8 * (old / 2) + localY)
    (localY_lt : localY < 8)
    (refines : ∀ node : Node,
      RowClear node (old % 2) → FineRowClear node localY)
    (westClear : ∀ node : Node, WestStripClear node localY) :
    FreeRowAt root (depth + 1) child := by
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
    selectedVerticalAt_succ_block root (depth + 1) blockX (old / 2)
      localX localY localX_lt localY_lt]
  by_cases boundary : blockX = 4 ^ depth
  · apply westClear
    · simp only [quarterWest, pow_succ] at hwest
      omega
    · exact localX_lt
  · have parentClear : RowClear
        (supertileNodeGrid (depth + 1) root blockX (old / 2))
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

private theorem freeColumn_refine {root : Node} {depth old child localX : Nat}
    (oldFree : FreeColumnAt root depth old)
    (child_eq : child = 8 * (old / 2) + localX)
    (localX_lt : localX < 8)
    (refines : ∀ node : Node,
      ColumnClear node (old % 2) → FineColumnClear node localX)
    (southClear : ∀ node : Node, SouthStripClear node localX) :
    FreeColumnAt root (depth + 1) child := by
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
    selectedHorizontalAt_succ_block root (depth + 1) (old / 2) blockY
      localX localY localX_lt localY_lt]
  by_cases boundary : blockY = 4 ^ depth
  · apply southClear
    · simp only [quarterSouth, pow_succ] at hsouth
      omega
    · exact localY_lt
  · have parentClear : ColumnClear
        (supertileNodeGrid (depth + 1) root (old / 2) blockY)
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

theorem freeRow_child {root : Node} {depth old child : Nat}
    (oldFree : FreeRowAt root depth old)
    (hchild : child ∈ CanonicalFreeLineCoordinates.children old) :
    FreeRowAt root (depth + 1) child := by
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

theorem freeColumn_child {root : Node} {depth old child : Nat}
    (oldFree : FreeColumnAt root depth old)
    (hchild : child ∈ CanonicalFreeLineCoordinates.children old) :
    FreeColumnAt root (depth + 1) child := by
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

theorem coordinate_free_lines (root : Node) (depth : Nat) {coordinate : Nat}
    (hcoordinate : coordinate ∈ coordinates depth) :
    FreeRowAt root depth coordinate ∧ FreeColumnAt root depth coordinate := by
  induction depth generalizing coordinate with
  | zero =>
      simp only [coordinates_zero, List.mem_singleton] at hcoordinate
      subst coordinate
      exact ⟨base_free_row root, base_free_column root⟩
  | succ depth ih =>
      rw [coordinates_succ, List.mem_flatMap] at hcoordinate
      rcases hcoordinate with ⟨old, hold, hchild⟩
      exact ⟨freeRow_child (ih hold).1 hchild,
        freeColumn_child (ih hold).2 hchild⟩

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
