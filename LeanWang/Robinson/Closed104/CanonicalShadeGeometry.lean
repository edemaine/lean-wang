/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalEvenFreeLines
import LeanWang.Robinson.Closed104.RedShadeGraphCoarsening

/-!
# Geometry of the canonical shaded substitution

This module identifies the selected decorated substitution with ordinary
two-level Robinson refinement and records the shade facts used by semantic
coarsening.  In particular, sparse refinement preserves the selected parent
shade block exactly.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalShadeGeometry

open RedCycles PlaneRedBoards RedShadePaths RedShadeGraph RedShadeGraphColoring
  RedShadeGraphRefinement RedShadeGraphLocalCoverage RedShadeCycles
  RefinementTranslation Signals.FreeCellEmbedding Signals.FreeCellLocal
  ShadedSubstitution CanonicalFreeLine CanonicalFreeLineLocal
  CanonicalEvenFreeLines

set_option maxRecDepth 20000

private theorem iterateRefine_two_eq_fineGrid
    (grid : Nat → Nat → Index) (x y : Nat) :
    iterateRefine 2 grid x y =
      fineGrid (grid (x / 4) (y / 4)) (x % 4) (y % 4) := by
  have refined := iterateRefine_two_block grid 0 (x / 4) (y / 4)
    (x % 4) (y % 4) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have hx : 4 * (x / 4) + x % 4 = x := by omega
  have hy : 4 * (y / 4) + y % 4 = y := by omega
  change iterateRefine 2 grid (4 * (x / 4) + x % 4)
      (4 * (y / 4) + y % 4) =
    iterateRefine 2 (fun _ _ => grid (x / 4) (y / 4))
      (x % 4) (y % 4) at refined
  change iterateRefine 2 grid x y =
    iterateRefine 2 (fun _ _ => grid (x / 4) (y / 4))
      (x % 4) (y % 4)
  simpa only [hx, hy] using refined

private theorem childPosition_mod_four (x y : Nat) :
    (childPosition x y : Nat) % 4 = x % 4 := by
  simp [childPosition, Nat.add_mod]

private theorem childPosition_div_four (x y : Nat) :
    (childPosition x y : Nat) / 4 = y % 4 := by
  change (x % 4 + 4 * (y % 4)) / 4 = y % 4
  have hx := Nat.mod_lt x (by decide : 0 < 4)
  omega

theorem supertileIndexGrid_eq_iterateRefine_apply
    (level : Nat) (root : Node) (x y : Nat) :
    supertileIndexGrid level root x y =
      iterateRefine (2 * level) (fun _ _ => root.data.parent) x y := by
  induction level generalizing x y with
  | zero => rfl
  | succ level ih =>
      change (refineNodeGrid (iterateNodeRefine level (fun _ _ => root))
        x y).data.parent = _
      rw [show 2 * (level + 1) = 2 + 2 * level by omega,
        ← iterateRefine_add]
      rw [iterateRefine_two_eq_fineGrid]
      unfold refineNodeGrid
      rw [Node.child_parent, childPosition_mod_four, childPosition_div_four]
      have ih' := ih (x / 4) (y / 4)
      change (iterateNodeRefine level (fun _ _ => root)
          (x / 4) (y / 4)).data.parent = _ at ih'
      rw [ih']

theorem supertileIndexGrid_eq_iterateRefine (level : Nat) (root : Node) :
    supertileIndexGrid level root =
      iterateRefine (2 * level) (fun _ _ => root.data.parent) := by
  funext x y
  exact supertileIndexGrid_eq_iterateRefine_apply level root x y

/-- Inside one coarse root block, the canonical and arbitrary refined index
grids agree. -/
theorem supertileIndexGrid_eq_coarse (level : Nat) (root : Node)
    (coarse : Nat → Nat → Index) (rootEq : coarse 0 0 = root.data.parent)
    {x y : Nat} (hx : x < 4 ^ level) (hy : y < 4 ^ level) :
    supertileIndexGrid level root x y =
      iterateRefine (2 * level) coarse x y := by
  rw [supertileIndexGrid_eq_iterateRefine]
  have localized := iterateRefine_shift_eq_constant
    (2 * level) coarse 0 0 x y
      (by simpa [pow_mul] using hx) (by simpa [pow_mul] using hy)
  have shiftZero : shiftGrid coarse 0 0 = coarse := by
    funext gridX gridY
    simp [shiftGrid]
  rw [shiftZero] at localized
  rw [localized, rootEq]

private theorem flipShade_allowedFor
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true) :
    RedShades.allowedFor component quadrant (flipShade state) = true := by
  apply RedShades.allowedFor_of
  · have present : state.west.isSome = RedShades.hasWest component quadrant := by
      simp [RedShades.allowedFor] at allowed
      aesop
    simpa [flipShade] using present
  · have present : state.east.isSome = RedShades.hasEast component quadrant := by
      simp [RedShades.allowedFor] at allowed
      aesop
    simpa [flipShade] using present
  · have present : state.south.isSome = RedShades.hasSouth component quadrant := by
      simp [RedShades.allowedFor] at allowed
      aesop
    simpa [flipShade] using present
  · have present : state.north.isSome = RedShades.hasNorth component quadrant := by
      simp [RedShades.allowedFor] at allowed
      aesop
    simpa [flipShade] using present
  · intro horizontal
    change state.west.map RedShades.Shade.opposite =
      state.east.map RedShades.Shade.opposite
    rw [RedShades.horizontal_eq_of_allowedFor allowed horizontal]
  · intro vertical
    change state.south.map RedShades.Shade.opposite =
      state.north.map RedShades.Shade.opposite
    rw [RedShades.vertical_eq_of_allowedFor allowed vertical]
  · intro east south
    change state.east.map RedShades.Shade.opposite =
      state.south.map RedShades.Shade.opposite
    rw [RedShadeGraph.east_south_corner_eq_of_allowedFor allowed east south]
  · intro east north
    change state.east.map RedShades.Shade.opposite =
      state.north.map RedShades.Shade.opposite
    rw [RedShades.east_north_corner_eq_of_allowedFor allowed east north]
  · intro west south
    change state.west.map RedShades.Shade.opposite =
      state.south.map RedShades.Shade.opposite
    rw [RedShades.west_south_corner_eq_of_allowedFor allowed west south]
  · intro west north
    change state.west.map RedShades.Shade.opposite =
      state.north.map RedShades.Shade.opposite
    rw [RedShades.west_north_corner_eq_of_allowedFor allowed west north]
  · intro horizontal vertical equal
    apply RedShades.crossing_opposite_of_allowedFor allowed horizontal vertical
    change state.west.map RedShades.Shade.opposite =
      state.south.map RedShades.Shade.opposite at equal
    have mapped := congrArg (Option.map RedShades.Shade.opposite) equal
    simpa [Option.map_map, Function.comp_def] using mapped

private theorem flipShade_validRectangle
    {grid : Nat → Nat → Index} {states : Nat → Nat → RedShades.State}
    {width height : Nat}
    (valid : ValidShadeRectangle grid states width height) :
    ValidShadeRectangle grid (fun x y => flipShade (states x y))
      width height := by
  constructor
  · intro x y hx hy
    unfold RedShades.locallyAllowed
    exact flipShade_allowedFor (valid.allowed x y hx hy)
  · intro x y hx hy
    change ((states x y).east.map RedShades.Shade.opposite) =
      ((states (x + 1) y).west.map RedShades.Shade.opposite)
    rw [valid.hmatch x y hx hy]
  · intro x y hx hy
    change ((states x y).north.map RedShades.Shade.opposite) =
      ((states x (y + 1)).south.map RedShades.Shade.opposite)
    rw [valid.vmatch x y hx hy]

/-- The flipped canonical shade assignment remains valid on its finite
supertile. -/
theorem validRectangle (level : Nat) (root : Node) :
    ValidShadeRectangle (indexGrid root level) (shadeGrid root level)
      (2 * 4 ^ level) (2 * 4 ^ level) :=
  flipShade_validRectangle (supertile_validShadeRectangle level root)

private def sparseBlockPreserved (node : Nat) : Bool :=
  match modelData node with
  | none => false
  | some data => decide (data.expansion[0]? = some data.block)

private def sparseBlocksComplete : Bool :=
  reachable.all sparseBlockPreserved

set_option linter.style.nativeDecide false in
private theorem sparseBlocksComplete_eq_true : sparseBlocksComplete = true := by
  native_decide

theorem child_zero_block (node : Node) :
    (node.child ⟨0, by decide⟩).data.block = node.data.block := by
  have all := List.all_eq_true.1 sparseBlocksComplete_eq_true
    node.val node.property
  unfold sparseBlockPreserved at all
  rw [Node.modelData_data] at all
  have parentBlock : node.data.expansion[0]? = some node.data.block :=
    of_decide_eq_true all
  have childBlock := node.child_block ⟨0, by decide⟩
  exact Option.some.inj (childBlock.symm.trans parentBlock)

private theorem supertileShadeGrid_succ_sparse
    (level : Nat) (root : Node) (x y : Nat) :
    supertileShadeGrid (level + 1) root
        (sparseCoordinate x) (sparseCoordinate y) =
      supertileShadeGrid level root x y := by
  have hxDiv : sparseCoordinate x / 2 = 4 * (x / 2) := by
    simp [sparseCoordinate, macroOrigin, localCoordinate]
    have := Nat.mod_lt x (by decide : 0 < 2)
    omega
  have hyDiv : sparseCoordinate y / 2 = 4 * (y / 2) := by
    simp [sparseCoordinate, macroOrigin, localCoordinate]
    have := Nat.mod_lt y (by decide : 0 < 2)
    omega
  have hxMod : sparseCoordinate x % 2 = x % 2 :=
    sparseCoordinate_mod_two x
  have hyMod : sparseCoordinate y % 2 = y % 2 :=
    sparseCoordinate_mod_two y
  unfold supertileShadeGrid supertileBlockGrid
  rw [hxDiv, hyDiv, hxMod, hyMod]
  change ((refineNodeGrid (iterateNodeRefine level (fun _ _ => root))
    (4 * (x / 2)) (4 * (y / 2))).data.block.at (x % 2) (y % 2)) = _
  unfold refineNodeGrid
  have childPositionZero :
      childPosition (4 * (x / 2)) (4 * (y / 2)) = ⟨0, by decide⟩ := by
    apply Fin.ext
    simp [childPosition]
  rw [childPositionZero, child_zero_block]
  simp [supertileNodeGrid]

/-- Sparse quarter coordinates retain the preceding canonical shade exactly. -/
theorem shadeGrid_succ_sparse (level : Nat) (root : Node) (x y : Nat) :
    shadeGrid root (level + 1)
        (sparseCoordinate x) (sparseCoordinate y) =
      shadeGrid root level x y := by
  unfold shadeGrid
  rw [supertileShadeGrid_succ_sparse]

/-- Every two-substitution macrocell is the level-one canonical supertile of
its preceding-level node. -/
theorem shadeGrid_succ_block (level : Nat) (root : Node)
    (blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    shadeGrid root (level + 1)
        (8 * blockX + localX) (8 * blockY + localY) =
      shadeGrid (supertileNodeGrid level root blockX blockY) 1
        localX localY := by
  rw [shadeGrid_one_eq_fineState]
  unfold shadeGrid supertileShadeGrid supertileBlockGrid
  have hxDiv : ((8 * blockX + localX) / 2) / 4 = blockX := by omega
  have hyDiv : ((8 * blockY + localY) / 2) / 4 = blockY := by omega
  have hxMod : ((8 * blockX + localX) / 2) % 4 = localX / 2 := by omega
  have hyMod : ((8 * blockY + localY) / 2) % 4 = localY / 2 := by omega
  have hxQuarter : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hyQuarter : (8 * blockY + localY) % 2 = localY % 2 := by omega
  have hxHalf : localX / 2 % 4 = localX / 2 :=
    Nat.mod_eq_of_lt (by omega)
  have hyHalf : localY / 2 % 4 = localY / 2 :=
    Nat.mod_eq_of_lt (by omega)
  simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid, fineNode,
    childPosition, hxDiv, hyDiv, hxMod, hyMod, hxQuarter, hyQuarter,
    hxHalf, hyHalf]

/-- The newly created local cell-cycle source is light after the canonical
global shade flip. -/
theorem cycleSource_light (node : Node) :
    value (shadeGrid node 1) cycleSource = some .light := by
  have dark := CanonicalFreeLine.cycleSourceShade_eq_dark node.property
  have dark' : ((fineNode node 4 3).data.block.at 0 1).west = some .dark := by
    simpa [cycleSourceShade?, Node.modelData_data] using dark
  simp only [value, cycleSource, quarterWest, quarterSouth]
  change (shadeGrid node 1 4 3).west = some .light
  rw [shadeGrid_one_eq_fineState]
  change ((fineNode node 4 3).data.block.at 0 1).west.map
    RedShades.Shade.opposite = some .light
  rw [dark']
  rfl

end CanonicalShadeGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
