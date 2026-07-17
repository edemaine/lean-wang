/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSubstitutionCertificate
import LeanWang.Robinson.Closed104.ShadedSubstitutionSeedCheck
import LeanWang.Robinson.Closed104.RedShadeGraphColoring

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

open RedShadeGraphRefinement Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A decorated substitution state certified reachable from the selected seed. -/
abbrev Node := { node : Nat // node ∈ reachable }

/-- The concrete root selected by the finite strategy. -/
def seedNode : Node := ⟨encodeNode false 0, seed_mem_reachable⟩

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
      node.data.expansion[(position : Nat)]? =
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
    node.data.expansion[(position : Nat)]? =
      some (node.child position).data.block :=
  (child_spec node position).2

theorem block_mem_validShadeBlocks (node : Node) :
    node.data.block ∈ validShadeBlocks node.data.parent :=
  (modelData_structure_of_mem node.property (modelData_data node)).1

theorem expansion_internally_valid (node : Node) :
    expansionInternallyValid node.data = true :=
  (modelData_structure_of_mem node.property (modelData_data node)).2

end Node

/-- Row-major position in a `4 x 4` expansion. -/
def blockPosition (x y : Fin 4) : Fin 16 :=
  ⟨x + 4 * y, by omega⟩

/-- Horizontal compatibility of both the corrected tile and its shade block. -/
def HCompatible (left right : Node) : Prop :=
  WangTile.HMatches
      (tile (components left.data.parent))
      (tile (components right.data.parent)) ∧
    left.data.block.hMatches right.data.block = true

/-- Vertical compatibility of both the corrected tile and its shade block. -/
def VCompatible (lower upper : Node) : Prop :=
  WangTile.VMatches
      (tile (components lower.data.parent))
      (tile (components upper.data.parent)) ∧
    lower.data.block.vMatches upper.data.block = true

theorem allowed_of_mem_allowedStates {parent : Index} {x y : Nat}
    {state : RedShades.State} (hstate : state ∈ allowedStates parent x y) :
    RedShades.locallyAllowed (parent, quadrantAt x y) state = true :=
  (List.mem_filter.1 hstate).2

theorem ShadeBlock.allowed_corners {parent : Index} {block : ShadeBlock}
    (hblock : block ∈ validShadeBlocks parent) :
    RedShades.locallyAllowed (parent, quadrantAt 0 0)
        block.southwest = true ∧
      RedShades.locallyAllowed (parent, quadrantAt 1 0)
        block.southeast = true ∧
      RedShades.locallyAllowed (parent, quadrantAt 0 1)
        block.northwest = true ∧
      RedShades.locallyAllowed (parent, quadrantAt 1 1)
        block.northeast = true := by
  have hshade : block ∈ shadeBlocks parent := (List.mem_filter.1 hblock).1
  unfold shadeBlocks at hshade
  rcases List.mem_flatMap.1 hshade with ⟨southwest, hsw, hshade⟩
  rcases List.mem_flatMap.1 hshade with ⟨southeast, hse, hshade⟩
  rcases List.mem_flatMap.1 hshade with ⟨northwest, hnw, hshade⟩
  rcases List.mem_map.1 hshade with ⟨northeast, hne, rfl⟩
  exact ⟨allowed_of_mem_allowedStates hsw,
    allowed_of_mem_allowedStates hse,
    allowed_of_mem_allowedStates hnw,
    allowed_of_mem_allowedStates hne⟩

theorem ShadeBlock.allowed {parent : Index} {block : ShadeBlock}
    (hblock : block ∈ validShadeBlocks parent) (x y : Nat)
    (hx : x < 2) (hy : y < 2) :
    RedShades.locallyAllowed (parent, quadrantAt x y) (block.at x y) = true := by
  have hxCases : x = 0 ∨ x = 1 := by omega
  have hyCases : y = 0 ∨ y = 1 := by omega
  have corners := ShadeBlock.allowed_corners hblock
  rcases hxCases with rfl | rfl <;> rcases hyCases with rfl | rfl
  · simpa [ShadeBlock.at] using corners.1
  · simpa [ShadeBlock.at] using corners.2.2.1
  · simpa [ShadeBlock.at] using corners.2.1
  · simpa [ShadeBlock.at] using corners.2.2.2

theorem ShadeBlock.internal_matches {parent : Index} {block : ShadeBlock}
    (hblock : block ∈ validShadeBlocks parent) :
    block.southwest.east = block.southeast.west ∧
      block.northwest.east = block.northeast.west ∧
      block.southwest.north = block.northwest.south ∧
      block.southeast.north = block.northeast.south := by
  have valid := (List.mem_filter.1 hblock).2
  simp only [ShadeBlock.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact ⟨valid.1.1.1, valid.1.1.2, valid.1.2, valid.2⟩

private theorem blockPosition_mod (x y : Fin 4) :
    (blockPosition x y : Nat) % 4 = x := by
  change (x.val + 4 * y.val) % 4 = x.val
  omega

private theorem blockPosition_div (x y : Fin 4) :
    (blockPosition x y : Nat) / 4 = y := by
  change (x.val + 4 * y.val) / 4 = y.val
  omega

theorem children_hCompatible_within (node : Node) (x : Fin 3) (y : Fin 4) :
    HCompatible
      (node.child (blockPosition ⟨x, by omega⟩ y))
      (node.child (blockPosition ⟨x + 1, by omega⟩ y)) := by
  have valid := node.expansion_internally_valid
  simp only [expansionInternallyValid, Bool.and_eq_true,
    decide_eq_true_eq] at valid
  have checked := List.all_eq_true.1
    (List.all_eq_true.1 valid.1.2 x (by simpa using x.isLt))
      y (by simpa using y.isLt)
  have leftBlock : node.data.expansion[x.val + 4 * y.val]? =
      some (node.child (blockPosition ⟨x, by omega⟩ y)).data.block := by
    simpa only [blockPosition] using
      node.child_block (blockPosition ⟨x, by omega⟩ y)
  have rightBlock : node.data.expansion[x.val + 1 + 4 * y.val]? =
      some (node.child (blockPosition ⟨x + 1, by omega⟩ y)).data.block := by
    simpa only [blockPosition] using
      node.child_block (blockPosition ⟨x + 1, by omega⟩ y)
  rw [leftBlock, rightBlock] at checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  constructor
  · simpa [node.child_parent, blockPosition_mod, blockPosition_div] using checked.1
  · exact checked.2

theorem children_vCompatible_within (node : Node) (x : Fin 4) (y : Fin 3) :
    VCompatible
      (node.child (blockPosition x ⟨y, by omega⟩))
      (node.child (blockPosition x ⟨y + 1, by omega⟩)) := by
  have valid := node.expansion_internally_valid
  simp only [expansionInternallyValid, Bool.and_eq_true,
    decide_eq_true_eq] at valid
  have checked := List.all_eq_true.1
    (List.all_eq_true.1 valid.2 x (by simpa using x.isLt))
      y (by simpa using y.isLt)
  have lowerBlock : node.data.expansion[x.val + 4 * y.val]? =
      some (node.child (blockPosition x ⟨y, by omega⟩)).data.block := by
    simpa only [blockPosition] using
      node.child_block (blockPosition x ⟨y, by omega⟩)
  have upperBlock : node.data.expansion[x.val + 4 * (y.val + 1)]? =
      some (node.child (blockPosition x ⟨y + 1, by omega⟩)).data.block := by
    simpa only [blockPosition] using
      node.child_block (blockPosition x ⟨y + 1, by omega⟩)
  rw [lowerBlock, upperBlock] at checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  constructor
  · simpa [node.child_parent, blockPosition_mod, blockPosition_div] using checked.1
  · exact checked.2

theorem children_hCompatible_boundary {left right : Node}
    (compatible : HCompatible left right) (y : Fin 4) :
    HCompatible
      (left.child (blockPosition ⟨3, by decide⟩ y))
      (right.child (blockPosition ⟨0, by decide⟩ y)) := by
  have preserved := (decoratedCompatible_data_of_mem
    left.property right.property (Node.modelData_data left)
      (Node.modelData_data right)).1
  unfold decoratedHCompatible at preserved
  have condition :
      (decide (WangTile.HMatches
          (tile (components left.data.parent))
          (tile (components right.data.parent))) &&
        left.data.block.hMatches right.data.block) = true := by
    simpa only [HCompatible, Bool.and_eq_true, decide_eq_true_eq] using compatible
  rw [if_pos condition] at preserved
  simp only [Bool.and_eq_true] at preserved
  have indexMatch := List.all_eq_true.1 preserved.1 y (by simpa using y.isLt)
  have blockMatch := List.all_eq_true.1 preserved.2 y (by simpa using y.isLt)
  have leftBlock : left.data.expansion[3 + 4 * y.val]? =
      some (left.child (blockPosition ⟨3, by decide⟩ y)).data.block := by
    simpa only [blockPosition] using
      left.child_block (blockPosition ⟨3, by decide⟩ y)
  have rightBlock : right.data.expansion[4 * y.val]? =
      some (right.child (blockPosition ⟨0, by decide⟩ y)).data.block := by
    simpa only [blockPosition, Nat.zero_add] using
      right.child_block (blockPosition ⟨0, by decide⟩ y)
  rw [leftBlock, rightBlock] at blockMatch
  constructor
  · have matchProp := of_decide_eq_true indexMatch
    simpa [Node.child_parent, blockPosition_mod, blockPosition_div] using matchProp
  · exact blockMatch

theorem children_vCompatible_boundary {lower upper : Node}
    (compatible : VCompatible lower upper) (x : Fin 4) :
    VCompatible
      (lower.child (blockPosition x ⟨3, by decide⟩))
      (upper.child (blockPosition x ⟨0, by decide⟩)) := by
  have preserved := (decoratedCompatible_data_of_mem
    lower.property upper.property (Node.modelData_data lower)
      (Node.modelData_data upper)).2
  unfold decoratedVCompatible at preserved
  have condition :
      (decide (WangTile.VMatches
          (tile (components lower.data.parent))
          (tile (components upper.data.parent))) &&
        lower.data.block.vMatches upper.data.block) = true := by
    simpa only [VCompatible, Bool.and_eq_true, decide_eq_true_eq] using compatible
  rw [if_pos condition] at preserved
  simp only [Bool.and_eq_true] at preserved
  have indexMatch := List.all_eq_true.1 preserved.1 x (by simpa using x.isLt)
  have blockMatch := List.all_eq_true.1 preserved.2 x (by simpa using x.isLt)
  have lowerBlock : lower.data.expansion[x.val + 12]? =
      some (lower.child (blockPosition x ⟨3, by decide⟩)).data.block := by
    simpa only [blockPosition] using
      lower.child_block (blockPosition x ⟨3, by decide⟩)
  have upperBlock : upper.data.expansion[x.val]? =
      some (upper.child (blockPosition x ⟨0, by decide⟩)).data.block := by
    simpa only [blockPosition, Nat.mul_zero, Nat.add_zero] using
      upper.child_block (blockPosition x ⟨0, by decide⟩)
  rw [lowerBlock, upperBlock] at blockMatch
  constructor
  · have matchProp := of_decide_eq_true indexMatch
    simpa [Node.child_parent, blockPosition_mod, blockPosition_div] using matchProp
  · exact blockMatch

/-- Position in a `4 x 4` child block, encoded in south-to-north row order. -/
def childPosition (x y : Nat) : Fin 16 :=
  ⟨x % 4 + 4 * (y % 4), by
    have hx := Nat.mod_lt x (by decide : 0 < 4)
    have hy := Nat.mod_lt y (by decide : 0 < 4)
    omega⟩

/-- Simultaneously replace every node in a grid by its certified child block. -/
def refineNodeGrid (grid : Nat → Nat → Node) : Nat → Nat → Node :=
  fun x y => (grid (x / 4) (y / 4)).child (childPosition x y)

/-- Tile-and-shade compatibility inside a bounded node rectangle. -/
structure CompatibleOn (grid : Nat → Nat → Node) (width height : Nat) : Prop where
  hmatch : ∀ x y, x + 1 < width → y < height →
    HCompatible (grid x y) (grid (x + 1) y)
  vmatch : ∀ x y, x < width → y + 1 < height →
    VCompatible (grid x y) (grid x (y + 1))

theorem CompatibleOn.refine {grid : Nat → Nat → Node} {width height : Nat}
    (compatible : CompatibleOn grid width height) :
    CompatibleOn (refineNodeGrid grid) (4 * width) (4 * height) := by
  constructor
  · intro x y hx hy
    have hxmod : x % 4 < 4 := Nat.mod_lt _ (by decide)
    have hymod : y % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hboundary : x % 4 = 3
    · have hnextDiv : (x + 1) / 4 = x / 4 + 1 := by omega
      have hnextMod : (x + 1) % 4 = 0 := by omega
      have hparentX : x / 4 + 1 < width := by omega
      have hparentY : y / 4 < height := by omega
      have parentMatch := compatible.hmatch (x / 4) (y / 4)
        hparentX hparentY
      have childMatch := children_hCompatible_boundary parentMatch
        ⟨y % 4, hymod⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hboundary,
        hnextDiv, hnextMod] using childMatch
    · have hlocal : x % 4 < 3 := by omega
      have hnextDiv : (x + 1) / 4 = x / 4 := by omega
      have hnextMod : (x + 1) % 4 = x % 4 + 1 := by omega
      have childMatch := children_hCompatible_within (grid (x / 4) (y / 4))
        ⟨x % 4, hlocal⟩ ⟨y % 4, hymod⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hnextDiv,
        hnextMod] using childMatch
  · intro x y hx hy
    have hxmod : x % 4 < 4 := Nat.mod_lt _ (by decide)
    have hymod : y % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hboundary : y % 4 = 3
    · have hnextDiv : (y + 1) / 4 = y / 4 + 1 := by omega
      have hnextMod : (y + 1) % 4 = 0 := by omega
      have hparentX : x / 4 < width := by omega
      have hparentY : y / 4 + 1 < height := by omega
      have parentMatch := compatible.vmatch (x / 4) (y / 4)
        hparentX hparentY
      have childMatch := children_vCompatible_boundary parentMatch
        ⟨x % 4, hxmod⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hboundary,
        hnextDiv, hnextMod] using childMatch
    · have hlocal : y % 4 < 3 := by omega
      have hnextDiv : (y + 1) / 4 = y / 4 := by omega
      have hnextMod : (y + 1) % 4 = y % 4 + 1 := by omega
      have childMatch := children_vCompatible_within (grid (x / 4) (y / 4))
        ⟨x % 4, hxmod⟩ ⟨y % 4, hlocal⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hnextDiv,
        hnextMod] using childMatch

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

theorem supertileNodeGrid_compatible (level : Nat) (root : Node) :
    CompatibleOn (supertileNodeGrid level root) (4 ^ level) (4 ^ level) := by
  induction level with
  | zero =>
      constructor <;> intro x y h <;> omega
  | succ level ih =>
      simpa [supertileNodeGrid, iterateNodeRefine, pow_succ, Nat.mul_comm] using
        ih.refine

theorem supertile_validShadeRectangle (level : Nat) (root : Node) :
    RedShadeGraphColoring.ValidShadeRectangle
      (supertileIndexGrid level root) (supertileShadeGrid level root)
      (2 * 4 ^ level) (2 * 4 ^ level) := by
  constructor
  · intro x y hx hy
    have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have allowed := ShadeBlock.allowed (Node.block_mem_validShadeBlocks
      (supertileNodeGrid level root (x / 2) (y / 2)))
        (x % 2) (y % 2) hxmod hymod
    simpa [supertileIndexGrid, supertileShadeGrid, supertileBlockGrid,
      quadrantAt, Nat.mod_mod] using allowed
  · intro x y hx hy
    have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have hparentY : y / 2 < 4 ^ level := by omega
    by_cases hboundary : x % 2 = 1
    · have hnextDiv : (x + 1) / 2 = x / 2 + 1 := by omega
      have hnextMod : (x + 1) % 2 = 0 := by omega
      have hparentX : x / 2 + 1 < 4 ^ level := by omega
      have compatible := (supertileNodeGrid_compatible level root).hmatch
        (x / 2) (y / 2) hparentX hparentY
      have blockMatch := compatible.2
      simp only [ShadeBlock.hMatches, Bool.and_eq_true,
        decide_eq_true_eq] at blockMatch
      have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hyCases with hyzero | hyone
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hyzero] using blockMatch.1
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hyone] using blockMatch.2
    · have hxzero : x % 2 = 0 := by omega
      have hnextDiv : (x + 1) / 2 = x / 2 := by omega
      have hnextMod : (x + 1) % 2 = 1 := by omega
      have internal := ShadeBlock.internal_matches
        (Node.block_mem_validShadeBlocks
          (supertileNodeGrid level root (x / 2) (y / 2)))
      have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hyCases with hyzero | hyone
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hxzero, hnextDiv, hnextMod, hyzero] using internal.1
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hxzero, hnextDiv, hnextMod, hyone] using internal.2.1
  · intro x y hx hy
    have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have hparentX : x / 2 < 4 ^ level := by omega
    by_cases hboundary : y % 2 = 1
    · have hnextDiv : (y + 1) / 2 = y / 2 + 1 := by omega
      have hnextMod : (y + 1) % 2 = 0 := by omega
      have hparentY : y / 2 + 1 < 4 ^ level := by omega
      have compatible := (supertileNodeGrid_compatible level root).vmatch
        (x / 2) (y / 2) hparentX hparentY
      have blockMatch := compatible.2
      simp only [ShadeBlock.vMatches, Bool.and_eq_true,
        decide_eq_true_eq] at blockMatch
      have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hxCases with hxzero | hxone
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hxzero] using blockMatch.1
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hxone] using blockMatch.2
    · have hyzero : y % 2 = 0 := by omega
      have hnextDiv : (y + 1) / 2 = y / 2 := by omega
      have hnextMod : (y + 1) % 2 = 1 := by omega
      have internal := ShadeBlock.internal_matches
        (Node.block_mem_validShadeBlocks
          (supertileNodeGrid level root (x / 2) (y / 2)))
      have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hxCases with hxzero | hxone
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hyzero, hnextDiv, hnextMod, hxzero] using internal.2.2.1
      · simpa [supertileShadeGrid, supertileBlockGrid, ShadeBlock.at,
          hyzero, hnextDiv, hnextMod, hxone] using internal.2.2.2

/-- Unconditional valid shaded supertiles of unbounded substitution depth. -/
theorem exists_validShadeRectangle (level : Nat) :
    ∃ indexGrid : Nat → Nat → Index,
      ∃ stateGrid : Nat → Nat → RedShades.State,
        RedShadeGraphColoring.ValidShadeRectangle indexGrid stateGrid
          (2 * 4 ^ level) (2 * 4 ^ level) :=
  ⟨supertileIndexGrid level seedNode,
    supertileShadeGrid level seedNode,
    supertile_validShadeRectangle level seedNode⟩

end ShadedSubstitution
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
