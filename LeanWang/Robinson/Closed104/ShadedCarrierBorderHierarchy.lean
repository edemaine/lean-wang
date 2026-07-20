/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificate
import LeanWang.Robinson.Closed104.ShadedCarrierBorderGeometry
import LeanWang.Robinson.Closed104.ShadedSubstitutionPlane
import Mathlib.Tactic.IntervalCases

/-!
# The selected-border hierarchy on substitution supertiles

The finite extended-patch certificate is promoted here to the general direct
border formula and then projected back to concrete substitution supertiles.

There are three representations in play:

* the actual decorated substitution node and its selected signal outputs;
* the direct arithmetic formula `selectedBorder`; and
* a finite certificate state containing a node, coordinate parities, and a
  `3 x 3` border patch.

The proof first normalizes the node outputs and derives the recursive equation
for `selectedBorder`.  It then proves that refining an arithmetic patch agrees
with refining a certificate state.  Closure of the finite state list promotes
the checked equality between visible patches and node outputs to every
supertile block.  The final theorems discard the certificate state and identify
the semantic row and column signals with the arithmetic border formula.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

open Signals.FreeCellLocal ShadedCarrierHierarchy
open ShadedCarrierBorderGeometry
open ShadedSubstitution ShadedSubstitutionPlane

/- These lemmas are representation bridges.  They identify the executable
node indices in the certificate with canonical supertile nodes, and unpack the
eight entries of `nodePatch` as the four horizontal and four vertical selected
signal observations of a `2 x 2` node. -/

theorem generatedNode_eq_supertileNodeGrid
    (level : Nat) (root : Node) (x y : Nat) :
    generatedNode level root x y = supertileNodeGrid level root x y := by
  induction level generalizing x y with
  | zero => rfl
  | succ level inductionHypothesis =>
      simp only [generatedNode, supertileNodeGrid, iterateNodeRefine,
        refineNodeGrid]
      rw [inductionHypothesis]
      change (childNode (supertileNodeGrid level root (x / 4) (y / 4))
          (childPosition x y)).getD 0 =
        ((supertileNodeGrid level root (x / 4) (y / 4)).child
          (childPosition x y) : Nat)
      simpa [childPosition] using congrArg (fun child => child.getD 0)
        (Node.childNode_child
          (supertileNodeGrid level root (x / 4) (y / 4))
          (childPosition x y))

theorem generatedNode_seed_eq_supertileNodeGrid
    (level x y : Nat) :
    generatedNode level (encodeNode false 0) x y =
      supertileNodeGrid level seedNode x y := by
  exact generatedNode_eq_supertileNodeGrid level seedNode x y

theorem nodeParent_state (level x y : Nat) :
    nodeParent (state level x y).node =
      some (supertileIndexGrid level seedNode x y) := by
  simp [nodeParent, state, generatedNode_seed_eq_supertileNodeGrid,
    Node.modelData_data, supertileIndexGrid]

theorem horizontalOutput_node (node : Node) (x y : Nat)
    (hx : x < 2) (hy : y < 2) :
    horizontalOutput node x y =
      ShadedSignalRectangle.horizontalInteriorCode
        (ShadedSignals.selectedVerticalFor
          (componentAt (fun _ _ => node.data.parent) x y)
          (quadrantAt x y) (node.data.block.at x y)) := by
  rw [horizontalOutput, nodePatch, Node.modelData_data]
  have xCases : x = 0 ∨ x = 1 := by omega
  have yCases : y = 0 ∨ y = 1 := by omega
  rcases xCases with rfl | rfl <;> rcases yCases with rfl | rfl <;>
    simp [patchData, List.range_succ, componentAt, quadrantAt, ShadeBlock.at]

theorem verticalOutput_node (node : Node) (x y : Nat)
    (hx : x < 2) (hy : y < 2) :
    verticalOutput node x y =
      ShadedSignalRectangle.verticalInteriorCode
        (ShadedSignals.selectedHorizontalFor
          (componentAt (fun _ _ => node.data.parent) x y)
          (quadrantAt x y) (node.data.block.at x y)) := by
  rw [verticalOutput, nodePatch, Node.modelData_data]
  have xCases : x = 0 ∨ x = 1 := by omega
  have yCases : y = 0 ∨ y = 1 := by omega
  rcases xCases with rfl | rfl <;> rcases yCases with rfl | rfl <;>
    simp [patchData, List.range_succ, componentAt, quadrantAt, ShadeBlock.at]

theorem rowInterior_eq_horizontalOutput
    (level : Nat) (root : Node) (x y : Nat) :
    rowInterior level root x y =
      horizontalOutput
        (supertileNodeGrid level root (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  have output := horizontalOutput_node
    (supertileNodeGrid level root (x / 2) (y / 2))
    (x % 2) (y % 2) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))
  simpa [rowInterior, ShadedSignalRectangle.horizontalInterior,
    componentAt, supertileIndexGrid, supertileShadeGrid,
    supertileBlockGrid, quadrantAt, Nat.mod_mod] using output.symm

theorem columnInterior_eq_verticalOutput
    (level : Nat) (root : Node) (x y : Nat) :
    columnInterior level root x y =
      verticalOutput
        (supertileNodeGrid level root (x / 2) (y / 2))
        (x % 2) (y % 2) := by
  have output := verticalOutput_node
    (supertileNodeGrid level root (x / 2) (y / 2))
    (x % 2) (y % 2) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))
  simpa [columnInterior, ShadedSignalRectangle.verticalInterior,
    componentAt, supertileIndexGrid, supertileShadeGrid,
    supertileBlockGrid, quadrantAt, Nat.mod_mod] using output.symm

/- The direct border formula satisfies the same local recurrence as the
substitution: lift all old borders through the coordinate map, then add the new
depth-one frame.  The block and child versions merely expose the bounded local
coordinates required by the finite patch computation. -/

/-- Splitting the direct finite formula at depth one recovers the local
substitution recurrence used by the finite-state factor. -/
theorem selectedBorder_succ (level coordinate transverse : Nat) :
    selectedBorder (level + 1) coordinate transverse =
      firstBorder
        (liftBorder coordinate <|
          selectedBorder level (ceilDivFour coordinate) (ceilDivFour transverse))
        (liftBorder coordinate <|
          frameBorder 0 (ceilDivFour coordinate) (ceilDivFour transverse)) := by
  apply Option.ext
  intro orientation
  rw [selectedBorder_eq_some_iff, firstBorder_eq_some_iff,
    lift_selectedBorder_eq_some_iff, frameBorder_succ]
  constructor
  · rintro (outer | ⟨depth, positive, bounded, border⟩)
    · exact Or.inl (Or.inl outer)
    · by_cases depthOne : depth = 1
      · right
        refine ⟨?_, by simpa [depthOne] using border⟩
        cases oldEq : liftBorder coordinate
            (selectedBorder level (ceilDivFour coordinate)
              (ceilDivFour transverse)) with
        | none => rfl
        | some oldOrientation =>
            exfalso
            rcases (lift_selectedBorder_eq_some_iff _ _ _ _).1 oldEq with
              oldOuter | ⟨oldDepth, oldLower, _, oldBorder⟩
            · exact outerBorder_frameBorder_disjoint oldOuter border
            · exact frameBorders_disjoint_of_lt (by omega) border oldBorder
      · left
        exact Or.inr ⟨depth, by omega, bounded, border⟩
  · rintro (old | ⟨_, new⟩)
    · rcases old with outer | ⟨depth, lower, bounded, border⟩
      · exact Or.inl outer
      · exact Or.inr ⟨depth, by omega, bounded, border⟩
    · exact Or.inr ⟨1, by omega, by omega, new⟩

theorem selectedBorder_succ_block
    (level blockX blockY offsetX offsetY : Nat) :
    selectedBorder (level + 1)
        (8 * blockX + offsetX) (8 * blockY + offsetY) =
      firstBorder
        (liftBorder offsetX <|
          selectedBorder level
            (2 * blockX + ceilDivFour offsetX)
            (2 * blockY + ceilDivFour offsetY))
        (liftBorder offsetX <|
          frameBorder 0
            (2 * (blockX % 2) + ceilDivFour offsetX)
            (2 * (blockY % 2) + ceilDivFour offsetY)) := by
  rw [selectedBorder_succ, ceilDivFour_eight_mul_add,
    ceilDivFour_eight_mul_add, liftBorder_eight_mul_add,
    liftBorder_eight_mul_add]
  rw [frameBorder_zero_parity]

theorem selectedBorder_succ_child
    (level blockX blockY childX childY x y : Nat) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY) + y) =
      firstBorder
        (liftBorder (2 * childX + x) <|
          selectedBorder level
            (2 * blockX + ceilDivFour (2 * childX + x))
            (2 * blockY + ceilDivFour (2 * childY + y)))
        (liftBorder (2 * childX + x) <|
          frameBorder 0
            (2 * (blockX % 2) + ceilDivFour (2 * childX + x))
            (2 * (blockY % 2) + ceilDivFour (2 * childY + y))) := by
  rw [show 2 * (4 * blockX + childX) + x =
      8 * blockX + (2 * childX + x) by omega]
  rw [show 2 * (4 * blockY + childY) + y =
      8 * blockY + (2 * childY + y) by omega]
  exact selectedBorder_succ_block level blockX blockY
    (2 * childX + x) (2 * childY + y)

theorem selectedBorder_eq_refinedBorder
    (level blockX blockY childX childY x y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4)
    (hx : x < 3) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY) + y) =
      refinedBorder (state level blockX blockY) childX childY x y := by
  rw [selectedBorder_succ_child]
  interval_cases childX <;> interval_cases childY <;>
    interval_cases x <;> interval_cases y <;>
    simp [refinedBorder, state, patchEntry, extendedPatch, ceilDivFour,
      List.range_succ]

theorem selectedBorder_eq_refinedColumnBorder
    (level blockX blockY childX childY x y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4)
    (hx : x < 3) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY) + y)
        (2 * (4 * blockX + childX) + x) =
      refinedColumnBorder (state level blockX blockY)
        childX childY x y := by
  rw [selectedBorder_succ_child level blockY blockX childY childX y x]
  interval_cases childX <;> interval_cases childY <;>
    interval_cases x <;> interval_cases y <;>
    simp [refinedColumnBorder, state, patchEntry, extendedPatch, ceilDivFour,
      List.range_succ]

theorem selectedBorder_eq_refinedBorder_zero_zero
    (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX))
        (2 * (4 * blockY + childY)) =
      refinedBorder (state level blockX blockY) childX childY 0 0 := by
  simpa using selectedBorder_eq_refinedBorder level blockX blockY
    childX childY 0 0 hchildX hchildY (by omega) (by omega)

theorem selectedBorder_eq_refinedBorder_x_zero
    (level blockX blockY childX childY y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX))
        (2 * (4 * blockY + childY) + y) =
      refinedBorder (state level blockX blockY) childX childY 0 y := by
  simpa using selectedBorder_eq_refinedBorder level blockX blockY
    childX childY 0 y hchildX hchildY (by omega) hy

theorem selectedBorder_eq_refinedBorder_y_zero
    (level blockX blockY childX childY x : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hx : x < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockX + childX) + x)
        (2 * (4 * blockY + childY)) =
      refinedBorder (state level blockX blockY) childX childY x 0 := by
  simpa using selectedBorder_eq_refinedBorder level blockX blockY
    childX childY x 0 hchildX hchildY hx (by omega)

theorem selectedBorder_eq_refinedColumnBorder_zero_zero
    (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY))
        (2 * (4 * blockX + childX)) =
      refinedColumnBorder (state level blockX blockY)
        childX childY 0 0 := by
  simpa using selectedBorder_eq_refinedColumnBorder level blockX blockY
    childX childY 0 0 hchildX hchildY (by omega) (by omega)

theorem selectedBorder_eq_refinedColumnBorder_x_zero
    (level blockX blockY childX childY y : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hy : y < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY) + y)
        (2 * (4 * blockX + childX)) =
      refinedColumnBorder (state level blockX blockY)
        childX childY 0 y := by
  simpa using selectedBorder_eq_refinedColumnBorder level blockX blockY
    childX childY 0 y hchildX hchildY (by omega) hy

theorem selectedBorder_eq_refinedColumnBorder_y_zero
    (level blockX blockY childX childY x : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) (hx : x < 3) :
    selectedBorder (level + 1)
        (2 * (4 * blockY + childY))
        (2 * (4 * blockX + childX) + x) =
      refinedColumnBorder (state level blockX blockY)
        childX childY x 0 := by
  simpa using selectedBorder_eq_refinedColumnBorder level blockX blockY
    childX childY x 0 hchildX hchildY hx (by omega)

/- The preceding bounded computations cover every entry of the `3 x 3` halo,
so an arithmetic extended patch refines exactly as the certificate says.  This
is the key connection between the closed formula and the finite state graph. -/

theorem extendedPatch_succ (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    extendedPatch (level + 1)
        (4 * blockX + childX) (4 * blockY + childY) =
      refinePatch (state level blockX blockY) childX childY := by
  unfold extendedPatch refinePatch
  apply congrArg₂ (fun rows columns => rows ++ columns)
  · simp [selectedBorder_eq_refinedBorder,
      selectedBorder_eq_refinedBorder_zero_zero,
      selectedBorder_eq_refinedBorder_x_zero,
      selectedBorder_eq_refinedBorder_y_zero,
      hchildX, hchildY, List.range_succ]
  · simp [selectedBorder_eq_refinedColumnBorder,
      selectedBorder_eq_refinedColumnBorder_zero_zero,
      selectedBorder_eq_refinedColumnBorder_x_zero,
      selectedBorder_eq_refinedColumnBorder_y_zero,
      hchildX, hchildY, List.range_succ]

@[ext] theorem State.ext {left right : State}
    (node : left.node = right.node)
    (blockXParity : left.blockXParity = right.blockXParity)
    (blockYParity : left.blockYParity = right.blockYParity)
    (patch : left.patch = right.patch) : left = right := by
  cases left
  cases right
  simp_all

theorem state_succ (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    state (level + 1)
        (4 * blockX + childX) (4 * blockY + childY) =
      refineState (state level blockX blockY) childX childY := by
  apply State.ext
  · have divX : (4 * blockX + childX) / 4 = blockX := by omega
    have divY : (4 * blockY + childY) / 4 = blockY := by omega
    have modX : (4 * blockX + childX) % 4 = childX := by omega
    have modY : (4 * blockY + childY) % 4 = childY := by omega
    simp [state, refineState, generatedNode, divX, divY, modX, modY]
  · simp [state, refineState, Nat.add_mod, Nat.mul_mod]
  · simp [state, refineState, Nat.add_mod, Nat.mul_mod]
  · exact extendedPatch_succ level blockX blockY childX childY
      hchildX hchildY

/- The native-decided certificate has three logical fields: every listed state
has the correct visible node patch, the list is closed under all sixteen child
positions, and the initial state is listed.  The special corner-transition
field is read separately to characterize where corrected tile index zero can
appear. -/

theorem visiblePatch_eq_nodePatch_of_mem {candidate : State}
    (member : candidate ∈ states) :
    visiblePatch candidate.patch = nodePatch candidate.node := by
  have valid := statesValid_eq_true
  simp only [statesValid, List.all_eq_true, stateValid, Bool.and_eq_true,
    decide_eq_true_eq] at valid
  exact (valid candidate member).2

theorem refineState_mem_of_mem {candidate : State}
    (member : candidate ∈ states) (childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    refineState candidate childX childY ∈ states := by
  have closed := closedValid_eq_true
  simp only [closedValid, List.all_eq_true, decide_eq_true_eq] at closed
  apply closed candidate member
  simp only [stateChildren, List.mem_flatMap, List.mem_map]
  exact ⟨childY, by simpa using hchildY,
    childX, by simpa using hchildX, rfl⟩

theorem cornerTransition_of_mem {candidate : State}
    (member : candidate ∈ states) (childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4)
    (childZero :
      nodeParent (refineState candidate childX childY).node = some 0) :
    (childX = 0 ∧ childY = 0 ∧
      nodeParent candidate.node = some 0 ∧
      candidate.blockXParity = 0 ∧ candidate.blockYParity = 0) ∨
    (childX = 0 ∧ childY = 0 ∧
      nodeParent candidate.node = some 4 ∧
      candidate.blockXParity = 1 ∧ candidate.blockYParity = 1) ∨
    (childX = 2 ∧ childY = 2 ∧
      candidate.blockXParity = 0 ∧ candidate.blockYParity = 0) := by
  have valid := cornerTransitionsValid_eq_true
  simp only [cornerTransitionsValid, List.all_eq_true] at valid
  have candidateValid := valid candidate member
  have childYValid := candidateValid childY (by simpa using hchildY)
  have transition := childYValid childX (by simpa using hchildX)
  have implication := transition
  simp only [cornerTransitionValid, decide_eq_true_eq] at implication
  exact implication childZero

theorem state_mem (level blockX blockY : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level) :
    state level blockX blockY ∈ states := by
  induction level generalizing blockX blockY with
  | zero =>
      have blockXZero : blockX = 0 := by simpa using hblockX
      have blockYZero : blockY = 0 := by simpa using hblockY
      subst blockX
      subst blockY
      exact initialState_mem
  | succ level inductionHypothesis =>
      have parentXBound : blockX / 4 < 4 ^ level := by
        apply Nat.div_lt_of_lt_mul
        simpa [pow_succ, Nat.mul_comm] using hblockX
      have parentYBound : blockY / 4 < 4 ^ level := by
        apply Nat.div_lt_of_lt_mul
        simpa [pow_succ, Nat.mul_comm] using hblockY
      have childXBound : blockX % 4 < 4 := Nat.mod_lt _ (by decide)
      have childYBound : blockY % 4 < 4 := Nat.mod_lt _ (by decide)
      have parentMember := inductionHypothesis
        (blockX / 4) (blockY / 4) parentXBound parentYBound
      have childMember := refineState_mem_of_mem parentMember
        (blockX % 4) (blockY % 4) childXBound childYBound
      rw [← state_succ level (blockX / 4) (blockY / 4)
        (blockX % 4) (blockY % 4) childXBound childYBound] at childMember
      have decomposeX : 4 * (blockX / 4) + blockX % 4 = blockX := by
        have := Nat.mod_add_div blockX 4
        omega
      have decomposeY : 4 * (blockY / 4) + blockY % 4 = blockY := by
        have := Nat.mod_add_div blockY 4
        omega
      simpa [decomposeX, decomposeY] using childMember

/- Induction on base-four block coordinates now places every bounded canonical
block in the certified state list.  From this point onward, finite-state facts
apply uniformly at arbitrary substitution depth. -/

/-- The three certified ways index zero occurs in a canonical child block.
This packages the corrected-tile and thin-layer finite analysis together. -/
theorem supertileIndexGrid_zero_cases
    (level x y : Nat) (hx : x < 4 ^ (level + 1))
    (hy : y < 4 ^ (level + 1))
    (indexZero : supertileIndexGrid (level + 1) seedNode x y = 0) :
    (x % 4 = 0 ∧ y % 4 = 0 ∧
      supertileIndexGrid level seedNode (x / 4) (y / 4) = 0 ∧
      (x / 4) % 2 = 0 ∧ (y / 4) % 2 = 0) ∨
    (x % 4 = 0 ∧ y % 4 = 0 ∧
      supertileIndexGrid level seedNode (x / 4) (y / 4) = 4 ∧
      (x / 4) % 2 = 1 ∧ (y / 4) % 2 = 1) ∨
    (x % 4 = 2 ∧ y % 4 = 2 ∧
      (x / 4) % 2 = 0 ∧ (y / 4) % 2 = 0) := by
  have parentXBound : x / 4 < 4 ^ level := by
    rw [pow_succ] at hx
    omega
  have parentYBound : y / 4 < 4 ^ level := by
    rw [pow_succ] at hy
    omega
  have childXBound : x % 4 < 4 := Nat.mod_lt _ (by decide)
  have childYBound : y % 4 < 4 := Nat.mod_lt _ (by decide)
  let candidate := state level (x / 4) (y / 4)
  have member : candidate ∈ states :=
    state_mem level (x / 4) (y / 4) parentXBound parentYBound
  have refinedEq :
      refineState candidate (x % 4) (y % 4) =
        state (level + 1) x y := by
    rw [← state_succ level (x / 4) (y / 4)
      (x % 4) (y % 4) childXBound childYBound]
    congr 1 <;>
      have decomposition := Nat.mod_add_div x 4 <;>
      have decompositionY := Nat.mod_add_div y 4 <;>
      omega
  have childZero :
      nodeParent (refineState candidate (x % 4) (y % 4)).node = some 0 := by
    rw [refinedEq, nodeParent_state, indexZero]
  have transition := cornerTransition_of_mem member
    (x % 4) (y % 4) childXBound childYBound childZero
  change
    (x % 4 = 0 ∧ y % 4 = 0 ∧
      nodeParent (state level (x / 4) (y / 4)).node = some 0 ∧
      (x / 4) % 2 = 0 ∧ (y / 4) % 2 = 0) ∨
    (x % 4 = 0 ∧ y % 4 = 0 ∧
      nodeParent (state level (x / 4) (y / 4)).node = some 4 ∧
      (x / 4) % 2 = 1 ∧ (y / 4) % 2 = 1) ∨
    (x % 4 = 2 ∧ y % 4 = 2 ∧
      (x / 4) % 2 = 0 ∧ (y / 4) % 2 = 0) at transition
  simpa only [nodeParent_state, Option.some.injEq] using transition

theorem visiblePatch_state_eq_nodePatch
    (level blockX blockY : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level) :
    visiblePatch (extendedPatch level blockX blockY) =
      nodePatch (supertileNodeGrid level seedNode blockX blockY) := by
  have patch := visiblePatch_eq_nodePatch_of_mem
    (state_mem level blockX blockY hblockX hblockY)
  simpa [state, generatedNode_seed_eq_supertileNodeGrid] using patch

/- Finally, read the visible entries of the certified patch and recombine the
block coordinate and its modulo-two local coordinate.  This removes all
certificate machinery from the public conclusion: actual selected signals on
the seed supertile equal `selectedBorder` pointwise. -/

theorem horizontalOutput_node_eq_selectedBorder
    (level blockX blockY x y : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level)
    (hx : x < 2) (hy : y < 2) :
    horizontalOutput (supertileNodeGrid level seedNode blockX blockY) x y =
      selectedBorder level (2 * blockX + x) (2 * blockY + y) := by
  have patchEquality := visiblePatch_state_eq_nodePatch
    level blockX blockY hblockX hblockY
  have entryEquality := congrArg
    (fun patch => patchEntry patch (x + 2 * y)) patchEquality
  interval_cases x <;> interval_cases y <;>
    simp [visiblePatch, extendedPatch, patchEntry,
      List.range_succ] at entryEquality <;>
    simpa [horizontalOutput] using entryEquality.symm

theorem verticalOutput_node_eq_selectedBorder
    (level blockX blockY x y : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level)
    (hx : x < 2) (hy : y < 2) :
    verticalOutput (supertileNodeGrid level seedNode blockX blockY) x y =
      selectedBorder level (2 * blockY + y) (2 * blockX + x) := by
  have patchEquality := visiblePatch_state_eq_nodePatch
    level blockX blockY hblockX hblockY
  have entryEquality := congrArg
    (fun patch => patchEntry patch (4 + x + 2 * y)) patchEquality
  interval_cases x <;> interval_cases y <;>
    simp [visiblePatch, extendedPatch, patchEntry,
      List.range_succ] at entryEquality <;>
    simpa [verticalOutput] using entryEquality.symm

theorem rowInterior_seed_eq_selectedBorder
    (level x y : Nat) (hx : x < side level) (hy : y < side level) :
    rowInterior level seedNode x y = selectedBorder level x y := by
  have hsideX : x < 2 * 4 ^ level := by simpa [side] using hx
  have hsideY : y < 2 * 4 ^ level := by simpa [side] using hy
  have blockXBound : x / 2 < 4 ^ level := by omega
  have blockYBound : y / 2 < 4 ^ level := by omega
  have localXBound : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have localYBound : y % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [rowInterior_eq_horizontalOutput]
  calc
    horizontalOutput (supertileNodeGrid level seedNode (x / 2) (y / 2))
          (x % 2) (y % 2) =
        selectedBorder level
          (2 * (x / 2) + x % 2) (2 * (y / 2) + y % 2) :=
      horizontalOutput_node_eq_selectedBorder level
        (x / 2) (y / 2) (x % 2) (y % 2)
        blockXBound blockYBound localXBound localYBound
    _ = selectedBorder level x y := by
      congr <;>
        have decomposition := Nat.mod_add_div x 2 <;>
        have decompositionY := Nat.mod_add_div y 2 <;>
        omega

theorem columnInterior_seed_eq_selectedBorder
    (level x y : Nat) (hx : x < side level) (hy : y < side level) :
    columnInterior level seedNode x y = selectedBorder level y x := by
  have hsideX : x < 2 * 4 ^ level := by simpa [side] using hx
  have hsideY : y < 2 * 4 ^ level := by simpa [side] using hy
  have blockXBound : x / 2 < 4 ^ level := by omega
  have blockYBound : y / 2 < 4 ^ level := by omega
  have localXBound : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have localYBound : y % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [columnInterior_eq_verticalOutput]
  calc
    verticalOutput (supertileNodeGrid level seedNode (x / 2) (y / 2))
          (x % 2) (y % 2) =
        selectedBorder level
          (2 * (y / 2) + y % 2) (2 * (x / 2) + x % 2) :=
      verticalOutput_node_eq_selectedBorder level
        (x / 2) (y / 2) (x % 2) (y % 2)
        blockXBound blockYBound localXBound localYBound
    _ = selectedBorder level y x := by
      congr <;>
        have decomposition := Nat.mod_add_div x 2 <;>
        have decompositionY := Nat.mod_add_div y 2 <;>
        omega

end ShadedCarrierBorderHierarchy
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
