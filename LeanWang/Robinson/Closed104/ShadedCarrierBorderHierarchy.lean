/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyCertificate
import LeanWang.Robinson.Closed104.ShadedCarrierBorderGeometry
import Mathlib.Tactic.IntervalCases

/-!
# The selected-border hierarchy on substitution supertiles

The finite extended-patch certificate is promoted here to the general direct
border formula and then projected back to concrete substitution supertiles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderHierarchy

open ShadedCarrierHierarchy ShadedCarrierBorderFactor
open ShadedCarrierBorderFactorSupertiles
open ShadedCarrierBorderGeometry
open ShadedSubstitution ShadedSubstitutionPlane

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

theorem generatedClass_succ_child
    (level blockX blockY childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    generatedClass (level + 1) 15
        (4 * blockX + childX) (4 * blockY + childY) =
      childClass (generatedClass level 15 blockX blockY)
        (childX + 4 * childY) := by
  have divX : (4 * blockX + childX) / 4 = blockX := by omega
  have divY : (4 * blockY + childY) / 4 = blockY := by omega
  have modX : (4 * blockX + childX) % 4 = childX := by omega
  have modY : (4 * blockY + childY) % 4 = childY := by omega
  simp [generatedClass, ShadedSubstitution.childPosition,
    divX, divY, modX, modY]

@[ext] theorem State.ext {left right : State}
    (classId : left.classId = right.classId)
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
  · exact generatedClass_succ_child level blockX blockY childX childY
      hchildX hchildY
  · simp [state, refineState, Nat.add_mod, Nat.mul_mod]
  · simp [state, refineState, Nat.add_mod, Nat.mul_mod]
  · exact extendedPatch_succ level blockX blockY childX childY
      hchildX hchildY

theorem visiblePatch_eq_classPatch_of_mem {candidate : State}
    (member : candidate ∈ states) :
    visiblePatch candidate.patch = classPatch candidate.classId := by
  have valid := statesValid_eq_true
  simp only [statesValid, Bool.and_eq_true, List.all_eq_true,
    stateValid, decide_eq_true_eq] at valid
  exact (valid.2 candidate member).2

theorem refineState_mem_of_mem {candidate : State}
    (member : candidate ∈ states) (childX childY : Nat)
    (hchildX : childX < 4) (hchildY : childY < 4) :
    refineState candidate childX childY ∈ states := by
  have closed := closedValid_eq_true
  simp only [closedValid, List.all_eq_true, decide_eq_true_eq] at closed
  exact closed candidate member childY (by simpa) childX (by simpa)

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

theorem visiblePatch_state_eq_classPatch
    (level blockX blockY : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level) :
    visiblePatch (extendedPatch level blockX blockY) =
      classPatch (generatedClass level 15 blockX blockY) := by
  simpa [state] using visiblePatch_eq_classPatch_of_mem
    (state_mem level blockX blockY hblockX hblockY)

theorem horizontalOutput_generatedClass_eq_selectedBorder
    (level blockX blockY x y : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level)
    (hx : x < 2) (hy : y < 2) :
    horizontalOutput (generatedClass level 15 blockX blockY) x y =
      selectedBorder level (2 * blockX + x) (2 * blockY + y) := by
  have patchEquality := visiblePatch_state_eq_classPatch
    level blockX blockY hblockX hblockY
  have entryEquality := congrArg
    (fun patch => patchEntry patch (x + 2 * y)) patchEquality
  interval_cases x <;> interval_cases y <;>
    simp [visiblePatch, extendedPatch, patchEntry,
      List.range_succ] at entryEquality <;>
    simpa [horizontalOutput] using entryEquality.symm

theorem verticalOutput_generatedClass_eq_selectedBorder
    (level blockX blockY x y : Nat)
    (hblockX : blockX < 4 ^ level) (hblockY : blockY < 4 ^ level)
    (hx : x < 2) (hy : y < 2) :
    verticalOutput (generatedClass level 15 blockX blockY) x y =
      selectedBorder level (2 * blockY + y) (2 * blockX + x) := by
  have patchEquality := visiblePatch_state_eq_classPatch
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
  rw [rowInterior_eq_horizontalOutput,
    classOf_seed_supertileNodeGrid]
  calc
    horizontalOutput (generatedClass level 15 (x / 2) (y / 2))
          (x % 2) (y % 2) =
        selectedBorder level
          (2 * (x / 2) + x % 2) (2 * (y / 2) + y % 2) :=
      horizontalOutput_generatedClass_eq_selectedBorder level
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
  rw [columnInterior_eq_verticalOutput,
    classOf_seed_supertileNodeGrid]
  calc
    verticalOutput (generatedClass level 15 (x / 2) (y / 2))
          (x % 2) (y % 2) =
        selectedBorder level
          (2 * (y / 2) + y % 2) (2 * (x / 2) + x % 2) :=
      verticalOutput_generatedClass_eq_selectedBorder level
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
