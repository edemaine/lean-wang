/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCycleRoute

/-!
# Created segments on the exceptional sparse line

Every live segment except local coordinates `4` and `5` is inherited from the
retained extra-pivot line.  Thus the cycle argument only has to cover two
local positions in each two-substitution macrocell.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCreatedPositions

open RedShadeGraphRefinement SparseFreeLineLocalStates Signals.FreeCellLocal

set_option maxRecDepth 20000

set_option linter.style.nativeDecide false in
theorem vertical_classification (parent : Index) (targetX : Fin 8) :
    verticalAncestorAt 0 0 parent targetX.val = true ∨
      targetX.val = 4 ∨ targetX.val = 5 := by
  revert parent targetX
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_classification (parent : Index) (targetY : Fin 8) :
    horizontalAncestorAt 0 0 parent targetY.val = true ∨
      targetY.val = 4 ∨ targetY.val = 5 := by
  revert parent targetY
  native_decide

theorem verticalAncestorAt_sound
    {parent : Index} {targetX : Nat}
    (checked : verticalAncestorAt 0 0 parent targetX = true)
    (interior : Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX 0)
      (quadrantAt targetX 0) ≠ none) :
    ∃ sourceX, sourceX < 2 ∧ sparseCoordinate sourceX = targetX ∧
      Signals.verticalInterior?
        (componentAt (coarseGrid parent) sourceX 0)
        (quadrantAt sourceX 0) ≠ none := by
  have required : (Signals.verticalInterior?
      (componentAt (fineGrid parent) targetX 0)
      (quadrantAt targetX 0)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [verticalAncestorAt, required, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    at checked
  rcases checked with ⟨sourceX, hsourceX, coordinate, sourceSome⟩
  exact ⟨sourceX, hsourceX, coordinate,
    Option.isSome_iff_ne_none.mp sourceSome⟩

theorem horizontalAncestorAt_sound
    {parent : Index} {targetY : Nat}
    (checked : horizontalAncestorAt 0 0 parent targetY = true)
    (interior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) 0 targetY)
      (quadrantAt 0 targetY) ≠ none) :
    ∃ sourceY, sourceY < 2 ∧ sparseCoordinate sourceY = targetY ∧
      Signals.horizontalInterior?
        (componentAt (coarseGrid parent) 0 sourceY)
        (quadrantAt 0 sourceY) ≠ none := by
  have required : (Signals.horizontalInterior?
      (componentAt (fineGrid parent) 0 targetY)
      (quadrantAt 0 targetY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [horizontalAncestorAt, required, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    at checked
  rcases checked with ⟨sourceY, hsourceY, coordinate, sourceSome⟩
  exact ⟨sourceY, hsourceY, coordinate,
    Option.isSome_iff_ne_none.mp sourceSome⟩

end SparseFreeLineEvenExtraCreatedPositions
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
