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

open RedCycles RedShadeGraphRefinement SparseFreeLineLocalStates
  SparseFreeLineLocalTransport Signals.FreeCellLocal Signals.FreeCellEmbedding

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

/-- Globally, only residues `4` and `5` can be newly created on a sparse row. -/
theorem vertical_global_classification
    {grid : Nat → Nat → Index} {oldRow x : Nat}
    (heven : oldRow % 2 = 0)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) x (sparseCoordinate oldRow))
      (quadrantAt x (sparseCoordinate oldRow)) ≠ none) :
    (∃ oldX, sparseCoordinate oldX = x ∧
      Signals.verticalInterior?
        (componentAt grid oldX oldRow) (quadrantAt oldX oldRow) ≠ none) ∨
      x % 8 = 4 ∨ x % 8 = 5 := by
  let blockX := x / 8
  let localX := x % 8
  let blockY := oldRow / 2
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hx : 8 * blockX + localX = x := by
    have := Nat.mod_add_div x 8
    dsimp [blockX, localX]
    omega
  have holdRow : 2 * blockY = oldRow := by
    have := Nat.mod_add_div oldRow 2
    dsimp [blockY]
    omega
  have hfineRow : 8 * blockY = sparseCoordinate oldRow := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, blockY, heven]
  let parent := grid blockX blockY
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid parent) localX 0)
      (quadrantAt localX 0) ≠ none := by
    have transported := interior
    rw [← hx, ← hfineRow] at transported
    have hcomponent := componentAt_two_block grid 0 blockX blockY localX 0
      hlocalX (by decide)
    simp only [Nat.zero_add] at hcomponent
    change componentAt (iterateRefine 2 grid)
        (8 * blockX + localX) (8 * blockY + 0) =
      componentAt (iterateRefine 2 (fun _ _ => grid blockX blockY))
        localX 0 at hcomponent
    have hquadrant : quadrantAt (8 * blockX + localX) (8 * blockY + 0) =
        quadrantAt localX 0 := by
      simpa using quadrantAt_block blockX blockY localX 0
    rw [show 8 * blockY = 8 * blockY + 0 by omega,
      hcomponent, hquadrant] at transported
    change Signals.verticalInterior?
      (componentAt (iterateRefine 2 (fun _ _ => parent)) localX 0)
      (quadrantAt localX 0) ≠ none
    simpa [parent] using transported
  rcases vertical_classification parent ⟨localX, hlocalX⟩ with
    checked | created
  · rcases verticalAncestorAt_sound checked localInterior with
      ⟨sourceX, hsourceX, sourceCoordinate, sourceInterior⟩
    left
    refine ⟨2 * blockX + sourceX, ?_, ?_⟩
    · rw [sparseCoordinate_two_block blockX sourceX hsourceX,
        sourceCoordinate, hx]
    · rw [← holdRow]
      have hcomponent := componentAt_old_block grid 0 blockX blockY sourceX 0
        hsourceX (by decide)
      simp only [iterateRefine, Nat.add_zero] at hcomponent
      have hquadrant : quadrantAt (2 * blockX + sourceX) (2 * blockY) =
          quadrantAt sourceX 0 := by
        simpa using quadrantAt_old_block blockX blockY sourceX 0
          hsourceX (by decide)
      rw [hcomponent, hquadrant]
      simpa [holdRow, parent] using sourceInterior
  · exact Or.inr (by simpa [localX] using created)

/-- Globally, only residues `4` and `5` can be newly created on a sparse column. -/
theorem horizontal_global_classification
    {grid : Nat → Nat → Index} {oldColumn y : Nat}
    (heven : oldColumn % 2 = 0)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) (sparseCoordinate oldColumn) y)
      (quadrantAt (sparseCoordinate oldColumn) y) ≠ none) :
    (∃ oldY, sparseCoordinate oldY = y ∧
      Signals.horizontalInterior?
        (componentAt grid oldColumn oldY) (quadrantAt oldColumn oldY) ≠ none) ∨
      y % 8 = 4 ∨ y % 8 = 5 := by
  let blockX := oldColumn / 2
  let blockY := y / 8
  let localY := y % 8
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hy : 8 * blockY + localY = y := by
    have := Nat.mod_add_div y 8
    dsimp [blockY, localY]
    omega
  have holdColumn : 2 * blockX = oldColumn := by
    have := Nat.mod_add_div oldColumn 2
    dsimp [blockX]
    omega
  have hfineColumn : 8 * blockX = sparseCoordinate oldColumn := by
    simp [sparseCoordinate, macroOrigin, localCoordinate, blockX, heven]
  let parent := grid blockX blockY
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid parent) 0 localY)
      (quadrantAt 0 localY) ≠ none := by
    have transported := interior
    rw [← hfineColumn, ← hy] at transported
    have hcomponent := componentAt_two_block grid 0 blockX blockY 0 localY
      (by decide) hlocalY
    simp only [Nat.zero_add] at hcomponent
    change componentAt (iterateRefine 2 grid)
        (8 * blockX + 0) (8 * blockY + localY) =
      componentAt (iterateRefine 2 (fun _ _ => grid blockX blockY))
        0 localY at hcomponent
    have hquadrant : quadrantAt (8 * blockX + 0) (8 * blockY + localY) =
        quadrantAt 0 localY := by
      simpa using quadrantAt_block blockX blockY 0 localY
    rw [show 8 * blockX = 8 * blockX + 0 by omega,
      hcomponent, hquadrant] at transported
    change Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (fun _ _ => parent)) 0 localY)
      (quadrantAt 0 localY) ≠ none
    simpa [parent] using transported
  rcases horizontal_classification parent ⟨localY, hlocalY⟩ with
    checked | created
  · rcases horizontalAncestorAt_sound checked localInterior with
      ⟨sourceY, hsourceY, sourceCoordinate, sourceInterior⟩
    left
    refine ⟨2 * blockY + sourceY, ?_, ?_⟩
    · rw [sparseCoordinate_two_block blockY sourceY hsourceY,
        sourceCoordinate, hy]
    · rw [← holdColumn]
      have hcomponent := componentAt_old_block grid 0 blockX blockY 0 sourceY
        (by decide) hsourceY
      simp only [iterateRefine, Nat.add_zero] at hcomponent
      have hquadrant : quadrantAt (2 * blockX) (2 * blockY + sourceY) =
          quadrantAt 0 sourceY := by
        simpa using quadrantAt_old_block blockX blockY 0 sourceY
          (by decide) hsourceY
      rw [hcomponent, hquadrant]
      simpa [holdColumn, parent] using sourceInterior
  · exact Or.inr (by simpa [localY] using created)

end SparseFreeLineEvenExtraCreatedPositions
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
