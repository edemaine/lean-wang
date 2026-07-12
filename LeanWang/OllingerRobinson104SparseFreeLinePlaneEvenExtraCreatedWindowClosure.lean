/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedWindowClosure
import LeanWang.OllingerRobinson104SparseFreeLinePlaneLocalStep

/-! Structural closure of recursive exceptional created-segment windows. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneEvenExtraCreatedWindowClosure

open RedCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphTranslation RefinementTranslation
  BorderGeometry ShadedFreeLineRecurrence Signals.FreeCellLocal
  SparseFreeLineEvenExtraCreatedWindowAudit
  SparseFreeLineEvenExtraCreatedWindowClosure SparseFreeLinePlaneBase

set_option maxRecDepth 20000

def oldGrid (depth : Nat) (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  refinedGrid .even (depth + 1) grid

def firstBlock (depth : Nat) : Nat := 4 ^ (depth + 1)

def blockCount (depth : Nat) : Nat := 2 * firstBlock depth

def centerBlock (depth : Nat) : Nat := 2 * firstBlock depth + 1

def verticalWindowAt (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) : Window :=
  (List.range 3).flatMap fun y =>
    (List.range 3).map fun x =>
      oldGrid depth grid (blockX - 1 + x) (centerBlock depth - 1 + y)

def horizontalWindowAt (depth : Nat) (grid : Nat → Nat → Index) (blockY : Nat) : Window :=
  (List.range 3).flatMap fun y =>
    (List.range 3).map fun x =>
      oldGrid depth grid (centerBlock depth - 1 + x) (blockY - 1 + y)

theorem oldGrid_succ (depth : Nat) (grid : Nat → Nat → Index) :
    oldGrid (depth + 1) grid = iterateRefine 2 (oldGrid depth grid) := by
  simpa [oldGrid, Nat.add_assoc] using
    SparseFreeLinePlaneLocalStep.refinedGrid_succ .even (depth + 1) grid

theorem firstBlock_zero : firstBlock 0 = 4 := by rfl

theorem firstBlock_succ (depth : Nat) :
    firstBlock (depth + 1) = 4 * firstBlock depth := by
  simp [firstBlock, pow_succ, Nat.mul_comm]

theorem blockCount_eq (depth : Nat) : blockCount depth = 2 * 4 ^ (depth + 1) := rfl

theorem centerBlock_zero : centerBlock 0 = 9 := by rfl

theorem centerOrigin_succ (depth : Nat) :
    centerBlock (depth + 1) - 1 = 4 * (centerBlock depth - 1) := by
  rw [centerBlock, centerBlock, firstBlock_succ]
  omega

theorem verticalWindowAt_zero_eq_constant
    (grid : Nat → Nat → Index) (delta : Nat) (hdelta : delta < 9) :
    verticalWindowAt 0 grid (4 + delta) =
      verticalWindowAt 0 (fun _ _ => grid 0 0) (4 + delta) := by
  unfold verticalWindowAt
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  have hlocal := iterateRefine_shift_eq_constant 4 grid 0 0
    (4 + delta - 1 + x) (centerBlock 0 - 1 + y)
    (by norm_num; omega) (by norm_num [centerBlock, firstBlock]; omega)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  simpa [oldGrid, refinedGrid, refinementDepth, Phase.extra] using hlocal

theorem horizontalWindowAt_zero_eq_constant
    (grid : Nat → Nat → Index) (delta : Nat) (hdelta : delta < 9) :
    horizontalWindowAt 0 grid (4 + delta) =
      horizontalWindowAt 0 (fun _ _ => grid 0 0) (4 + delta) := by
  unfold horizontalWindowAt
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  have hlocal := iterateRefine_shift_eq_constant 4 grid 0 0
    (centerBlock 0 - 1 + x) (4 + delta - 1 + y)
    (by norm_num [centerBlock, firstBlock]; omega) (by norm_num; omega)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  simpa [oldGrid, refinedGrid, refinementDepth, Phase.extra] using hlocal

theorem verticalWindowAt_eq (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) :
    verticalWindowAt depth grid blockX =
      [oldGrid depth grid (blockX - 1) (centerBlock depth - 1),
       oldGrid depth grid (blockX - 1 + 1) (centerBlock depth - 1),
       oldGrid depth grid (blockX - 1 + 2) (centerBlock depth - 1),
       oldGrid depth grid (blockX - 1) (centerBlock depth - 1 + 1),
       oldGrid depth grid (blockX - 1 + 1) (centerBlock depth - 1 + 1),
       oldGrid depth grid (blockX - 1 + 2) (centerBlock depth - 1 + 1),
       oldGrid depth grid (blockX - 1) (centerBlock depth - 1 + 2),
       oldGrid depth grid (blockX - 1 + 1) (centerBlock depth - 1 + 2),
       oldGrid depth grid (blockX - 1 + 2) (centerBlock depth - 1 + 2)] := by
  rfl

theorem horizontalWindowAt_eq (depth : Nat) (grid : Nat → Nat → Index) (blockY : Nat) :
    horizontalWindowAt depth grid blockY =
      [oldGrid depth grid (centerBlock depth - 1) (blockY - 1),
       oldGrid depth grid (centerBlock depth - 1 + 1) (blockY - 1),
       oldGrid depth grid (centerBlock depth - 1 + 2) (blockY - 1),
       oldGrid depth grid (centerBlock depth - 1) (blockY - 1 + 1),
       oldGrid depth grid (centerBlock depth - 1 + 1) (blockY - 1 + 1),
       oldGrid depth grid (centerBlock depth - 1 + 2) (blockY - 1 + 1),
       oldGrid depth grid (centerBlock depth - 1) (blockY - 1 + 2),
       oldGrid depth grid (centerBlock depth - 1 + 1) (blockY - 1 + 2),
       oldGrid depth grid (centerBlock depth - 1 + 2) (blockY - 1 + 2)] := by
  rfl

theorem windowGrid_verticalWindowAt
    (depth : Nat) (grid : Nat → Nat → Index) (blockX x y : Nat)
    (hx : x < 3) (hy : y < 3) :
    windowGrid (verticalWindowAt depth grid blockX) x y =
      oldGrid depth grid (blockX - 1 + x) (centerBlock depth - 1 + y) := by
  rw [verticalWindowAt_eq]
  interval_cases x <;> interval_cases y <;> simp [windowGrid]

theorem windowGrid_horizontalWindowAt
    (depth : Nat) (grid : Nat → Nat → Index) (blockY x y : Nat)
    (hx : x < 3) (hy : y < 3) :
    windowGrid (horizontalWindowAt depth grid blockY) x y =
      oldGrid depth grid (centerBlock depth - 1 + x) (blockY - 1 + y) := by
  rw [horizontalWindowAt_eq]
  interval_cases x <;> interval_cases y <;> simp [windowGrid]

theorem iterateRefine_two_congr_at
    {first second : Nat → Nat → Index} {x y : Nat}
    (hcell : first (x / 2 / 2) (y / 2 / 2) =
      second (x / 2 / 2) (y / 2 / 2)) :
    iterateRefine 2 first x y = iterateRefine 2 second x y := by
  simp only [iterateRefine, refineIndexGrid]
  rw [hcell]

set_option maxHeartbeats 1000000 in
-- Normalizing the translated two-refinement window requires extra elaboration.
/-- Every successor row window is a residue slice of a predecessor window. -/
theorem verticalWindowAt_succ
    (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) :
    verticalWindowAt (depth + 1) grid blockX =
      refineWindow
        (verticalWindowAt depth grid ((blockX - 1) / 4 + 1))
        ((blockX - 1) % 4) 0 := by
  rw [verticalWindowAt, refineWindow, oldGrid_succ, centerOrigin_succ]
  have hmodlt := Nat.mod_lt (blockX - 1) (by decide : 0 < 4)
  have horigin : blockX - 1 =
      4 * ((blockX - 1) / 4) + (blockX - 1) % 4 := by
    have := Nat.mod_add_div (blockX - 1) 4
    omega
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  rw [horigin]
  have hdiv :
      (4 * ((blockX - 1) / 4) + (blockX - 1) % 4) / 4 =
        (blockX - 1) / 4 := by omega
  have hmod :
      (4 * ((blockX - 1) / 4) + (blockX - 1) % 4) % 4 =
        (blockX - 1) % 4 := by omega
  rw [hdiv, hmod]
  have hshift := iterateRefine_shift 2 (oldGrid depth grid)
    ((blockX - 1) / 4) (centerBlock depth - 1)
    ((blockX - 1) % 4 + x) y
  norm_num at hshift
  rw [← Nat.add_assoc] at hshift
  rw [← hshift]
  simp only [Nat.zero_add]
  apply iterateRefine_two_congr_at
  rw [windowGrid_verticalWindowAt]
  · simp [shiftGrid]
  · omega
  · omega

set_option maxHeartbeats 1000000 in
-- Normalizing the translated two-refinement window requires extra elaboration.
/-- Every successor column window is a residue slice of a predecessor window. -/
theorem horizontalWindowAt_succ
    (depth : Nat) (grid : Nat → Nat → Index) (blockY : Nat) :
    horizontalWindowAt (depth + 1) grid blockY =
      refineWindow
        (horizontalWindowAt depth grid ((blockY - 1) / 4 + 1))
        0 ((blockY - 1) % 4) := by
  rw [horizontalWindowAt, refineWindow, oldGrid_succ, centerOrigin_succ]
  have hmodlt := Nat.mod_lt (blockY - 1) (by decide : 0 < 4)
  have horigin : blockY - 1 =
      4 * ((blockY - 1) / 4) + (blockY - 1) % 4 := by
    have := Nat.mod_add_div (blockY - 1) 4
    omega
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  rw [horigin]
  have hdiv :
      (4 * ((blockY - 1) / 4) + (blockY - 1) % 4) / 4 =
        (blockY - 1) / 4 := by omega
  have hmod :
      (4 * ((blockY - 1) / 4) + (blockY - 1) % 4) % 4 =
        (blockY - 1) % 4 := by omega
  rw [hdiv, hmod]
  have hshift := iterateRefine_shift 2 (oldGrid depth grid)
    (centerBlock depth - 1) ((blockY - 1) / 4)
    x ((blockY - 1) % 4 + y)
  norm_num at hshift
  rw [← Nat.add_assoc] at hshift
  rw [← hshift]
  simp only [Nat.zero_add]
  apply iterateRefine_two_congr_at
  rw [windowGrid_horizontalWindowAt]
  · simp [shiftGrid]
  · omega
  · omega

set_option linter.style.nativeDecide false in
theorem canonicalIndex_zero : BorderSubstitution.canonicalIndex 0 = 0 := by
  native_decide

theorem windowGrid_canonicalWindow (window : Window) (x y : Nat) :
    windowGrid (canonicalWindow window) x y =
      BorderSubstitution.canonicalIndex (windowGrid window x y) := by
  simp only [windowGrid, canonicalWindow, List.getElem?_map]
  cases hentry : window[y * 3 + x]? <;> simp [canonicalIndex_zero]

theorem canonicalWindow_refineWindow
    (window : Window) (residueX residueY : Nat) :
    canonicalWindow (refineWindow window residueX residueY) =
      canonicalWindow
        (refineWindow (canonicalWindow window) residueX residueY) := by
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext gridX gridY
    exact windowGrid_canonicalWindow window gridX gridY
  simp only [canonicalWindow, refineWindow, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro y _
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  change BorderSubstitution.canonicalIndex
      (iterateRefine 2 (windowGrid window) (residueX + x) (residueY + y)) =
    BorderSubstitution.canonicalIndex
      (iterateRefine 2 (windowGrid (canonicalWindow window))
        (residueX + x) (residueY + y))
  rw [hgrid]
  have hstate := BorderGeometry.indexState_iterateRefine_canonicalizeGrid
    2 (windowGrid window) (residueX + x) (residueY + y)
  simpa [Function.comp_def, BorderSubstitution.canonicalIndex] using
    congrArg BorderSubstitution.representative hstate.symm

theorem verticalBase_mem (grid : Nat → Nat → Index) (delta : Nat) (hdelta : delta < 9) :
    canonicalWindow (verticalWindowAt 0 grid (4 + delta)) ∈
      verticalBaseWindows := by
  rw [verticalWindowAt_zero_eq_constant grid delta hdelta,
    verticalBaseWindows, List.mem_eraseDups,
    List.mem_flatMap]
  refine ⟨grid 0 0, by simp, ?_⟩
  rw [List.mem_map]
  exact ⟨delta, by simpa using hdelta, rfl⟩

theorem horizontalBase_mem (grid : Nat → Nat → Index) (delta : Nat) (hdelta : delta < 9) :
    canonicalWindow (horizontalWindowAt 0 grid (4 + delta)) ∈
      horizontalBaseWindows := by
  rw [horizontalWindowAt_zero_eq_constant grid delta hdelta,
    horizontalBaseWindows, List.mem_eraseDups,
    List.mem_flatMap]
  refine ⟨grid 0 0, by simp, ?_⟩
  rw [List.mem_map]
  exact ⟨delta, by simpa using hdelta, rfl⟩

theorem verticalBase_mem_closed {window : Window}
    (hwindow : window ∈ verticalBaseWindows) : window ∈ verticalClosed := by
  rw [verticalClosed, closeVertical, List.mem_eraseDups, List.mem_append]
  exact Or.inl hwindow

theorem horizontalBase_mem_closed {window : Window}
    (hwindow : window ∈ horizontalBaseWindows) : window ∈ horizontalClosed := by
  rw [horizontalClosed, closeHorizontal, List.mem_eraseDups, List.mem_append]
  exact Or.inl hwindow

theorem verticalRefine_mem_closed {window : Window}
    (hwindow : window ∈ verticalClosed) {residueX : Nat}
    (hresidue : residueX < 4) :
    canonicalWindow (refineWindow window residueX 0) ∈ verticalClosed := by
  have hmem : canonicalWindow (refineWindow window residueX 0) ∈
      closeVertical verticalClosed := by
    rw [closeVertical, List.mem_eraseDups, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨window, hwindow, ?_⟩
    rw [List.mem_map]
    exact ⟨residueX, by simpa using hresidue, rfl⟩
  rwa [vertical_closed] at hmem

theorem horizontalRefine_mem_closed {window : Window}
    (hwindow : window ∈ horizontalClosed) {residueY : Nat}
    (hresidue : residueY < 4) :
    canonicalWindow (refineWindow window 0 residueY) ∈ horizontalClosed := by
  have hmem : canonicalWindow (refineWindow window 0 residueY) ∈
      closeHorizontal horizontalClosed := by
    rw [closeHorizontal, List.mem_eraseDups, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨window, hwindow, ?_⟩
    rw [List.mem_map]
    exact ⟨residueY, by simpa using hresidue, rfl⟩
  rwa [horizontal_closed] at hmem

/-- Every actual recursive row window belongs to the vertical finite quotient. -/
theorem canonical_verticalWindowAt_mem
    (depth : Nat) (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta ≤ blockCount depth) :
    canonicalWindow
      (verticalWindowAt depth grid (firstBlock depth + delta)) ∈
      verticalClosed := by
  induction depth generalizing delta with
  | zero =>
      rw [firstBlock_zero]
      apply verticalBase_mem_closed
      exact verticalBase_mem grid delta
        (by simp [blockCount, firstBlock] at hdelta ⊢; omega)
  | succ depth ih =>
      let oldDelta := (delta + 3) / 4
      have holdDelta : oldDelta ≤ blockCount depth := by
        simp only [blockCount, firstBlock_succ] at hdelta ⊢
        dsimp [oldDelta]
        have hpositive : 0 < firstBlock depth := pow_pos (by decide) _
        omega
      have hblock :
          (firstBlock (depth + 1) + delta - 1) / 4 + 1 =
            firstBlock depth + oldDelta := by
        rw [firstBlock_succ]
        dsimp [oldDelta]
        have hpositive : 0 < firstBlock depth := by
          exact pow_pos (by decide) _
        omega
      rw [verticalWindowAt_succ, hblock, canonicalWindow_refineWindow]
      apply verticalRefine_mem_closed (ih oldDelta holdDelta)
      exact Nat.mod_lt _ (by decide)

/-- Every actual recursive column window belongs to the horizontal quotient. -/
theorem canonical_horizontalWindowAt_mem
    (depth : Nat) (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta ≤ blockCount depth) :
    canonicalWindow
      (horizontalWindowAt depth grid (firstBlock depth + delta)) ∈
      horizontalClosed := by
  induction depth generalizing delta with
  | zero =>
      rw [firstBlock_zero]
      apply horizontalBase_mem_closed
      exact horizontalBase_mem grid delta
        (by simp [blockCount, firstBlock] at hdelta ⊢; omega)
  | succ depth ih =>
      let oldDelta := (delta + 3) / 4
      have holdDelta : oldDelta ≤ blockCount depth := by
        simp only [blockCount, firstBlock_succ] at hdelta ⊢
        dsimp [oldDelta]
        have hpositive : 0 < firstBlock depth := pow_pos (by decide) _
        omega
      have hblock :
          (firstBlock (depth + 1) + delta - 1) / 4 + 1 =
            firstBlock depth + oldDelta := by
        rw [firstBlock_succ]
        dsimp [oldDelta]
        have hpositive : 0 < firstBlock depth := by
          exact pow_pos (by decide) _
        omega
      rw [horizontalWindowAt_succ, hblock, canonicalWindow_refineWindow]
      apply horizontalRefine_mem_closed (ih oldDelta holdDelta)
      exact Nat.mod_lt _ (by decide)

set_option linter.style.nativeDecide false in
theorem verticalLocal_canonical (grid : Index) {x : Nat}
    (hx : x = 4 ∨ x = 5) :
    (Signals.verticalInterior?
      (componentAt (fineGrid (BorderSubstitution.canonicalIndex grid)) x 0)
      (quadrantAt x 0)).isSome =
      (Signals.verticalInterior?
        (componentAt (fineGrid grid) x 0) (quadrantAt x 0)).isSome ∧
    SparseFreeLineLocalStates.verticalAncestorAt 0 0
      (BorderSubstitution.canonicalIndex grid) x =
      SparseFreeLineLocalStates.verticalAncestorAt 0 0 grid x := by
  rcases hx with rfl | rfl <;> revert grid <;> native_decide

set_option linter.style.nativeDecide false in
theorem horizontalLocal_canonical (grid : Index) {y : Nat}
    (hy : y = 4 ∨ y = 5) :
    (Signals.horizontalInterior?
      (componentAt (fineGrid (BorderSubstitution.canonicalIndex grid)) 0 y)
      (quadrantAt 0 y)).isSome =
      (Signals.horizontalInterior?
        (componentAt (fineGrid grid) 0 y) (quadrantAt 0 y)).isSome ∧
    SparseFreeLineLocalStates.horizontalAncestorAt 0 0
      (BorderSubstitution.canonicalIndex grid) y =
      SparseFreeLineLocalStates.horizontalAncestorAt 0 0 grid y := by
  rcases hy with rfl | rfl <;> revert grid <;> native_decide

theorem vertical_case_mem {window : Window} (hwindow :
    canonicalWindow window ∈ verticalClosed) {x : Nat}
    (hx : x = 4 ∨ x = 5)
    (required : (Signals.verticalInterior?
      (componentAt (fineGrid (windowGrid window 1 1)) x 0)
      (quadrantAt x 0)).isSome = true)
    (created : SparseFreeLineLocalStates.verticalAncestorAt 0 0
      (windowGrid window 1 1) x = false) :
    (canonicalWindow window, x) ∈
      SparseFreeLineEvenExtraCreatedWindowClosure.verticalCases := by
  rw [SparseFreeLineEvenExtraCreatedWindowClosure.verticalCases,
    List.mem_eraseDups, List.mem_flatMap]
  refine ⟨canonicalWindow window, hwindow, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨x, by simp [hx], ?_⟩
  have hcenter := windowGrid_canonicalWindow window 1 1
  have hlocal := verticalLocal_canonical (windowGrid window 1 1) hx
  rw [hcenter, hlocal.1, hlocal.2]
  simp [required, created]

theorem horizontal_case_mem {window : Window} (hwindow :
    canonicalWindow window ∈ horizontalClosed) {y : Nat}
    (hy : y = 4 ∨ y = 5)
    (required : (Signals.horizontalInterior?
      (componentAt (fineGrid (windowGrid window 1 1)) 0 y)
      (quadrantAt 0 y)).isSome = true)
    (created : SparseFreeLineLocalStates.horizontalAncestorAt 0 0
      (windowGrid window 1 1) y = false) :
    (canonicalWindow window, y) ∈
      SparseFreeLineEvenExtraCreatedWindowClosure.horizontalCases := by
  rw [SparseFreeLineEvenExtraCreatedWindowClosure.horizontalCases,
    List.mem_eraseDups, List.mem_flatMap]
  refine ⟨canonicalWindow window, hwindow, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨y, by simp [hy], ?_⟩
  have hcenter := windowGrid_canonicalWindow window 1 1
  have hlocal := horizontalLocal_canonical (windowGrid window 1 1) hy
  rw [hcenter, hlocal.1, hlocal.2]
  simp [required, created]

theorem vertical_route_of_mem {entry : Window × Nat}
    (hentry : entry ∈
      SparseFreeLineEvenExtraCreatedWindowClosure.verticalCases) :
    Route entry.1 ⟨8 + entry.2, 8, .south⟩ ∨
      Route entry.1 ⟨8 + entry.2, 8, .north⟩ := by
  have checked := vertical_routes_complete
  simp only [List.all_eq_true] at checked
  exact verticalCaseCheck_sound (checked entry hentry)

theorem horizontal_route_of_mem {entry : Window × Nat}
    (hentry : entry ∈
      SparseFreeLineEvenExtraCreatedWindowClosure.horizontalCases) :
    Route entry.1 ⟨8, 8 + entry.2, .west⟩ ∨
      Route entry.1 ⟨8, 8 + entry.2, .east⟩ := by
  have checked := horizontal_routes_complete
  simp only [List.all_eq_true] at checked
  exact horizontalCaseCheck_sound (checked entry hentry)

/-- A canonical quotient route is a route in the original 104-symbol window. -/
theorem route_of_canonicalWindow {window : Window} {target : Port}
    (route : Route (canonicalWindow window) target) : Route window target := by
  have hgrid : windowGrid (canonicalWindow window) =
      BorderSubstitution.canonicalizeGrid (windowGrid window) := by
    funext x y
    exact windowGrid_canonicalWindow window x y
  have same : SameComponents
      (iterateRefine 2 (windowGrid (canonicalWindow window)))
      (iterateRefine 2 (windowGrid window)) := by
    rw [hgrid]
    exact BorderGeometry.sameComponents_iterateRefine_canonicalizeGrid
      2 (windowGrid window)
  rcases route with ⟨witness⟩
  refine ⟨{
    start := witness.start
    start_mem := witness.start_mem
    path := BoundedPath.congr_of_component_eq
      (fun x y _ _ => same x y) witness.path
    targetLive := ?_
  }⟩
  have targetLive := witness.targetLive
  rwa [portPresent_congr same target] at targetLive

/-- Every created segment in an actual recursive row window has an odd route. -/
theorem vertical_actual_route {window : Window}
    (hwindow : canonicalWindow window ∈ verticalClosed) {x : Nat}
    (hx : x = 4 ∨ x = 5)
    (required : (Signals.verticalInterior?
      (componentAt (fineGrid (windowGrid window 1 1)) x 0)
      (quadrantAt x 0)).isSome = true)
    (created : SparseFreeLineLocalStates.verticalAncestorAt 0 0
      (windowGrid window 1 1) x = false) :
    Route window ⟨8 + x, 8, .south⟩ ∨ Route window ⟨8 + x, 8, .north⟩ := by
  have hentry := vertical_case_mem hwindow hx required created
  rcases vertical_route_of_mem hentry with route | route
  · exact Or.inl (route_of_canonicalWindow route)
  · exact Or.inr (route_of_canonicalWindow route)

/-- Every created segment in an actual recursive column window has an odd route. -/
theorem horizontal_actual_route {window : Window}
    (hwindow : canonicalWindow window ∈ horizontalClosed) {y : Nat}
    (hy : y = 4 ∨ y = 5)
    (required : (Signals.horizontalInterior?
      (componentAt (fineGrid (windowGrid window 1 1)) 0 y)
      (quadrantAt 0 y)).isSome = true)
    (created : SparseFreeLineLocalStates.horizontalAncestorAt 0 0
      (windowGrid window 1 1) y = false) :
    Route window ⟨8, 8 + y, .west⟩ ∨ Route window ⟨8, 8 + y, .east⟩ := by
  have hentry := horizontal_case_mem hwindow hy required created
  rcases horizontal_route_of_mem hentry with route | route
  · exact Or.inl (route_of_canonicalWindow route)
  · exact Or.inr (route_of_canonicalWindow route)

theorem componentAt_iterateRefine_two_congr_at
    {first second : Nat → Nat → Index} {x y : Nat}
    (hcell : first (x / 2 / 2 / 2) (y / 2 / 2 / 2) =
      second (x / 2 / 2 / 2) (y / 2 / 2 / 2)) :
    componentAt (iterateRefine 2 first) x y =
      componentAt (iterateRefine 2 second) x y := by
  unfold componentAt
  simp only [iterateRefine, refineIndexGrid]
  rw [hcell]

theorem sameComponents_verticalWindowAt_shift
    (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) :
    ∀ x y, x < 24 → y < 24 →
      componentAt
          (iterateRefine 2 (windowGrid (verticalWindowAt depth grid blockX)))
          x y =
        componentAt
          (iterateRefine 2 (shiftGrid (oldGrid depth grid)
            (blockX - 1) (centerBlock depth - 1))) x y := by
  intro x y hx hy
  apply componentAt_iterateRefine_two_congr_at
  rw [windowGrid_verticalWindowAt]
  · simp [shiftGrid]
  · omega
  · omega

theorem sameComponents_horizontalWindowAt_shift
    (depth : Nat) (grid : Nat → Nat → Index) (blockY : Nat) :
    ∀ x y, x < 24 → y < 24 →
      componentAt
          (iterateRefine 2 (windowGrid (horizontalWindowAt depth grid blockY)))
          x y =
        componentAt
          (iterateRefine 2 (shiftGrid (oldGrid depth grid)
            (centerBlock depth - 1) (blockY - 1))) x y := by
  intro x y hx hy
  apply componentAt_iterateRefine_two_congr_at
  rw [windowGrid_horizontalWindowAt]
  · simp [shiftGrid]
  · omega
  · omega

/-- Transport a vertical-window route to its shifted recursive neighborhood. -/
theorem shiftedRoute_of_verticalWindowAt
    {depth : Nat} {grid : Nat → Nat → Index} {blockX : Nat} {target : Port}
    (route : Route (verticalWindowAt depth grid blockX) target) :
    SparseFreeLineLocalProjection.ShiftedBoundedRoute
      (oldGrid depth grid) (blockX - 1) (centerBlock depth - 1)
      24 24 (windowStarts (verticalWindowAt depth grid blockX)) target := by
  have same := sameComponents_verticalWindowAt_shift depth grid blockX
  rcases route with ⟨witness⟩
  have htarget := witness.path.second_inBounds
  refine ⟨witness.start, witness.start_mem,
    BoundedPath.congr_of_component_eq same witness.path, ?_⟩
  have targetLive := witness.targetLive
  simp only [portPresent] at targetLive ⊢
  rw [← same target.x target.y htarget.1 htarget.2]
  exact targetLive

/-- Transport a horizontal-window route to its shifted recursive neighborhood. -/
theorem shiftedRoute_of_horizontalWindowAt
    {depth : Nat} {grid : Nat → Nat → Index} {blockY : Nat} {target : Port}
    (route : Route (horizontalWindowAt depth grid blockY) target) :
    SparseFreeLineLocalProjection.ShiftedBoundedRoute
      (oldGrid depth grid) (centerBlock depth - 1) (blockY - 1)
      24 24 (windowStarts (horizontalWindowAt depth grid blockY)) target := by
  have same := sameComponents_horizontalWindowAt_shift depth grid blockY
  rcases route with ⟨witness⟩
  have htarget := witness.path.second_inBounds
  refine ⟨witness.start, witness.start_mem,
    BoundedPath.congr_of_component_eq same witness.path, ?_⟩
  have targetLive := witness.targetLive
  simp only [portPresent] at targetLive ⊢
  rw [← same target.x target.y htarget.1 htarget.2]
  exact targetLive

end SparseFreeLinePlaneEvenExtraCreatedWindowClosure
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
