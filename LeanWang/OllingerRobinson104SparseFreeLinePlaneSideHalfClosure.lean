/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineSideHalfClosure
import LeanWang.OllingerRobinson104SparseFreeLinePlaneLocalStep

/-!
# Structural closure of side-half windows

This module connects the finite 80-state window quotient to the actual
odd-phase pivot-extra row at every recursive depth.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneSideHalfClosure

open RedCycles RedShadeCycles ShadedFreeLineRecurrence SparseFreeLineOffsets
  SparseFreeLineSideHalfAudit RefinementTranslation
  SparseFreeLinePlaneBase

set_option maxRecDepth 20000

def oldGrid (depth : Nat) (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  refinedGrid .odd (depth + 1) grid

def oldRow (depth : Nat) : Nat :=
  lineCoordinate .odd (depth + 1) (extraChild (pivot depth))

def lowerBlockY (depth : Nat) : Nat := oldRow depth / 2 - 1

def firstBlock (depth : Nat) : Nat :=
  quarterWest (4 * west .odd (depth + 1)) / 8

def blockCount (depth : Nat) : Nat :=
  quarterEast (4 * east .odd (depth + 1)) / 8 - firstBlock depth + 1

def windowAt (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) : Window :=
  let originX := blockX - 1
  (List.range 2).flatMap fun y =>
    (List.range 3).map fun x =>
      oldGrid depth grid (originX + x) (lowerBlockY depth + y)

def windowsAt (depth : Nat) (grid : Nat → Nat → Index) : List Window :=
  windowsIn (oldGrid depth grid)
    (west .odd (depth + 1)) (east .odd (depth + 1)) (oldRow depth)

theorem oldRow_eq (depth : Nat) : oldRow depth = 32 * 4 ^ depth + 3 := by
  exact odd_extra_coordinate depth

theorem lowerBlockY_eq (depth : Nat) : lowerBlockY depth = 16 * 4 ^ depth := by
  rw [lowerBlockY, oldRow_eq]
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) depth
  omega

theorem firstBlock_eq (depth : Nat) : firstBlock depth = 8 * 4 ^ depth := by
  rw [firstBlock]
  have heq : quarterWest (4 * west .odd (depth + 1)) =
      8 * (8 * 4 ^ depth) + 1 := by
    simp [west, scale, Phase.factor, quarterWest, pow_succ]
    calc
      2 * (4 * (2 * (4 ^ depth * 4))) = (2 * 4 * 2 * 4) * 4 ^ depth := by
        ac_rfl
      _ = 8 * (8 * 4 ^ depth) := by norm_num [← mul_assoc]
  rw [heq]
  let n := 8 * 4 ^ depth
  have hdiv : (8 * n + 1) / 8 = n := by omega
  exact hdiv

theorem blockCount_eq (depth : Nat) : blockCount depth = 16 * 4 ^ depth + 1 := by
  rw [blockCount, firstBlock_eq]
  simp [east, scale, Phase.factor, quarterEast, pow_succ]
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) depth
  omega

theorem recurrenceWindows_eq :
    recurrenceWindows =
      ((List.finRange 104).flatMap fun parent =>
        windowsAt 0 (fun _ _ => parent)).eraseDups := by
  rfl

theorem windowAt_zero_eq_constant
    (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta < blockCount 0) :
    windowAt 0 grid (firstBlock 0 + delta) =
      windowAt 0 (fun _ _ => grid 0 0) (firstBlock 0 + delta) := by
  unfold windowAt
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  have hlocal := iterateRefine_shift_eq_constant 5 grid 0 0
    (firstBlock 0 + delta - 1 + x) (lowerBlockY 0 + y)
    (by
      rw [blockCount_eq] at hdelta
      rw [firstBlock_eq]
      omega)
    (by rw [lowerBlockY_eq]; omega)
  rw [shiftGrid_zero] at hlocal
  simpa [oldGrid, refinedGrid, refinementDepth, Phase.extra] using hlocal

theorem mem_recurrenceWindows_of_mem_windowsAt_zero
    (grid : Nat → Nat → Index) {window : Window} (hwindow : window ∈ windowsAt 0 grid) :
    window ∈ recurrenceWindows := by
  change window ∈ (List.range (blockCount 0)).map
    (fun delta => windowAt 0 grid (firstBlock 0 + delta)) at hwindow
  rcases List.mem_map.1 hwindow with ⟨delta, hdelta, rfl⟩
  have hdelta' : delta < blockCount 0 := by simpa using hdelta
  rw [windowAt_zero_eq_constant grid delta hdelta']
  rw [recurrenceWindows_eq, List.mem_eraseDups, List.mem_flatMap]
  refine ⟨grid 0 0, by simp, ?_⟩
  change windowAt 0 (fun _ _ => grid 0 0) (firstBlock 0 + delta) ∈
    (List.range (blockCount 0)).map
      (fun offset => windowAt 0 (fun _ _ => grid 0 0)
        (firstBlock 0 + offset))
  exact List.mem_map_of_mem (by simpa using hdelta')

theorem oldGrid_succ (depth : Nat) (grid : Nat → Nat → Index) :
    oldGrid (depth + 1) grid = iterateRefine 2 (oldGrid depth grid) := by
  simpa [oldGrid, Nat.add_assoc] using
    SparseFreeLinePlaneLocalStep.refinedGrid_succ .odd (depth + 1) grid

theorem lowerBlockY_succ (depth : Nat) :
    lowerBlockY (depth + 1) = 4 * lowerBlockY depth := by
  rw [lowerBlockY_eq, lowerBlockY_eq, pow_succ]
  omega

theorem firstBlock_succ (depth : Nat) :
    firstBlock (depth + 1) = 4 * firstBlock depth := by
  rw [firstBlock_eq, firstBlock_eq, pow_succ]
  omega

theorem windowAt_eq (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) :
    windowAt depth grid blockX =
      [oldGrid depth grid (blockX - 1) (lowerBlockY depth),
       oldGrid depth grid (blockX - 1 + 1) (lowerBlockY depth),
       oldGrid depth grid (blockX - 1 + 2) (lowerBlockY depth),
       oldGrid depth grid (blockX - 1) (lowerBlockY depth + 1),
       oldGrid depth grid (blockX - 1 + 1) (lowerBlockY depth + 1),
       oldGrid depth grid (blockX - 1 + 2) (lowerBlockY depth + 1)] := by
  rfl

theorem refineWindow_eq (window : Window) (residueX : Nat) :
    refineWindow window residueX =
      [iterateRefine 2 (windowGrid window) residueX 0,
       iterateRefine 2 (windowGrid window) (residueX + 1) 0,
       iterateRefine 2 (windowGrid window) (residueX + 2) 0,
       iterateRefine 2 (windowGrid window) residueX 1,
       iterateRefine 2 (windowGrid window) (residueX + 1) 1,
       iterateRefine 2 (windowGrid window) (residueX + 2) 1] := by
  rfl

theorem iterateRefine_two_congr_at
    {first second : Nat → Nat → Index} {x y : Nat}
    (hcell : first (x / 2 / 2) (y / 2 / 2) =
      second (x / 2 / 2) (y / 2 / 2)) :
    iterateRefine 2 first x y = iterateRefine 2 second x y := by
  simp only [iterateRefine, refineIndexGrid]
  rw [hcell]

theorem windowGrid_windowAt (depth : Nat) (grid : Nat → Nat → Index) (blockX x y : Nat)
    (hx : x < 3) (hy : y < 2) :
    windowGrid (windowAt depth grid blockX) x y =
      oldGrid depth grid (blockX - 1 + x) (lowerBlockY depth + y) := by
  interval_cases x <;> interval_cases y <;>
    simp [windowGrid, windowAt_eq]

set_option linter.style.nativeDecide false in
theorem canonicalIndex_zero : BorderSubstitution.canonicalIndex 0 = 0 := by
  native_decide

theorem windowGrid_canonicalWindow (window : Window) (x y : Nat) :
    windowGrid (canonicalWindow window) x y =
      BorderSubstitution.canonicalIndex (windowGrid window x y) := by
  simp only [windowGrid, canonicalWindow, List.getElem?_map]
  cases hentry : window[y * 3 + x]? <;>
    simp [canonicalIndex_zero]

theorem canonicalWindow_refineWindow (window : Window) (residueX : Nat) :
    canonicalWindow (refineWindow window residueX) =
      canonicalWindow (refineWindow (canonicalWindow window) residueX) := by
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
      (iterateRefine 2 (windowGrid window) (residueX + x) y) =
    BorderSubstitution.canonicalIndex
      (iterateRefine 2 (windowGrid (canonicalWindow window))
        (residueX + x) y)
  rw [hgrid]
  have hstate := BorderGeometry.indexState_iterateRefine_canonicalizeGrid
    2 (windowGrid window) (residueX + x) y
  simpa [Function.comp_def, BorderSubstitution.canonicalIndex] using
    congrArg BorderSubstitution.representative hstate.symm

theorem windowAt_mem_windowsAt (depth : Nat) (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta < blockCount depth) :
    windowAt depth grid (firstBlock depth + delta) ∈ windowsAt depth grid := by
  change windowAt depth grid (firstBlock depth + delta) ∈
    (List.range (blockCount depth)).map
      (fun offset => windowAt depth grid (firstBlock depth + offset))
  exact List.mem_map_of_mem (by simpa using hdelta)

/-- Every successor window is a residue slice of a refined predecessor window. -/
theorem windowAt_succ (depth : Nat) (grid : Nat → Nat → Index) (blockX : Nat) :
    windowAt (depth + 1) grid blockX =
      refineWindow
        (windowAt depth grid ((blockX - 1) / 4 + 1))
        ((blockX - 1) % 4) := by
  rw [windowAt, refineWindow, oldGrid_succ, lowerBlockY_succ]
  have hmodlt := Nat.mod_lt (blockX - 1) (by decide : 0 < 4)
  have horigin : blockX - 1 = 4 * ((blockX - 1) / 4) +
      (blockX - 1) % 4 := by
    have := Nat.mod_add_div (blockX - 1) 4
    omega
  apply List.flatMap_congr
  intro y hy
  apply List.map_congr_left
  intro x hx
  simp only [List.mem_range] at hx hy
  rw [horigin]
  have hdiv : (4 * ((blockX - 1) / 4) + (blockX - 1) % 4) / 4 =
      (blockX - 1) / 4 := by omega
  have hmod : (4 * ((blockX - 1) / 4) + (blockX - 1) % 4) % 4 =
      (blockX - 1) % 4 := by omega
  rw [hdiv, hmod]
  have hshift := iterateRefine_shift 2 (oldGrid depth grid)
    ((blockX - 1) / 4) (lowerBlockY depth)
    ((blockX - 1) % 4 + x) y
  norm_num at hshift
  rw [← Nat.add_assoc] at hshift
  rw [← hshift]
  apply iterateRefine_two_congr_at
  rw [windowGrid_windowAt]
  · simp [shiftGrid]
  · omega
  · omega

/-- Every actual side-half window belongs to the finite canonical quotient. -/
theorem canonicalWindow_windowAt_mem_closedWindows
    (depth : Nat) (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta < blockCount depth) :
    canonicalWindow (windowAt depth grid (firstBlock depth + delta)) ∈
      closedWindows := by
  induction depth generalizing delta with
  | zero =>
      apply canonicalWindow_mem_closedWindows
      apply mem_recurrenceWindows_of_mem_windowsAt_zero
      exact windowAt_mem_windowsAt 0 grid delta hdelta
  | succ depth ih =>
      let oldDelta := (delta + 3) / 4
      have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
      have holdDelta : oldDelta < blockCount depth := by
        rw [blockCount_eq] at hdelta ⊢
        simp only [oldDelta, pow_succ] at hdelta ⊢
        omega
      have hblock :
          (firstBlock (depth + 1) + delta - 1) / 4 + 1 =
            firstBlock depth + oldDelta := by
        rw [firstBlock_succ]
        simp only [oldDelta]
        rw [firstBlock_eq]
        omega
      rw [windowAt_succ, hblock, canonicalWindow_refineWindow]
      apply refineWindow_mem_closedWindows (ih oldDelta holdDelta)
      exact Nat.mod_lt _ (by decide)

theorem boundaryWindow_eq (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta < blockCount 0) :
    boundaryWindow (grid 0 0) delta =
      windowAt 0 grid (firstBlock 0 + delta) := by
  rw [windowAt_zero_eq_constant grid delta hdelta]
  rfl

theorem canonical_boundary_mem (grid : Nat → Nat → Index) (delta : Nat)
    (hdelta : delta < blockCount 0) :
    canonicalWindow (windowAt 0 grid (firstBlock 0 + delta)) ∈
      boundaryBase delta := by
  rw [← boundaryWindow_eq grid delta hdelta, boundaryBase,
    List.mem_eraseDups, List.mem_map]
  exact ⟨grid 0 0, by simp, rfl⟩

theorem mem_closeWindowsAt_self {residues : List Nat} {windows : List Window}
    {window : Window} (hwindow : window ∈ windows) :
    window ∈ closeWindowsAt residues windows := by
  rw [closeWindowsAt, List.mem_eraseDups, List.mem_append]
  exact Or.inl hwindow

theorem mem_closeWindowsAt_refine {residues : List Nat} {windows : List Window}
    {window : Window} (hwindow : window ∈ windows) {residue : Nat}
    (hresidue : residue ∈ residues) :
    canonicalWindow (refineWindow window residue) ∈
      closeWindowsAt residues windows := by
  rw [closeWindowsAt, List.mem_eraseDups, List.mem_append]
  right
  rw [List.mem_flatMap]
  refine ⟨window, hwindow, ?_⟩
  rw [List.mem_map]
  exact ⟨residue, hresidue, rfl⟩

theorem canonical_refine_mem_of_closedAt
    {residues : List Nat} {windows : List Window} {window : Window} {residue : Nat}
    (hclosed : closeWindowsAt residues windows = windows)
    (hwindow : window ∈ windows) (hresidue : residue ∈ residues) :
    canonicalWindow (refineWindow window residue) ∈ windows := by
  rw [← hclosed]
  exact mem_closeWindowsAt_refine hwindow hresidue

theorem canonical_leftmost_mem (depth : Nat) (grid : Nat → Nat → Index) :
    canonicalWindow (windowAt depth grid (firstBlock depth)) ∈
      leftmostWindows := by
  induction depth with
  | zero =>
      apply mem_closeWindowsAt_self
      exact canonical_boundary_mem grid 0 (by rw [blockCount_eq]; omega)
  | succ depth ih =>
      have hblock :
          (firstBlock (depth + 1) - 1) / 4 + 1 = firstBlock depth := by
        rw [firstBlock_succ, firstBlock_eq]
        have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
        omega
      have hresidue : (firstBlock (depth + 1) - 1) % 4 = 3 := by
        rw [firstBlock_succ, firstBlock_eq]
        have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
        omega
      rw [windowAt_succ, hblock, hresidue, canonicalWindow_refineWindow]
      exact canonical_refine_mem_of_closedAt leftmostWindows_closed ih (by simp)

theorem canonical_nextLeft_mem (depth : Nat) (grid : Nat → Nat → Index) :
    canonicalWindow (windowAt depth grid (firstBlock depth + 1)) ∈
      nextLeftWindows := by
  induction depth with
  | zero =>
      apply mem_closeWindowsAt_self
      exact canonical_boundary_mem grid 1 (by rw [blockCount_eq]; omega)
  | succ depth ih =>
      have hblock :
          (firstBlock (depth + 1) + 1 - 1) / 4 + 1 =
            firstBlock depth + 1 := by
        rw [firstBlock_succ]
        omega
      have hresidue : (firstBlock (depth + 1) + 1 - 1) % 4 = 0 := by
        rw [firstBlock_succ]
        omega
      rw [windowAt_succ, hblock, hresidue, canonicalWindow_refineWindow]
      exact canonical_refine_mem_of_closedAt nextLeftWindows_closed ih (by simp)

def lastBlock (depth : Nat) : Nat :=
  firstBlock depth + blockCount depth - 1

def lastRelevantBlock (depth : Nat) : Nat :=
  firstBlock depth + blockCount depth - 2

theorem lastBlock_eq (depth : Nat) : lastBlock depth = 24 * 4 ^ depth := by
  rw [lastBlock, firstBlock_eq, blockCount_eq]
  omega

theorem lastRelevantBlock_eq (depth : Nat) :
    lastRelevantBlock depth = 24 * 4 ^ depth - 1 := by
  rw [lastRelevantBlock, firstBlock_eq, blockCount_eq]
  omega

theorem canonical_rightEdge_mem (depth : Nat) (grid : Nat → Nat → Index) :
    canonicalWindow (windowAt depth grid (lastBlock depth)) ∈
      rightEdgeWindows := by
  induction depth with
  | zero =>
      apply mem_closeWindowsAt_self
      have hdelta : quarterEast (4 * east .odd 1) / 8 -
          quarterWest (4 * west .odd 1) / 8 = blockCount 0 - 1 := by
        norm_num [blockCount, firstBlock, west, east, scale, Phase.factor,
          quarterWest, quarterEast]
      rw [hdelta]
      have hblock : firstBlock 0 + blockCount 0 - 1 =
          firstBlock 0 + (blockCount 0 - 1) := by
        rw [blockCount_eq]
        omega
      rw [lastBlock, hblock]
      exact canonical_boundary_mem grid (blockCount 0 - 1)
        (by rw [blockCount_eq]; omega)
  | succ depth ih =>
      have hlast : lastBlock (depth + 1) = 4 * lastBlock depth := by
        rw [lastBlock_eq, lastBlock_eq, pow_succ]
        omega
      have hblock : (lastBlock (depth + 1) - 1) / 4 + 1 =
          lastBlock depth := by
        rw [hlast, lastBlock_eq]
        have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
        omega
      have hresidue : (lastBlock (depth + 1) - 1) % 4 = 3 := by
        rw [hlast, lastBlock_eq]
        have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
        omega
      rw [windowAt_succ, hblock, hresidue, canonicalWindow_refineWindow]
      exact canonical_refine_mem_of_closedAt rightEdgeWindows_closed ih (by simp)

theorem canonical_rightmostRelevant_mem (depth : Nat) (grid : Nat → Nat → Index) :
    canonicalWindow (windowAt depth grid (lastRelevantBlock depth)) ∈
      rightmostRelevantWindows := by
  cases depth with
  | zero =>
      rw [rightmostRelevantWindows, List.mem_eraseDups, List.mem_append]
      left
      have hdelta : quarterEast (4 * east .odd 1) / 8 -
          quarterWest (4 * west .odd 1) / 8 - 1 = blockCount 0 - 2 := by
        norm_num [blockCount, firstBlock, west, east, scale, Phase.factor,
          quarterWest, quarterEast]
      rw [hdelta]
      have hblock : firstBlock 0 + blockCount 0 - 2 =
          firstBlock 0 + (blockCount 0 - 2) := by
        rw [blockCount_eq]
        omega
      rw [lastRelevantBlock, hblock]
      exact canonical_boundary_mem grid (blockCount 0 - 2)
        (by rw [blockCount_eq]; omega)
  | succ depth =>
      have hblock : (lastRelevantBlock (depth + 1) - 1) / 4 + 1 =
          lastBlock depth := by
        rw [lastRelevantBlock_eq, lastBlock_eq, pow_succ]
        have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
        omega
      have hresidue : (lastRelevantBlock (depth + 1) - 1) % 4 = 2 := by
        rw [lastRelevantBlock_eq, pow_succ]
        have hpower : 0 < 4 ^ depth := pow_pos (by decide) depth
        omega
      rw [windowAt_succ, hblock, hresidue, canonicalWindow_refineWindow]
      rw [rightmostRelevantWindows, List.mem_eraseDups, List.mem_append]
      right
      rw [List.mem_map]
      exact ⟨canonicalWindow (windowAt depth grid (lastBlock depth)),
        canonical_rightEdge_mem depth grid, rfl⟩

end SparseFreeLinePlaneSideHalfClosure
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
