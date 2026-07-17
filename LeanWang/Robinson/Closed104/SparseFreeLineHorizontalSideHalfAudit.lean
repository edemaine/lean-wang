/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.BorderCoverageLocalAudit
import LeanWang.Robinson.Closed104.RedShadeGraphTranslation
import LeanWang.Robinson.Closed104.ShadedFreeLineRecurrence
import LeanWang.Robinson.Closed104.SparseFreeLineOffsets

/-!
# Finite horizontal side-half routing windows

This is the coordinate-dual audit to the recursive side-half row audit. Every
strict horizontal target lies in the middle row of a `2 x 3` macrocell window.
The finite quotient records the retained-column starts in the right three
macrocells and checks one bounded weighted flood per window.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineHorizontalSideHalfAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  RedShadeGraphTranslation
  ShadedFreeLineRecurrence SparseFreeLineOffsets Signals.FreeCellLocal
  BorderCoverageLocalAudit

set_option maxRecDepth 20000

/-- A row-major `2 x 3` window of parent symbols. -/
abbrev Window := List Index

def windowGrid (window : Window) (x y : Nat) : Index :=
  (window[y * 2 + x]?).getD 0

def translateStart (start : WeightedStart) (dx dy : Nat) : WeightedStart where
  port := translatePort start.port dx dy
  parity := start.parity

/-- Live retained-column starts in the right three macrocells. -/
def windowStarts (window : Window) : List WeightedStart :=
  (List.range 3).flatMap fun y =>
    (columnStarts (windowGrid window 1 y) .retained 1).map fun start =>
      translateStart start 8 (8 * y)

theorem windowStarts_inBounds (window : Window) :
    ∀ start ∈ windowStarts window, PortInBounds start.port 16 24 := by
  intro start hstart
  rw [windowStarts, List.mem_flatMap] at hstart
  rcases hstart with ⟨y, hy, hstart⟩
  simp only [List.mem_range] at hy
  rcases List.mem_map.1 hstart with ⟨source, hsource, rfl⟩
  have bounded := columnStarts_retained_one_inBounds
    (windowGrid window 1 y) source hsource
  rcases source with ⟨⟨sourceX, sourceY, side⟩, parity⟩
  simp only [PortInBounds] at bounded ⊢
  simp only [translateStart, translatePort]
  constructor <;> omega

def windowNodes (window : Window) : List Node :=
  exploreFastWeighted (iterateRefine 2 (windowGrid window))
    16 24 4000 (windowStarts window)

def reached (window : Window) (target : Port) : Bool :=
  portPresent (iterateRefine 2 (windowGrid window)) target &&
    (windowNodes window).any fun node =>
      node.parity && decide (node.current = target)

def Route (window : Window) (target : Port) : Prop :=
  BoundedRouteIn (iterateRefine 2 (windowGrid window))
    16 24 (windowStarts window) target

theorem reached_sound {window : Window} {target : Port}
    (checked : reached window target = true) : Route window target := by
  simp only [reached, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound
      (windowStarts_inBounds window) hnode with ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

/-- Every live horizontal target in the middle left macrocell is reached. -/
def windowCheck (window : Window) : Bool :=
  (List.range 8).all fun y =>
    let targetY := 8 + y
    let required := (Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (windowGrid window)) 3 targetY)
      (quadrantAt 3 targetY)).isSome
    !required || reached window ⟨3, targetY, .west⟩ ||
      reached window ⟨3, targetY, .east⟩

set_option linter.flexible false in
theorem windowCheck_sound {window : Window}
    (checked : windowCheck window = true) :
    ∀ y, y < 8 →
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (windowGrid window)) 3 (8 + y))
        (quadrantAt 3 (8 + y)) ≠ none →
      Route window ⟨3, 8 + y, .west⟩ ∨
        Route window ⟨3, 8 + y, .east⟩ := by
  simp only [windowCheck, List.all_eq_true, List.mem_range] at checked
  intro y hy interior
  have covered := checked y hy
  have required : (Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (windowGrid window)) 3 (8 + y))
      (quadrantAt 3 (8 + y))).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered)
  · exact Or.inr (reached_sound covered)

/-- Restrict local sources to those whose translated old-column coordinate is
strictly inside the old board. -/
def windowStartsIn (window : Window) (lower upper : Nat) :
    List WeightedStart :=
  (windowStarts window).filter fun start =>
    lower ≤ start.port.y && start.port.y < upper

def windowNodesIn (window : Window) (lower upper : Nat) : List Node :=
  exploreFastWeighted (iterateRefine 2 (windowGrid window))
    16 24 4000 (windowStartsIn window lower upper)

def reachedIn (window : Window) (lower upper : Nat) (target : Port) : Bool :=
  portPresent (iterateRefine 2 (windowGrid window)) target &&
    (windowNodesIn window lower upper).any fun node =>
      node.parity && decide (node.current = target)

def RouteIn (window : Window) (lower upper : Nat) (target : Port) : Prop :=
  BoundedRouteIn (iterateRefine 2 (windowGrid window))
    16 24 (windowStartsIn window lower upper) target

set_option maxHeartbeats 1000000 in
-- Unfolding the filtered executable start list needs more elaboration work.
theorem reachedIn_sound {window : Window} {lower upper : Nat} {target : Port}
    (checked : reachedIn window lower upper target = true) :
    RouteIn window lower upper target := by
  simp only [reachedIn, windowNodesIn, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rcases exploreFastWeighted_bounded_sound
      (fun start hstart => windowStarts_inBounds window start
        (List.mem_of_mem_filter hstart)) hnode with ⟨start, hstart, path⟩
  refine ⟨start, hstart, ?_, checked.1⟩
  rw [hcurrent] at path
  simpa [hparity] using path

/-- Check only the strict targets belonging to this boundary-window class. -/
def windowCheckIn (window : Window) (lower upper targetLower targetUpper : Nat) :
    Bool :=
  (List.range 8).all fun y =>
    if targetLower ≤ y && y < targetUpper then
      let targetY := 8 + y
      let required := (Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (windowGrid window)) 3 targetY)
        (quadrantAt 3 targetY)).isSome
      !required || reachedIn window lower upper ⟨3, targetY, .west⟩ ||
        reachedIn window lower upper ⟨3, targetY, .east⟩
    else true

set_option linter.flexible false in
theorem windowCheckIn_sound {window : Window}
    {lower upper targetLower targetUpper : Nat}
    (checked : windowCheckIn window lower upper targetLower targetUpper = true) :
    ∀ y, y < 8 → targetLower ≤ y → y < targetUpper →
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (windowGrid window)) 3 (8 + y))
        (quadrantAt 3 (8 + y)) ≠ none →
      RouteIn window lower upper ⟨3, 8 + y, .west⟩ ∨
        RouteIn window lower upper ⟨3, 8 + y, .east⟩ := by
  simp only [windowCheckIn, List.all_eq_true, List.mem_range] at checked
  intro y hy htargetLower htargetUpper interior
  have covered := checked y hy
  simp only [htargetLower, htargetUpper, decide_true, Bool.true_and,
    if_true] at covered
  have required : (Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (windowGrid window)) 3 (8 + y))
      (quadrantAt 3 (8 + y))).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reachedIn_sound covered)
  · exact Or.inr (reachedIn_sound covered)

/-- Enumerate all strict target blocks for one predecessor column. -/
def windowsIn (grid : Nat → Nat → Index)
    (oldSouth oldNorth oldColumn : Nat) : List Window :=
  let lowerBlockX := oldColumn / 2 - 1
  let firstBlock := quarterSouth (4 * oldSouth) / 8
  let blockCount := quarterNorth (4 * oldNorth) / 8 - firstBlock + 1
  (List.range blockCount).map fun delta =>
    let blockY := firstBlock + delta
    let originY := blockY - 1
    (List.range 3).flatMap fun y =>
      (List.range 2).map fun x =>
        grid (lowerBlockX + x) (originY + y)

/-- The distinct horizontal side-half windows in all first recursive boards. -/
def recurrenceWindows : List Window :=
  ((List.finRange 104).flatMap fun parent =>
    windowsIn (localGrid .odd 1 parent)
      (west .odd 1) (east .odd 1) (lineCoordinate .odd 1 9)).eraseDups

def canonicalWindow (window : Window) : Window :=
  window.map BorderSubstitution.canonicalIndex

def canonicalWindows : List Window :=
  (recurrenceWindows.map canonicalWindow).eraseDups

/-- Extract a successor window at one of the four vertical residues. -/
def refineWindow (window : Window) (residueY : Nat) : Window :=
  let refined := iterateRefine 2 (windowGrid window)
  (List.range 3).flatMap fun y =>
    (List.range 2).map fun x => refined x (residueY + y)

def closeWindows (windows : List Window) : List Window :=
  (windows ++ windows.flatMap fun window =>
    (List.range 4).map fun residueY =>
      canonicalWindow (refineWindow window residueY)).eraseDups

/-- The stable 80-state quotient used by the horizontal side-half induction. -/
def closedWindows : List Window := closeWindows canonicalWindows

def boundaryWindow (parent : Index) (delta : Nat) : Window :=
  let grid := localGrid .odd 1 parent
  let oldSouth := west .odd 1
  let oldColumn := lineCoordinate .odd 1 9
  let blockY := quarterSouth (4 * oldSouth) / 8 + delta
  let originY := blockY - 1
  (List.range 3).flatMap fun y =>
    (List.range 2).map fun x =>
      grid (oldColumn / 2 - 1 + x) (originY + y)

def boundaryBase (delta : Nat) : List Window :=
  ((List.finRange 104).map fun parent =>
    canonicalWindow (boundaryWindow parent delta)).eraseDups

def closeWindowsAt (residues : List Nat) (windows : List Window) : List Window :=
  (windows ++ windows.flatMap fun window => residues.map fun residue =>
    canonicalWindow (refineWindow window residue)).eraseDups

def bottommostWindows : List Window := closeWindowsAt [3] (boundaryBase 0)

def nextBottomWindows : List Window := closeWindowsAt [0] (boundaryBase 1)

def topEdgeWindows : List Window :=
  let last :=
    quarterNorth (4 * east .odd 1) / 8 - quarterSouth (4 * west .odd 1) / 8
  closeWindowsAt [3] (boundaryBase last)

def topmostRelevantWindows : List Window :=
  let lastRelevant :=
    quarterNorth (4 * east .odd 1) / 8 - quarterSouth (4 * west .odd 1) / 8 - 1
  (boundaryBase lastRelevant ++ topEdgeWindows.map fun window =>
    canonicalWindow (refineWindow window 2)).eraseDups

set_option linter.style.nativeDecide false in
theorem closedWindows_complete :
    ∀ window ∈ closedWindows, windowCheck window = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem bottommostWindows_complete :
    ∀ window ∈ bottommostWindows, windowCheckIn window 10 24 2 8 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem nextBottomWindows_complete :
    ∀ window ∈ nextBottomWindows, windowCheckIn window 2 24 0 8 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem topmostRelevantWindows_complete :
    ∀ window ∈ topmostRelevantWindows,
      windowCheckIn window 0 16 0 8 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem bottommostWindows_closed :
    closeWindowsAt [3] bottommostWindows = bottommostWindows := by
  native_decide

set_option linter.style.nativeDecide false in
theorem nextBottomWindows_closed :
    closeWindowsAt [0] nextBottomWindows = nextBottomWindows := by
  native_decide

set_option linter.style.nativeDecide false in
theorem topEdgeWindows_closed :
    closeWindowsAt [3] topEdgeWindows = topEdgeWindows := by
  native_decide

set_option linter.style.nativeDecide false in
theorem recurrenceWindows_length : recurrenceWindows.length = 68 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem canonicalWindows_length : canonicalWindows.length = 60 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem closedWindows_length : closedWindows.length = 80 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem closedWindows_closed : closeWindows closedWindows = closedWindows := by
  native_decide

theorem canonicalWindow_mem_closedWindows {window : Window}
    (hwindow : window ∈ recurrenceWindows) :
    canonicalWindow window ∈ closedWindows := by
  rw [closedWindows, closeWindows, List.mem_eraseDups, List.mem_append]
  left
  rw [canonicalWindows, List.mem_eraseDups, List.mem_map]
  exact ⟨window, hwindow, rfl⟩

theorem refineWindow_mem_closedWindows {window : Window}
    (hwindow : window ∈ closedWindows) {residueY : Nat}
    (hresidue : residueY < 4) :
    canonicalWindow (refineWindow window residueY) ∈ closedWindows := by
  have hmem : canonicalWindow (refineWindow window residueY) ∈
      closeWindows closedWindows := by
    rw [closeWindows, List.mem_eraseDups, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨window, hwindow, ?_⟩
    rw [List.mem_map]
    exact ⟨residueY, by simpa using hresidue, rfl⟩
  rw [closedWindows_closed] at hmem
  exact hmem

end SparseFreeLineHorizontalSideHalfAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
