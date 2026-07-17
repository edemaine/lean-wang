/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104BorderCoverageLocalAudit
import LeanWang.OllingerRobinson104RedShadeGraphTranslation
import LeanWang.OllingerRobinson104ShadedFreeLineRecurrence
import LeanWang.OllingerRobinson104SparseFreeLineOffsets

/-!
# Finite side-half routing windows

The odd pivot-extra row at the next scale is six cells below the sparse copy
of its predecessor.  Every strict target lies in the middle column of a
`3 x 2` macrocell window.  This module enumerates the 68 windows occurring in
the first recursive board and checks one bounded weighted flood per window.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineSideHalfAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphSearch RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  RedShadeGraphTranslation
  ShadedFreeLineRecurrence SparseFreeLineOffsets Signals.FreeCellLocal
  BorderCoverageLocalAudit

set_option maxRecDepth 20000

/-- A row-major `3 x 2` window of parent symbols. -/
abbrev Window := List Index

def windowGrid (window : Window) (x y : Nat) : Index :=
  (window[y * 3 + x]?).getD 0

def translateStart (start : WeightedStart) (dx dy : Nat) : WeightedStart where
  port := translatePort start.port dx dy
  parity := start.parity

/-- Live retained-row starts in the upper three macrocells. -/
def windowStarts (window : Window) : List WeightedStart :=
  (List.range 3).flatMap fun x =>
    (rowStarts (windowGrid window x 1) .retained 1).map fun start =>
      translateStart start (8 * x) 8

theorem windowStarts_inBounds (window : Window) :
    ∀ start ∈ windowStarts window, PortInBounds start.port 24 16 := by
  intro start hstart
  rw [windowStarts, List.mem_flatMap] at hstart
  rcases hstart with ⟨x, hx, hstart⟩
  simp only [List.mem_range] at hx
  rcases List.mem_map.1 hstart with ⟨source, hsource, rfl⟩
  have bounded := rowStarts_retained_one_inBounds
    (windowGrid window x 1) source hsource
  rcases source with ⟨⟨sourceX, sourceY, side⟩, parity⟩
  simp only [PortInBounds] at bounded ⊢
  simp only [translateStart, translatePort]
  constructor <;> omega

def windowNodes (window : Window) : List Node :=
  exploreFastWeighted (iterateRefine 2 (windowGrid window))
    24 16 4000 (windowStarts window)

def reached (window : Window) (target : Port) : Bool :=
  portPresent (iterateRefine 2 (windowGrid window)) target &&
    (windowNodes window).any fun node =>
      node.parity && decide (node.current = target)

def Route (window : Window) (target : Port) : Prop :=
  BoundedRouteIn (iterateRefine 2 (windowGrid window))
    24 16 (windowStarts window) target

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

/-- Every live vertical target in the middle lower macrocell is reached. -/
def windowCheck (window : Window) : Bool :=
  (List.range 8).all fun x =>
    let targetX := 8 + x
    let required := (Signals.verticalInterior?
      (componentAt (iterateRefine 2 (windowGrid window)) targetX 3)
      (quadrantAt targetX 3)).isSome
    !required || reached window ⟨targetX, 3, .south⟩ ||
      reached window ⟨targetX, 3, .north⟩

set_option linter.flexible false in
theorem windowCheck_sound {window : Window}
    (checked : windowCheck window = true) :
    ∀ x, x < 8 →
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 (windowGrid window)) (8 + x) 3)
        (quadrantAt (8 + x) 3) ≠ none →
      Route window ⟨8 + x, 3, .south⟩ ∨
        Route window ⟨8 + x, 3, .north⟩ := by
  simp only [windowCheck, List.all_eq_true, List.mem_range] at checked
  intro x hx interior
  have covered := checked x hx
  have required : (Signals.verticalInterior?
      (componentAt (iterateRefine 2 (windowGrid window)) (8 + x) 3)
      (quadrantAt (8 + x) 3)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reached_sound covered)
  · exact Or.inr (reached_sound covered)

/-- Restrict local sources to those whose translated old-row coordinate is
strictly inside the old board. -/
def windowStartsIn (window : Window) (lower upper : Nat) :
    List WeightedStart :=
  (windowStarts window).filter fun start =>
    lower ≤ start.port.x && start.port.x < upper

def windowNodesIn (window : Window) (lower upper : Nat) : List Node :=
  exploreFastWeighted (iterateRefine 2 (windowGrid window))
    24 16 4000 (windowStartsIn window lower upper)

def reachedIn (window : Window) (lower upper : Nat) (target : Port) : Bool :=
  portPresent (iterateRefine 2 (windowGrid window)) target &&
    (windowNodesIn window lower upper).any fun node =>
      node.parity && decide (node.current = target)

def RouteIn (window : Window) (lower upper : Nat) (target : Port) : Prop :=
  BoundedRouteIn (iterateRefine 2 (windowGrid window))
    24 16 (windowStartsIn window lower upper) target

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
  (List.range 8).all fun x =>
    if targetLower ≤ x && x < targetUpper then
      let targetX := 8 + x
      let required := (Signals.verticalInterior?
        (componentAt (iterateRefine 2 (windowGrid window)) targetX 3)
        (quadrantAt targetX 3)).isSome
      !required || reachedIn window lower upper ⟨targetX, 3, .south⟩ ||
        reachedIn window lower upper ⟨targetX, 3, .north⟩
    else true

set_option linter.flexible false in
theorem windowCheckIn_sound {window : Window}
    {lower upper targetLower targetUpper : Nat}
    (checked : windowCheckIn window lower upper targetLower targetUpper = true) :
    ∀ x, x < 8 → targetLower ≤ x → x < targetUpper →
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 (windowGrid window)) (8 + x) 3)
        (quadrantAt (8 + x) 3) ≠ none →
      RouteIn window lower upper ⟨8 + x, 3, .south⟩ ∨
        RouteIn window lower upper ⟨8 + x, 3, .north⟩ := by
  simp only [windowCheckIn, List.all_eq_true, List.mem_range] at checked
  intro x hx htargetLower htargetUpper interior
  have covered := checked x hx
  simp only [htargetLower, htargetUpper, decide_true, Bool.true_and,
    if_true] at covered
  have required : (Signals.verticalInterior?
      (componentAt (iterateRefine 2 (windowGrid window)) (8 + x) 3)
      (quadrantAt (8 + x) 3)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at covered
  rcases covered with covered | covered
  · exact Or.inl (reachedIn_sound covered)
  · exact Or.inr (reachedIn_sound covered)

/-- Enumerate all strict target blocks for one predecessor row. -/
def windowsIn (grid : Nat → Nat → Index)
    (oldWest oldEast oldRow : Nat) : List Window :=
  let lowerBlockY := oldRow / 2 - 1
  let firstBlock := quarterWest (4 * oldWest) / 8
  let blockCount := quarterEast (4 * oldEast) / 8 - firstBlock + 1
  (List.range blockCount).map fun delta =>
    let blockX := firstBlock + delta
    let originX := blockX - 1
    (List.range 2).flatMap fun y =>
      (List.range 3).map fun x =>
        grid (originX + x) (lowerBlockY + y)

/-- The distinct side-half windows in all 104 first recursive boards. -/
def recurrenceWindows : List Window :=
  ((List.finRange 104).flatMap fun parent =>
    windowsIn (localGrid .odd 1 parent)
      (west .odd 1) (east .odd 1) (lineCoordinate .odd 1 9)).eraseDups

/-- Erase the graph-invisible black layer pointwise. -/
def canonicalWindow (window : Window) : Window :=
  window.map BorderSubstitution.canonicalIndex

/-- The 60 border-state windows occurring at the first recursive depth. -/
def canonicalWindows : List Window :=
  (recurrenceWindows.map canonicalWindow).eraseDups

/-- Extract a successor window at one of the four horizontal residues. -/
def refineWindow (window : Window) (residueX : Nat) : Window :=
  let refined := iterateRefine 2 (windowGrid window)
  (List.range 2).flatMap fun y =>
    (List.range 3).map fun x => refined (residueX + x) y

def closeWindows (windows : List Window) : List Window :=
  (windows ++ windows.flatMap fun window =>
    (List.range 4).map fun residueX =>
      canonicalWindow (refineWindow window residueX)).eraseDups

/-- The stable 80-state quotient used by the side-half induction. -/
def closedWindows : List Window := closeWindows canonicalWindows

def boundaryWindow (parent : Index) (delta : Nat) : Window :=
  let grid := localGrid .odd 1 parent
  let oldWest := west .odd 1
  let oldRow := lineCoordinate .odd 1 9
  let blockX := quarterWest (4 * oldWest) / 8 + delta
  let originX := blockX - 1
  (List.range 2).flatMap fun y =>
    (List.range 3).map fun x =>
      grid (originX + x) (oldRow / 2 - 1 + y)

def boundaryBase (delta : Nat) : List Window :=
  ((List.finRange 104).map fun parent =>
    canonicalWindow (boundaryWindow parent delta)).eraseDups

def closeWindowsAt (residues : List Nat) (windows : List Window) : List Window :=
  (windows ++ windows.flatMap fun window => residues.map fun residue =>
    canonicalWindow (refineWindow window residue)).eraseDups

def leftmostWindows : List Window := closeWindowsAt [3] (boundaryBase 0)

def nextLeftWindows : List Window := closeWindowsAt [0] (boundaryBase 1)

def rightEdgeWindows : List Window :=
  let last :=
    quarterEast (4 * east .odd 1) / 8 - quarterWest (4 * west .odd 1) / 8
  closeWindowsAt [3] (boundaryBase last)

def rightmostRelevantWindows : List Window :=
  let lastRelevant :=
    quarterEast (4 * east .odd 1) / 8 - quarterWest (4 * west .odd 1) / 8 - 1
  (boundaryBase lastRelevant ++ rightEdgeWindows.map fun window =>
    canonicalWindow (refineWindow window 2)).eraseDups

set_option linter.style.nativeDecide false in
theorem closedWindows_complete :
    ∀ window ∈ closedWindows, windowCheck window = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem leftmostWindows_complete :
    ∀ window ∈ leftmostWindows, windowCheckIn window 10 24 2 8 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem nextLeftWindows_complete :
    ∀ window ∈ nextLeftWindows, windowCheckIn window 2 24 0 8 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem rightmostRelevantWindows_complete :
    ∀ window ∈ rightmostRelevantWindows,
      windowCheckIn window 0 16 0 8 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem leftmostWindows_closed :
    closeWindowsAt [3] leftmostWindows = leftmostWindows := by
  native_decide

set_option linter.style.nativeDecide false in
theorem nextLeftWindows_closed :
    closeWindowsAt [0] nextLeftWindows = nextLeftWindows := by
  native_decide

set_option linter.style.nativeDecide false in
theorem rightEdgeWindows_closed :
    closeWindowsAt [3] rightEdgeWindows = rightEdgeWindows := by
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
    (hwindow : window ∈ closedWindows) {residueX : Nat}
    (hresidue : residueX < 4) :
    canonicalWindow (refineWindow window residueX) ∈ closedWindows := by
  have hmem : canonicalWindow (refineWindow window residueX) ∈
      closeWindows closedWindows := by
    rw [closeWindows, List.mem_eraseDups, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨window, hwindow, ?_⟩
    rw [List.mem_map]
    exact ⟨residueX, by simpa using hresidue, rfl⟩
  rw [closedWindows_closed] at hmem
  exact hmem

end SparseFreeLineSideHalfAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
