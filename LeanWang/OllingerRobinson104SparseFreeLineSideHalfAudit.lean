/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineLocalRecurrence

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
  ShadedFreeLineProjectionCandidates ShadedFreeLineProjectionSourceLists
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

/-- The distinct side-half windows in all 104 first recursive boards. -/
def recurrenceWindows : List Window :=
  ((List.finRange 104).flatMap fun parent =>
    let grid := localGrid .odd 1 parent
    let oldWest := west .odd 1
    let oldEast := east .odd 1
    let oldRow := lineCoordinate .odd 1 9
    let lowerBlockY := oldRow / 2 - 1
    let firstBlock := quarterWest (4 * oldWest) / 8
    let blockCount := quarterEast (4 * oldEast) / 8 - firstBlock + 1
    (List.range blockCount).map fun delta =>
      let blockX := firstBlock + delta
      let originX := blockX - 1
      (List.range 2).flatMap fun y =>
        (List.range 3).map fun x =>
          grid (originX + x) (lowerBlockY + y)).eraseDups

set_option linter.style.nativeDecide false in
theorem recurrenceWindows_complete :
    ∀ window ∈ recurrenceWindows, windowCheck window = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem recurrenceWindows_length : recurrenceWindows.length = 68 := by
  native_decide

end SparseFreeLineSideHalfAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
