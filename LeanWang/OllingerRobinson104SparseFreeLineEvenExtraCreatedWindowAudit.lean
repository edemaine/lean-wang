/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphWeightedReachBounded
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedWindowAuditCheck

/-! Proposition-level soundness for neighboring-window created-segment routes. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenExtraCreatedWindowAudit

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoards RedShadeGraphRefinement
  RedShadeGraphSearchSoundness RedShadeGraphWeightedSearch
  ShadedFreeLineProjectionSourceLists
  RedShadeGraphWeightedReachBounded
  ShadedFreeLineRecurrence Signals.FreeCellLocal SparseFreeLineLocalStates

set_option maxRecDepth 20000

structure RouteWitness (window : Window) (target : Port) where
  start : WeightedStart
  start_mem : start ∈ windowStarts window
  path : BoundedPath (RedCycles.iterateRefine 2 (windowGrid window)) 24 24
    start.port target (Bool.xor start.parity true)
  targetLive :
    portPresent (RedCycles.iterateRefine 2 (windowGrid window)) target = true

def Route (window : Window) (target : Port) : Prop :=
  Nonempty (RouteWitness window target)

/-- Every enumerated source lies on one of the nine explicit cell cycles. -/
theorem start_on_cell_cycle {window : Window} {start : WeightedStart}
    (hstart : start ∈ windowStarts window) :
    ∃ x < 3, ∃ y < 3,
      start.parity = false ∧
      OnCycle (4 * x + 1) (4 * x + 3)
        (4 * y + 1) (4 * y + 3) start.port := by
  rw [windowStarts, List.mem_flatMap] at hstart
  rcases hstart with ⟨y, hy, hstart⟩
  rw [List.mem_flatMap] at hstart
  rcases hstart with ⟨x, hx, hstart⟩
  rcases List.mem_map.1 hstart with ⟨port, hport, hstart⟩
  subst start
  simp only [List.mem_range] at hx hy
  refine ⟨x, hx, y, hy, rfl, ?_⟩
  exact onCycle_of_mem_cyclePorts (by omega) (by omega) hport

theorem onCellCycle_inBounds {x y : Nat} (hx : x < 3) (hy : y < 3)
    {port : Port}
    (onCycle : OnCycle (4 * x + 1) (4 * x + 3)
      (4 * y + 1) (4 * y + 3) port) :
    PortInBounds port 24 24 := by
  cases onCycle <;>
    simp_all [PortInBounds, quarterWest, quarterEast,
      quarterSouth, quarterNorth] <;>
    omega

theorem windowStarts_inBounds (window : Window) :
    ∀ start ∈ windowStarts window, PortInBounds start.port 24 24 := by
  intro start hstart
  rcases start_on_cell_cycle hstart with ⟨x, hx, y, hy, _, onCycle⟩
  exact onCellCycle_inBounds hx hy onCycle

theorem reached_sound {window : Window}
    {nodes : List RedShadeGraphSearch.ReachNode} {target : Port}
    (checked : reached window nodes target = true)
    (hnodes : nodes = windowNodes window) : Route window target := by
  simp only [reached, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at checked
  rcases checked.2 with ⟨node, hnode, hparity, hcurrent⟩
  rw [hnodes] at hnode
  rcases exploreFastWeightedReach_bounded_sound
      (windowStarts_inBounds window) hnode with ⟨start, hstart, path⟩
  refine ⟨⟨start, hstart, ?_, checked.1⟩⟩
  rw [hcurrent] at path
  simpa [hparity] using path

theorem verticalCaseCheck_sound {entry : Window × Nat}
    (checked : verticalCaseCheck entry = true) :
    Route entry.1 ⟨8 + entry.2, 8, .south⟩ ∨
      Route entry.1 ⟨8 + entry.2, 8, .north⟩ := by
  rw [verticalCaseCheck_eq] at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with checked | checked
  · exact Or.inl (reached_sound checked rfl)
  · exact Or.inr (reached_sound checked rfl)

theorem horizontalCaseCheck_sound {entry : Window × Nat}
    (checked : horizontalCaseCheck entry = true) :
    Route entry.1 ⟨8, 8 + entry.2, .west⟩ ∨
      Route entry.1 ⟨8, 8 + entry.2, .east⟩ := by
  rw [horizontalCaseCheck_eq] at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with checked | checked
  · exact Or.inl (reached_sound checked rfl)
  · exact Or.inr (reached_sound checked rfl)

theorem vertical_route_of_mem {entry : Window × Nat}
    (hentry : entry ∈ verticalCases) :
    Route entry.1 ⟨8 + entry.2, 8, .south⟩ ∨
      Route entry.1 ⟨8 + entry.2, 8, .north⟩ := by
  have checked := vertical_complete
  simp only [List.all_eq_true] at checked
  exact verticalCaseCheck_sound (checked entry hentry)

theorem horizontal_route_of_mem {entry : Window × Nat}
    (hentry : entry ∈ horizontalCases) :
    Route entry.1 ⟨8, 8 + entry.2, .west⟩ ∨
      Route entry.1 ⟨8, 8 + entry.2, .east⟩ := by
  have checked := horizontal_complete
  simp only [List.all_eq_true] at checked
  exact horizontalCaseCheck_sound (checked entry hentry)

theorem vertical_entry_mem (parent : Index) {blockX x : Nat}
    (hblockLower : 4 ≤ blockX) (hblockUpper : blockX < 12)
    (hx : x = 4 ∨ x = 5)
    (required : (Signals.verticalInterior?
      (componentAt (fineGrid (localGrid .even 1 parent blockX 9)) x 0)
      (quadrantAt x 0)).isSome = true)
    (created : verticalAncestorAt 0 0
      (localGrid .even 1 parent blockX 9) x = false) :
    (windowAt parent blockX 9, x) ∈ verticalCases := by
  simp only [verticalCases, List.mem_eraseDups, List.mem_flatMap,
    List.mem_filterMap, List.mem_finRange, true_and, List.mem_range]
  refine ⟨parent, blockX - 4, by omega, x, by simp [hx], ?_⟩
  have hblock : 4 + (blockX - 4) = blockX := by omega
  rw [hblock]
  simp [required, created]

theorem horizontal_entry_mem (parent : Index) {blockY y : Nat}
    (hblockLower : 4 ≤ blockY) (hblockUpper : blockY < 12)
    (hy : y = 4 ∨ y = 5)
    (required : (Signals.horizontalInterior?
      (componentAt (fineGrid (localGrid .even 1 parent 9 blockY)) 0 y)
      (quadrantAt 0 y)).isSome = true)
    (created : horizontalAncestorAt 0 0
      (localGrid .even 1 parent 9 blockY) y = false) :
    (windowAt parent 9 blockY, y) ∈ horizontalCases := by
  simp only [horizontalCases, List.mem_eraseDups, List.mem_flatMap,
    List.mem_filterMap, List.mem_finRange, true_and, List.mem_range]
  refine ⟨parent, blockY - 4, by omega, y, by simp [hy], ?_⟩
  have hblock : 4 + (blockY - 4) = blockY := by omega
  rw [hblock]
  simp [required, created]

/-- Every created center-band vertical segment has an audited neighboring route. -/
theorem vertical_created_route (parent : Index) {blockX x : Nat}
    (hblockLower : 4 ≤ blockX) (hblockUpper : blockX < 12)
    (hx : x = 4 ∨ x = 5)
    (required : (Signals.verticalInterior?
      (componentAt (fineGrid (localGrid .even 1 parent blockX 9)) x 0)
      (quadrantAt x 0)).isSome = true)
    (created : verticalAncestorAt 0 0
      (localGrid .even 1 parent blockX 9) x = false) :
    Route (windowAt parent blockX 9) ⟨8 + x, 8, .south⟩ ∨
      Route (windowAt parent blockX 9) ⟨8 + x, 8, .north⟩ :=
  vertical_route_of_mem
    (vertical_entry_mem parent hblockLower hblockUpper hx required created)

/-- Every created center-band horizontal segment has an audited neighboring route. -/
theorem horizontal_created_route (parent : Index) {blockY y : Nat}
    (hblockLower : 4 ≤ blockY) (hblockUpper : blockY < 12)
    (hy : y = 4 ∨ y = 5)
    (required : (Signals.horizontalInterior?
      (componentAt (fineGrid (localGrid .even 1 parent 9 blockY)) 0 y)
      (quadrantAt 0 y)).isSome = true)
    (created : horizontalAncestorAt 0 0
      (localGrid .even 1 parent 9 blockY) y = false) :
    Route (windowAt parent 9 blockY) ⟨8, 8 + y, .west⟩ ∨
      Route (windowAt parent 9 blockY) ⟨8, 8 + y, .east⟩ :=
  horizontal_route_of_mem
    (horizontal_entry_mem parent hblockLower hblockUpper hy required created)

end SparseFreeLineEvenExtraCreatedWindowAudit
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
