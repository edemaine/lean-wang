/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageCheck
import LeanWang.Robinson.Closed104.RedShadeGraphTranslation
import LeanWang.Robinson.Closed104.RedShadeGraphStaticCertificate
import LeanWang.Robinson.Closed104.SignalFreeCellEmbedding

/-!
# Certified local red-graph coverage

The executable all-parent audit is promoted to a bounded path theorem.  The
bounded path can subsequently be translated into any macrocell of an
arbitrary refined grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphBoundedPath
  RedShadeGraphRefinement RedShadeGraphStaticCertificate
  RedShadeGraphTranslation RefinementTranslation
  Signals.FreeCellLocal Signals.FreeCellEmbedding

set_option maxRecDepth 20000

theorem parentCovered_eq_true (parent : Index) : parentCovered parent = true := by
  have checked : ∀ candidate ∈ List.finRange 104,
      parentCovered candidate = true := by
    simpa [allParentsCovered, List.all_eq_true] using allParentsCovered_eq_true
  exact checked parent (List.mem_finRange parent)

theorem sources_inBounds (parent : Index) :
    ∀ source ∈ sources parent, PortInBounds source 8 8 := by
  intro source hsource
  simp only [sources, List.mem_cons] at hsource
  rcases hsource with rfl | hsource
  · change 4 < 8 ∧ 3 < 8
    omega
  · rw [inheritedSources, List.mem_map] at hsource
    rcases hsource with ⟨old, hold, rfl⟩
    simp only [List.mem_filter] at hold
    have oldBounds := hold.1
    unfold portsIn at oldBounds
    rw [List.mem_flatMap] at oldBounds
    rcases oldBounds with ⟨y, hy, oldBounds⟩
    rw [List.mem_flatMap] at oldBounds
    rcases oldBounds with ⟨x, hx, oldBounds⟩
    simp only [List.mem_range] at hy hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at oldBounds
    rcases oldBounds with rfl | rfl | rfl | rfl <;>
      simp [PortInBounds, sparsePort, sparseCoordinate, macroOrigin,
        localCoordinate] <;> omega

/-- Every present port in one two-substitution macrocell has a bounded route
from either the new cell cycle or a sparse inherited old port. -/
theorem exists_boundedPath
    (parent : Index) {target : Port}
    (targetMem : target ∈ portsIn 8 8)
    (targetPresent : portPresent (fineGrid parent) target = true) :
    ∃ source ∈ sources parent, ∃ parity,
      BoundedPath (fineGrid parent) 8 8 source target parity := by
  have checked := parentCovered_eq_true parent
  simp only [parentCovered, List.all_eq_true] at checked
  have targetChecked := checked target targetMem
  simp only [targetCovered, targetPresent, if_true,
    Option.isSome_iff_exists] at targetChecked
  rcases targetChecked with ⟨⟨index, state⟩, route⟩
  have routeMem : (index, state) ∈ routes parent := by
    unfold routeNode? at route
    exact List.mem_of_find?_eq_some route
  have current := List.find?_some route
  simp only [decide_eq_true_eq] at current
  have evaluated := evaluate_of_mem_evaluated routeMem
  have sourceMem := origin_mem_sources_of_evaluate evaluated
  have path := boundedPath_of_evaluate evaluated
  refine ⟨state.origin, sourceMem, state.parity, ?_⟩
  simpa only [current] using path

theorem base_exists_boundedPath {target : Port}
    (targetMem : target ∈ portsIn 8 8)
    (targetWest : 2 ≤ target.x) (targetEast : target.x < 6)
    (targetSouth : 2 ≤ target.y) (targetNorth : target.y < 6)
    (targetPresent : portPresent (fineGrid 0) target = true) :
    ∃ parity, BoundedPath (fineGrid 0) 8 8 cycleSource target parity := by
  have checked := baseCovered_eq_true
  simp only [baseCovered, List.all_eq_true] at checked
  have targetChecked := checked target targetMem
  simp only [baseTargetCovered, targetWest, targetEast, targetSouth, targetNorth,
    targetPresent, decide_true, Bool.true_and, if_true]
    at targetChecked
  simp only [Option.isSome_iff_exists] at targetChecked
  rcases targetChecked with ⟨⟨index, state⟩, route⟩
  have routeMem : (index, state) ∈ baseRoutes := by
    unfold baseRoute? routeNode? at route
    exact List.mem_of_find?_eq_some route
  have current := List.find?_some route
  simp only [decide_eq_true_eq] at current
  have evaluated := evaluate_of_mem_evaluated routeMem
  have sourceMem := origin_mem_sources_of_evaluate evaluated
  simp only [List.mem_singleton] at sourceMem
  refine ⟨state.parity, ?_⟩
  have path := boundedPath_of_evaluate evaluated
  simpa only [sourceMem, current] using path

/-- Translate a bounded local route into the corresponding macrocell. -/
theorem boundedPath_two_block
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath (fineGrid (grid blockX blockY)) 8 8
      first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity := by
  have componentsEq : ∀ x y, x < 8 → y < 8 →
      componentAt (fineGrid (grid blockX blockY)) x y =
        componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact (componentAt_shift_eq_constant 2 grid blockX blockY x y hx hy).symm
  have shifted :=
    (BoundedPath.congr_of_component_eq componentsEq path).path
  simpa using path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted

theorem componentAt_old_block
    (grid : Nat → Nat → Index) (level blockX blockY localX localY : Nat)
    (hx : localX < 2) (hy : localY < 2) :
    componentAt (iterateRefine level grid)
        (2 * blockX + localX) (2 * blockY + localY) =
      componentAt (coarseGrid (iterateRefine level grid blockX blockY))
        localX localY := by
  simp [componentAt, coarseGrid]
  congr <;> omega

theorem quadrantAt_old_block
    (blockX blockY localX localY : Nat)
    (hx : localX < 2) (hy : localY < 2) :
    quadrantAt (2 * blockX + localX) (2 * blockY + localY) =
      quadrantAt localX localY := by
  have hxCases : localX = 0 ∨ localX = 1 := by omega
  have hyCases : localY = 0 ∨ localY = 1 := by omega
  rcases hxCases with rfl | rfl <;> rcases hyCases with rfl | rfl <;>
    simp [quadrantAt]

theorem portPresent_old_block
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) (hx : port.x < 2) (hy : port.y < 2) :
    portPresent (coarseGrid (grid blockX blockY)) port =
      portPresent grid
        (translatePort port (2 * blockX) (2 * blockY)) := by
  rcases port with ⟨x, y, side⟩
  have hcomponent : componentAt (coarseGrid (grid blockX blockY)) x y =
      componentAt grid (2 * blockX + x) (2 * blockY + y) := by
    change componentAt (coarseGrid (grid blockX blockY)) x y =
      componentAt (iterateRefine 0 grid) (2 * blockX + x) (2 * blockY + y)
    exact (componentAt_old_block grid 0 blockX blockY x y hx hy).symm
  have hquadrant := quadrantAt_old_block blockX blockY x y hx hy
  cases side <;> simp only [portPresent, translatePort] <;>
    rw [hcomponent, hquadrant]

theorem portPresent_two_block
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (port : Port) (hx : port.x < 8) (hy : port.y < 8) :
    portPresent (fineGrid (grid blockX blockY)) port =
      portPresent (iterateRefine 2 grid)
        (translatePort port (8 * blockX) (8 * blockY)) := by
  rcases port with ⟨x, y, side⟩
  have hcomponent : componentAt (fineGrid (grid blockX blockY)) x y =
      componentAt (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
    change componentAt
        (iterateRefine 2 (fun _ _ => iterateRefine 0 grid blockX blockY)) x y = _
    exact (componentAt_two_block grid 0 blockX blockY x y hx hy).symm
  have hquadrant := quadrantAt_block blockX blockY x y
  cases side <;> simp only [portPresent, translatePort] <;>
    rw [hcomponent, hquadrant]

/-- Split the local source into the newly created cycle source and an inherited
old port. -/
theorem source_cases {parent : Index} {source : Port}
    (sourceMem : source ∈ sources parent) :
    source = cycleSource ∨
      ∃ old ∈ portsIn 2 2,
        portPresent (coarseGrid parent) old = true ∧ source = sparsePort old := by
  simp only [sources, List.mem_cons] at sourceMem
  rcases sourceMem with hcycle | inherited
  · exact Or.inl hcycle
  · right
    rw [inheritedSources, List.mem_map] at inherited
    rcases inherited with ⟨old, hold, rfl⟩
    simp only [List.mem_filter] at hold
    exact ⟨old, hold.1, hold.2, rfl⟩

end RedShadeGraphLocalCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
