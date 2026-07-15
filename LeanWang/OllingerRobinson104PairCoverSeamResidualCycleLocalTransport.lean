/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedRouteParityAudit
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorTransport
import LeanWang.OllingerRobinson104SparseFreeLineEvenExtraCreatedWindowBacking

/-!
# Transport created residual sources to local hierarchy cycles

The finite created-coordinate audit is translated into every macrocell of an
arbitrary two-substitution refinement.  Its parity-labelled route terminates
on the canonical depth-two cycle in that macrocell.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCycleLocalTransport

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeGraphTranslation
  PairCoverSeamShadePaths PairCoverSeamCreatedLocalTransport
  PairCoverSeamCreatedRouteParityAudit
  SparseFreeLineEvenExtraCreatedWindowBacking
  RefinedCoordinateProjection ShadedFreeLineProjectionSourceLists
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def LocalCycleRouteAt (grid : Nat → Nat → Index) (target : Port) : Prop :=
  ∃ blockX blockY entry parity,
    CycleOn (iterateRefine 2 grid)
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) ∧
    OnCycle (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) entry ∧
    Path (iterateRefine 2 grid) target entry parity

/-- A local-cycle route retaining the exact two-substitution macrocell in
which the target was audited. -/
def LocalCycleRouteAtBlock (grid : Nat → Nat → Index) (target : Port)
    (blockX blockY : Nat) : Prop :=
  ∃ entry parity,
    CycleOn (iterateRefine 2 grid)
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) ∧
    OnCycle (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) entry ∧
    Path (iterateRefine 2 grid) target entry parity

/-- A local-cycle route retaining both the audited macrocell and its exact
path parity. -/
def LocalCycleRouteAtBlockWithParity (grid : Nat → Nat → Index)
    (target : Port) (blockX blockY : Nat) (parity : Bool) : Prop :=
  ∃ entry,
    CycleOn (iterateRefine 2 grid)
      (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) ∧
    OnCycle (4 * blockX + 1) (4 * blockX + 3)
      (4 * blockY + 1) (4 * blockY + 3) entry ∧
    Path (iterateRefine 2 grid) target entry parity

/-- Forgetting the exact parity recovers the previous local route. -/
theorem LocalCycleRouteAtBlockWithParity.toRoute
    {grid : Nat → Nat → Index} {target : Port}
    {blockX blockY : Nat} {parity : Bool}
    (route : LocalCycleRouteAtBlockWithParity grid target
      blockX blockY parity) :
    LocalCycleRouteAtBlock grid target blockX blockY := by
  rcases route with ⟨entry, cycle, entryOnCycle, path⟩
  exact ⟨entry, parity, cycle, entryOnCycle, path⟩

private theorem local_created_of_not_sparse {coordinate : Nat}
    (created : ¬ IsSparseCoordinate coordinate) :
    coordinate % 8 ∈
      PairCoverSeamResidualCycleLocalAudit.createdCoordinates := by
  have hlocal : coordinate % 8 < 8 := Nat.mod_lt _ (by decide)
  have hdecompose := Nat.mod_add_div coordinate 8
  simp only [PairCoverSeamResidualCycleLocalAudit.createdCoordinates,
    List.mem_cons, List.not_mem_nil, or_false]
  by_contra hnot
  have hsparse : coordinate % 8 = 0 ∨ coordinate % 8 = 1 := by omega
  apply created
  rcases hsparse with hzero | hone
  · refine ⟨2 * (coordinate / 8), ?_⟩
    rw [sparseCoordinate_two_mul]
    omega
  · refine ⟨2 * (coordinate / 8) + 1, ?_⟩
    rw [sparseCoordinate_two_mul_add_one]
    omega

set_option maxHeartbeats 2000000 in
-- The translated selector and cycle entry both depend on the macrocell split.
theorem horizontalCreatedAtBlockWithParity
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    LocalCycleRouteAtBlockWithParity grid
      (horizontalPort (iterateRefine 2 grid) column boundary)
      (column / 8) (boundary / 8) (createdParity (boundary % 8)) := by
  let blockX := column / 8
  let blockY := boundary / 8
  let localX := column % 8
  let localY := boundary % 8
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hcolumn : 8 * blockX + localX = column := by
    have := Nat.mod_add_div column 8
    dsimp [blockX, localX]
    omega
  have hboundary : 8 * blockY + localY = boundary := by
    have := Nat.mod_add_div boundary 8
    dsimp [blockY, localY]
    omega
  have hcreatedY : localY ∈
      PairCoverSeamResidualCycleLocalAudit.createdCoordinates := by
    exact local_created_of_not_sparse createdBoundary
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid (grid blockX blockY)) localX localY)
      (quadrantAt localX localY) ≠ none := by
    rw [horizontalInterior_twoBlock grid blockX blockY
      localX localY hlocalX hlocalY]
    simpa only [hcolumn, hboundary] using interior
  have checked := horizontalAt_of_checkParent
    (complete (grid blockX blockY)) hlocalX hcreatedY
  rcases horizontalAt_sound checked localInterior with
    ⟨entry, hentry, localPath⟩
  have translated := boundedPath_twoBlock grid blockX blockY localPath
  have targetPort := horizontalPort_twoBlock grid blockX blockY
    localX localY hlocalX hlocalY
  rw [targetPort, hcolumn, hboundary] at translated
  let globalEntry := translatePort entry (8 * blockX) (8 * blockY)
  refine ⟨globalEntry,
    OrientedRedBoardTranslations.depthTwo_at grid blockX blockY, ?_, ?_⟩
  · exact onCycle_translate_cell blockX blockY 0 0
      (onCycle_of_mem_cyclePorts (by omega) (by omega) hentry)
  · exact path_symm translated

/-- Compatibility projection of `horizontalCreatedAtBlockWithParity`. -/
theorem horizontalCreatedAtBlock
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    LocalCycleRouteAtBlock grid
      (horizontalPort (iterateRefine 2 grid) column boundary)
      (column / 8) (boundary / 8) :=
  (horizontalCreatedAtBlockWithParity grid column boundary
    createdBoundary interior).toRoute

/-- Forgetting the audited macrocell recovers the original horizontal route. -/
theorem horizontalCreated
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    LocalCycleRouteAt grid
      (horizontalPort (iterateRefine 2 grid) column boundary) := by
  rcases horizontalCreatedAtBlock grid column boundary createdBoundary interior with
    ⟨entry, parity, cycle, entryOnCycle, path⟩
  exact ⟨column / 8, boundary / 8, entry, parity,
    cycle, entryOnCycle, path⟩

set_option maxHeartbeats 2000000 in
-- The translated selector and cycle entry both depend on the macrocell split.
theorem verticalCreatedAtBlockWithParity
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    LocalCycleRouteAtBlockWithParity grid
      (verticalPort (iterateRefine 2 grid) boundary row)
      (boundary / 8) (row / 8) (createdParity (boundary % 8)) := by
  let blockX := boundary / 8
  let blockY := row / 8
  let localX := boundary % 8
  let localY := row % 8
  have hlocalX : localX < 8 := Nat.mod_lt _ (by decide)
  have hlocalY : localY < 8 := Nat.mod_lt _ (by decide)
  have hboundary : 8 * blockX + localX = boundary := by
    have := Nat.mod_add_div boundary 8
    dsimp [blockX, localX]
    omega
  have hrow : 8 * blockY + localY = row := by
    have := Nat.mod_add_div row 8
    dsimp [blockY, localY]
    omega
  have hcreatedX : localX ∈
      PairCoverSeamResidualCycleLocalAudit.createdCoordinates := by
    exact local_created_of_not_sparse createdBoundary
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid (grid blockX blockY)) localX localY)
      (quadrantAt localX localY) ≠ none := by
    rw [verticalInterior_twoBlock grid blockX blockY
      localX localY hlocalX hlocalY]
    simpa only [hboundary, hrow] using interior
  have checked := verticalAt_of_checkParent
    (complete (grid blockX blockY)) hcreatedX hlocalY
  rcases verticalAt_sound checked localInterior with
    ⟨entry, hentry, localPath⟩
  have translated := boundedPath_twoBlock grid blockX blockY localPath
  have targetPort := verticalPort_twoBlock grid blockX blockY
    localX localY hlocalX hlocalY
  rw [targetPort, hboundary, hrow] at translated
  let globalEntry := translatePort entry (8 * blockX) (8 * blockY)
  refine ⟨globalEntry,
    OrientedRedBoardTranslations.depthTwo_at grid blockX blockY, ?_, ?_⟩
  · exact onCycle_translate_cell blockX blockY 0 0
      (onCycle_of_mem_cyclePorts (by omega) (by omega) hentry)
  · exact path_symm translated

/-- Compatibility projection of `verticalCreatedAtBlockWithParity`. -/
theorem verticalCreatedAtBlock
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    LocalCycleRouteAtBlock grid
      (verticalPort (iterateRefine 2 grid) boundary row)
      (boundary / 8) (row / 8) :=
  (verticalCreatedAtBlockWithParity grid boundary row
    createdBoundary interior).toRoute

/-- Forgetting the audited macrocell recovers the original vertical route. -/
theorem verticalCreated
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    LocalCycleRouteAt grid
      (verticalPort (iterateRefine 2 grid) boundary row) := by
  rcases verticalCreatedAtBlock grid boundary row createdBoundary interior with
    ⟨entry, parity, cycle, entryOnCycle, path⟩
  exact ⟨boundary / 8, row / 8, entry, parity,
    cycle, entryOnCycle, path⟩

end PairCoverSeamResidualCycleLocalTransport
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
