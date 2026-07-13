/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorAudit
import LeanWang.OllingerRobinson104PairCoverSeamCreatedLocalTransport

/-!
# Transport residual-cycle predecessors into arbitrary macrocells

The finite predecessor audit is stated on a constant-parent `8 x 8` block.
Here its bounded paths are translated into an arbitrary two-substitution
refinement, with the source identified as the literal sparse copy of a coarse
selector.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCyclePredecessorTransport

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphTranslation
  PairCoverSeamShadePaths PairCoverSeamResidualCyclePredecessorAudit
  PairCoverSeamCreatedLocalTransport SparseFreeLineLocalTransport
  RefinedCoordinateProjection Signals.FreeCellLocal Signals.FreeCellEmbedding

set_option maxRecDepth 20000

def HorizontalPredecessor (grid : Nat → Nat → Index)
    (column boundary : Nat) : Prop :=
  ∃ oldColumn oldBoundary,
    sparseCoordinate oldBoundary = boundary ∧
    Signals.horizontalInterior?
      (componentAt grid oldColumn oldBoundary)
      (quadrantAt oldColumn oldBoundary) ≠ none ∧
    Path (iterateRefine 2 grid)
      (horizontalPort (iterateRefine 2 grid) column boundary)
      (sparsePort (horizontalPort grid oldColumn oldBoundary)) false

def VerticalPredecessor (grid : Nat → Nat → Index)
    (boundary row : Nat) : Prop :=
  ∃ oldBoundary oldRow,
    sparseCoordinate oldBoundary = boundary ∧
    Signals.verticalInterior?
      (componentAt grid oldBoundary oldRow)
      (quadrantAt oldBoundary oldRow) ≠ none ∧
    Path (iterateRefine 2 grid)
      (verticalPort (iterateRefine 2 grid) boundary row)
      (sparsePort (verticalPort grid oldBoundary oldRow)) false

private theorem horizontalSparsePort_oldBlock
    (grid : Nat → Nat → Index) (blockX blockY sourceX sourceY : Nat)
    (hsourceX : sourceX < 2) (hsourceY : sourceY < 2) :
    translatePort
        (sparsePort (horizontalPort (coarseGrid (grid blockX blockY))
          sourceX sourceY)) (8 * blockX) (8 * blockY) =
      sparsePort (horizontalPort grid
        (2 * blockX + sourceX) (2 * blockY + sourceY)) := by
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY hsourceX hsourceY
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY hsourceX hsourceY
  change componentAt grid (2 * blockX + sourceX) (2 * blockY + sourceY) =
    componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY at component
  unfold horizontalPort
  rw [← component, ← quadrant]
  split <;>
    simp [translatePort, sparsePort,
      sparseCoordinate_two_block blockX sourceX hsourceX,
      sparseCoordinate_two_block blockY sourceY hsourceY]

private theorem verticalSparsePort_oldBlock
    (grid : Nat → Nat → Index) (blockX blockY sourceX sourceY : Nat)
    (hsourceX : sourceX < 2) (hsourceY : sourceY < 2) :
    translatePort
        (sparsePort (verticalPort (coarseGrid (grid blockX blockY))
          sourceX sourceY)) (8 * blockX) (8 * blockY) =
      sparsePort (verticalPort grid
        (2 * blockX + sourceX) (2 * blockY + sourceY)) := by
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY hsourceX hsourceY
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY hsourceX hsourceY
  change componentAt grid (2 * blockX + sourceX) (2 * blockY + sourceY) =
    componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY at component
  unfold verticalPort
  rw [← component, ← quadrant]
  split <;>
    simp [translatePort, sparsePort,
      sparseCoordinate_two_block blockX sourceX hsourceX,
      sparseCoordinate_two_block blockY sourceY hsourceY]

set_option maxHeartbeats 2000000 in
-- Translated selectors occur dependently in the bounded path endpoints.
theorem horizontalPredecessor
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    HorizontalPredecessor grid column boundary := by
  rcases sparseBoundary with ⟨oldBoundary, hboundary⟩
  let blockX := column / 8
  let targetX := column % 8
  let blockY := oldBoundary / 2
  let sourceY := oldBoundary % 2
  have htargetX : targetX < 8 := Nat.mod_lt _ (by decide)
  have hsourceY : sourceY < 2 := Nat.mod_lt _ (by decide)
  have hcolumn : 8 * blockX + targetX = column := by
    have := Nat.mod_add_div column 8
    dsimp [blockX, targetX]
    omega
  have holdBoundary : 2 * blockY + sourceY = oldBoundary := by
    have := Nat.mod_add_div oldBoundary 2
    dsimp [blockY, sourceY]
    omega
  have hlocalY : sparseCoordinate sourceY < 8 := by
    simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega
  have hboundaryLocal :
      8 * blockY + sparseCoordinate sourceY = boundary := by
    rw [← hboundary, ← holdBoundary,
      sparseCoordinate_two_block blockY sourceY hsourceY]
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid (grid blockX blockY))
        targetX (sparseCoordinate sourceY))
      (quadrantAt targetX (sparseCoordinate sourceY)) ≠ none := by
    rw [horizontalInterior_twoBlock grid blockX blockY targetX
      (sparseCoordinate sourceY) htargetX hlocalY]
    simpa only [hcolumn, hboundaryLocal] using interior
  have checked := horizontalAt_of_checkParent
    (complete (grid blockX blockY)) hsourceY htargetX
  rcases horizontalAt_sound hsourceY checked localInterior with
    ⟨sourceX, hsourceX, sourceInterior, localPath⟩
  let oldColumn := 2 * blockX + sourceX
  have globalSourceInterior : Signals.horizontalInterior?
      (componentAt grid oldColumn oldBoundary)
      (quadrantAt oldColumn oldBoundary) ≠ none := by
    have component := componentAt_old_block grid 0 blockX blockY
      sourceX sourceY hsourceX hsourceY
    have quadrant := quadrantAt_old_block blockX blockY
      sourceX sourceY hsourceX hsourceY
    have component' : componentAt grid (2 * blockX + sourceX)
        (2 * blockY + sourceY) =
        componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY := by
      simpa only [iterateRefine] using component
    dsimp only [oldColumn]
    rw [← holdBoundary, component', quadrant]
    exact sourceInterior
  have translated := boundedPath_twoBlock grid blockX blockY localPath
  have targetPort := horizontalPort_twoBlock grid blockX blockY
    targetX (sparseCoordinate sourceY) htargetX hlocalY
  have sourcePort := horizontalSparsePort_oldBlock grid blockX blockY
    sourceX sourceY hsourceX hsourceY
  have globalPath : Path (iterateRefine 2 grid)
      (sparsePort (horizontalPort grid oldColumn oldBoundary))
      (horizontalPort (iterateRefine 2 grid) column boundary) false := by
    rw [sourcePort, targetPort, hcolumn, hboundaryLocal] at translated
    simpa only [oldColumn, holdBoundary] using translated
  exact ⟨oldColumn, oldBoundary, hboundary, globalSourceInterior,
    path_symm globalPath⟩

set_option maxHeartbeats 2000000 in
-- Translated selectors occur dependently in the bounded path endpoints.
theorem verticalPredecessor
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    VerticalPredecessor grid boundary row := by
  rcases sparseBoundary with ⟨oldBoundary, hboundary⟩
  let blockX := oldBoundary / 2
  let sourceX := oldBoundary % 2
  let blockY := row / 8
  let targetY := row % 8
  have hsourceX : sourceX < 2 := Nat.mod_lt _ (by decide)
  have htargetY : targetY < 8 := Nat.mod_lt _ (by decide)
  have holdBoundary : 2 * blockX + sourceX = oldBoundary := by
    have := Nat.mod_add_div oldBoundary 2
    dsimp [blockX, sourceX]
    omega
  have hrow : 8 * blockY + targetY = row := by
    have := Nat.mod_add_div row 8
    dsimp [blockY, targetY]
    omega
  have hlocalX : sparseCoordinate sourceX < 8 := by
    simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega
  have hboundaryLocal :
      8 * blockX + sparseCoordinate sourceX = boundary := by
    rw [← hboundary, ← holdBoundary,
      sparseCoordinate_two_block blockX sourceX hsourceX]
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid (grid blockX blockY))
        (sparseCoordinate sourceX) targetY)
      (quadrantAt (sparseCoordinate sourceX) targetY) ≠ none := by
    rw [verticalInterior_twoBlock grid blockX blockY
      (sparseCoordinate sourceX) targetY hlocalX htargetY]
    simpa only [hboundaryLocal, hrow] using interior
  have checked := verticalAt_of_checkParent
    (complete (grid blockX blockY)) hsourceX htargetY
  rcases verticalAt_sound hsourceX checked localInterior with
    ⟨sourceY, hsourceY, sourceInterior, localPath⟩
  let oldRow := 2 * blockY + sourceY
  have globalSourceInterior : Signals.verticalInterior?
      (componentAt grid oldBoundary oldRow)
      (quadrantAt oldBoundary oldRow) ≠ none := by
    have component := componentAt_old_block grid 0 blockX blockY
      sourceX sourceY hsourceX hsourceY
    have quadrant := quadrantAt_old_block blockX blockY
      sourceX sourceY hsourceX hsourceY
    have component' : componentAt grid (2 * blockX + sourceX)
        (2 * blockY + sourceY) =
        componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY := by
      simpa only [iterateRefine] using component
    dsimp only [oldRow]
    rw [← holdBoundary, component', quadrant]
    exact sourceInterior
  have translated := boundedPath_twoBlock grid blockX blockY localPath
  have targetPort := verticalPort_twoBlock grid blockX blockY
    (sparseCoordinate sourceX) targetY hlocalX htargetY
  have sourcePort := verticalSparsePort_oldBlock grid blockX blockY
    sourceX sourceY hsourceX hsourceY
  have globalPath : Path (iterateRefine 2 grid)
      (sparsePort (verticalPort grid oldBoundary oldRow))
      (verticalPort (iterateRefine 2 grid) boundary row) false := by
    rw [sourcePort, targetPort, hboundaryLocal, hrow] at translated
    simpa only [oldRow, holdBoundary] using translated
  exact ⟨oldBoundary, oldRow, hboundary, globalSourceInterior,
    path_symm globalPath⟩

end PairCoverSeamResidualCyclePredecessorTransport
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
