/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyPredecessor
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorHierarchy

/-!
# All-depth hierarchy-family predecessors

The local predecessor audit is packaged at the coordinates used by the
all-depth Robinson hierarchy.  Besides preserving a predecessor's family, the
result retains its coarse collar bounds.  Target recognition can therefore
recurse on the actual coarse source selected by the finite audit.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyPredecessorHierarchy

open RedCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic
  PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCyclePredecessorTransport
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamRefinementCoordinates
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A sparse horizontal source at the fine hierarchy level retains a
collar-contained coarse predecessor and every family carried by it. -/
theorem horizontalPredecessorWithin
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary : Nat}
    (columnBounds : InCollar
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column)
    (boundaryBounds : InCollar
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    ∃ oldColumn oldBoundary,
      InCollar (successorWest phase depth parentX)
        (successorEast phase depth parentX) oldColumn ∧
      InCollar (successorWest phase depth parentY)
        (successorEast phase depth parentY) oldBoundary ∧
      oldColumn / 2 = column / 8 ∧
      sparseCoordinate oldBoundary = boundary ∧
      Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          oldColumn oldBoundary)
        (quadrantAt oldColumn oldBoundary) ≠ none ∧
      ∀ family,
        CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 1) grid)
          (horizontalPort (refinedGrid phase (depth + 1) grid)
            oldColumn oldBoundary)
          (outerLevel phase depth) parentX parentY family →
        CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 2) grid)
          (horizontalPort (refinedGrid phase (depth + 2) grid)
            column boundary)
          (outerLevel phase (depth + 1)) parentX parentY family := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  have fineGridEq : iterateRefine 2 oldGrid =
      refinedGrid phase (depth + 2) grid := by
    exact (SparseFreeLinePlaneLocalStep.refinedGrid_succ
      phase (depth + 1) grid).symm
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 oldGrid) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [fineGridEq]
    exact interior
  rcases horizontalPredecessor oldGrid column boundary
      sparseBoundary interior' with
    ⟨oldColumn, oldBoundary, sameBlock, boundarySparse,
      oldInterior, connector⟩
  have fineColumnBounds : InCollar
      (4 * successorWest phase depth parentX)
      (4 * successorEast phase depth parentX) column := by
    simpa only [successorWest_succ, successorEast_succ] using columnBounds
  have fineBoundaryBounds : InCollar
      (4 * successorWest phase depth parentY)
      (4 * successorEast phase depth parentY) boundary := by
    simpa only [successorWest_succ, successorEast_succ] using boundaryBounds
  have oldColumnBounds : InCollar
      (successorWest phase depth parentX)
      (successorEast phase depth parentX) oldColumn :=
    predecessor_in_collar_of_collar sameBlock
      fineColumnBounds.1 fineColumnBounds.2
  have oldBoundaryBounds : InCollar
      (successorWest phase depth parentY)
      (successorEast phase depth parentY) oldBoundary :=
    sparse_preimage_in_collar boundarySparse
      fineBoundaryBounds.1 fineBoundaryBounds.2
  refine ⟨oldColumn, oldBoundary, oldColumnBounds, oldBoundaryBounds,
    sameBlock, boundarySparse, oldInterior, ?_⟩
  intro family ancestor
  have transported := ancestor.refineThrough
    (horizontalPort_present_of_interior oldInterior) connector
  have levelEq : outerLevel phase depth + 2 =
      outerLevel phase (depth + 1) := by
    simp [outerLevel]
    omega
  simpa only [oldGrid, fineGridEq, levelEq] using transported

/-- Vertical dual of `horizontalPredecessorWithin`. -/
theorem verticalPredecessorWithin
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row : Nat}
    (boundaryBounds : InCollar
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) boundary)
    (rowBounds : InCollar
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    ∃ oldBoundary oldRow,
      InCollar (successorWest phase depth parentX)
        (successorEast phase depth parentX) oldBoundary ∧
      InCollar (successorWest phase depth parentY)
        (successorEast phase depth parentY) oldRow ∧
      oldRow / 2 = row / 8 ∧
      sparseCoordinate oldBoundary = boundary ∧
      Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          oldBoundary oldRow)
        (quadrantAt oldBoundary oldRow) ≠ none ∧
      ∀ family,
        CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 1) grid)
          (verticalPort (refinedGrid phase (depth + 1) grid)
            oldBoundary oldRow)
          (outerLevel phase depth) parentX parentY family →
        CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 2) grid)
          (verticalPort (refinedGrid phase (depth + 2) grid)
            boundary row)
          (outerLevel phase (depth + 1)) parentX parentY family := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  have fineGridEq : iterateRefine 2 oldGrid =
      refinedGrid phase (depth + 2) grid := by
    exact (SparseFreeLinePlaneLocalStep.refinedGrid_succ
      phase (depth + 1) grid).symm
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 oldGrid) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [fineGridEq]
    exact interior
  rcases verticalPredecessor oldGrid boundary row
      sparseBoundary interior' with
    ⟨oldBoundary, oldRow, sameBlock, boundarySparse,
      oldInterior, connector⟩
  have fineBoundaryBounds : InCollar
      (4 * successorWest phase depth parentX)
      (4 * successorEast phase depth parentX) boundary := by
    simpa only [successorWest_succ, successorEast_succ] using boundaryBounds
  have fineRowBounds : InCollar
      (4 * successorWest phase depth parentY)
      (4 * successorEast phase depth parentY) row := by
    simpa only [successorWest_succ, successorEast_succ] using rowBounds
  have oldBoundaryBounds : InCollar
      (successorWest phase depth parentX)
      (successorEast phase depth parentX) oldBoundary :=
    sparse_preimage_in_collar boundarySparse
      fineBoundaryBounds.1 fineBoundaryBounds.2
  have oldRowBounds : InCollar
      (successorWest phase depth parentY)
      (successorEast phase depth parentY) oldRow :=
    predecessor_in_collar_of_collar sameBlock
      fineRowBounds.1 fineRowBounds.2
  refine ⟨oldBoundary, oldRow, oldBoundaryBounds, oldRowBounds,
    sameBlock, boundarySparse, oldInterior, ?_⟩
  intro family ancestor
  have transported := ancestor.refineThrough
    (verticalPort_present_of_interior oldInterior) connector
  have levelEq : outerLevel phase depth + 2 =
      outerLevel phase (depth + 1) := by
    simp [outerLevel]
    omega
  simpa only [oldGrid, fineGridEq, levelEq] using transported

/-- Every sparse horizontal fine source inherits an actual hierarchy family
from a collar-contained coarse predecessor.  This removes source discovery
from the finite family-target search. -/
theorem horizontalSourceFamily
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary : Nat}
    (columnBounds : InCollar
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column)
    (boundaryBounds : InCollar
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    ∃ oldColumn oldBoundary family,
      InCollar (successorWest phase depth parentX)
        (successorEast phase depth parentX) oldColumn ∧
      InCollar (successorWest phase depth parentY)
        (successorEast phase depth parentY) oldBoundary ∧
      oldColumn / 2 = column / 8 ∧
      sparseCoordinate oldBoundary = boundary ∧
      Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          oldColumn oldBoundary)
        (quadrantAt oldColumn oldBoundary) ≠ none ∧
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 1) grid)
        (horizontalPort (refinedGrid phase (depth + 1) grid)
          oldColumn oldBoundary)
        (outerLevel phase depth) parentX parentY family ∧
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (horizontalPort (refinedGrid phase (depth + 2) grid)
          column boundary)
        (outerLevel phase (depth + 1)) parentX parentY family := by
  rcases horizontalPredecessorWithin phase depth grid parentX parentY
      columnBounds boundaryBounds sparseBoundary interior with
    ⟨oldColumn, oldBoundary, oldColumnBounds, oldBoundaryBounds,
      sameBlock, boundarySparse, oldInterior, transport⟩
  have oldHierarchy := sourceAncestorsWithinAt phase depth
    grid parentX parentY
  have oldAncestor := oldHierarchy.horizontal
    oldColumnBounds oldBoundaryBounds oldInterior
  rcases CanonicalCycleAncestorWithin.exists_family oldAncestor with
    ⟨family, oldFamily⟩
  exact ⟨oldColumn, oldBoundary, family,
    oldColumnBounds, oldBoundaryBounds, sameBlock, boundarySparse,
    oldInterior, oldFamily, transport family oldFamily⟩

/-- Vertical dual of `horizontalSourceFamily`. -/
theorem verticalSourceFamily
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row : Nat}
    (boundaryBounds : InCollar
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) boundary)
    (rowBounds : InCollar
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    ∃ oldBoundary oldRow family,
      InCollar (successorWest phase depth parentX)
        (successorEast phase depth parentX) oldBoundary ∧
      InCollar (successorWest phase depth parentY)
        (successorEast phase depth parentY) oldRow ∧
      oldRow / 2 = row / 8 ∧
      sparseCoordinate oldBoundary = boundary ∧
      Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          oldBoundary oldRow)
        (quadrantAt oldBoundary oldRow) ≠ none ∧
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 1) grid)
        (verticalPort (refinedGrid phase (depth + 1) grid)
          oldBoundary oldRow)
        (outerLevel phase depth) parentX parentY family ∧
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (verticalPort (refinedGrid phase (depth + 2) grid)
          boundary row)
        (outerLevel phase (depth + 1)) parentX parentY family := by
  rcases verticalPredecessorWithin phase depth grid parentX parentY
      boundaryBounds rowBounds sparseBoundary interior with
    ⟨oldBoundary, oldRow, oldBoundaryBounds, oldRowBounds,
      sameBlock, boundarySparse, oldInterior, transport⟩
  have oldHierarchy := sourceAncestorsWithinAt phase depth
    grid parentX parentY
  have oldAncestor := oldHierarchy.vertical
    oldBoundaryBounds oldRowBounds oldInterior
  rcases CanonicalCycleAncestorWithin.exists_family oldAncestor with
    ⟨family, oldFamily⟩
  exact ⟨oldBoundary, oldRow, family,
    oldBoundaryBounds, oldRowBounds, sameBlock, boundarySparse,
    oldInterior, oldFamily, transport family oldFamily⟩

end PairCoverSeamResidualDirectPathFamilyPredecessorHierarchy
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
