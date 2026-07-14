/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorTransport
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorHierarchy
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence

/-!
# Exact inherited hierarchy-family sources

The exact predecessor connector is combined with the all-depth canonical
source hierarchy.  The resulting records retain both the coarse and fine
family ancestors while identifying the coarse parallel selector by
`coarseCoordinate` exactly.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorHierarchy

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic
  PairCoverSeamRefinementCoordinates
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCyclePredecessorTransport
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathExactPredecessorTransport
  PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence
  PairCoverSeamResidualDirectPathFamilyTargetLiftTransport
  PairCoverSeamResidualDirectPathTargets
  PairCoverSeamShadePaths RefinedCoordinateProjection
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Exact coarse source and hierarchy family inherited by a sparse horizontal
fine source. -/
structure HorizontalExactInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY column boundary : Nat) where
  oldBoundary : Nat
  family : HierarchyFamily
  oldColumnBounds : InCollar
    (successorWest phase depth parentX)
    (successorEast phase depth parentX) (coarseCoordinate column)
  oldColumnWeakBounds :
    quarterWest (successorWest phase depth parentX) ≤
        coarseCoordinate column ∧
      coarseCoordinate column <
        quarterEast (successorEast phase depth parentX)
  oldBoundaryBounds : InCollar
    (successorWest phase depth parentY)
    (successorEast phase depth parentY) oldBoundary
  oldBoundaryStrictBounds :
    quarterSouth (successorWest phase depth parentY) < oldBoundary ∧
      oldBoundary < quarterNorth (successorEast phase depth parentY)
  boundarySparse : sparseCoordinate oldBoundary = boundary
  oldInterior : Signals.horizontalInterior?
    (componentAt (refinedGrid phase (depth + 1) grid)
      (coarseCoordinate column) oldBoundary)
    (quadrantAt (coarseCoordinate column) oldBoundary) ≠ none
  orientationEq : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 1) grid)
        (coarseCoordinate column) oldBoundary)
      (quadrantAt (coarseCoordinate column) oldBoundary) =
    Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary)
  refineFamily : ∀ selectedFamily,
    CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 1) grid)
        (horizontalPort (refinedGrid phase (depth + 1) grid)
          (coarseCoordinate column) oldBoundary)
        (outerLevel phase depth) parentX parentY selectedFamily →
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (horizontalPort (refinedGrid phase (depth + 2) grid) column boundary)
        (outerLevel phase (depth + 1)) parentX parentY selectedFamily
  oldFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 1) grid)
    (horizontalPort (refinedGrid phase (depth + 1) grid)
      (coarseCoordinate column) oldBoundary)
    (outerLevel phase depth) parentX parentY family
  fineFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 2) grid)
    (horizontalPort (refinedGrid phase (depth + 2) grid) column boundary)
    (outerLevel phase (depth + 1)) parentX parentY family

/-- Vertical dual of `HorizontalExactInheritedSource`. -/
structure VerticalExactInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY boundary row : Nat) where
  oldBoundary : Nat
  family : HierarchyFamily
  oldBoundaryBounds : InCollar
    (successorWest phase depth parentX)
    (successorEast phase depth parentX) oldBoundary
  oldBoundaryStrictBounds :
    quarterWest (successorWest phase depth parentX) < oldBoundary ∧
      oldBoundary < quarterEast (successorEast phase depth parentX)
  oldRowBounds : InCollar
    (successorWest phase depth parentY)
    (successorEast phase depth parentY) (coarseCoordinate row)
  oldRowWeakBounds :
    quarterSouth (successorWest phase depth parentY) ≤
        coarseCoordinate row ∧
      coarseCoordinate row <
        quarterNorth (successorEast phase depth parentY)
  boundarySparse : sparseCoordinate oldBoundary = boundary
  oldInterior : Signals.verticalInterior?
    (componentAt (refinedGrid phase (depth + 1) grid)
      oldBoundary (coarseCoordinate row))
    (quadrantAt oldBoundary (coarseCoordinate row)) ≠ none
  orientationEq : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 1) grid)
        oldBoundary (coarseCoordinate row))
      (quadrantAt oldBoundary (coarseCoordinate row)) =
    Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row)
  refineFamily : ∀ selectedFamily,
    CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 1) grid)
        (verticalPort (refinedGrid phase (depth + 1) grid)
          oldBoundary (coarseCoordinate row))
        (outerLevel phase depth) parentX parentY selectedFamily →
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (verticalPort (refinedGrid phase (depth + 2) grid) boundary row)
        (outerLevel phase (depth + 1)) parentX parentY selectedFamily
  oldFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 1) grid)
    (verticalPort (refinedGrid phase (depth + 1) grid)
      oldBoundary (coarseCoordinate row))
    (outerLevel phase depth) parentX parentY family
  fineFamily : CanonicalCycleAncestorWithinFamily
    (refinedGrid phase (depth + 2) grid)
    (verticalPort (refinedGrid phase (depth + 2) grid) boundary row)
    (outerLevel phase (depth + 1)) parentX parentY family

private theorem fineGrid_eq
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      refinedGrid phase (depth + 2) grid := by
  exact (SparseFreeLinePlaneLocalStep.refinedGrid_succ
    phase (depth + 1) grid).symm

private theorem outerLevel_succ (phase : Phase) (depth : Nat) :
    outerLevel phase depth + 2 = outerLevel phase (depth + 1) := by
  simp [outerLevel]
  omega

set_option maxHeartbeats 1000000 in
-- The family witness depends on the exact predecessor endpoint.
/-- Package the exact predecessor and its inherited horizontal family. -/
theorem horizontalExactInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary : Nat}
    (columnLower : quarterWest (successorWest phase (depth + 1) parentX) <
      column)
    (columnUpper : column <
      quarterEast (successorEast phase (depth + 1) parentX))
    (boundaryLower :
      quarterSouth (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryUpper : boundary <
      quarterNorth (successorEast phase (depth + 1) parentY))
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    Nonempty (HorizontalExactInheritedSource phase depth grid
      parentX parentY column boundary) := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 oldGrid) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [fineGrid_eq phase depth grid]
    exact interior
  rcases horizontalExactPredecessor oldGrid column boundary
      sparseBoundary interior' with ⟨oldBoundary, predecessor⟩
  have boundarySparse := predecessor.1
  have oldInterior := predecessor.2.1
  have orientationEq := predecessor.2.2.1
  have connector := predecessor.2.2.2
  have oldColumnBounds : InCollar
      (successorWest phase depth parentX)
      (successorEast phase depth parentX) (coarseCoordinate column) :=
    predecessor_in_collar_of_collar
      (div_two_eq_div_eight_of_coarseCoordinate rfl)
      (by
        rw [successorWest_succ] at columnLower
        omega)
      (by simpa only [successorEast_succ] using columnUpper)
  have oldColumnWeakBounds := coarse_successor_bounds_of_fine_bounds
    columnLower columnUpper
  have oldBoundaryBounds : InCollar
      (successorWest phase depth parentY)
      (successorEast phase depth parentY) oldBoundary :=
    sparse_preimage_in_collar boundarySparse
      (by
        rw [successorWest_succ] at boundaryLower
        simp only [quarterSouth, quarterWest] at boundaryLower ⊢
        omega)
      (by
        rw [successorEast_succ] at boundaryUpper
        simpa only [quarterNorth, quarterEast] using boundaryUpper)
  have oldBoundaryStrictBounds :
      quarterSouth (successorWest phase depth parentY) < oldBoundary ∧
        oldBoundary < quarterNorth (successorEast phase depth parentY) := by
    have projected := coarse_successor_bounds_of_fine_bounds
      (by simpa only [quarterSouth, quarterWest] using boundaryLower)
      (by simpa only [quarterNorth, quarterEast] using boundaryUpper)
    have boundaryCoarse : coarseCoordinate boundary = oldBoundary := by
      rw [← boundarySparse, coarseCoordinate_sparseCoordinate]
    constructor
    · have sparseLower :
          sparseCoordinate (quarterSouth (successorWest phase depth parentY)) <
            sparseCoordinate oldBoundary := by
        rw [boundarySparse]
        simpa only [successorWest_succ, sparseCoordinate_quarterSouth]
          using boundaryLower
      exact sparseCoordinate_lt_iff.mp sparseLower
    · simpa only [boundaryCoarse, quarterNorth, quarterEast] using projected.2
  have hierarchy := sourceAncestorsWithinAt phase depth
    grid parentX parentY
  have oldAncestor := hierarchy.horizontal
    oldColumnBounds oldBoundaryBounds (by
      simpa only [oldGrid] using oldInterior)
  rcases CanonicalCycleAncestorWithin.exists_family oldAncestor with
    ⟨family, oldFamily⟩
  have refineFamily : ∀ selectedFamily,
      CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 1) grid)
          (horizontalPort (refinedGrid phase (depth + 1) grid)
            (coarseCoordinate column) oldBoundary)
          (outerLevel phase depth) parentX parentY selectedFamily →
        CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 2) grid)
          (horizontalPort (refinedGrid phase (depth + 2) grid) column boundary)
          (outerLevel phase (depth + 1)) parentX parentY selectedFamily := by
    intro selectedFamily ancestor
    have refined := ancestor.refineThrough
      (horizontalPort_present_of_interior (by
        simpa only [oldGrid] using oldInterior)) connector
    simpa only [oldGrid, fineGrid_eq phase depth grid,
      outerLevel_succ phase depth] using refined
  have fineFamily := refineFamily family oldFamily
  refine ⟨⟨oldBoundary, family, oldColumnBounds, oldColumnWeakBounds,
    oldBoundaryBounds, oldBoundaryStrictBounds, boundarySparse, ?_, ?_,
    refineFamily, oldFamily, fineFamily⟩⟩
  · simpa only [oldGrid] using oldInterior
  · simpa only [oldGrid, fineGrid_eq phase depth grid] using orientationEq

set_option maxHeartbeats 1000000 in
-- The family witness depends on the exact predecessor endpoint.
/-- Package the exact predecessor and its inherited vertical family. -/
theorem verticalExactInheritedSource
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row : Nat}
    (boundaryLower :
      quarterWest (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryUpper : boundary <
      quarterEast (successorEast phase (depth + 1) parentX))
    (rowLower : quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowUpper : row <
      quarterNorth (successorEast phase (depth + 1) parentY))
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    Nonempty (VerticalExactInheritedSource phase depth grid
      parentX parentY boundary row) := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 oldGrid) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [fineGrid_eq phase depth grid]
    exact interior
  rcases verticalExactPredecessor oldGrid boundary row
      sparseBoundary interior' with ⟨oldBoundary, predecessor⟩
  have boundarySparse := predecessor.1
  have oldInterior := predecessor.2.1
  have orientationEq := predecessor.2.2.1
  have connector := predecessor.2.2.2
  have oldBoundaryBounds : InCollar
      (successorWest phase depth parentX)
      (successorEast phase depth parentX) oldBoundary :=
    sparse_preimage_in_collar boundarySparse
      (by
        rw [successorWest_succ] at boundaryLower
        omega)
      (by simpa only [successorEast_succ] using boundaryUpper)
  have oldBoundaryStrictBounds :
      quarterWest (successorWest phase depth parentX) < oldBoundary ∧
        oldBoundary < quarterEast (successorEast phase depth parentX) := by
    have projected := coarse_successor_bounds_of_fine_bounds
      boundaryLower boundaryUpper
    have boundaryCoarse : coarseCoordinate boundary = oldBoundary := by
      rw [← boundarySparse, coarseCoordinate_sparseCoordinate]
    constructor
    · have sparseLower :
          sparseCoordinate (quarterWest (successorWest phase depth parentX)) <
            sparseCoordinate oldBoundary := by
        rw [boundarySparse]
        simpa only [successorWest_succ, sparseCoordinate_quarterWest]
          using boundaryLower
      exact sparseCoordinate_lt_iff.mp sparseLower
    · simpa only [boundaryCoarse] using projected.2
  have oldRowBounds : InCollar
      (successorWest phase depth parentY)
      (successorEast phase depth parentY) (coarseCoordinate row) :=
    predecessor_in_collar_of_collar
      (div_two_eq_div_eight_of_coarseCoordinate rfl)
      (by
        rw [successorWest_succ] at rowLower
        simp only [quarterSouth, quarterWest] at rowLower ⊢
        omega)
      (by simpa only [successorEast_succ, quarterNorth, quarterEast]
        using rowUpper)
  have oldRowWeakBounds := coarse_successor_bounds_of_fine_bounds
    (by simpa only [quarterSouth, quarterWest] using rowLower)
    (by simpa only [quarterNorth, quarterEast] using rowUpper)
  have hierarchy := sourceAncestorsWithinAt phase depth
    grid parentX parentY
  have oldAncestor := hierarchy.vertical
    oldBoundaryBounds oldRowBounds (by
      simpa only [oldGrid] using oldInterior)
  rcases CanonicalCycleAncestorWithin.exists_family oldAncestor with
    ⟨family, oldFamily⟩
  have refineFamily : ∀ selectedFamily,
      CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 1) grid)
          (verticalPort (refinedGrid phase (depth + 1) grid)
            oldBoundary (coarseCoordinate row))
          (outerLevel phase depth) parentX parentY selectedFamily →
        CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 2) grid)
          (verticalPort (refinedGrid phase (depth + 2) grid) boundary row)
          (outerLevel phase (depth + 1)) parentX parentY selectedFamily := by
    intro selectedFamily ancestor
    have refined := ancestor.refineThrough
      (verticalPort_present_of_interior (by
        simpa only [oldGrid] using oldInterior)) connector
    simpa only [oldGrid, fineGrid_eq phase depth grid,
      outerLevel_succ phase depth] using refined
  have fineFamily := refineFamily family oldFamily
  refine ⟨⟨oldBoundary, family, oldBoundaryBounds, oldBoundaryStrictBounds,
    oldRowBounds, oldRowWeakBounds, boundarySparse, ?_, ?_, refineFamily,
    oldFamily, fineFamily⟩⟩
  · simpa only [oldGrid] using oldInterior
  · simpa only [oldGrid, fineGrid_eq phase depth grid] using orientationEq

set_option maxHeartbeats 1000000 in
-- The target contains dependent refined-grid family endpoints.
/-- Lift a target for an exact coarse horizontal source to its fine query. -/
theorem HorizontalExactInheritedSource.refineTarget
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {parentX parentY column row boundary : Nat}
    (source : HorizontalExactInheritedSource phase depth grid
      parentX parentY column boundary)
    (target : RowFamilyTarget grid (outerLevel phase depth) parentX parentY
      (successorWest phase depth parentX)
      (successorEast phase depth parentX)
      (coarseCoordinate column) (coarseCoordinate row)
      source.oldBoundary source.family) :
    RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX)
      column row boundary source.family := by
  have refined := RowFamilyTarget.refineAt target
    (fineColumn := column) (fineRow := row) rfl rfl
  simpa only [outerLevel_succ, successorWest_succ, successorEast_succ,
    source.boundarySparse] using refined

set_option maxHeartbeats 1000000 in
-- The target contains dependent refined-grid family endpoints.
/-- Lift a target in any coarse source family, without committing to the
record's canonical family choice. -/
theorem HorizontalExactInheritedSource.refineFamilyTarget
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {parentX parentY column row boundary : Nat}
    (source : HorizontalExactInheritedSource phase depth grid
      parentX parentY column boundary)
    {selectedFamily : HierarchyFamily}
    (oldFamily : CanonicalCycleAncestorWithinFamily
      (refinedGrid phase (depth + 1) grid)
      (horizontalPort (refinedGrid phase (depth + 1) grid)
        (coarseCoordinate column) source.oldBoundary)
      (outerLevel phase depth) parentX parentY selectedFamily)
    (target : RowFamilyTarget grid (outerLevel phase depth) parentX parentY
      (successorWest phase depth parentX)
      (successorEast phase depth parentX)
      (coarseCoordinate column) (coarseCoordinate row)
      source.oldBoundary selectedFamily) :
    CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (horizontalPort (refinedGrid phase (depth + 2) grid) column boundary)
        (outerLevel phase (depth + 1)) parentX parentY selectedFamily ∧
      RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX)
        column row boundary selectedFamily := by
  have refined := RowFamilyTarget.refineAt target
    (fineColumn := column) (fineRow := row) rfl rfl
  exact ⟨source.refineFamily selectedFamily oldFamily, by
    simpa only [outerLevel_succ, successorWest_succ, successorEast_succ,
      source.boundarySparse] using refined⟩

set_option maxHeartbeats 1000000 in
-- The target contains dependent refined-grid family endpoints.
/-- Column-dual exact-source target refinement. -/
theorem VerticalExactInheritedSource.refineTarget
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {parentX parentY boundary row column : Nat}
    (source : VerticalExactInheritedSource phase depth grid
      parentX parentY boundary row)
    (target : ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
      (successorWest phase depth parentY)
      (successorEast phase depth parentY)
      (coarseCoordinate row) (coarseCoordinate column)
      source.oldBoundary source.family) :
    ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY)
      row column boundary source.family := by
  have refined := ColumnFamilyTarget.refineAt target
    (fineRow := row) (fineColumn := column) rfl rfl
  simpa only [outerLevel_succ, successorWest_succ, successorEast_succ,
    source.boundarySparse] using refined

set_option maxHeartbeats 1000000 in
-- The target contains dependent refined-grid family endpoints.
/-- Column-dual arbitrary-family source and target refinement. -/
theorem VerticalExactInheritedSource.refineFamilyTarget
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {parentX parentY boundary row column : Nat}
    (source : VerticalExactInheritedSource phase depth grid
      parentX parentY boundary row)
    {selectedFamily : HierarchyFamily}
    (oldFamily : CanonicalCycleAncestorWithinFamily
      (refinedGrid phase (depth + 1) grid)
      (verticalPort (refinedGrid phase (depth + 1) grid)
        source.oldBoundary (coarseCoordinate row))
      (outerLevel phase depth) parentX parentY selectedFamily)
    (target : ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
      (successorWest phase depth parentY)
      (successorEast phase depth parentY)
      (coarseCoordinate row) (coarseCoordinate column)
      source.oldBoundary selectedFamily) :
    CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (verticalPort (refinedGrid phase (depth + 2) grid) boundary row)
        (outerLevel phase (depth + 1)) parentX parentY selectedFamily ∧
      ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY)
        row column boundary selectedFamily := by
  have refined := ColumnFamilyTarget.refineAt target
    (fineRow := row) (fineColumn := column) rfl rfl
  exact ⟨source.refineFamily selectedFamily oldFamily, by
    simpa only [outerLevel_succ, successorWest_succ, successorEast_succ,
      source.boundarySparse] using refined⟩

end PairCoverSeamResidualDirectPathExactPredecessorHierarchy
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
