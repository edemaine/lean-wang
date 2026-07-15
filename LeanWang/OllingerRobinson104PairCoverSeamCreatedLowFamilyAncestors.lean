/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathBridges
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorHierarchy

/-!
# Low family ancestors for created selectors

The created-selector audit reaches the local level-zero cell cycle with an
arbitrary route parity.  Parity normalization either stays at level zero or
crosses to its level-one parent.  These wrappers retain that low-level fact
together with the resulting even/odd hierarchy family.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedLowFamilyAncestors

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamRefinementCoordinates
  PairCoverSeamShadePaths PairCoverSeamResidualCycleLocalTransport
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualDirectPathBridges RefinedCoordinateProjection
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxHeartbeats 2000000 in
-- The translated selector depends on the equality between nested refinements.
/-- A horizontal created selector reaches the cycle at its exact audited
level-zero block or at that block's level-one parent. -/
theorem horizontalCreatedWithinExact
    (grid : Nat → Nat → Index) (column boundary : Nat)
    {outerLevel outerBlockX outerBlockY : Nat}
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 3 grid) column boundary)
      (quadrantAt column boundary) ≠ none)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 (column / 8))
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 (boundary / 8)) :
    ∃ family, ExactLowCanonicalCycleAncestorWithinFamily (iterateRefine 3 grid)
      (horizontalPort (iterateRefine 3 grid) column boundary)
      (column / 8) (boundary / 8)
      (outerLevel + 2) outerBlockX outerBlockY family := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.horizontalCreatedAtBlock
    (iterateRefine 1 grid) column boundary createdBoundary interior'
  have low : ExactLowCanonicalCycleAncestorWithin (iterateRefine 3 grid)
      (horizontalPort (iterateRefine 3 grid) column boundary)
      (column / 8) (boundary / 8)
      (outerLevel + 2) outerBlockX outerBlockY := by
    simpa only [hgrid] using
      ofLocalCycleRouteAtBlockWithinExactLow grid route xWithin yWithin
  exact ExactLowCanonicalCycleAncestorWithin.exists_family (ancestor := low)

/-- Compatibility projection of `horizontalCreatedWithinExact`. -/
theorem horizontalCreatedWithin
    (grid : Nat → Nat → Index) (column boundary : Nat)
    {outerLevel outerBlockX outerBlockY : Nat}
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 3 grid) column boundary)
      (quadrantAt column boundary) ≠ none)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 (column / 8))
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 (boundary / 8)) :
    ∃ family, LowCanonicalCycleAncestorWithinFamily (iterateRefine 3 grid)
      (horizontalPort (iterateRefine 3 grid) column boundary)
      (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases horizontalCreatedWithinExact grid column boundary createdBoundary
      interior xWithin yWithin with ⟨family, ancestor⟩
  exact ⟨family, ancestor.toLowFamily⟩

set_option maxHeartbeats 2000000 in
-- The translated selector depends on the equality between nested refinements.
/-- Vertical dual of `horizontalCreatedWithinExact`. -/
theorem verticalCreatedWithinExact
    (grid : Nat → Nat → Index) (boundary row : Nat)
    {outerLevel outerBlockX outerBlockY : Nat}
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 3 grid) boundary row)
      (quadrantAt boundary row) ≠ none)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 (boundary / 8))
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 (row / 8)) :
    ∃ family, ExactLowCanonicalCycleAncestorWithinFamily (iterateRefine 3 grid)
      (verticalPort (iterateRefine 3 grid) boundary row)
      (boundary / 8) (row / 8)
      (outerLevel + 2) outerBlockX outerBlockY family := by
  have hgrid : iterateRefine 2 (iterateRefine 1 grid) =
      iterateRefine 3 grid := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 grid
  have interior' : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (iterateRefine 1 grid)) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [hgrid]
    exact interior
  have route := PairCoverSeamResidualCycleLocalTransport.verticalCreatedAtBlock
    (iterateRefine 1 grid) boundary row createdBoundary interior'
  have low : ExactLowCanonicalCycleAncestorWithin (iterateRefine 3 grid)
      (verticalPort (iterateRefine 3 grid) boundary row)
      (boundary / 8) (row / 8)
      (outerLevel + 2) outerBlockX outerBlockY := by
    simpa only [hgrid] using
      ofLocalCycleRouteAtBlockWithinExactLow grid route xWithin yWithin
  exact ExactLowCanonicalCycleAncestorWithin.exists_family (ancestor := low)

/-- Compatibility projection of `verticalCreatedWithinExact`. -/
theorem verticalCreatedWithin
    (grid : Nat → Nat → Index) (boundary row : Nat)
    {outerLevel outerBlockX outerBlockY : Nat}
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 3 grid) boundary row)
      (quadrantAt boundary row) ≠ none)
    (xWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX 0 (boundary / 8))
    (yWithin : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY 0 (row / 8)) :
    ∃ family, LowCanonicalCycleAncestorWithinFamily (iterateRefine 3 grid)
      (verticalPort (iterateRefine 3 grid) boundary row)
      (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases verticalCreatedWithinExact grid boundary row createdBoundary
      interior xWithin yWithin with ⟨family, ancestor⟩
  exact ⟨family, ancestor.toLowFamily⟩

private def rootAt (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  iterateRefine (refinementDepth phase (depth + 1) - 1) grid

private theorem queryGrid_eq_rootAt
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      iterateRefine 3 (rootAt phase depth grid) := by
  unfold refinedGrid rootAt
  rw [PlaneRedBoards.iterateRefine_add,
    PlaneRedBoards.iterateRefine_add]
  congr 1
  simp only [refinementDepth]
  omega

private theorem outerLevel_succ (phase : Phase) (depth : Nat) :
    outerLevel phase depth + 2 = outerLevel phase (depth + 1) := by
  simp only [outerLevel]
  omega

private theorem inFineCollar
    {west east coordinate : Nat}
    (lower : quarterWest (4 * west) < coordinate)
    (upper : coordinate < quarterEast (4 * east)) :
    PairCoverSeamResidualCanonicalAncestorRecurrence.InCollar
      (4 * west) (4 * east) coordinate := by
  exact ⟨by omega, upper⟩

set_option maxHeartbeats 2000000 in
-- The source route is exposed through the root one level below the old grid.
/-- A created horizontal selector in a recurrence board reaches the exact
audited level-zero block or its level-one parent, retaining the hierarchy
family. -/
theorem horizontalCreatedAtExact
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (boundarySouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryNorth :
      boundary < quarterNorth (successorEast phase (depth + 1) parentY))
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) column boundary)
      (quadrantAt column boundary) ≠ none) :
    ∃ family, ExactLowCanonicalCycleAncestorWithinFamily
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (horizontalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (column / 8) (boundary / 8)
      (outerLevel phase (depth + 1)) parentX parentY family := by
  have westEq := successorWest_eq_canonical phase depth parentX
  have eastEq := successorEast_eq_canonical phase depth parentX
  have southEq := successorWest_eq_canonical phase depth parentY
  have northEq := successorEast_eq_canonical phase depth parentY
  rw [successorWest_succ] at columnWest boundarySouth
  rw [successorEast_succ] at columnEast boundaryNorth
  have xWithin := levelZeroWithin_of_fine_collar westEq eastEq
    (inFineCollar columnWest columnEast)
  have yWithin := levelZeroWithin_of_fine_collar southEq northEq
    (by simpa only [quarterSouth, quarterWest, quarterNorth, quarterEast]
      using inFineCollar boundarySouth boundaryNorth)
  have gridEq := queryGrid_eq_rootAt phase depth grid
  have result := horizontalCreatedWithinExact (rootAt phase depth grid)
    column boundary createdBoundary (by simpa only [gridEq] using interior)
    xWithin yWithin
  simpa only [gridEq, outerLevel_succ] using result

/-- Compatibility projection of `horizontalCreatedAtExact`. -/
theorem horizontalCreatedAt
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (boundarySouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryNorth :
      boundary < quarterNorth (successorEast phase (depth + 1) parentY))
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) column boundary)
      (quadrantAt column boundary) ≠ none) :
    ∃ family, LowCanonicalCycleAncestorWithinFamily
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (horizontalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (outerLevel phase (depth + 1)) parentX parentY family := by
  rcases horizontalCreatedAtExact phase depth grid parentX parentY
      columnWest columnEast boundarySouth boundaryNorth createdBoundary
      interior with ⟨family, ancestor⟩
  exact ⟨family, ancestor.toLowFamily⟩

set_option maxHeartbeats 2000000 in
-- The source route is exposed through the root one level below the old grid.
/-- Vertical dual of `horizontalCreatedAtExact`. -/
theorem verticalCreatedAtExact
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row : Nat}
    (boundaryWest :
      quarterWest (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryEast :
      boundary < quarterEast (successorEast phase (depth + 1) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) boundary row)
      (quadrantAt boundary row) ≠ none) :
    ∃ family, ExactLowCanonicalCycleAncestorWithinFamily
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (verticalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (boundary / 8) (row / 8)
      (outerLevel phase (depth + 1)) parentX parentY family := by
  have westEq := successorWest_eq_canonical phase depth parentX
  have eastEq := successorEast_eq_canonical phase depth parentX
  have southEq := successorWest_eq_canonical phase depth parentY
  have northEq := successorEast_eq_canonical phase depth parentY
  rw [successorWest_succ] at boundaryWest rowSouth
  rw [successorEast_succ] at boundaryEast rowNorth
  have xWithin := levelZeroWithin_of_fine_collar westEq eastEq
    (inFineCollar boundaryWest boundaryEast)
  have yWithin := levelZeroWithin_of_fine_collar southEq northEq
    (by simpa only [quarterSouth, quarterWest, quarterNorth, quarterEast]
      using inFineCollar rowSouth rowNorth)
  have gridEq := queryGrid_eq_rootAt phase depth grid
  have result := verticalCreatedWithinExact (rootAt phase depth grid)
    boundary row createdBoundary (by simpa only [gridEq] using interior)
    xWithin yWithin
  simpa only [gridEq, outerLevel_succ] using result

/-- Compatibility projection of `verticalCreatedAtExact`. -/
theorem verticalCreatedAt
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {boundary row : Nat}
    (boundaryWest :
      quarterWest (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryEast :
      boundary < quarterEast (successorEast phase (depth + 1) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (createdBoundary : ¬ IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2
        (refinedGrid phase (depth + 1) grid)) boundary row)
      (quadrantAt boundary row) ≠ none) :
    ∃ family, LowCanonicalCycleAncestorWithinFamily
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (verticalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (outerLevel phase (depth + 1)) parentX parentY family := by
  rcases verticalCreatedAtExact phase depth grid parentX parentY
      boundaryWest boundaryEast rowSouth rowNorth createdBoundary interior with
    ⟨family, ancestor⟩
  exact ⟨family, ancestor.toLowFamily⟩

end PairCoverSeamCreatedLowFamilyAncestors
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
