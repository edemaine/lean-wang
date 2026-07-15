/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathBridges

/-!
# Low family ancestors for created selectors

The created-selector audit reaches the local level-zero cell cycle with an
arbitrary route parity.  Parity normalization either stays at level zero or
crosses to its level-one parent.  These wrappers retain that low-level fact
together with the resulting even/odd hierarchy family.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedLowFamilyAncestors

open RedCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamShadePaths PairCoverSeamResidualCycleLocalTransport
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualDirectPathBridges RefinedCoordinateProjection
  Signals.FreeCellLocal

set_option maxHeartbeats 2000000 in
-- The translated selector depends on the equality between nested refinements.
/-- A horizontal created selector reaches a level-zero or level-one cycle in a
named hierarchy family. -/
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
  have low : LowCanonicalCycleAncestorWithin (iterateRefine 3 grid)
      (horizontalPort (iterateRefine 3 grid) column boundary)
      (outerLevel + 2) outerBlockX outerBlockY := by
    simpa only [hgrid] using
      ofLocalCycleRouteAtBlockWithinLow grid route xWithin yWithin
  exact LowCanonicalCycleAncestorWithin.exists_family (ancestor := low)

set_option maxHeartbeats 2000000 in
-- The translated selector depends on the equality between nested refinements.
/-- Vertical dual of `horizontalCreatedWithin`. -/
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
  have low : LowCanonicalCycleAncestorWithin (iterateRefine 3 grid)
      (verticalPort (iterateRefine 3 grid) boundary row)
      (outerLevel + 2) outerBlockX outerBlockY := by
    simpa only [hgrid] using
      ofLocalCycleRouteAtBlockWithinLow grid route xWithin yWithin
  exact LowCanonicalCycleAncestorWithin.exists_family (ancestor := low)

end PairCoverSeamCreatedLowFamilyAncestors
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
