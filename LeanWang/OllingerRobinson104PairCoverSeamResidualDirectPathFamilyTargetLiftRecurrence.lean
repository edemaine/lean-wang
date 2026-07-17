/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftTransport
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Semantic recurrence from transported family-target lifts

Each constructor below lifts one of the two alternatives in `RowFamilyTarget`
or `ColumnFamilyTarget` to arbitrary fine query coordinates.  The finite audit
is restricted to coordinates selected by the old target's sparse interval, so
the constructors apply uniformly to all 104 parent tiles.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyTargetRecurrence
  PairCoverSeamResidualDirectPathFamilyTargetLiftTransport
  PairCoverSeamResidualDirectPathTargets
  RefinedCoordinateProjection Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem refinedGrid_eq
    (root : Nat → Nat → Index) (outerLevel : Nat) :
    iterateRefine 2 (iterateRefine (outerLevel + 2) root) =
      iterateRefine (outerLevel + 2 + 2) root := by
  rw [PlaneRedBoards.iterateRefine_add]
  congr 1
  omega

set_option maxHeartbeats 1000000 in
-- The family witness contains a dependent refined-grid endpoint.
/-- Lift the transverse vertical alternative of a row target. -/
theorem RowFamilyTarget.ofVerticalLift
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {fineColumn fineRow fineBoundary oldRow targetX : Nat}
    {family : HierarchyFamily}
    (rowCoarse : coarseCoordinate fineRow = oldRow)
    (targetWest : quarterWest outerWest < targetX)
    (targetEast : targetX < quarterEast outerEast)
    (targetInterior : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX oldRow)
      (quadrantAt targetX oldRow) ≠ none)
    (targetFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX oldRow)
      outerLevel outerBlockX outerBlockY family) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow fineBoundary family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  rcases verticalTargetFamily oldGrid targetX oldRow fineRow rowCoarse
      (by simpa only [oldGrid] using targetInterior)
      (by simpa only [oldGrid] using targetFamily) with
    ⟨fineTargetX, targetCoarse, fineInterior, fineFamily⟩
  have targetBounds := fine_board_bounds_of_coarse_bounds
    (coordinate := fineTargetX) (by simpa only [targetCoarse] using targetWest)
    (by simpa only [targetCoarse] using targetEast)
  left
  refine ⟨fineTargetX, targetBounds.1, targetBounds.2, ?_, ?_⟩
  · rw [← refinedGrid_eq root outerLevel]
    exact fineInterior
  · rw [← refinedGrid_eq root outerLevel]
    exact fineFamily

set_option maxHeartbeats 1000000 in
-- The family witness contains a dependent refined-grid endpoint.
/-- Lift the parallel horizontal alternative of a row target. -/
theorem RowFamilyTarget.ofHorizontalLift
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {oldColumn oldRow oldBoundary targetY fineColumn fineRow : Nat}
    {family : HierarchyFamily}
    (columnCoarse : coarseCoordinate fineColumn = oldColumn)
    (rowCoarse : coarseCoordinate fineRow = oldRow)
    (between : StrictBetween oldRow oldBoundary targetY)
    (targetInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) oldColumn targetY)
      (quadrantAt oldColumn targetY) ≠ none)
    (targetFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) oldColumn targetY)
      outerLevel outerBlockX outerBlockY family) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow (sparseCoordinate oldBoundary) family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  rcases horizontalTargetFamily oldGrid oldColumn targetY fineColumn columnCoarse
      (by simpa only [oldGrid] using targetInterior)
      (by simpa only [oldGrid] using targetFamily) with
    ⟨fineTargetY, targetCoarse, fineInterior, fineFamily⟩
  right
  refine ⟨fineTargetY,
    strictBetween_of_coarseCoordinates rowCoarse targetCoarse between, ?_, ?_⟩
  · rw [← refinedGrid_eq root outerLevel]
    exact fineInterior
  · rw [← refinedGrid_eq root outerLevel]
    exact fineFamily

set_option maxHeartbeats 1000000 in
-- The family witness contains a dependent refined-grid endpoint.
/-- Lift the parallel horizontal alternative when the fine boundary is an
arbitrary point of the old boundary's coarse interval. -/
theorem RowFamilyTarget.ofHorizontalLiftAtBoundary
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {oldColumn oldRow oldBoundary targetY fineColumn fineRow fineBoundary : Nat}
    {family : HierarchyFamily}
    (columnCoarse : coarseCoordinate fineColumn = oldColumn)
    (rowCoarse : coarseCoordinate fineRow = oldRow)
    (boundaryCoarse : coarseCoordinate fineBoundary = oldBoundary)
    (between : StrictBetween oldRow oldBoundary targetY)
    (targetInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) oldColumn targetY)
      (quadrantAt oldColumn targetY) ≠ none)
    (targetFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) oldColumn targetY)
      outerLevel outerBlockX outerBlockY family) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow fineBoundary family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  rcases horizontalTargetFamily oldGrid oldColumn targetY fineColumn columnCoarse
      (by simpa only [oldGrid] using targetInterior)
      (by simpa only [oldGrid] using targetFamily) with
    ⟨fineTargetY, targetCoarse, fineInterior, fineFamily⟩
  right
  refine ⟨fineTargetY,
    strictBetween_of_threeCoarseCoordinates rowCoarse boundaryCoarse
      targetCoarse between, ?_, ?_⟩
  · rw [← refinedGrid_eq root outerLevel]
    exact fineInterior
  · rw [← refinedGrid_eq root outerLevel]
    exact fineFamily

set_option maxHeartbeats 1000000 in
-- The family witness contains a dependent refined-grid endpoint.
/-- Lift the transverse horizontal alternative of a column target. -/
theorem ColumnFamilyTarget.ofHorizontalLift
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {oldColumn targetY fineColumn fineRow fineBoundary : Nat}
    {family : HierarchyFamily}
    (columnCoarse : coarseCoordinate fineColumn = oldColumn)
    (targetSouth : quarterSouth outerSouth < targetY)
    (targetNorth : targetY < quarterNorth outerNorth)
    (targetInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) oldColumn targetY)
      (quadrantAt oldColumn targetY) ≠ none)
    (targetFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) oldColumn targetY)
      outerLevel outerBlockX outerBlockY family) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn fineBoundary family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  rcases horizontalTargetFamily oldGrid oldColumn targetY fineColumn columnCoarse
      (by simpa only [oldGrid] using targetInterior)
      (by simpa only [oldGrid] using targetFamily) with
    ⟨fineTargetY, targetCoarse, fineInterior, fineFamily⟩
  have targetBounds := fine_board_bounds_of_coarse_bounds
    (coordinate := fineTargetY)
    (by
      simpa only [quarterWest, quarterSouth, targetCoarse] using targetSouth)
    (by
      simpa only [quarterEast, quarterNorth, targetCoarse] using targetNorth)
  left
  refine ⟨fineTargetY, ?_, ?_, ?_, ?_⟩
  · simpa only [quarterWest, quarterSouth] using targetBounds.1
  · simpa only [quarterEast, quarterNorth] using targetBounds.2
  · rw [← refinedGrid_eq root outerLevel]
    exact fineInterior
  · rw [← refinedGrid_eq root outerLevel]
    exact fineFamily

set_option maxHeartbeats 1000000 in
-- The family witness contains a dependent refined-grid endpoint.
/-- Lift the parallel vertical alternative of a column target. -/
theorem ColumnFamilyTarget.ofVerticalLift
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {oldRow oldColumn oldBoundary targetX fineRow fineColumn : Nat}
    {family : HierarchyFamily}
    (rowCoarse : coarseCoordinate fineRow = oldRow)
    (columnCoarse : coarseCoordinate fineColumn = oldColumn)
    (between : StrictBetween oldColumn oldBoundary targetX)
    (targetInterior : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX oldRow)
      (quadrantAt targetX oldRow) ≠ none)
    (targetFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX oldRow)
      outerLevel outerBlockX outerBlockY family) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn (sparseCoordinate oldBoundary) family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  rcases verticalTargetFamily oldGrid targetX oldRow fineRow rowCoarse
      (by simpa only [oldGrid] using targetInterior)
      (by simpa only [oldGrid] using targetFamily) with
    ⟨fineTargetX, targetCoarse, fineInterior, fineFamily⟩
  right
  refine ⟨fineTargetX,
    strictBetween_of_coarseCoordinates columnCoarse targetCoarse between,
    ?_, ?_⟩
  · rw [← refinedGrid_eq root outerLevel]
    exact fineInterior
  · rw [← refinedGrid_eq root outerLevel]
    exact fineFamily

set_option maxHeartbeats 1000000 in
-- The family witness contains a dependent refined-grid endpoint.
/-- Lift the parallel vertical alternative when the fine boundary is an
arbitrary point of the old boundary's coarse interval. -/
theorem ColumnFamilyTarget.ofVerticalLiftAtBoundary
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {oldRow oldColumn oldBoundary targetX fineRow fineColumn fineBoundary : Nat}
    {family : HierarchyFamily}
    (rowCoarse : coarseCoordinate fineRow = oldRow)
    (columnCoarse : coarseCoordinate fineColumn = oldColumn)
    (boundaryCoarse : coarseCoordinate fineBoundary = oldBoundary)
    (between : StrictBetween oldColumn oldBoundary targetX)
    (targetInterior : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX oldRow)
      (quadrantAt targetX oldRow) ≠ none)
    (targetFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX oldRow)
      outerLevel outerBlockX outerBlockY family) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn fineBoundary family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  rcases verticalTargetFamily oldGrid targetX oldRow fineRow rowCoarse
      (by simpa only [oldGrid] using targetInterior)
      (by simpa only [oldGrid] using targetFamily) with
    ⟨fineTargetX, targetCoarse, fineInterior, fineFamily⟩
  right
  refine ⟨fineTargetX,
    strictBetween_of_threeCoarseCoordinates columnCoarse boundaryCoarse
      targetCoarse between, ?_, ?_⟩
  · rw [← refinedGrid_eq root outerLevel]
    exact fineInterior
  · rw [← refinedGrid_eq root outerLevel]
    exact fineFamily

set_option maxHeartbeats 1000000 in
-- Each target alternative contains a dependent refined-grid family endpoint.
/-- Lift an arbitrary row target to fine query coordinates selected by the
coarse-coordinate projection. -/
theorem RowFamilyTarget.refineAt
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary fineColumn fineRow : Nat}
    {family : HierarchyFamily}
    (target : RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family)
    (columnCoarse : coarseCoordinate fineColumn = column)
    (rowCoarse : coarseCoordinate fineRow = row) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow (sparseCoordinate boundary) family := by
  rcases target with target | target
  · rcases target with
      ⟨targetX, targetWest, targetEast, targetInterior, targetFamily⟩
    exact RowFamilyTarget.ofVerticalLift rowCoarse targetWest targetEast
      targetInterior targetFamily
  · rcases target with ⟨targetY, between, targetInterior, targetFamily⟩
    exact RowFamilyTarget.ofHorizontalLift columnCoarse rowCoarse between
      targetInterior targetFamily

set_option maxHeartbeats 1000000 in
-- Each target alternative contains a dependent refined-grid family endpoint.
/-- Lift a row target when all three fine query coordinates are arbitrary
points of their old coarse intervals. -/
theorem RowFamilyTarget.refineAtBoundary
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary fineColumn fineRow fineBoundary : Nat}
    {family : HierarchyFamily}
    (target : RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family)
    (columnCoarse : coarseCoordinate fineColumn = column)
    (rowCoarse : coarseCoordinate fineRow = row)
    (boundaryCoarse : coarseCoordinate fineBoundary = boundary) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow fineBoundary family := by
  rcases target with target | target
  · rcases target with
      ⟨targetX, targetWest, targetEast, targetInterior, targetFamily⟩
    exact RowFamilyTarget.ofVerticalLift rowCoarse targetWest targetEast
      targetInterior targetFamily
  · rcases target with ⟨targetY, between, targetInterior, targetFamily⟩
    exact RowFamilyTarget.ofHorizontalLiftAtBoundary columnCoarse rowCoarse
      boundaryCoarse between targetInterior targetFamily

set_option maxHeartbeats 1000000 in
-- Each target alternative contains a dependent refined-grid family endpoint.
/-- Column-dual arbitrary-coordinate target refinement. -/
theorem ColumnFamilyTarget.refineAt
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary fineRow fineColumn : Nat}
    {family : HierarchyFamily}
    (target : ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family)
    (rowCoarse : coarseCoordinate fineRow = row)
    (columnCoarse : coarseCoordinate fineColumn = column) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn (sparseCoordinate boundary) family := by
  rcases target with target | target
  · rcases target with
      ⟨targetY, targetSouth, targetNorth, targetInterior, targetFamily⟩
    exact ColumnFamilyTarget.ofHorizontalLift columnCoarse targetSouth
      targetNorth targetInterior targetFamily
  · rcases target with ⟨targetX, between, targetInterior, targetFamily⟩
    exact ColumnFamilyTarget.ofVerticalLift rowCoarse columnCoarse between
      targetInterior targetFamily

set_option maxHeartbeats 1000000 in
-- Each target alternative contains a dependent refined-grid family endpoint.
/-- Column-dual target lift with an arbitrary fine selected boundary. -/
theorem ColumnFamilyTarget.refineAtBoundary
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary fineRow fineColumn fineBoundary : Nat}
    {family : HierarchyFamily}
    (target : ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family)
    (rowCoarse : coarseCoordinate fineRow = row)
    (columnCoarse : coarseCoordinate fineColumn = column)
    (boundaryCoarse : coarseCoordinate fineBoundary = boundary) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn fineBoundary family := by
  rcases target with target | target
  · rcases target with
      ⟨targetY, targetSouth, targetNorth, targetInterior, targetFamily⟩
    exact ColumnFamilyTarget.ofHorizontalLift columnCoarse targetSouth
      targetNorth targetInterior targetFamily
  · rcases target with ⟨targetX, between, targetInterior, targetFamily⟩
    exact ColumnFamilyTarget.ofVerticalLiftAtBoundary rowCoarse columnCoarse
      boundaryCoarse between targetInterior targetFamily

end PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
