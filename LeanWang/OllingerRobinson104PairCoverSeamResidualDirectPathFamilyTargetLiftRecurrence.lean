/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftTransport

/-!
# Semantic recurrence from transported family-target lifts

Each constructor below lifts one of the two alternatives in `RowFamilyTarget`
or `ColumnFamilyTarget` to arbitrary fine query coordinates.  It asks only
that the single macrocell containing the selected old target is outside the
eight exceptional parent tiles.
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
      outerLevel outerBlockX outerBlockY family)
    (nonexceptional : 8 ≤
      (iterateRefine (outerLevel + 2) root (targetX / 2) (oldRow / 2)).val) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow fineBoundary family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  have sameBlock : oldRow / 2 = fineRow / 8 :=
    div_two_eq_div_eight_of_coarseCoordinate rowCoarse
  rcases verticalTargetFamily oldGrid targetX oldRow fineRow sameBlock
      (by simpa only [oldGrid] using nonexceptional)
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
      outerLevel outerBlockX outerBlockY family)
    (nonexceptional : 8 ≤
      (iterateRefine (outerLevel + 2) root
        (oldColumn / 2) (targetY / 2)).val) :
    RowFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerWest) (4 * outerEast)
      fineColumn fineRow (sparseCoordinate oldBoundary) family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  have sameBlock : oldColumn / 2 = fineColumn / 8 :=
    div_two_eq_div_eight_of_coarseCoordinate columnCoarse
  rcases horizontalTargetFamily oldGrid oldColumn targetY fineColumn sameBlock
      (by simpa only [oldGrid] using nonexceptional)
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
      outerLevel outerBlockX outerBlockY family)
    (nonexceptional : 8 ≤
      (iterateRefine (outerLevel + 2) root
        (oldColumn / 2) (targetY / 2)).val) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn fineBoundary family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  have sameBlock : oldColumn / 2 = fineColumn / 8 :=
    div_two_eq_div_eight_of_coarseCoordinate columnCoarse
  rcases horizontalTargetFamily oldGrid oldColumn targetY fineColumn sameBlock
      (by simpa only [oldGrid] using nonexceptional)
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
      outerLevel outerBlockX outerBlockY family)
    (nonexceptional : 8 ≤
      (iterateRefine (outerLevel + 2) root (targetX / 2) (oldRow / 2)).val) :
    ColumnFamilyTarget root (outerLevel + 2) outerBlockX outerBlockY
      (4 * outerSouth) (4 * outerNorth)
      fineRow fineColumn (sparseCoordinate oldBoundary) family := by
  let oldGrid := iterateRefine (outerLevel + 2) root
  have sameBlock : oldRow / 2 = fineRow / 8 :=
    div_two_eq_div_eight_of_coarseCoordinate rowCoarse
  rcases verticalTargetFamily oldGrid targetX oldRow fineRow sameBlock
      (by simpa only [oldGrid] using nonexceptional)
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

end PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
