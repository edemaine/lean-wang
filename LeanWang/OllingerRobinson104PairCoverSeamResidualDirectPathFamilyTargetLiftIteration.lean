/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence

/-!
# All-depth iteration of residual family targets

The proof-producing two-substitution audit can be iterated without repeating
any finite search.  A final query coordinate need only project to the original
coordinate after the requested number of coarse-coordinate steps.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftIteration

open PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyTargetLiftRecurrence
  PairCoverSeamResidualDirectPathTargets RedShadeGraphRefinement
  RefinedCoordinateProjection

set_option maxRecDepth 20000

/-- Repeated coarse-coordinate projection through two substitutions. -/
def iteratedCoarseCoordinate : Nat → Nat → Nat
  | 0, coordinate => coordinate
  | depth + 1, coordinate =>
      iteratedCoarseCoordinate depth (coarseCoordinate coordinate)

/-- Repeated literal sparse embedding through two substitutions. -/
def iteratedSparseCoordinate : Nat → Nat → Nat
  | 0, coordinate => coordinate
  | depth + 1, coordinate =>
      sparseCoordinate (iteratedSparseCoordinate depth coordinate)

/-- The hierarchy level after repeated two-substitution refinement. -/
def iteratedOuterLevel : Nat → Nat → Nat
  | 0, level => level
  | depth + 1, level => iteratedOuterLevel depth level + 2

/-- A board-coordinate bound after repeated two-substitution refinement. -/
def iteratedScale : Nat → Nat → Nat
  | 0, coordinate => coordinate
  | depth + 1, coordinate => 4 * iteratedScale depth coordinate

theorem iteratedOuterLevel_eq (depth level : Nat) :
    iteratedOuterLevel depth level = level + 2 * depth := by
  induction depth with
  | zero => simp [iteratedOuterLevel]
  | succ depth ih => simp [iteratedOuterLevel, ih, Nat.mul_succ]; omega

theorem iteratedScale_eq (depth coordinate : Nat) :
    iteratedScale depth coordinate = 4 ^ depth * coordinate := by
  induction depth with
  | zero => simp [iteratedScale]
  | succ depth ih =>
      simp only [iteratedScale, ih, pow_succ]
      ring

set_option maxHeartbeats 1000000 in
-- Dependent family endpoints are normalized after each refinement step.
/-- Transport a row target through any number of hierarchy refinements. -/
theorem RowFamilyTarget.refineIterate
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary fineColumn fineRow : Nat}
    {family : HierarchyFamily}
    (target : RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family)
    (depth : Nat)
    (columnCoarse : iteratedCoarseCoordinate depth fineColumn = column)
    (rowCoarse : iteratedCoarseCoordinate depth fineRow = row) :
    RowFamilyTarget root (iteratedOuterLevel depth outerLevel)
      outerBlockX outerBlockY
      (iteratedScale depth outerWest) (iteratedScale depth outerEast)
      fineColumn fineRow (iteratedSparseCoordinate depth boundary) family := by
  induction depth generalizing fineColumn fineRow with
  | zero =>
      simp only [iteratedCoarseCoordinate] at columnCoarse rowCoarse
      subst fineColumn
      subst fineRow
      simpa [iteratedSparseCoordinate, iteratedOuterLevel, iteratedScale]
        using target
  | succ depth ih =>
      have coarseTarget := ih
        (fineColumn := coarseCoordinate fineColumn)
        (fineRow := coarseCoordinate fineRow)
        (by simpa [iteratedCoarseCoordinate] using columnCoarse)
        (by simpa [iteratedCoarseCoordinate] using rowCoarse)
      have refined := RowFamilyTarget.refineAt coarseTarget
        (fineColumn := fineColumn) (fineRow := fineRow) rfl rfl
      exact refined

set_option maxHeartbeats 1000000 in
-- Dependent family endpoints are normalized after each refinement step.
/-- Column-dual all-depth target transport. -/
theorem ColumnFamilyTarget.refineIterate
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary fineRow fineColumn : Nat}
    {family : HierarchyFamily}
    (target : ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family)
    (depth : Nat)
    (rowCoarse : iteratedCoarseCoordinate depth fineRow = row)
    (columnCoarse : iteratedCoarseCoordinate depth fineColumn = column) :
    ColumnFamilyTarget root (iteratedOuterLevel depth outerLevel)
      outerBlockX outerBlockY
      (iteratedScale depth outerSouth) (iteratedScale depth outerNorth)
      fineRow fineColumn (iteratedSparseCoordinate depth boundary) family := by
  induction depth generalizing fineRow fineColumn with
  | zero =>
      simp only [iteratedCoarseCoordinate] at rowCoarse columnCoarse
      subst fineRow
      subst fineColumn
      simpa [iteratedSparseCoordinate, iteratedOuterLevel, iteratedScale]
        using target
  | succ depth ih =>
      have coarseTarget := ih
        (fineRow := coarseCoordinate fineRow)
        (fineColumn := coarseCoordinate fineColumn)
        (by simpa [iteratedCoarseCoordinate] using rowCoarse)
        (by simpa [iteratedCoarseCoordinate] using columnCoarse)
      have refined := ColumnFamilyTarget.refineAt coarseTarget
        (fineRow := fineRow) (fineColumn := fineColumn) rfl rfl
      exact refined

end PairCoverSeamResidualDirectPathFamilyTargetLiftIteration
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
