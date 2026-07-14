/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Recover same-family targets from direct seam paths

The created-coordinate audits already produce even seam paths.  Reversing the
accepted path transports the source's hierarchy-family ancestor to its target,
so those audits can seed the target recurrence without another family search.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetOfPath

open RedCycles RedShadeGraph RedShadeGraphRefinement PairCoverSeamPathSearch
  PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathTargets

/-- An even vertical seam path from a family-tagged horizontal source records
exactly a row target in that family. -/
theorem RowFamilyTarget.ofVerticalSeamPath
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary : Nat} {family : HierarchyFamily}
    (sourceFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) column boundary)
      outerLevel outerBlockX outerBlockY family)
    (path : VerticalSeamPath (iterateRefine (outerLevel + 2) root)
      outerWest outerEast column row boundary) :
    RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family := by
  rcases path with path | path
  · rcases path with
      ⟨targetX, targetWest, targetEast, targetInterior, connector⟩
    left
    exact ⟨targetX, targetWest, targetEast, targetInterior,
      sourceFamily.of_evenPath (path_symm connector)⟩
  · rcases path with ⟨targetY, between, targetInterior, connector⟩
    right
    exact ⟨targetY, between, targetInterior,
      sourceFamily.of_evenPath (path_symm connector)⟩

/-- Column-dual conversion from an even horizontal seam path. -/
theorem ColumnFamilyTarget.ofHorizontalSeamPath
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary : Nat} {family : HierarchyFamily}
    (sourceFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) boundary row)
      outerLevel outerBlockX outerBlockY family)
    (path : HorizontalSeamPath (iterateRefine (outerLevel + 2) root)
      outerSouth outerNorth row column boundary) :
    ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family := by
  rcases path with path | path
  · rcases path with
      ⟨targetY, targetSouth, targetNorth, targetInterior, connector⟩
    left
    exact ⟨targetY, targetSouth, targetNorth, targetInterior,
      sourceFamily.of_evenPath (path_symm connector)⟩
  · rcases path with ⟨targetX, between, targetInterior, connector⟩
    right
    exact ⟨targetX, between, targetInterior,
      sourceFamily.of_evenPath (path_symm connector)⟩

end PairCoverSeamResidualDirectPathFamilyTargetOfPath
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
