/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathAllFamilyTargets

/-!
# Seam paths from projection-closed family targets

Unlike `FamilyTargetsAt`, the projection-closed target state does not require
the free-line coordinate to be created.  Its same-family witnesses therefore
give direct seam paths for every query with a sparse selected boundary.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargets

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPaths
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathTargets
  PairCoverSeamResidualCanonicalAncestorHierarchy
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

private theorem fineGrid_eq
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  unfold refinedGrid
  rw [PlaneRedBoards.iterateRefine_add]
  unfold outerLevel refinementDepth
  congr 1
  omega

set_option maxRecDepth 20000 in
/-- A projection-closed row target supplies its direct vertical seam path. -/
theorem AllFamilyTargetsAt.verticalPath
    {phase : Phase} {depth : Nat}
    (targets : AllFamilyTargetsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (boundarySouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryNorth :
      boundary < quarterNorth (successorEast phase (depth + 1) parentY))
    (notFits : ¬FitsContainedVerticalChild phase (depth + 1)
      parentX parentY column row boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .north)) :
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary := by
  rcases targets.row grid parentX parentY columnWest columnEast
      rowSouth rowNorth boundarySouth boundaryNorth notFits sparseBoundary
      wrongFacing with ⟨family, sourceFamily, target⟩
  rw [fineGrid_eq phase depth grid]
  rcases target with target | target
  · rcases target with
      ⟨targetX, targetWest, targetEast, targetInterior, targetFamily⟩
    exact verticalSeamPath_of_sameFamilyTarget rfl sourceFamily targetFamily
      targetWest targetEast targetInterior
  · rcases target with ⟨targetY, between, targetInterior, targetFamily⟩
    exact verticalSeamPath_of_sameFamilyBetweenTarget rfl sourceFamily
      targetFamily between targetInterior

set_option maxRecDepth 20000 in
/-- Column-dual direct seam path from a projection-closed target. -/
theorem AllFamilyTargetsAt.horizontalPath
    {phase : Phase} {depth : Nat}
    (targets : AllFamilyTargetsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (boundaryWest :
      quarterWest (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryEast :
      boundary < quarterEast (successorEast phase (depth + 1) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 1)
      parentX parentY column row boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .east)) :
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary := by
  rcases targets.column grid parentX parentY columnWest columnEast
      boundaryWest boundaryEast rowSouth rowNorth notFits sparseBoundary
      wrongFacing with ⟨family, sourceFamily, target⟩
  rw [fineGrid_eq phase depth grid]
  rcases target with target | target
  · rcases target with
      ⟨targetY, targetSouth, targetNorth, targetInterior, targetFamily⟩
    exact horizontalSeamPath_of_sameFamilyTarget rfl sourceFamily targetFamily
      targetSouth targetNorth targetInterior
  · rcases target with ⟨targetX, between, targetInterior, targetFamily⟩
    exact horizontalSeamPath_of_sameFamilyBetweenTarget rfl sourceFamily
      targetFamily between targetInterior

end PairCoverSeamResidualDirectPathAllFamilyTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
