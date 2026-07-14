/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamPathEvenBase
import LeanWang.OllingerRobinson104PairCoverSeamPathOddBase
import LeanWang.OllingerRobinson104PairCoverSeamPathTranslation
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetOfPath

/-!
# Cached seam-path bases as same-family target seeds

The complete bounded seam-path certificates at the even and odd base depths
already select a usable endpoint for every wrong-facing residual query.  This
module converts those endpoints into the family-target interface used by the
all-depth recurrence, without running a new family search.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetPathBase

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamPathBoundedBase
  PairCoverSeamShadePaths PairCoverSeamPathTranslation
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathTargets
  PairCoverSeamResidualDirectPathFamilyTargetOfPath
  PairCoverSeamResidualCanonicalAncestorHierarchy
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem fineGrid_eq_outerLevel
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase depth grid) =
      iterateRefine (outerLevel phase depth + 2) grid := by
  calc
    _ = iterateRefine (refinementDepth phase depth + 2) grid :=
      PairCoverSeamPathTranslation.globalGrid_eq_total phase depth grid
    _ = _ := by
      congr 1
      simp only [outerLevel, refinementDepth]
      omega

/-- A bounded seam-path base supplies a row target in the source's exact
hierarchy family. -/
theorem BoundedPaths.rowFamilyTarget
    {phase : Phase} {depth : Nat} (paths : BoundedPaths phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat} {family : HierarchyFamily}
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (hboundarySouth :
      quarterSouth (successorWest phase depth parentY) < boundary)
    (hboundaryNorth :
      boundary < quarterNorth (successorEast phase depth parentY))
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            column boundary)
          (quadrantAt column boundary) = some .north))
    (notFits : ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary)
    (sourceFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel phase depth + 2) grid)
      (horizontalPort (iterateRefine (outerLevel phase depth + 2) grid)
        column boundary)
      (outerLevel phase depth) parentX parentY family) :
    RowFamilyTarget grid (outerLevel phase depth) parentX parentY
      (successorWest phase depth parentX) (successorEast phase depth parentX)
      column row boundary family := by
  have path := PairCoverSeamPathTranslation.BoundedPaths.verticalSeamPath
    paths grid parentX parentY
    hcolumnWest hcolumnEast hrowSouth hrowNorth
    hboundarySouth hboundaryNorth
    (by simpa [fineGrid_eq_outerLevel phase depth grid] using wrongFacing)
    notFits
  rw [fineGrid_eq_outerLevel phase depth grid] at path
  exact RowFamilyTarget.ofVerticalSeamPath sourceFamily path

/-- Column-dual conversion of a bounded seam-path base. -/
theorem BoundedPaths.columnFamilyTarget
    {phase : Phase} {depth : Nat} (paths : BoundedPaths phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat} {family : HierarchyFamily}
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hboundaryWest :
      quarterWest (successorWest phase depth parentX) < boundary)
    (hboundaryEast :
      boundary < quarterEast (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            boundary row)
          (quadrantAt boundary row) = some .east))
    (notFits : ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary)
    (sourceFamily : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel phase depth + 2) grid)
      (verticalPort (iterateRefine (outerLevel phase depth + 2) grid)
        boundary row)
      (outerLevel phase depth) parentX parentY family) :
    ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
      (successorWest phase depth parentY) (successorEast phase depth parentY)
      row column boundary family := by
  have path := PairCoverSeamPathTranslation.BoundedPaths.horizontalSeamPath
    paths grid parentX parentY
    hcolumnWest hcolumnEast hrowSouth hrowNorth
    hboundaryWest hboundaryEast
    (by simpa [fineGrid_eq_outerLevel phase depth grid] using wrongFacing)
    notFits
  rw [fineGrid_eq_outerLevel phase depth grid] at path
  exact ColumnFamilyTarget.ofHorizontalSeamPath sourceFamily path

/-- The cached even target seed is available at recurrence depth one. -/
def evenPaths : BoundedPaths .even 1 :=
  PairCoverSeamPathEvenBase.boundedPaths

/-- The cached odd target seed is available at recurrence depth zero. -/
def oddPaths : BoundedPaths .odd 0 :=
  PairCoverSeamPathOddBase.boundedPaths

end PairCoverSeamResidualDirectPathFamilyTargetPathBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
