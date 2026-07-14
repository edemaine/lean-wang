/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorQueryCases
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetPathBase

/-!
# Odd depth-zero family targets

One exact predecessor step reduces every odd depth-one residual query to the
cached odd depth-zero path base.  Strict projected queries use the cached
paths directly; lower-edge and source-boundary cases use the certified
exceptional target base.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyOddBase

open RedCycles RedShadeCycles RedShadeGraphRefinement PairCoverSeamArithmetic
  PairCoverSeamPathBoundedBase PairCoverSeamRefinementCoordinates
  PairCoverSeamRefinementQueryCases
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathExactPredecessorHierarchy
  PairCoverSeamResidualDirectPathExactPredecessorQueryCases
  PairCoverSeamResidualDirectPathFamilyExceptionalBase
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport
  PairCoverSeamResidualDirectPathFamilyTargetPathBase
  PairCoverSeamResidualDirectPathTargets RefinedCoordinateProjection
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem oldGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 1) grid =
      iterateRefine (outerLevel phase depth + 2) grid := by
  unfold refinedGrid
  congr 1

private theorem fineGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 2) grid =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  unfold refinedGrid
  congr 1

private theorem queryGrid_eq_fineGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      refinedGrid phase (depth + 2) grid :=
  (SparseFreeLinePlaneLocalStep.refinedGrid_succ
    phase (depth + 1) grid).symm

set_option maxHeartbeats 2000000 in
-- The selected family depends on the exact predecessor and projected case.
/-- Every odd depth-one residual query has a same-family endpoint target. -/
theorem oddFamilyTargets : FamilyTargetsAt .odd 0 := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary _createdRow wrongFacing
    have wrongFacingFine := wrongFacing
    rw [queryGrid_eq_fineGrid .odd 0 grid] at wrongFacingFine
    have sourceInterior : Signals.horizontalInterior?
        (componentAt (refinedGrid .odd 2 grid) column boundary)
        (quadrantAt column boundary) ≠ none := by
      rcases wrongFacingFine with south | north
      · rw [south.2]
        simp
      · rw [north.2]
        simp
    rcases horizontalExactInheritedSource .odd 0 grid parentX parentY
      columnWest columnEast boundarySouth boundaryNorth sparseBoundary
      sourceInterior with ⟨source⟩
    have projected := HorizontalExactInheritedSource.projectedQuery
      source rowSouth rowNorth wrongFacingFine
    have boundaryCoarse : coarseCoordinate boundary = source.oldBoundary := by
      calc
        _ = coarseCoordinate (sparseCoordinate source.oldBoundary) :=
          congrArg coarseCoordinate source.boundarySparse.symm
        _ = _ := coarseCoordinate_sparseCoordinate source.oldBoundary
    have notFitsCoarse : ¬FitsContainedVerticalChild .odd 0 parentX parentY
        (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary := by
      simpa only [boundaryCoarse] using
        notFitsContainedVerticalChild_coarseCoordinate notFits
    rcases projected with below | above
    · rcases below.1 with ⟨queryEq, queryBelow⟩ |
        ⟨queryLower, queryUpper, queryBelow⟩
      · have orientation := below.2
        rw [oldGrid_eq_outerGrid] at orientation
        rcases BoundedExceptionalTargetsAt.translateRowSouthLower
            oddTargets grid parentX parentY
            source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 orientation with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid] at oldFamily'
        have target' : RowFamilyTarget grid (outerLevel .odd 0)
            parentX parentY (successorWest .odd 0 parentX)
            (successorEast .odd 0 parentX) (coarseCoordinate column)
            (coarseCoordinate row) source.oldBoundary family := by
          simpa only [queryEq] using target
        have refined := source.refineFamilyTarget oldFamily' target'
        rw [fineGrid_eq_outerGrid] at refined
        exact ⟨family, refined⟩
      · have orientation :
            (coarseCoordinate row < source.oldBoundary ∧
              Signals.horizontalInterior?
                (componentAt (refinedGrid .odd 1 grid)
                  (coarseCoordinate column) source.oldBoundary)
                (quadrantAt (coarseCoordinate column) source.oldBoundary) =
                  some .south) := ⟨queryBelow, below.2⟩
        rcases source.oldColumnWeakBounds.1.eq_or_lt with atLower | inside
        · have columnAtLower : coarseCoordinate column =
              quarterSouth (successorWest .odd 0 parentX) := by
            simpa only [quarterSouth, quarterWest] using atLower.symm
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have orientation'' :
              coarseCoordinate row < source.oldBoundary ∧
                Signals.horizontalInterior?
                  (componentAt
                    (iterateRefine (outerLevel .odd 0 + 2) grid)
                    (quarterSouth (successorWest .odd 0 parentX))
                    source.oldBoundary)
                  (quadrantAt
                    (quarterSouth (successorWest .odd 0 parentX))
                    source.oldBoundary) = some .south := by
            simpa only [columnAtLower] using orientation'
          have notFits' : ¬FitsContainedVerticalChild .odd 0 parentX parentY
              (quarterSouth (successorWest .odd 0 parentX))
              (coarseCoordinate row) source.oldBoundary := by
            simpa only [columnAtLower] using notFitsCoarse
          rcases BoundedExceptionalTargetsAt.translateRowLowerSource
              oddTargets grid parentX parentY
              queryLower queryUpper
              source.oldBoundaryStrictBounds.1
              source.oldBoundaryStrictBounds.2 (Or.inl orientation'')
              notFits' with ⟨family, oldFamily, target⟩
          have oldFamily' := oldFamily
          rw [← oldGrid_eq_outerGrid] at oldFamily'
          rw [← columnAtLower] at oldFamily'
          have target' : RowFamilyTarget grid (outerLevel .odd 0)
              parentX parentY (successorWest .odd 0 parentX)
              (successorEast .odd 0 parentX) (coarseCoordinate column)
              (coarseCoordinate row) source.oldBoundary family := by
            simpa only [columnAtLower] using target
          have refined := source.refineFamilyTarget oldFamily' target'
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨family, refined⟩
        · have oldFamily := source.oldFamily
          rw [oldGrid_eq_outerGrid] at oldFamily
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have target := BoundedPaths.rowFamilyTarget oddPaths grid parentX parentY
            inside source.oldColumnWeakBounds.2
            queryLower queryUpper
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 (Or.inl orientation')
            notFitsCoarse oldFamily
          have refined := source.refineFamilyTarget source.oldFamily target
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨source.family, refined⟩
    · rcases above.1 with ⟨queryEq⟩ |
        ⟨queryLower, queryUpper, queryAbove⟩
      · have orientation := above.2
        rw [oldGrid_eq_outerGrid] at orientation
        rcases BoundedExceptionalTargetsAt.translateRowNorthBoundary
            oddTargets grid parentX parentY
            source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 orientation with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid] at oldFamily'
        have target' : RowFamilyTarget grid (outerLevel .odd 0)
            parentX parentY (successorWest .odd 0 parentX)
            (successorEast .odd 0 parentX) (coarseCoordinate column)
            (coarseCoordinate row) source.oldBoundary family := by
          simpa only [queryEq] using target
        have refined := source.refineFamilyTarget oldFamily' target'
        rw [fineGrid_eq_outerGrid] at refined
        exact ⟨family, refined⟩
      · have orientation :
            (source.oldBoundary < coarseCoordinate row ∧
              Signals.horizontalInterior?
                (componentAt (refinedGrid .odd 1 grid)
                  (coarseCoordinate column) source.oldBoundary)
                (quadrantAt (coarseCoordinate column) source.oldBoundary) =
                  some .north) := ⟨queryAbove, above.2⟩
        rcases source.oldColumnWeakBounds.1.eq_or_lt with atLower | inside
        · have columnAtLower : coarseCoordinate column =
              quarterSouth (successorWest .odd 0 parentX) := by
            simpa only [quarterSouth, quarterWest] using atLower.symm
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have orientation'' :
              source.oldBoundary < coarseCoordinate row ∧
                Signals.horizontalInterior?
                  (componentAt
                    (iterateRefine (outerLevel .odd 0 + 2) grid)
                    (quarterSouth (successorWest .odd 0 parentX))
                    source.oldBoundary)
                  (quadrantAt
                    (quarterSouth (successorWest .odd 0 parentX))
                    source.oldBoundary) = some .north := by
            simpa only [columnAtLower] using orientation'
          have notFits' : ¬FitsContainedVerticalChild .odd 0 parentX parentY
              (quarterSouth (successorWest .odd 0 parentX))
              (coarseCoordinate row) source.oldBoundary := by
            simpa only [columnAtLower] using notFitsCoarse
          rcases BoundedExceptionalTargetsAt.translateRowLowerSource
              oddTargets grid parentX parentY
              queryLower queryUpper
              source.oldBoundaryStrictBounds.1
              source.oldBoundaryStrictBounds.2 (Or.inr orientation'')
              notFits' with ⟨family, oldFamily, target⟩
          have oldFamily' := oldFamily
          rw [← oldGrid_eq_outerGrid] at oldFamily'
          rw [← columnAtLower] at oldFamily'
          have target' : RowFamilyTarget grid (outerLevel .odd 0)
              parentX parentY (successorWest .odd 0 parentX)
              (successorEast .odd 0 parentX) (coarseCoordinate column)
              (coarseCoordinate row) source.oldBoundary family := by
            simpa only [columnAtLower] using target
          have refined := source.refineFamilyTarget oldFamily' target'
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨family, refined⟩
        · have oldFamily := source.oldFamily
          rw [oldGrid_eq_outerGrid] at oldFamily
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have target := BoundedPaths.rowFamilyTarget oddPaths grid parentX parentY
            inside source.oldColumnWeakBounds.2
            queryLower queryUpper
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 (Or.inr orientation')
            notFitsCoarse oldFamily
          have refined := source.refineFamilyTarget source.oldFamily target
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨source.family, refined⟩
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary _createdColumn wrongFacing
    have wrongFacingFine := wrongFacing
    rw [queryGrid_eq_fineGrid .odd 0 grid] at wrongFacingFine
    have sourceInterior : Signals.verticalInterior?
        (componentAt (refinedGrid .odd 2 grid) boundary row)
        (quadrantAt boundary row) ≠ none := by
      rcases wrongFacingFine with west | east
      · rw [west.2]
        simp
      · rw [east.2]
        simp
    rcases verticalExactInheritedSource .odd 0 grid parentX parentY
      boundaryWest boundaryEast rowSouth rowNorth sparseBoundary
      sourceInterior with ⟨source⟩
    have projected := VerticalExactInheritedSource.projectedQuery
      source columnWest columnEast wrongFacingFine
    have boundaryCoarse : coarseCoordinate boundary = source.oldBoundary := by
      calc
        _ = coarseCoordinate (sparseCoordinate source.oldBoundary) :=
          congrArg coarseCoordinate source.boundarySparse.symm
        _ = _ := coarseCoordinate_sparseCoordinate source.oldBoundary
    have notFitsCoarse : ¬FitsContainedHorizontalChild .odd 0 parentX parentY
        (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary := by
      simpa only [boundaryCoarse] using
        notFitsContainedHorizontalChild_coarseCoordinate notFits
    rcases projected with below | above
    · rcases below.1 with ⟨queryEq, queryBelow⟩ |
        ⟨queryLower, queryUpper, queryBelow⟩
      · have orientation := below.2
        rw [oldGrid_eq_outerGrid] at orientation
        rcases BoundedExceptionalTargetsAt.translateColumnWestLower
            oddTargets grid parentX parentY
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 source.oldRowWeakBounds.1
            source.oldRowWeakBounds.2 orientation with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid] at oldFamily'
        have target' : ColumnFamilyTarget grid (outerLevel .odd 0)
            parentX parentY (successorWest .odd 0 parentY)
            (successorEast .odd 0 parentY) (coarseCoordinate row)
            (coarseCoordinate column) source.oldBoundary family := by
          simpa only [queryEq] using target
        have refined := source.refineFamilyTarget oldFamily' target'
        rw [fineGrid_eq_outerGrid] at refined
        exact ⟨family, refined⟩
      · have orientation :
            (coarseCoordinate column < source.oldBoundary ∧
              Signals.verticalInterior?
                (componentAt (refinedGrid .odd 1 grid)
                  source.oldBoundary (coarseCoordinate row))
                (quadrantAt source.oldBoundary (coarseCoordinate row)) =
                  some .west) := ⟨queryBelow, below.2⟩
        rcases source.oldRowWeakBounds.1.eq_or_lt with atLower | inside
        · have rowAtLower : coarseCoordinate row =
              quarterSouth (successorWest .odd 0 parentY) := atLower.symm
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have orientation'' :
              coarseCoordinate column < source.oldBoundary ∧
                Signals.verticalInterior?
                  (componentAt
                    (iterateRefine (outerLevel .odd 0 + 2) grid)
                    source.oldBoundary
                    (quarterSouth (successorWest .odd 0 parentY)))
                  (quadrantAt source.oldBoundary
                    (quarterSouth (successorWest .odd 0 parentY))) =
                    some .west := by
            simpa only [rowAtLower] using orientation'
          have notFits' : ¬FitsContainedHorizontalChild .odd 0 parentX parentY
              (coarseCoordinate column)
              (quarterSouth (successorWest .odd 0 parentY))
              source.oldBoundary := by
            simpa only [rowAtLower] using notFitsCoarse
          rcases BoundedExceptionalTargetsAt.translateColumnLowerSource
              oddTargets grid parentX parentY
              queryLower queryUpper
              source.oldBoundaryStrictBounds.1
              source.oldBoundaryStrictBounds.2 (Or.inl orientation'')
              notFits' with ⟨family, oldFamily, target⟩
          have oldFamily' := oldFamily
          rw [← oldGrid_eq_outerGrid] at oldFamily'
          rw [← rowAtLower] at oldFamily'
          have target' : ColumnFamilyTarget grid (outerLevel .odd 0)
              parentX parentY (successorWest .odd 0 parentY)
              (successorEast .odd 0 parentY) (coarseCoordinate row)
              (coarseCoordinate column) source.oldBoundary family := by
            simpa only [rowAtLower] using target
          have refined := source.refineFamilyTarget oldFamily' target'
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨family, refined⟩
        · have oldFamily := source.oldFamily
          rw [oldGrid_eq_outerGrid] at oldFamily
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have target := BoundedPaths.columnFamilyTarget oddPaths grid parentX parentY
            queryLower queryUpper
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 inside
            source.oldRowWeakBounds.2 (Or.inl orientation')
            notFitsCoarse oldFamily
          have refined := source.refineFamilyTarget source.oldFamily target
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨source.family, refined⟩
    · rcases above.1 with ⟨queryEq⟩ |
        ⟨queryLower, queryUpper, queryAbove⟩
      · have orientation := above.2
        rw [oldGrid_eq_outerGrid] at orientation
        rcases BoundedExceptionalTargetsAt.translateColumnEastBoundary
            oddTargets grid parentX parentY
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 source.oldRowWeakBounds.1
            source.oldRowWeakBounds.2 orientation with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid] at oldFamily'
        have target' : ColumnFamilyTarget grid (outerLevel .odd 0)
            parentX parentY (successorWest .odd 0 parentY)
            (successorEast .odd 0 parentY) (coarseCoordinate row)
            (coarseCoordinate column) source.oldBoundary family := by
          simpa only [queryEq] using target
        have refined := source.refineFamilyTarget oldFamily' target'
        rw [fineGrid_eq_outerGrid] at refined
        exact ⟨family, refined⟩
      · have orientation :
            (source.oldBoundary < coarseCoordinate column ∧
              Signals.verticalInterior?
                (componentAt (refinedGrid .odd 1 grid)
                  source.oldBoundary (coarseCoordinate row))
                (quadrantAt source.oldBoundary (coarseCoordinate row)) =
                  some .east) := ⟨queryAbove, above.2⟩
        rcases source.oldRowWeakBounds.1.eq_or_lt with atLower | inside
        · have rowAtLower : coarseCoordinate row =
              quarterSouth (successorWest .odd 0 parentY) := atLower.symm
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have orientation'' :
              source.oldBoundary < coarseCoordinate column ∧
                Signals.verticalInterior?
                  (componentAt
                    (iterateRefine (outerLevel .odd 0 + 2) grid)
                    source.oldBoundary
                    (quarterSouth (successorWest .odd 0 parentY)))
                  (quadrantAt source.oldBoundary
                    (quarterSouth (successorWest .odd 0 parentY))) =
                    some .east := by
            simpa only [rowAtLower] using orientation'
          have notFits' : ¬FitsContainedHorizontalChild .odd 0 parentX parentY
              (coarseCoordinate column)
              (quarterSouth (successorWest .odd 0 parentY))
              source.oldBoundary := by
            simpa only [rowAtLower] using notFitsCoarse
          rcases BoundedExceptionalTargetsAt.translateColumnLowerSource
              oddTargets grid parentX parentY
              queryLower queryUpper
              source.oldBoundaryStrictBounds.1
              source.oldBoundaryStrictBounds.2 (Or.inr orientation'')
              notFits' with ⟨family, oldFamily, target⟩
          have oldFamily' := oldFamily
          rw [← oldGrid_eq_outerGrid] at oldFamily'
          rw [← rowAtLower] at oldFamily'
          have target' : ColumnFamilyTarget grid (outerLevel .odd 0)
              parentX parentY (successorWest .odd 0 parentY)
              (successorEast .odd 0 parentY) (coarseCoordinate row)
              (coarseCoordinate column) source.oldBoundary family := by
            simpa only [rowAtLower] using target
          have refined := source.refineFamilyTarget oldFamily' target'
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨family, refined⟩
        · have oldFamily := source.oldFamily
          rw [oldGrid_eq_outerGrid] at oldFamily
          have orientation' := orientation
          rw [oldGrid_eq_outerGrid] at orientation'
          have target := BoundedPaths.columnFamilyTarget oddPaths grid parentX parentY
            queryLower queryUpper
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2 inside
            source.oldRowWeakBounds.2 (Or.inr orientation')
            notFitsCoarse oldFamily
          have refined := source.refineFamilyTarget source.oldFamily target
          rw [fineGrid_eq_outerGrid] at refined
          exact ⟨source.family, refined⟩

end PairCoverSeamResidualDirectPathFamilyOddBase
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
