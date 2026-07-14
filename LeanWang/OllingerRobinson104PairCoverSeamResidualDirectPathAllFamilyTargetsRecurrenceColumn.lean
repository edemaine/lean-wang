/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsCreated
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorQueryCases
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalTargets

/-!
# Column half of the free-line-general target recurrence

An exact sparse predecessor exposes one coarse selected boundary.  Ordinary
queries recurse when that boundary is retained and use the created-path seed
when it is new.  Projection stopping cases and weak lower transverse bounds
are delegated to the exceptional target state.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceColumn

open RedCycles RedShadeCycles RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamRefinementCoordinates
  PairCoverSeamRefinementQueryCases PairCoverSeamCreatedPaths
  PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathAllFamilyTargets
  PairCoverSeamResidualDirectPathAllFamilyTargetsCreated
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathExactPredecessorHierarchy
  PairCoverSeamResidualDirectPathExactPredecessorQueryCases
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
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
-- The branch chooses whether the projected boundary is retained or created.
/-- Supply the coarse target for an ordinary strict projected column query. -/
private theorem ordinaryCoarseTarget
    {phase : Phase} {depth : Nat}
    (old : AllFamilyTargetsAt phase depth)
    (created : CoveredCreatedPathsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (source : VerticalExactInheritedSource phase (depth + 1) grid
      parentX parentY boundary row)
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) <
        coarseCoordinate row)
    (rowNorth :
      coarseCoordinate row <
        quarterNorth (successorEast phase (depth + 1) parentY))
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) <
        coarseCoordinate column)
    (columnEast :
      coarseCoordinate column <
        quarterEast (successorEast phase (depth + 1) parentX))
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 1)
      parentX parentY (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary)
    (wrongFacing :
      (coarseCoordinate column < source.oldBoundary ∧
        Signals.verticalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid)
            source.oldBoundary (coarseCoordinate row))
          (quadrantAt source.oldBoundary (coarseCoordinate row)) =
            some .west) ∨
      (source.oldBoundary < coarseCoordinate column ∧
        Signals.verticalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid)
            source.oldBoundary (coarseCoordinate row))
          (quadrantAt source.oldBoundary (coarseCoordinate row)) =
            some .east)) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (verticalPort (refinedGrid phase (depth + 2) grid)
          source.oldBoundary (coarseCoordinate row))
        (outerLevel phase (depth + 1)) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY)
        (coarseCoordinate row) (coarseCoordinate column)
        source.oldBoundary family := by
  rcases old with ⟨_oldRow, oldColumn⟩
  have wrongFacing' := wrongFacing
  rw [← queryGrid_eq_fineGrid phase depth grid] at wrongFacing'
  by_cases oldSparse : IsSparseCoordinate source.oldBoundary
  · rcases oldColumn (grid := grid) (parentX := parentX) (parentY := parentY)
        (column := coarseCoordinate column) (row := coarseCoordinate row)
        (boundary := source.oldBoundary) columnWest columnEast
        source.oldBoundaryStrictBounds.1
        source.oldBoundaryStrictBounds.2 rowSouth rowNorth notFits oldSparse
        wrongFacing' with
      ⟨family, oldFamily, target⟩
    have oldFamily' := oldFamily
    rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
    exact ⟨family, oldFamily', target⟩
  · have oldFamily := source.oldFamily
    rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily
    have target := columnTarget (phase := phase) (depth := depth) created grid
      parentX parentY (column := coarseCoordinate column)
      (row := coarseCoordinate row) (boundary := source.oldBoundary)
      columnWest columnEast
      source.oldBoundaryStrictBounds.1
      source.oldBoundaryStrictBounds.2 rowSouth rowNorth wrongFacing' notFits
      oldSparse oldFamily
    exact ⟨source.family, source.oldFamily, target⟩

set_option maxHeartbeats 2000000 in
-- The selected family and projected-query constructor are dependent choices.
/-- One recurrence step for column targets. -/
theorem columnSucc
    {phase : Phase} {depth : Nat}
    (old : AllFamilyTargetsAt phase depth)
    (exceptional : ExceptionalFamilyTargetsAt phase (depth + 1))
    (created : CoveredCreatedPathsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 2) parentX) < column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 2) parentX))
    (boundaryWest :
      quarterWest (successorWest phase (depth + 2) parentX) < boundary)
    (boundaryEast :
      boundary < quarterEast (successorEast phase (depth + 2) parentX))
    (rowSouth :
      quarterSouth (successorWest phase (depth + 2) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 2) parentY))
    (notFits : ¬FitsContainedHorizontalChild phase (depth + 2)
      parentX parentY column row boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 2) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 2) grid)) boundary row)
          (quadrantAt boundary row) = some .east)) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
        (verticalPort
          (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
          boundary row)
        (outerLevel phase (depth + 2)) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase (depth + 2)) parentX parentY
        (successorWest phase (depth + 2) parentY)
        (successorEast phase (depth + 2) parentY)
        row column boundary family := by
  have wrongFacingFine := wrongFacing
  rw [queryGrid_eq_fineGrid phase (depth + 1) grid] at wrongFacingFine
  have sourceInterior : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 3) grid) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rcases wrongFacingFine with south | north
    · rw [south.2]
      simp
    · rw [north.2]
      simp
  rcases verticalExactInheritedSource phase (depth + 1) grid
      parentX parentY boundaryWest boundaryEast rowSouth rowNorth
      sparseBoundary sourceInterior with ⟨source⟩
  have projected := VerticalExactInheritedSource.projectedQuery source
    columnWest columnEast wrongFacingFine
  have boundaryCoarse : coarseCoordinate boundary = source.oldBoundary := by
    calc
      _ = coarseCoordinate (sparseCoordinate source.oldBoundary) :=
        congrArg coarseCoordinate source.boundarySparse.symm
      _ = _ := coarseCoordinate_sparseCoordinate source.oldBoundary
  have notFitsCoarse :
      ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
        (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary := by
    simpa only [boundaryCoarse] using
      notFitsContainedHorizontalChild_coarseCoordinate notFits
  have refineResult : ∀ {family : HierarchyFamily},
      CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 2) grid)
          (verticalPort (refinedGrid phase (depth + 2) grid)
            source.oldBoundary (coarseCoordinate row))
          (outerLevel phase (depth + 1)) parentX parentY family →
      ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
          (successorWest phase (depth + 1) parentY)
          (successorEast phase (depth + 1) parentY)
          (coarseCoordinate row) (coarseCoordinate column)
          source.oldBoundary family →
      ∃ family,
        CanonicalCycleAncestorWithinFamily
          (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
          (verticalPort
            (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
            boundary row)
          (outerLevel phase (depth + 2)) parentX parentY family ∧
        ColumnFamilyTarget grid (outerLevel phase (depth + 2)) parentX parentY
          (successorWest phase (depth + 2) parentY)
          (successorEast phase (depth + 2) parentY)
          row column boundary family := by
    intro family oldFamily target
    have refined := source.refineFamilyTarget oldFamily target
    rw [fineGrid_eq_outerGrid phase (depth + 1) grid] at refined
    exact ⟨family, refined⟩
  rcases projected with below | above
  · rcases below.1 with ⟨queryEq, queryBelow⟩ |
      ⟨queryLower, queryUpper, queryBelow⟩
    · have orientation := below.2
      rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation
      rcases exceptional.column grid parentX parentY
          source.oldRowWeakBounds.1 source.oldRowWeakBounds.2
          source.oldBoundaryStrictBounds.1
          source.oldBoundaryStrictBounds.2
          (Or.inl ⟨queryEq, orientation⟩) with
        ⟨family, oldFamily, target⟩
      have oldFamily' := oldFamily
      rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
      exact refineResult oldFamily' target
    · have orientation :
          coarseCoordinate column < source.oldBoundary ∧
            Signals.verticalInterior?
              (componentAt (refinedGrid phase (depth + 2) grid)
                source.oldBoundary (coarseCoordinate row))
              (quadrantAt source.oldBoundary (coarseCoordinate row)) =
                some .west := ⟨queryBelow, below.2⟩
      rcases source.oldRowWeakBounds.1.eq_or_lt with atLower | inside
      · have rowAtLower : coarseCoordinate row =
            quarterSouth (successorWest phase (depth + 1) parentY) :=
          atLower.symm
        have orientation' := orientation
        rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation'
        rcases exceptional.column grid parentX parentY
            source.oldRowWeakBounds.1 source.oldRowWeakBounds.2
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2
            (Or.inr (Or.inr ⟨rowAtLower, queryLower, queryUpper,
              Or.inl orientation', notFitsCoarse⟩)) with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
        exact refineResult oldFamily' target
      · rcases ordinaryCoarseTarget old created grid parentX parentY source
            inside source.oldRowWeakBounds.2 queryLower queryUpper
            notFitsCoarse (Or.inl orientation) with
          ⟨family, oldFamily, target⟩
        exact refineResult oldFamily target
  · rcases above.1 with ⟨queryEq⟩ |
      ⟨queryLower, queryUpper, queryAbove⟩
    · have orientation := above.2
      rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation
      rcases exceptional.column grid parentX parentY
          source.oldRowWeakBounds.1 source.oldRowWeakBounds.2
          source.oldBoundaryStrictBounds.1
          source.oldBoundaryStrictBounds.2
          (Or.inr (Or.inl ⟨queryEq, orientation⟩)) with
        ⟨family, oldFamily, target⟩
      have oldFamily' := oldFamily
      rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
      exact refineResult oldFamily' target
    · have orientation :
          source.oldBoundary < coarseCoordinate column ∧
            Signals.verticalInterior?
              (componentAt (refinedGrid phase (depth + 2) grid)
                source.oldBoundary (coarseCoordinate row))
              (quadrantAt source.oldBoundary (coarseCoordinate row)) =
                some .east := ⟨queryAbove, above.2⟩
      rcases source.oldRowWeakBounds.1.eq_or_lt with atLower | inside
      · have rowAtLower : coarseCoordinate row =
            quarterSouth (successorWest phase (depth + 1) parentY) :=
          atLower.symm
        have orientation' := orientation
        rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation'
        rcases exceptional.column grid parentX parentY
            source.oldRowWeakBounds.1 source.oldRowWeakBounds.2
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2
            (Or.inr (Or.inr ⟨rowAtLower, queryLower, queryUpper,
              Or.inr orientation', notFitsCoarse⟩)) with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
        exact refineResult oldFamily' target
      · rcases ordinaryCoarseTarget old created grid parentX parentY source
            inside source.oldRowWeakBounds.2 queryLower queryUpper
            notFitsCoarse (Or.inr orientation) with
          ⟨family, oldFamily, target⟩
        exact refineResult oldFamily target

end PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceColumn
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
