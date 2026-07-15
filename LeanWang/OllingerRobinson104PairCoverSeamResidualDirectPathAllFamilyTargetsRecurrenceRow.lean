/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsCreated
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorQueryCases
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalTargets

/-!
# Row half of the free-line-general target recurrence

An exact sparse predecessor exposes one coarse selected boundary.  Ordinary
queries recurse when that boundary is retained and use the created-path seed
when it is new.  Projection stopping cases and weak lower transverse bounds
are delegated to the exceptional target state.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceRow

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
/-- Supply the coarse target for an ordinary strict projected row query. -/
private theorem ordinaryCoarseTarget
    {phase : Phase} {depth : Nat}
    (old : AllFamilyTargetsAt phase depth)
    (created : CoveredCreatedPathsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (source : HorizontalExactInheritedSource phase (depth + 1) grid
      parentX parentY column boundary)
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) <
        coarseCoordinate column)
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) <
        coarseCoordinate row)
    (rowNorth :
      coarseCoordinate row <
        quarterNorth (successorEast phase (depth + 1) parentY))
    (notFits : ¬FitsContainedVerticalChild phase (depth + 1)
      parentX parentY (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary)
    (wrongFacing :
      (coarseCoordinate row < source.oldBoundary ∧
        Signals.horizontalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid)
            (coarseCoordinate column) source.oldBoundary)
          (quadrantAt (coarseCoordinate column) source.oldBoundary) =
            some .south) ∨
      (source.oldBoundary < coarseCoordinate row ∧
        Signals.horizontalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid)
            (coarseCoordinate column) source.oldBoundary)
          (quadrantAt (coarseCoordinate column) source.oldBoundary) =
            some .north)) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (refinedGrid phase (depth + 2) grid)
        (horizontalPort (refinedGrid phase (depth + 2) grid)
          (coarseCoordinate column) source.oldBoundary)
        (outerLevel phase (depth + 1)) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX)
        (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary family := by
  rcases old with ⟨oldRow, _oldColumn⟩
  have wrongFacing' := wrongFacing
  rw [← queryGrid_eq_fineGrid phase depth grid] at wrongFacing'
  by_cases oldSparse : IsSparseCoordinate source.oldBoundary
  · rcases oldRow (grid := grid) (parentX := parentX) (parentY := parentY)
        (column := coarseCoordinate column) (row := coarseCoordinate row)
        (boundary := source.oldBoundary) columnWest
        source.oldColumnWeakBounds.2 rowSouth rowNorth
        source.oldBoundaryStrictBounds.1
        source.oldBoundaryStrictBounds.2 notFits oldSparse wrongFacing' with
      ⟨family, oldFamily, target⟩
    have oldFamily' := oldFamily
    rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
    exact ⟨family, oldFamily', target⟩
  · have oldFamily := source.oldFamily
    rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily
    have target := rowTarget (phase := phase) (depth := depth) created grid
      parentX parentY (column := coarseCoordinate column)
      (row := coarseCoordinate row) (boundary := source.oldBoundary) columnWest
      source.oldColumnWeakBounds.2 rowSouth rowNorth
      source.oldBoundaryStrictBounds.1
      source.oldBoundaryStrictBounds.2 wrongFacing' notFits oldSparse oldFamily
    exact ⟨source.family, source.oldFamily, target⟩

set_option maxHeartbeats 2000000 in
-- The selected family and projected-query constructor are dependent choices.
/-- One recurrence step for row targets. -/
theorem rowSucc
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
    (rowSouth :
      quarterSouth (successorWest phase (depth + 2) parentY) < row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 2) parentY))
    (boundarySouth :
      quarterSouth (successorWest phase (depth + 2) parentY) < boundary)
    (boundaryNorth :
      boundary < quarterNorth (successorEast phase (depth + 2) parentY))
    (notFits : ¬FitsContainedVerticalChild phase (depth + 2)
      parentX parentY column row boundary)
    (sparseBoundary : IsSparseCoordinate boundary)
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 2) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 2) grid)) column boundary)
          (quadrantAt column boundary) = some .north)) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
        (horizontalPort
          (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
          column boundary)
        (outerLevel phase (depth + 2)) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase (depth + 2)) parentX parentY
        (successorWest phase (depth + 2) parentX)
        (successorEast phase (depth + 2) parentX)
        column row boundary family := by
  have wrongFacingFine := wrongFacing
  rw [queryGrid_eq_fineGrid phase (depth + 1) grid] at wrongFacingFine
  have sourceInterior : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 3) grid) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rcases wrongFacingFine with south | north
    · rw [south.2]
      simp
    · rw [north.2]
      simp
  rcases horizontalExactInheritedSource phase (depth + 1) grid
      parentX parentY columnWest.le columnEast boundarySouth boundaryNorth
      sparseBoundary sourceInterior with ⟨source⟩
  have projected := HorizontalExactInheritedSource.projectedQuery source
    rowSouth rowNorth wrongFacingFine
  have boundaryCoarse : coarseCoordinate boundary = source.oldBoundary := by
    calc
      _ = coarseCoordinate (sparseCoordinate source.oldBoundary) :=
        congrArg coarseCoordinate source.boundarySparse.symm
      _ = _ := coarseCoordinate_sparseCoordinate source.oldBoundary
  have notFitsCoarse :
      ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
        (coarseCoordinate column) (coarseCoordinate row)
        source.oldBoundary := by
    simpa only [boundaryCoarse] using
      notFitsContainedVerticalChild_coarseCoordinate notFits
  have refineResult : ∀ {family : HierarchyFamily},
      CanonicalCycleAncestorWithinFamily
          (refinedGrid phase (depth + 2) grid)
          (horizontalPort (refinedGrid phase (depth + 2) grid)
            (coarseCoordinate column) source.oldBoundary)
          (outerLevel phase (depth + 1)) parentX parentY family →
      RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
          (successorWest phase (depth + 1) parentX)
          (successorEast phase (depth + 1) parentX)
          (coarseCoordinate column) (coarseCoordinate row)
          source.oldBoundary family →
      ∃ family,
        CanonicalCycleAncestorWithinFamily
          (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
          (horizontalPort
            (iterateRefine (outerLevel phase (depth + 2) + 2) grid)
            column boundary)
          (outerLevel phase (depth + 2)) parentX parentY family ∧
        RowFamilyTarget grid (outerLevel phase (depth + 2)) parentX parentY
          (successorWest phase (depth + 2) parentX)
          (successorEast phase (depth + 2) parentX)
          column row boundary family := by
    intro family oldFamily target
    have refined := source.refineFamilyTarget oldFamily target
    rw [fineGrid_eq_outerGrid phase (depth + 1) grid] at refined
    exact ⟨family, refined⟩
  rcases projected with below | above
  · rcases below.1 with ⟨queryEq, queryBelow⟩ |
      ⟨queryLower, queryUpper, queryBelow⟩
    · have orientation := below.2
      rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation
      rcases exceptional.row grid parentX parentY
          source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
          source.oldBoundaryStrictBounds.1
          source.oldBoundaryStrictBounds.2
          (Or.inl ⟨queryEq, orientation⟩) with
        ⟨family, oldFamily, target⟩
      have oldFamily' := oldFamily
      rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
      exact refineResult oldFamily' target
    · have orientation :
          coarseCoordinate row < source.oldBoundary ∧
            Signals.horizontalInterior?
              (componentAt (refinedGrid phase (depth + 2) grid)
                (coarseCoordinate column) source.oldBoundary)
              (quadrantAt (coarseCoordinate column) source.oldBoundary) =
                some .south := ⟨queryBelow, below.2⟩
      rcases source.oldColumnWeakBounds.1.eq_or_lt with atLower | inside
      · have columnAtLower : coarseCoordinate column =
            quarterSouth (successorWest phase (depth + 1) parentX) := by
          simpa only [quarterSouth, quarterWest] using atLower.symm
        have orientation' := orientation
        rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation'
        rcases exceptional.row grid parentX parentY
            source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2
            (Or.inr (Or.inr ⟨columnAtLower, queryLower, queryUpper,
              Or.inl orientation', notFitsCoarse⟩)) with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
        exact refineResult oldFamily' target
      · rcases ordinaryCoarseTarget old created grid parentX parentY source
            inside queryLower queryUpper notFitsCoarse (Or.inl orientation) with
          ⟨family, oldFamily, target⟩
        exact refineResult oldFamily target
  · rcases above.1 with ⟨queryEq⟩ |
      ⟨queryLower, queryUpper, queryAbove⟩
    · have orientation := above.2
      rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation
      rcases exceptional.row grid parentX parentY
          source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
          source.oldBoundaryStrictBounds.1
          source.oldBoundaryStrictBounds.2
          (Or.inr (Or.inl ⟨queryEq, orientation⟩)) with
        ⟨family, oldFamily, target⟩
      have oldFamily' := oldFamily
      rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
      exact refineResult oldFamily' target
    · have orientation :
          source.oldBoundary < coarseCoordinate row ∧
            Signals.horizontalInterior?
              (componentAt (refinedGrid phase (depth + 2) grid)
                (coarseCoordinate column) source.oldBoundary)
              (quadrantAt (coarseCoordinate column) source.oldBoundary) =
                some .north := ⟨queryAbove, above.2⟩
      rcases source.oldColumnWeakBounds.1.eq_or_lt with atLower | inside
      · have columnAtLower : coarseCoordinate column =
            quarterSouth (successorWest phase (depth + 1) parentX) := by
          simpa only [quarterSouth, quarterWest] using atLower.symm
        have orientation' := orientation
        rw [oldGrid_eq_outerGrid phase (depth + 1) grid] at orientation'
        rcases exceptional.row grid parentX parentY
            source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
            source.oldBoundaryStrictBounds.1
            source.oldBoundaryStrictBounds.2
            (Or.inr (Or.inr ⟨columnAtLower, queryLower, queryUpper,
              Or.inr orientation', notFitsCoarse⟩)) with
          ⟨family, oldFamily, target⟩
        have oldFamily' := oldFamily
        rw [← oldGrid_eq_outerGrid phase (depth + 1) grid] at oldFamily'
        exact refineResult oldFamily' target
      · rcases ordinaryCoarseTarget old created grid parentX parentY source
            inside queryLower queryUpper notFitsCoarse (Or.inr orientation) with
          ⟨family, oldFamily, target⟩
        exact refineResult oldFamily target

end PairCoverSeamResidualDirectPathAllFamilyTargetsRecurrenceRow
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
