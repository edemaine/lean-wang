/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorQueryCases
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalTargets

/-!
# Inherited exceptional row targets

An exceptional selected source that is literally retained by the next
two-substitution step has an exact predecessor.  Its projected query is again
one of the three exceptional shapes, and the old target lifts in the same
hierarchy family.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceRow

open RedCycles RedShadeCycles RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamRefinementCoordinates
  PairCoverSeamRefinementQueryCases PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathExactPredecessorHierarchy
  PairCoverSeamResidualDirectPathExactPredecessorQueryCases
  PairCoverSeamResidualDirectPathExactPredecessorQueryCases.HorizontalExactInheritedSource
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  PairCoverSeamResidualDirectPathTargets RefinedCoordinateProjection
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem oldGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 1) grid =
      iterateRefine (outerLevel phase depth + 2) grid := by
  unfold refinedGrid outerLevel refinementDepth
  congr 1

private theorem fineGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 2) grid =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  unfold refinedGrid outerLevel refinementDepth
  congr 1

private theorem coarseCoordinate_quarterWest_four (west : Nat) :
    coarseCoordinate (quarterWest (4 * west)) = quarterWest west := by
  have hmod : (2 * (4 * west) + 1) % 8 = 1 := by omega
  have hdiv : (2 * (4 * west) + 1) / 8 = west := by omega
  unfold coarseCoordinate quarterWest
  rw [hmod]
  norm_num [hdiv]

private theorem coarseCoordinate_successorLower
    (phase : Phase) (depth parent : Nat) :
    coarseCoordinate
        (quarterSouth (successorWest phase (depth + 1) parent)) =
      quarterSouth (successorWest phase depth parent) := by
  simp only [quarterSouth, successorWest_succ]
  exact coarseCoordinate_quarterWest_four _

set_option maxHeartbeats 2000000 in
-- The dependent family endpoint is transported through each projection case.
/-- A retained exceptional horizontal source inherits its target from the
preceding hierarchy depth. -/
theorem rowSucc_of_sparseBoundary
    {phase : Phase} {depth : Nat}
    (old : ExceptionalFamilyTargetsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column query boundary : Nat}
    (columnLower :
      quarterSouth (successorWest phase (depth + 1) parentX) ≤ column)
    (columnUpper : column <
      quarterNorth (successorEast phase (depth + 1) parentX))
    (boundaryLower :
      quarterSouth (successorWest phase (depth + 1) parentY) < boundary)
    (boundaryUpper : boundary <
      quarterNorth (successorEast phase (depth + 1) parentY))
    (exceptional : RowExceptionalCase phase (depth + 1) parentX parentY
      grid column query boundary)
    (sparseBoundary : IsSparseCoordinate boundary) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
        (horizontalPort
          (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
          column boundary)
        (outerLevel phase (depth + 1)) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX)
        column query boundary family := by
  have sourceInterior : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [fineGrid_eq_outerGrid phase depth grid]
    rcases exceptional with south | north | lowerSource
    · rw [south.2]
      simp
    · rw [north.2]
      simp
    · rcases lowerSource.2.2.2.1 with south | north
      · rw [south.2]
        simp
      · rw [north.2]
        simp
  rcases horizontalExactInheritedSource phase depth grid parentX parentY
      (by simpa only [quarterSouth, quarterWest] using columnLower)
      (by simpa only [quarterNorth, quarterEast] using columnUpper)
      boundaryLower boundaryUpper sparseBoundary sourceInterior with ⟨source⟩
  have boundaryCoarse : coarseCoordinate boundary = source.oldBoundary := by
    calc
      _ = coarseCoordinate (sparseCoordinate source.oldBoundary) :=
        congrArg coarseCoordinate source.boundarySparse.symm
      _ = _ := coarseCoordinate_sparseCoordinate source.oldBoundary
  have liftTarget
      (coarseExceptional : RowExceptionalCase phase depth parentX parentY grid
        (coarseCoordinate column) (coarseCoordinate query)
        source.oldBoundary) :
      ∃ family,
        CanonicalCycleAncestorWithinFamily
          (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
          (horizontalPort
            (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
            column boundary)
          (outerLevel phase (depth + 1)) parentX parentY family ∧
        RowFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
          (successorWest phase (depth + 1) parentX)
          (successorEast phase (depth + 1) parentX)
          column query boundary family := by
    rcases old.row grid parentX parentY
        source.oldColumnWeakBounds.1 source.oldColumnWeakBounds.2
        source.oldBoundaryStrictBounds.1 source.oldBoundaryStrictBounds.2
        coarseExceptional with ⟨family, oldFamily, target⟩
    have oldFamily' := oldFamily
    rw [← oldGrid_eq_outerGrid phase depth grid] at oldFamily'
    have lifted := source.refineFamilyTarget oldFamily' target
    rw [fineGrid_eq_outerGrid phase depth grid] at lifted
    exact ⟨family, lifted⟩
  rcases exceptional with south | north | lowerSource
  · rcases south with ⟨rfl, south⟩
    have south' : Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
        (quadrantAt column boundary) = some .south := by
      rw [fineGrid_eq_outerGrid phase depth grid]
      exact south
    have oldSouth := source.orientationEq.trans south'
    apply liftTarget
    left
    exact ⟨coarseCoordinate_successorLower phase depth parentY, by
      rw [oldGrid_eq_outerGrid phase depth grid] at oldSouth
      exact oldSouth⟩
  · rcases north with ⟨queryEq, north⟩
    have north' : Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
        (quadrantAt column boundary) = some .north := by
      rw [fineGrid_eq_outerGrid phase depth grid]
      exact north
    have oldNorth := source.orientationEq.trans north'
    apply liftTarget
    right
    left
    exact ⟨by rw [queryEq, boundaryCoarse], by
      rw [oldGrid_eq_outerGrid phase depth grid] at oldNorth
      exact oldNorth⟩
  · rcases lowerSource with
      ⟨rfl, queryLower, queryUpper, wrongFacing, notFits⟩
    have wrongFacing' :
        (query < boundary ∧
          Signals.horizontalInterior?
            (componentAt (refinedGrid phase (depth + 2) grid)
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary)
            (quadrantAt
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary) = some .south) ∨
        (boundary < query ∧
          Signals.horizontalInterior?
            (componentAt (refinedGrid phase (depth + 2) grid)
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary)
            (quadrantAt
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary) = some .north) := by
      rw [fineGrid_eq_outerGrid phase depth grid]
      exact wrongFacing
    have projected := projectedQuery source queryLower queryUpper wrongFacing'
    have notFitsCoarse :
        ¬FitsContainedVerticalChild phase depth parentX parentY
          (coarseCoordinate
            (quarterSouth (successorWest phase (depth + 1) parentX)))
          (coarseCoordinate query) source.oldBoundary := by
      simpa only [boundaryCoarse] using
        notFitsContainedVerticalChild_coarseCoordinate notFits
    have columnCoarse := coarseCoordinate_successorLower phase depth parentX
    rcases projected with below | above
    · rcases below.1 with ⟨queryEq, queryBelow⟩ |
        ⟨coarseLower, coarseUpper, queryBelow⟩
      · apply liftTarget
        left
        exact ⟨queryEq, by
          have orientation := below.2
          rw [oldGrid_eq_outerGrid phase depth grid] at orientation
          exact orientation⟩
      · apply liftTarget
        right
        right
        exact ⟨columnCoarse, coarseLower, coarseUpper,
          Or.inl ⟨queryBelow, by
            have orientation := below.2
            rw [oldGrid_eq_outerGrid phase depth grid] at orientation
            exact orientation⟩, notFitsCoarse⟩
    · rcases above.1 with ⟨queryEq⟩ |
        ⟨coarseLower, coarseUpper, queryAbove⟩
      · apply liftTarget
        right
        left
        exact ⟨queryEq, by
          have orientation := above.2
          rw [oldGrid_eq_outerGrid phase depth grid] at orientation
          exact orientation⟩
      · apply liftTarget
        right
        right
        exact ⟨columnCoarse, coarseLower, coarseUpper,
          Or.inr ⟨queryAbove, by
            have orientation := above.2
            rw [oldGrid_eq_outerGrid phase depth grid] at orientation
            exact orientation⟩, notFitsCoarse⟩

end PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceRow
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
