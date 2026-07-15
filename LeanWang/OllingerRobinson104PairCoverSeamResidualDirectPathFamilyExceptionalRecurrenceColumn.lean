/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorQueryCases
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalTargets

/-!
# Inherited exceptional column targets

Column-dual of the inherited row recurrence.  A retained selected source has
an exact predecessor, its exceptional query projects to an exceptional query,
and the old same-family target lifts through two substitutions.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceColumn

open RedCycles RedShadeCycles RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamRefinementCoordinates
  PairCoverSeamRefinementQueryCases PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathExactPredecessorHierarchy
  PairCoverSeamResidualDirectPathExactPredecessorQueryCases
  PairCoverSeamResidualDirectPathExactPredecessorQueryCases.VerticalExactInheritedSource
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
        (quarterWest (successorWest phase (depth + 1) parent)) =
      quarterWest (successorWest phase depth parent) := by
  simp only [successorWest_succ]
  exact coarseCoordinate_quarterWest_four _

set_option maxHeartbeats 2000000 in
-- The dependent family endpoint is transported through each projection case.
/-- A retained exceptional vertical source inherits its target from the
preceding hierarchy depth. -/
theorem columnSucc_of_sparseBoundary
    {phase : Phase} {depth : Nat}
    (old : ExceptionalFamilyTargetsAt phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {row query boundary : Nat}
    (rowLower :
      quarterSouth (successorWest phase (depth + 1) parentY) ≤ row)
    (rowUpper : row <
      quarterNorth (successorEast phase (depth + 1) parentY))
    (boundaryLower :
      quarterWest (successorWest phase (depth + 1) parentX) < boundary)
    (boundaryUpper : boundary <
      quarterEast (successorEast phase (depth + 1) parentX))
    (exceptional : ColumnExceptionalCase phase (depth + 1) parentX parentY
      grid row query boundary)
    (sparseBoundary : IsSparseCoordinate boundary) :
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
        (verticalPort
          (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
          boundary row)
        (outerLevel phase (depth + 1)) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY)
        row query boundary family := by
  have sourceInterior : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [fineGrid_eq_outerGrid phase depth grid]
    rcases exceptional with west | east | lowerSource
    · rw [west.2]
      simp
    · rw [east.2]
      simp
    · rcases lowerSource.2.2.2.1 with west | east
      · rw [west.2]
        simp
      · rw [east.2]
        simp
  rcases verticalExactInheritedSource phase depth grid parentX parentY
      boundaryLower boundaryUpper
      (by simpa only [quarterSouth, quarterWest] using rowLower)
      (by simpa only [quarterNorth, quarterEast] using rowUpper)
      sparseBoundary sourceInterior with ⟨source⟩
  have boundaryCoarse : coarseCoordinate boundary = source.oldBoundary := by
    calc
      _ = coarseCoordinate (sparseCoordinate source.oldBoundary) :=
        congrArg coarseCoordinate source.boundarySparse.symm
      _ = _ := coarseCoordinate_sparseCoordinate source.oldBoundary
  have liftTarget
      (coarseExceptional : ColumnExceptionalCase phase depth parentX parentY
        grid (coarseCoordinate row) (coarseCoordinate query)
        source.oldBoundary) :
      ∃ family,
        CanonicalCycleAncestorWithinFamily
          (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
          (verticalPort
            (iterateRefine (outerLevel phase (depth + 1) + 2) grid)
            boundary row)
          (outerLevel phase (depth + 1)) parentX parentY family ∧
        ColumnFamilyTarget grid (outerLevel phase (depth + 1)) parentX parentY
          (successorWest phase (depth + 1) parentY)
          (successorEast phase (depth + 1) parentY)
          row query boundary family := by
    rcases old.column grid parentX parentY
        source.oldRowWeakBounds.1 source.oldRowWeakBounds.2
        source.oldBoundaryStrictBounds.1 source.oldBoundaryStrictBounds.2
        coarseExceptional with ⟨family, oldFamily, target⟩
    have oldFamily' := oldFamily
    rw [← oldGrid_eq_outerGrid phase depth grid] at oldFamily'
    have lifted := source.refineFamilyTarget oldFamily' target
    rw [fineGrid_eq_outerGrid phase depth grid] at lifted
    exact ⟨family, lifted⟩
  rcases exceptional with west | east | lowerSource
  · rcases west with ⟨rfl, west⟩
    have west' : Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
        (quadrantAt boundary row) = some .west := by
      rw [fineGrid_eq_outerGrid phase depth grid]
      exact west
    have oldWest := source.orientationEq.trans west'
    apply liftTarget
    left
    exact ⟨coarseCoordinate_successorLower phase depth parentX, by
      rw [oldGrid_eq_outerGrid phase depth grid] at oldWest
      exact oldWest⟩
  · rcases east with ⟨queryEq, east⟩
    have east' : Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
        (quadrantAt boundary row) = some .east := by
      rw [fineGrid_eq_outerGrid phase depth grid]
      exact east
    have oldEast := source.orientationEq.trans east'
    apply liftTarget
    right
    left
    exact ⟨by rw [queryEq, boundaryCoarse], by
      rw [oldGrid_eq_outerGrid phase depth grid] at oldEast
      exact oldEast⟩
  · rcases lowerSource with
      ⟨rfl, queryLower, queryUpper, wrongFacing, notFits⟩
    have wrongFacing' :
        (query < boundary ∧
          Signals.verticalInterior?
            (componentAt (refinedGrid phase (depth + 2) grid) boundary
              (quarterSouth (successorWest phase (depth + 1) parentY)))
            (quadrantAt boundary
              (quarterSouth (successorWest phase (depth + 1) parentY))) =
                some .west) ∨
        (boundary < query ∧
          Signals.verticalInterior?
            (componentAt (refinedGrid phase (depth + 2) grid) boundary
              (quarterSouth (successorWest phase (depth + 1) parentY)))
            (quadrantAt boundary
              (quarterSouth (successorWest phase (depth + 1) parentY))) =
                some .east) := by
      rw [fineGrid_eq_outerGrid phase depth grid]
      exact wrongFacing
    have projected := projectedQuery source queryLower queryUpper wrongFacing'
    have notFitsCoarse :
        ¬FitsContainedHorizontalChild phase depth parentX parentY
          (coarseCoordinate query)
          (coarseCoordinate
            (quarterSouth (successorWest phase (depth + 1) parentY)))
          source.oldBoundary := by
      simpa only [boundaryCoarse] using
        notFitsContainedHorizontalChild_coarseCoordinate notFits
    have rowCoarse :
        coarseCoordinate
            (quarterSouth (successorWest phase (depth + 1) parentY)) =
          quarterSouth (successorWest phase depth parentY) := by
      change coarseCoordinate
          (quarterWest (successorWest phase (depth + 1) parentY)) =
        quarterWest (successorWest phase depth parentY)
      exact coarseCoordinate_successorLower phase depth parentY
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
        exact ⟨rowCoarse, coarseLower, coarseUpper,
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
        exact ⟨rowCoarse, coarseLower, coarseUpper,
          Or.inr ⟨queryAbove, by
            have orientation := above.2
            rw [oldGrid_eq_outerGrid phase depth grid] at orientation
            exact orientation⟩, notFitsCoarse⟩

end PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceColumn
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
