/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceColumn
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceRow

/-!
# Exceptional target recurrence

At the next hierarchy depth, a selected exceptional source is either a sparse
boundary retained from the previous depth or a boundary created by the latest
two substitutions.  Exact predecessor projection handles the retained case.
This module isolates the remaining created case as a local semantic obligation.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalRecurrence

open RedCycles RedShadeCycles PairCoverSeamArithmetic PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceColumn
  PairCoverSeamResidualDirectPathFamilyExceptionalRecurrenceRow
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  PairCoverSeamResidualDirectPathTargets RefinedCoordinateProjection
  ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence Signals.FreeCellLocal

/-- Same-family targets for exceptional sources created at one hierarchy
depth, as opposed to sparse boundaries retained from the previous depth. -/
structure CreatedExceptionalFamilyTargetsAt
    (phase : Phase) (depth : Nat) : Prop where
  row : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column query boundary : Nat},
    quarterSouth (successorWest phase depth parentX) ≤ column →
    column < quarterNorth (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < boundary →
    boundary < quarterNorth (successorEast phase depth parentY) →
    RowExceptionalCase phase depth parentX parentY grid
      column query boundary →
    ¬ IsSparseCoordinate boundary →
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (horizontalPort (iterateRefine (outerLevel phase depth + 2) grid)
          column boundary)
        (outerLevel phase depth) parentX parentY family ∧
      RowFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentX)
        (successorEast phase depth parentX)
        column query boundary family
  column : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {row query boundary : Nat},
    quarterSouth (successorWest phase depth parentY) ≤ row →
    row < quarterNorth (successorEast phase depth parentY) →
    quarterWest (successorWest phase depth parentX) < boundary →
    boundary < quarterEast (successorEast phase depth parentX) →
    ColumnExceptionalCase phase depth parentX parentY grid
      row query boundary →
    ¬ IsSparseCoordinate boundary →
    ∃ family,
      CanonicalCycleAncestorWithinFamily
        (iterateRefine (outerLevel phase depth + 2) grid)
        (verticalPort (iterateRefine (outerLevel phase depth + 2) grid)
          boundary row)
        (outerLevel phase depth) parentX parentY family ∧
      ColumnFamilyTarget grid (outerLevel phase depth) parentX parentY
        (successorWest phase depth parentY)
        (successorEast phase depth parentY)
        row query boundary family

/-- Exceptional targets advance one hierarchy depth once the newly created
sources at that depth have been handled locally. -/
theorem ExceptionalFamilyTargetsAt.succ
    {phase : Phase} {depth : Nat}
    (old : ExceptionalFamilyTargetsAt phase depth)
    (created : CreatedExceptionalFamilyTargetsAt phase (depth + 1)) :
    ExceptionalFamilyTargetsAt phase (depth + 1) := by
  constructor
  · intro grid parentX parentY column query boundary columnLower columnUpper
      boundaryLower boundaryUpper exceptional
    by_cases sparseBoundary : IsSparseCoordinate boundary
    · exact rowSucc_of_sparseBoundary old grid parentX parentY
        columnLower columnUpper boundaryLower boundaryUpper exceptional
        sparseBoundary
    · exact created.row grid parentX parentY columnLower columnUpper
        boundaryLower boundaryUpper exceptional sparseBoundary
  · intro grid parentX parentY row query boundary rowLower rowUpper
      boundaryLower boundaryUpper exceptional
    by_cases sparseBoundary : IsSparseCoordinate boundary
    · exact columnSucc_of_sparseBoundary old grid parentX parentY
        rowLower rowUpper boundaryLower boundaryUpper exceptional
        sparseBoundary
    · exact created.column grid parentX parentY rowLower rowUpper
        boundaryLower boundaryUpper exceptional sparseBoundary

end PairCoverSeamResidualDirectPathFamilyExceptionalRecurrence
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
