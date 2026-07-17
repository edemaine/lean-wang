/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport

/-!
# Semantic exceptional family targets

Coarse-coordinate projection can stop at the lower collar edge, at the source
boundary, or at an ordinary strict query whose transverse source lies on the
lower edge.  This module packages those three row cases and their column duals
as the semantic recurrence state, independently of the finite base checker.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalTargets

open RedCycles RedShadeCycles RedShadeGraph PairCoverSeamArithmetic
  PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseCheck
  PairCoverSeamResidualDirectPathFamilyExceptionalBaseTransport
  PairCoverSeamResidualDirectPathTargets ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence
  Signals.FreeCellLocal

open PairCoverSeamResidualDirectPathFamilyExceptionalBase

set_option maxRecDepth 20000

/-- The three exceptional row-query shapes preserved by target recursion. -/
def RowExceptionalCase
    (phase : Phase) (depth parentX parentY : Nat)
    (grid : Nat → Nat → Index) (column query boundary : Nat) : Prop :=
  (query = quarterSouth (successorWest phase depth parentY) ∧
    Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        column boundary)
      (quadrantAt column boundary) = some .south) ∨
  (query = boundary ∧
    Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        column boundary)
      (quadrantAt column boundary) = some .north) ∨
  (column = quarterSouth (successorWest phase depth parentX) ∧
    quarterSouth (successorWest phase depth parentY) < query ∧
    query < quarterNorth (successorEast phase depth parentY) ∧
    ((query < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < query ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            column boundary)
          (quadrantAt column boundary) = some .north)) ∧
    ¬FitsContainedVerticalChild phase depth parentX parentY
      column query boundary)

/-- Column dual of `RowExceptionalCase`. -/
def ColumnExceptionalCase
    (phase : Phase) (depth parentX parentY : Nat)
    (grid : Nat → Nat → Index) (row query boundary : Nat) : Prop :=
  (query = quarterWest (successorWest phase depth parentX) ∧
    Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        boundary row)
      (quadrantAt boundary row) = some .west) ∨
  (query = boundary ∧
    Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
        boundary row)
      (quadrantAt boundary row) = some .east) ∨
  (row = quarterSouth (successorWest phase depth parentY) ∧
    quarterWest (successorWest phase depth parentX) < query ∧
    query < quarterEast (successorEast phase depth parentX) ∧
    ((query < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < query ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine (outerLevel phase depth + 2) grid)
            boundary row)
          (quadrantAt boundary row) = some .east)) ∧
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      query row boundary)

/-- Same-family targets for every exceptional query at one hierarchy depth. -/
structure ExceptionalFamilyTargetsAt (phase : Phase) (depth : Nat) : Prop where
  row : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column query boundary : Nat},
    quarterSouth (successorWest phase depth parentX) ≤ column →
    column < quarterNorth (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < boundary →
    boundary < quarterNorth (successorEast phase depth parentY) →
    RowExceptionalCase phase depth parentX parentY grid
      column query boundary →
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

/-- The finite exceptional checker supplies the semantic exceptional state. -/
theorem BoundedExceptionalTargetsAt.toExceptionalFamilyTargetsAt
    {phase : Phase} {depth fuel : Nat}
    (targets : BoundedExceptionalTargetsAt phase depth fuel) :
    ExceptionalFamilyTargetsAt phase depth := by
  constructor
  · intro grid parentX parentY column query boundary
      columnLower columnUpper boundaryLower boundaryUpper exceptional
    rcases exceptional with south | north | lowerSource
    · rcases south with ⟨rfl, south⟩
      exact BoundedExceptionalTargetsAt.translateRowSouthLower targets
        grid parentX parentY
        columnLower columnUpper boundaryLower boundaryUpper south
    · rcases north with ⟨rfl, north⟩
      exact BoundedExceptionalTargetsAt.translateRowNorthBoundary targets
        grid parentX parentY
        columnLower columnUpper boundaryLower boundaryUpper north
    · rcases lowerSource with
        ⟨rfl, queryLower, queryUpper, wrongFacing, notFits⟩
      exact BoundedExceptionalTargetsAt.translateRowLowerSource targets
        grid parentX parentY
        queryLower queryUpper boundaryLower boundaryUpper wrongFacing notFits
  · intro grid parentX parentY row query boundary
      rowLower rowUpper boundaryLower boundaryUpper exceptional
    rcases exceptional with west | east | lowerSource
    · rcases west with ⟨rfl, west⟩
      exact BoundedExceptionalTargetsAt.translateColumnWestLower targets
        grid parentX parentY
        boundaryLower boundaryUpper rowLower rowUpper west
    · rcases east with ⟨rfl, east⟩
      exact BoundedExceptionalTargetsAt.translateColumnEastBoundary targets
        grid parentX parentY
        boundaryLower boundaryUpper rowLower rowUpper east
    · rcases lowerSource with
        ⟨rfl, queryLower, queryUpper, wrongFacing, notFits⟩
      exact BoundedExceptionalTargetsAt.translateColumnLowerSource targets
        grid parentX parentY
        queryLower queryUpper boundaryLower boundaryUpper wrongFacing notFits

/-- Certified even depth-zero semantic exceptional targets. -/
theorem evenBase : ExceptionalFamilyTargetsAt .even 0 :=
  BoundedExceptionalTargetsAt.toExceptionalFamilyTargetsAt evenTargets

/-- Certified odd depth-zero semantic exceptional targets. -/
theorem oddBase : ExceptionalFamilyTargetsAt .odd 0 :=
  BoundedExceptionalTargetsAt.toExceptionalFamilyTargetsAt oddTargets

end PairCoverSeamResidualDirectPathFamilyExceptionalTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
