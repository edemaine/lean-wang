/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedBoundaryFar
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedSourceBoundaryTransport
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyExceptionalRecurrence
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilyTargetOfPath

/-! Created-boundary exceptional row targets at every hierarchy depth. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalCreatedRow

open RedCycles RedShadeCycles RedShadeGraph PairCoverSeamArithmetic
  PairCoverSeamCreatedSourceBoundaryTransport PairCoverSeamPathSearch
  PairCoverSeamPathTranslation PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets
  PairCoverSeamResidualDirectPathFamilyTargetOfPath
  PairCoverSeamResidualDirectPathTargets RefinedCoordinateProjection
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem queryGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  calc
    _ = iterateRefine (refinementDepth phase (depth + 1) + 2) grid :=
      globalGrid_eq_total phase (depth + 1) grid
    _ = _ := by
      congr 1
      simp only [outerLevel, refinementDepth]
      omega

private theorem createdVerticalPath
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) ≤ column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
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
          (quadrantAt column boundary) = some .north))
    (createdBoundary : ¬ IsSparseCoordinate boundary) :
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX)
      column row boundary := by
  by_cases sameBlock : row / 8 = boundary / 8
  · exact PairCoverSeamCreatedBoundarySameBlock.vertical phase depth grid
      parentX parentY columnWest columnEast wrongFacing createdBoundary
      sameBlock
  by_cases adjacent :
      row / 8 + 1 = boundary / 8 ∨ boundary / 8 + 1 = row / 8
  · exact PairCoverSeamCreatedBoundaryAdjacent.vertical phase depth grid
      parentX parentY columnWest columnEast wrongFacing createdBoundary
      adjacent
  have far : row / 8 + 1 < boundary / 8 ∨
      boundary / 8 + 1 < row / 8 := by
    omega
  exact PairCoverSeamCreatedBoundaryFar.vertical phase depth grid
    parentX parentY wrongFacing createdBoundary far

set_option maxHeartbeats 2000000 in
-- Source ancestry and the selected path carry a dependent hierarchy family.
/-- Every exceptional row query with a boundary created by the latest two
substitutions has a same-family target. -/
theorem row
    {phase : Phase} {depth : Nat}
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
    (createdBoundary : ¬ IsSparseCoordinate boundary) :
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
  have gridEq := queryGrid_eq_outerGrid phase depth grid
  have sourceInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [gridEq]
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
  have hierarchy := sourceAncestorsWithinAt phase (depth + 1)
    grid parentX parentY
  have sourceInterior' : Signals.horizontalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
      (quadrantAt column boundary) ≠ none := by
    rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
    exact sourceInterior
  have sourceAncestor := hierarchy.horizontal
    (by
      unfold InCollar
      constructor
      · simp only [quarterSouth, quarterWest] at columnLower ⊢
        omega
      · simpa only [quarterNorth, quarterEast] using columnUpper)
    (by
      unfold InCollar
      constructor
      · simp only [quarterSouth, quarterWest] at boundaryLower ⊢
        omega
      · simpa only [quarterNorth, quarterEast] using boundaryUpper)
    sourceInterior'
  have sourceAncestor' : CanonicalCycleAncestorWithin
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (horizontalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (outerLevel phase (depth + 1)) parentX parentY := by
    simpa only [SparseFreeLinePlaneLocalStep.refinedGrid_succ] using
      sourceAncestor
  rcases CanonicalCycleAncestorWithin.exists_family sourceAncestor' with
    ⟨family, sourceFamily⟩
  have sourceFamilyOuter := sourceFamily
  rw [gridEq] at sourceFamilyOuter
  have columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) ≤ column := by
    simpa only [quarterSouth, quarterWest] using columnLower
  have columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX) := by
    simpa only [quarterNorth, quarterEast] using columnUpper
  rcases exceptional with south | north | lowerSource
  · rcases south with ⟨rfl, south⟩
    have south' : Signals.horizontalInterior?
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) column boundary)
        (quadrantAt column boundary) = some .south := by
      rw [gridEq]
      exact south
    have path := createdVerticalPath phase depth grid parentX parentY
      columnWest columnEast (Or.inl ⟨boundaryLower, south'⟩)
      createdBoundary
    rw [gridEq] at path
    exact ⟨family, sourceFamilyOuter,
      RowFamilyTarget.ofVerticalSeamPath sourceFamilyOuter path⟩
  · rcases north with ⟨queryEq, north⟩
    have north' : Signals.horizontalInterior?
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) column boundary)
        (quadrantAt column boundary) = some .north := by
      rw [gridEq]
      exact north
    have path := PairCoverSeamCreatedSourceBoundaryTransport.vertical
      phase depth grid parentX parentY columnWest columnEast north'
      createdBoundary
    rw [gridEq] at path
    exact ⟨family, sourceFamilyOuter, by
      simpa only [queryEq] using
        RowFamilyTarget.ofVerticalSeamPath sourceFamilyOuter path⟩
  · rcases lowerSource with
      ⟨rfl, _queryLower, _queryUpper, wrongFacing, _notFits⟩
    have wrongFacing' :
        (query < boundary ∧
          Signals.horizontalInterior?
            (componentAt (iterateRefine 2
              (refinedGrid phase (depth + 1) grid))
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary)
            (quadrantAt
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary) = some .south) ∨
        (boundary < query ∧
          Signals.horizontalInterior?
            (componentAt (iterateRefine 2
              (refinedGrid phase (depth + 1) grid))
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary)
            (quadrantAt
              (quarterSouth (successorWest phase (depth + 1) parentX))
              boundary) = some .north) := by
      rw [gridEq]
      exact wrongFacing
    have path := createdVerticalPath phase depth grid parentX parentY
      columnWest columnEast wrongFacing' createdBoundary
    rw [gridEq] at path
    exact ⟨family, sourceFamilyOuter,
      RowFamilyTarget.ofVerticalSeamPath sourceFamilyOuter path⟩

end PairCoverSeamResidualDirectPathFamilyExceptionalCreatedRow
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
