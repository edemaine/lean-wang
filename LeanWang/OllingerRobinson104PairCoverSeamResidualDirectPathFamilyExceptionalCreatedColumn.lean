/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedBoundaryFar
import LeanWang.OllingerRobinson104PairCoverSeamCreatedSourceBoundaryTransport
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalRecurrence
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetOfPath

/-! Created-boundary exceptional column targets at every hierarchy depth. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyExceptionalCreatedColumn

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

private theorem createdHorizontalPath
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX parentY : Nat) {row column boundary : Nat}
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) ≤ row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
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
          (quadrantAt boundary row) = some .east))
    (createdBoundary : ¬ IsSparseCoordinate boundary) :
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY)
      row column boundary := by
  by_cases sameBlock : column / 8 = boundary / 8
  · exact PairCoverSeamCreatedBoundarySameBlock.horizontal phase depth grid
      parentX parentY rowSouth rowNorth wrongFacing createdBoundary sameBlock
  by_cases adjacent :
      column / 8 + 1 = boundary / 8 ∨ boundary / 8 + 1 = column / 8
  · exact PairCoverSeamCreatedBoundaryAdjacent.horizontal phase depth grid
      parentX parentY rowSouth rowNorth wrongFacing createdBoundary adjacent
  have far : column / 8 + 1 < boundary / 8 ∨
      boundary / 8 + 1 < column / 8 := by
    omega
  exact PairCoverSeamCreatedBoundaryFar.horizontal phase depth grid
    parentX parentY wrongFacing createdBoundary far

set_option maxHeartbeats 2000000 in
-- Source ancestry and the selected path carry a dependent hierarchy family.
/-- Every exceptional column query with a boundary created by the latest two
substitutions has a same-family target. -/
theorem column
    {phase : Phase} {depth : Nat}
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
    (createdBoundary : ¬ IsSparseCoordinate boundary) :
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
  have gridEq := queryGrid_eq_outerGrid phase depth grid
  have sourceInterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [gridEq]
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
  have hierarchy := sourceAncestorsWithinAt phase (depth + 1)
    grid parentX parentY
  have sourceInterior' : Signals.verticalInterior?
      (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
      (quadrantAt boundary row) ≠ none := by
    rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
    exact sourceInterior
  have sourceAncestor := hierarchy.vertical
    (by
      unfold InCollar
      constructor
      · simp only [quarterWest] at boundaryLower ⊢
        omega
      · exact boundaryUpper)
    (by
      unfold InCollar
      constructor
      · simp only [quarterSouth, quarterWest] at rowLower ⊢
        omega
      · simpa only [quarterNorth, quarterEast] using rowUpper)
    sourceInterior'
  have sourceAncestor' : CanonicalCycleAncestorWithin
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (verticalPort
        (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (outerLevel phase (depth + 1)) parentX parentY := by
    simpa only [SparseFreeLinePlaneLocalStep.refinedGrid_succ] using
      sourceAncestor
  rcases CanonicalCycleAncestorWithin.exists_family sourceAncestor' with
    ⟨family, sourceFamily⟩
  have sourceFamilyOuter := sourceFamily
  rw [gridEq] at sourceFamilyOuter
  rcases exceptional with west | east | lowerSource
  · rcases west with ⟨rfl, west⟩
    have west' : Signals.verticalInterior?
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) boundary row)
        (quadrantAt boundary row) = some .west := by
      rw [gridEq]
      exact west
    have queryBelow :
        quarterWest (successorWest phase (depth + 1) parentX) < boundary :=
      boundaryLower
    have path := createdHorizontalPath phase depth grid parentX parentY
      rowLower rowUpper (Or.inl ⟨queryBelow, west'⟩) createdBoundary
    rw [gridEq] at path
    exact ⟨family, sourceFamilyOuter,
      ColumnFamilyTarget.ofHorizontalSeamPath sourceFamilyOuter path⟩
  · rcases east with ⟨queryEq, east⟩
    have east' : Signals.verticalInterior?
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) boundary row)
        (quadrantAt boundary row) = some .east := by
      rw [gridEq]
      exact east
    have path := PairCoverSeamCreatedSourceBoundaryTransport.horizontal
      phase depth grid parentX parentY rowLower rowUpper east'
      createdBoundary
    rw [gridEq] at path
    exact ⟨family, sourceFamilyOuter, by
      simpa only [queryEq] using
        ColumnFamilyTarget.ofHorizontalSeamPath sourceFamilyOuter path⟩
  · rcases lowerSource with
      ⟨rfl, _queryLower, _queryUpper, wrongFacing, _notFits⟩
    have wrongFacing' :
        (query < boundary ∧
          Signals.verticalInterior?
            (componentAt (iterateRefine 2
              (refinedGrid phase (depth + 1) grid)) boundary
              (quarterSouth (successorWest phase (depth + 1) parentY)))
            (quadrantAt boundary
              (quarterSouth (successorWest phase (depth + 1) parentY))) =
                some .west) ∨
        (boundary < query ∧
          Signals.verticalInterior?
            (componentAt (iterateRefine 2
              (refinedGrid phase (depth + 1) grid)) boundary
              (quarterSouth (successorWest phase (depth + 1) parentY)))
            (quadrantAt boundary
              (quarterSouth (successorWest phase (depth + 1) parentY))) =
                some .east) := by
      rw [gridEq]
      exact wrongFacing
    have path := createdHorizontalPath phase depth grid parentX parentY
      rowLower rowUpper wrongFacing' createdBoundary
    rw [gridEq] at path
    exact ⟨family, sourceFamilyOuter,
      ColumnFamilyTarget.ofHorizontalSeamPath sourceFamilyOuter path⟩

end PairCoverSeamResidualDirectPathFamilyExceptionalCreatedColumn
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
