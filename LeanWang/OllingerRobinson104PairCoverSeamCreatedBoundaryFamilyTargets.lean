/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedBoundaryAdjacent
import LeanWang.OllingerRobinson104PairCoverSeamCreatedLowFamilyAncestors
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Same-family targets for far created boundaries

A far created source need not meet a canonical cycle side at the query line.
The correct invariant is instead that the source's hierarchy family contains
some endpoint accepted by `RowFamilyTarget` or `ColumnFamilyTarget`.  Such an
endpoint may be a noncanonical red segment produced by target refinement.

The adapter below handles same-block and adjacent queries by their finite
local certificates.  Only genuinely far queries consume the family-target
invariant and the exact parity-normalized source ancestor.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundaryFamilyTargets

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamCreatedBoundaryPaths
  PairCoverSeamCreatedBoundaryAdjacent PairCoverSeamCreatedBoundarySameBlock
  PairCoverSeamCreatedLowFamilyAncestors PairCoverSeamCreatedRouteParityAudit
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathTargets RefinedCoordinateProjection
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Endpoint targets in the exact hierarchy family of every far created
source.  Unlike the rejected canonical-side condition, the target is allowed
to be any red segment carrying the same family ancestor. -/
structure FarFamilyTargetsAt (phase : Phase) (depth : Nat) : Prop where
  vertical : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    ((row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .north)) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬IsSparseCoordinate boundary →
    (row / 8 + 1 < boundary / 8 ∨ boundary / 8 + 1 < row / 8) →
    ∀ family,
      InHierarchyFamily (outerLevel phase (depth + 1))
        (if createdParity (boundary % 8) then 1 else 0) family →
      RowFamilyTarget grid (outerLevel phase (depth + 1))
        parentX parentY
        (successorWest phase (depth + 1) parentX)
        (successorEast phase (depth + 1) parentX)
        column row boundary family
  horizontal : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    ((column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .east)) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬IsSparseCoordinate boundary →
    (column / 8 + 1 < boundary / 8 ∨ boundary / 8 + 1 < column / 8) →
    ∀ family,
      InHierarchyFamily (outerLevel phase (depth + 1))
        (if createdParity (boundary % 8) then 1 else 0) family →
      ColumnFamilyTarget grid (outerLevel phase (depth + 1))
        parentX parentY
        (successorWest phase (depth + 1) parentY)
        (successorEast phase (depth + 1) parentY)
        row column boundary family

private theorem queryGrid_eq_outerGrid
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  unfold refinedGrid
  rw [PlaneRedBoards.iterateRefine_add]
  unfold outerLevel refinementDepth
  congr 1
  omega

/-- Same-family targets reconstruct every created-boundary seam path. -/
theorem FarFamilyTargetsAt.toCreatedBoundaryPathsAt
    {phase : Phase} {depth : Nat}
    (targets : FarFamilyTargetsAt phase depth) :
    CreatedBoundaryPathsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      wrongFacing notFits createdBoundary
    by_cases sameBlock : row / 8 = boundary / 8
    · exact PairCoverSeamCreatedBoundarySameBlock.vertical
        phase depth grid parentX parentY columnWest columnEast
        wrongFacing createdBoundary sameBlock
    by_cases adjacent :
        row / 8 + 1 = boundary / 8 ∨ boundary / 8 + 1 = row / 8
    · exact PairCoverSeamCreatedBoundaryAdjacent.vertical
        phase depth grid parentX parentY columnWest columnEast
        wrongFacing createdBoundary adjacent
    have far : row / 8 + 1 < boundary / 8 ∨
        boundary / 8 + 1 < row / 8 := by
      omega
    have sourceInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) column boundary)
        (quadrantAt column boundary) ≠ none := by
      rcases wrongFacing with south | north
      · rw [south.2]
        simp
      · rw [north.2]
        simp
    rcases horizontalCreatedAtExactParity phase depth grid parentX parentY
        columnWest columnEast boundarySouth boundaryNorth createdBoundary
        sourceInterior with ⟨family, source⟩
    have target := targets.vertical grid parentX parentY
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      wrongFacing notFits createdBoundary far family source.inFamily
    have sourceFamily := source.toAncestorFamily
    rw [queryGrid_eq_outerGrid phase depth grid]
    rw [queryGrid_eq_outerGrid phase depth grid] at sourceFamily
    rcases target with target | target
    · rcases target with
        ⟨targetX, targetWest, targetEast, targetInterior, targetFamily⟩
      exact verticalSeamPath_of_sameFamilyTarget rfl
        sourceFamily targetFamily targetWest targetEast targetInterior
    · rcases target with
        ⟨targetY, between, targetInterior, targetFamily⟩
      exact verticalSeamPath_of_sameFamilyBetweenTarget rfl
        sourceFamily targetFamily between targetInterior
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
      wrongFacing notFits createdBoundary
    by_cases sameBlock : column / 8 = boundary / 8
    · exact PairCoverSeamCreatedBoundarySameBlock.horizontal
        phase depth grid parentX parentY rowSouth rowNorth
        wrongFacing createdBoundary sameBlock
    by_cases adjacent :
        column / 8 + 1 = boundary / 8 ∨ boundary / 8 + 1 = column / 8
    · exact PairCoverSeamCreatedBoundaryAdjacent.horizontal
        phase depth grid parentX parentY rowSouth rowNorth
        wrongFacing createdBoundary adjacent
    have far : column / 8 + 1 < boundary / 8 ∨
        boundary / 8 + 1 < column / 8 := by
      omega
    have sourceInterior : Signals.verticalInterior?
        (componentAt (iterateRefine 2
          (refinedGrid phase (depth + 1) grid)) boundary row)
        (quadrantAt boundary row) ≠ none := by
      rcases wrongFacing with west | east
      · rw [west.2]
        simp
      · rw [east.2]
        simp
    rcases verticalCreatedAtExactParity phase depth grid parentX parentY
        boundaryWest boundaryEast rowSouth rowNorth createdBoundary
        sourceInterior with ⟨family, source⟩
    have target := targets.horizontal grid parentX parentY
      columnWest columnEast rowSouth rowNorth boundaryWest boundaryEast
      wrongFacing notFits createdBoundary far family source.inFamily
    have sourceFamily := source.toAncestorFamily
    rw [queryGrid_eq_outerGrid phase depth grid]
    rw [queryGrid_eq_outerGrid phase depth grid] at sourceFamily
    rcases target with target | target
    · rcases target with
        ⟨targetY, targetSouth, targetNorth, targetInterior, targetFamily⟩
      exact horizontalSeamPath_of_sameFamilyTarget rfl
        sourceFamily targetFamily targetSouth targetNorth targetInterior
    · rcases target with
        ⟨targetX, between, targetInterior, targetFamily⟩
      exact horizontalSeamPath_of_sameFamilyBetweenTarget rfl
        sourceFamily targetFamily between targetInterior

end PairCoverSeamCreatedBoundaryFamilyTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
