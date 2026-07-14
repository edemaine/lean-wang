/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetPathBase

/-!
# Projection-closed residual family targets

Coarse projection does not preserve the fact that a free-line coordinate was
newly created.  This downstream interface therefore strengthens
`FamilyTargetsAt` by accepting either kind of free-line coordinate.  It stays
outside the finite-audit import cone, so recurrence work does not invalidate
the cached native certificates.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathAllFamilyTargets

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamPathBoundedBase
  PairCoverSeamShadePaths PairCoverSeamPathTranslation
  PairCoverSeamResidualCanonicalAncestorHierarchy
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyTargetOfPath
  PairCoverSeamResidualDirectPathFamilyTargetPathBase
  PairCoverSeamResidualDirectPathTargets RefinedCoordinateProjection
  ShadedFreeLineRecurrence ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Endpoint-selection obligations closed under coarse-coordinate projection.
Unlike `FamilyTargetsAt`, this state does not require the free-line coordinate
to be newly created. -/
structure AllFamilyTargetsAt (phase : Phase) (depth : Nat) : Prop where
  row : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    (((row < boundary) ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      ((boundary < row) ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .north)) →
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
        column row boundary family
  column : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    (((column < boundary) ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      ((boundary < column) ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .east)) →
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
        row column boundary family

/-- Projection-closed targets supply the created-free-line target interface. -/
theorem AllFamilyTargetsAt.toFamilyTargetsAt
    {phase : Phase} {depth : Nat}
    (targets : AllFamilyTargetsAt phase depth) :
    FamilyTargetsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary _createdRow orientation
    exact targets.row grid parentX parentY columnWest columnEast rowSouth
      rowNorth boundarySouth boundaryNorth notFits sparseBoundary orientation
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary _createdColumn orientation
    exact targets.column grid parentX parentY columnWest columnEast
      boundaryWest boundaryEast rowSouth rowNorth notFits sparseBoundary
      orientation

private theorem evenQueryGrid_eq_refinedGrid
    (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid .even 1 grid) =
      refinedGrid .even 2 grid := by
  exact (SparseFreeLinePlaneLocalStep.refinedGrid_succ .even 1 grid).symm

private theorem evenQueryGrid_eq_outerGrid
    (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid .even 1 grid) =
      iterateRefine (outerLevel .even 1 + 2) grid := by
  calc
    _ = iterateRefine (refinementDepth .even 1 + 2) grid :=
      PairCoverSeamPathTranslation.globalGrid_eq_total .even 1 grid
    _ = _ := by
      congr 1

private theorem inCollar_of_horizontal_bounds
    {west east coordinate : Nat}
    (lower : quarterWest west < coordinate)
    (upper : coordinate < quarterEast east) :
    InCollar west east coordinate := by
  constructor
  · omega
  · exact upper

private theorem inCollar_of_vertical_bounds
    {south north coordinate : Nat}
    (lower : quarterSouth south < coordinate)
    (upper : coordinate < quarterNorth north) :
    InCollar south north coordinate := by
  constructor
  · simp only [quarterSouth] at lower
    simp only [quarterWest]
    omega
  · simpa only [quarterNorth, quarterEast] using upper

set_option maxHeartbeats 1000000 in
-- The selected source family occurs dependently in the target conclusion.
/-- The cached even depth-one paths establish the projection-closed base. -/
theorem evenBase : AllFamilyTargetsAt .even 0 := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits _sparseBoundary wrongFacing
    have sourceInterior : Signals.horizontalInterior?
        (componentAt (refinedGrid .even 2 grid) column boundary)
        (quadrantAt column boundary) ≠ none := by
      rw [← evenQueryGrid_eq_refinedGrid grid]
      rcases wrongFacing with wrongFacing | wrongFacing
      · rw [wrongFacing.2]
        simp
      · rw [wrongFacing.2]
        simp
    have ancestor :=
      (sourceAncestorsWithinAt .even 1 grid parentX parentY).horizontal
        (inCollar_of_horizontal_bounds columnWest columnEast)
        (inCollar_of_vertical_bounds boundarySouth boundaryNorth)
        sourceInterior
    rcases CanonicalCycleAncestorWithin.exists_family ancestor with
      ⟨family, sourceFamily⟩
    have boardEq : refinedGrid .even 2 grid =
        iterateRefine (outerLevel .even 1 + 2) grid :=
      (evenQueryGrid_eq_refinedGrid grid).symm.trans
        (evenQueryGrid_eq_outerGrid grid)
    rw [boardEq] at sourceFamily
    have wrongFacing' := wrongFacing
    rw [evenQueryGrid_eq_outerGrid grid] at wrongFacing'
    refine ⟨family, sourceFamily, ?_⟩
    exact BoundedPaths.rowFamilyTarget evenPaths grid parentX parentY
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      wrongFacing' notFits sourceFamily
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits _sparseBoundary wrongFacing
    have sourceInterior : Signals.verticalInterior?
        (componentAt (refinedGrid .even 2 grid) boundary row)
        (quadrantAt boundary row) ≠ none := by
      rw [← evenQueryGrid_eq_refinedGrid grid]
      rcases wrongFacing with wrongFacing | wrongFacing
      · rw [wrongFacing.2]
        simp
      · rw [wrongFacing.2]
        simp
    have ancestor :=
      (sourceAncestorsWithinAt .even 1 grid parentX parentY).vertical
        (inCollar_of_horizontal_bounds boundaryWest boundaryEast)
        (inCollar_of_vertical_bounds rowSouth rowNorth)
        sourceInterior
    rcases CanonicalCycleAncestorWithin.exists_family ancestor with
      ⟨family, sourceFamily⟩
    have boardEq : refinedGrid .even 2 grid =
        iterateRefine (outerLevel .even 1 + 2) grid :=
      (evenQueryGrid_eq_refinedGrid grid).symm.trans
        (evenQueryGrid_eq_outerGrid grid)
    rw [boardEq] at sourceFamily
    have wrongFacing' := wrongFacing
    rw [evenQueryGrid_eq_outerGrid grid] at wrongFacing'
    refine ⟨family, sourceFamily, ?_⟩
    exact BoundedPaths.columnFamilyTarget evenPaths grid parentX parentY
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      wrongFacing' notFits sourceFamily

end PairCoverSeamResidualDirectPathAllFamilyTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
