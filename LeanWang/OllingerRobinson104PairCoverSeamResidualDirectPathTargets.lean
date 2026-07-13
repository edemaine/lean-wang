/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathBridges

/-!
# Same-family target selection for residual seam paths

This is the finite endpoint obligation left after hierarchy connectivity is
removed.  For the actual family reached by a selected source, choose either a
live transverse target on the query line or a live parallel target strictly
between the query and source.  The generic bridge then supplies the even path.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathTargets

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPaths
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorHierarchy
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence Signals.FreeCellLocal
  SparseFreeLinePlaneBase

set_option maxRecDepth 20000

/-- A row target in the source's hierarchy family. -/
def RowFamilyTarget
    (root : Nat → Nat → Index)
    (outerLevel outerBlockX outerBlockY outerWest outerEast : Nat)
    (column row boundary : Nat) (family : HierarchyFamily) : Prop :=
  (∃ targetX,
    quarterWest outerWest < targetX ∧
    targetX < quarterEast outerEast ∧
    Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row) ≠ none ∧
    CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)
      outerLevel outerBlockX outerBlockY family) ∨
  (∃ targetY,
    StrictBetween row boundary targetY ∧
    Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY) ≠ none ∧
    CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)
      outerLevel outerBlockX outerBlockY family)

/-- Horizontal dual of `RowFamilyTarget`. -/
def ColumnFamilyTarget
    (root : Nat → Nat → Index)
    (outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat)
    (row column boundary : Nat) (family : HierarchyFamily) : Prop :=
  (∃ targetY,
    quarterSouth outerSouth < targetY ∧
    targetY < quarterNorth outerNorth ∧
    Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY) ≠ none ∧
    CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)
      outerLevel outerBlockX outerBlockY family) ∨
  (∃ targetX,
    StrictBetween column boundary targetX ∧
    Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row) ≠ none ∧
    CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)
      outerLevel outerBlockX outerBlockY family)

/-- Endpoint-selection obligations at one recurrence depth. -/
structure FamilyTargetsAt (phase : Phase) (depth : Nat) : Prop where
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
    ¬IsSparseCoordinate row →
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
    ¬IsSparseCoordinate column →
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

private theorem fineGrid_eq
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) :
    iterateRefine 2 (refinedGrid phase (depth + 1) grid) =
      iterateRefine (outerLevel phase (depth + 1) + 2) grid := by
  unfold refinedGrid
  rw [PlaneRedBoards.iterateRefine_add]
  unfold outerLevel refinementDepth
  congr 1
  omega

/-- Same-family endpoint targets instantiate the direct residual paths. -/
theorem FamilyTargetsAt.toDirectPaths
    {phase : Phase} {depth : Nat}
    (targets : FamilyTargetsAt phase depth) :
    DirectResidualPathsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast rowSouth rowNorth boundarySouth boundaryNorth
      notFits sparseBoundary createdRow orientation
    rcases targets.row grid parentX parentY columnWest columnEast
      rowSouth rowNorth boundarySouth boundaryNorth notFits sparseBoundary
      createdRow orientation with ⟨family, sourceFamily, target⟩
    rcases target with target | target
    · rcases target with
        ⟨targetX, targetWest, targetEast, targetInterior, targetFamily⟩
      rw [fineGrid_eq phase depth grid]
      exact verticalSeamPath_of_sameFamilyTarget rfl sourceFamily targetFamily
        targetWest targetEast targetInterior
    · rcases target with
        ⟨targetY, between, targetInterior, targetFamily⟩
      rw [fineGrid_eq phase depth grid]
      exact verticalSeamPath_of_sameFamilyBetweenTarget rfl
        sourceFamily targetFamily between targetInterior
  · intro grid parentX parentY column row boundary
      columnWest columnEast boundaryWest boundaryEast rowSouth rowNorth
      notFits sparseBoundary createdColumn orientation
    rcases targets.column grid parentX parentY columnWest columnEast
      boundaryWest boundaryEast rowSouth rowNorth notFits sparseBoundary
      createdColumn orientation with ⟨family, sourceFamily, target⟩
    rcases target with target | target
    · rcases target with
        ⟨targetY, targetSouth, targetNorth, targetInterior, targetFamily⟩
      rw [fineGrid_eq phase depth grid]
      exact horizontalSeamPath_of_sameFamilyTarget rfl
        sourceFamily targetFamily targetSouth targetNorth targetInterior
    · rcases target with
        ⟨targetX, between, targetInterior, targetFamily⟩
      rw [fineGrid_eq phase depth grid]
      exact horizontalSeamPath_of_sameFamilyBetweenTarget rfl
        sourceFamily targetFamily between targetInterior

end PairCoverSeamResidualDirectPathTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
