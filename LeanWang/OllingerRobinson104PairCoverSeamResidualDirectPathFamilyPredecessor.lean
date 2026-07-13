/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathBridges
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorTransport

/-!
# Preserve hierarchy families through residual predecessors

The finite predecessor audit connects every live fine selector on a sparse
boundary to a live coarse selector by an even path.  This file packages that
connector with the canonical-cycle family invariant.  It is the local
two-substitution induction step used by residual target recognition.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyPredecessor

open RedCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamShadePaths PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCyclePredecessorTransport
  PairCoverSeamResidualDirectPathBridges
  RefinedCoordinateProjection
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- An even horizontal predecessor connector preserves the predecessor's
canonical hierarchy family. -/
theorem HorizontalPredecessor.refineFamily
    {grid : Nat → Nat → Index} {column boundary : Nat}
    (predecessor : HorizontalPredecessor grid column boundary)
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (oldAncestor : ∀ {oldColumn oldBoundary : Nat},
      oldColumn / 2 = column / 8 →
      sparseCoordinate oldBoundary = boundary →
      Signals.horizontalInterior?
        (componentAt grid oldColumn oldBoundary)
        (quadrantAt oldColumn oldBoundary) ≠ none →
      CanonicalCycleAncestorWithinFamily grid
        (horizontalPort grid oldColumn oldBoundary)
        outerLevel outerBlockX outerBlockY family) :
    CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
      (horizontalPort (iterateRefine 2 grid) column boundary)
      (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases predecessor with
    ⟨oldColumn, oldBoundary, sameBlock, boundarySparse,
      oldInterior, connector⟩
  exact (oldAncestor sameBlock boundarySparse oldInterior).refineThrough
    (horizontalPort_present_of_interior oldInterior) connector

/-- Vertical dual of `HorizontalPredecessor.refineFamily`. -/
theorem VerticalPredecessor.refineFamily
    {grid : Nat → Nat → Index} {boundary row : Nat}
    (predecessor : VerticalPredecessor grid boundary row)
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (oldAncestor : ∀ {oldBoundary oldRow : Nat},
      oldRow / 2 = row / 8 →
      sparseCoordinate oldBoundary = boundary →
      Signals.verticalInterior?
        (componentAt grid oldBoundary oldRow)
        (quadrantAt oldBoundary oldRow) ≠ none →
      CanonicalCycleAncestorWithinFamily grid
        (verticalPort grid oldBoundary oldRow)
        outerLevel outerBlockX outerBlockY family) :
    CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
      (verticalPort (iterateRefine 2 grid) boundary row)
      (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases predecessor with
    ⟨oldBoundary, oldRow, sameBlock, boundarySparse,
      oldInterior, connector⟩
  exact (oldAncestor sameBlock boundarySparse oldInterior).refineThrough
    (verticalPort_present_of_interior oldInterior) connector

/-- Invoke the audited horizontal predecessor and preserve the supplied
coarse family through its even connector. -/
theorem horizontalFamilyAncestor
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) column boundary)
      (quadrantAt column boundary) ≠ none)
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (oldAncestor : ∀ {oldColumn oldBoundary : Nat},
      oldColumn / 2 = column / 8 →
      sparseCoordinate oldBoundary = boundary →
      Signals.horizontalInterior?
        (componentAt grid oldColumn oldBoundary)
        (quadrantAt oldColumn oldBoundary) ≠ none →
      CanonicalCycleAncestorWithinFamily grid
        (horizontalPort grid oldColumn oldBoundary)
        outerLevel outerBlockX outerBlockY family) :
    CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
      (horizontalPort (iterateRefine 2 grid) column boundary)
      (outerLevel + 2) outerBlockX outerBlockY family :=
  HorizontalPredecessor.refineFamily
    (horizontalPredecessor grid column boundary sparseBoundary interior)
    oldAncestor

/-- Vertical dual of `horizontalFamilyAncestor`. -/
theorem verticalFamilyAncestor
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) boundary row)
      (quadrantAt boundary row) ≠ none)
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (oldAncestor : ∀ {oldBoundary oldRow : Nat},
      oldRow / 2 = row / 8 →
      sparseCoordinate oldBoundary = boundary →
      Signals.verticalInterior?
        (componentAt grid oldBoundary oldRow)
        (quadrantAt oldBoundary oldRow) ≠ none →
      CanonicalCycleAncestorWithinFamily grid
        (verticalPort grid oldBoundary oldRow)
        outerLevel outerBlockX outerBlockY family) :
    CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
      (verticalPort (iterateRefine 2 grid) boundary row)
      (outerLevel + 2) outerBlockX outerBlockY family :=
  VerticalPredecessor.refineFamily
    (verticalPredecessor grid boundary row sparseBoundary interior)
    oldAncestor

end PairCoverSeamResidualDirectPathFamilyPredecessor
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
