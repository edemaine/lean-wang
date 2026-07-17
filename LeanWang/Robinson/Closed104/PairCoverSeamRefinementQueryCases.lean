/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamRefinementCoordinates

/-!
# Projected residual-query stopping cases

Projection across two substitutions preserves a strict query/source relation
except at two geometrically forced stopping cases: a lower-facing query may
land on the lower collar edge, and an upper-facing query may land on its
source boundary.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamRefinementQueryCases

open RedShadeCycles RedShadeGraphRefinement PairCoverSeamArithmetic
  PairCoverSeamRefinementCoordinates RefinedCoordinateProjection
  ShadedFreeLineRecurrence

/-- Projection alternatives for a query below its sparse source boundary. -/
inductive ProjectedBelow (lower upper query boundary : Nat) : Prop where
  | lowerEdge (queryEq : query = lower) (queryBelow : query < boundary)
  | strict (queryLower : lower < query) (queryUpper : query < upper)
      (queryBelow : query < boundary)

/-- Projection alternatives for a query above its sparse source boundary. -/
inductive ProjectedAbove (lower upper query boundary : Nat) : Prop where
  | sourceBoundary (queryEq : query = boundary)
  | strict (queryLower : lower < query) (queryUpper : query < upper)
      (queryAbove : boundary < query)

/-- A fine query below a literal sparse boundary projects either to an
ordinary strict query or exactly to the lower collar edge. -/
theorem projectedBelow_sparseBoundary
    {phase : Phase} {depth parent query boundary oldBoundary : Nat}
    (queryLower : quarterWest (successorWest phase (depth + 1) parent) < query)
    (queryUpper : query <
      quarterEast (successorEast phase (depth + 1) parent))
    (boundarySparse : sparseCoordinate oldBoundary = boundary)
    (below : query < boundary) :
    ProjectedBelow
      (quarterWest (successorWest phase depth parent))
      (quarterEast (successorEast phase depth parent))
      (coarseCoordinate query) oldBoundary := by
  have projectedBounds := coarse_successor_bounds_or_lower queryLower queryUpper
  have projectedBelow : coarseCoordinate query < oldBoundary := by
    apply coarseCoordinate_lt_of_lt_sparseCoordinate
    simpa only [boundarySparse] using below
  rcases projectedBounds with lower | strict
  · exact .lowerEdge lower projectedBelow
  · exact .strict strict.1 strict.2 projectedBelow

/-- A fine query above a literal sparse boundary projects either to an
ordinary strict query or exactly to the source boundary. -/
theorem projectedAbove_sparseBoundary
    {phase : Phase} {depth parent query boundary oldBoundary : Nat}
    (queryLower : quarterWest (successorWest phase (depth + 1) parent) < query)
    (queryUpper : query <
      quarterEast (successorEast phase (depth + 1) parent))
    (oldBoundaryLower :
      quarterWest (successorWest phase depth parent) < oldBoundary)
    (boundarySparse : sparseCoordinate oldBoundary = boundary)
    (above : boundary < query) :
    ProjectedAbove
      (quarterWest (successorWest phase depth parent))
      (quarterEast (successorEast phase depth parent))
      (coarseCoordinate query) oldBoundary := by
  have projectedBounds := coarse_successor_bounds_of_fine_bounds
    queryLower queryUpper
  have boundaryLe : oldBoundary ≤ coarseCoordinate query := by
    apply le_coarseCoordinate_of_sparseCoordinate_lt
    simpa only [boundarySparse] using above
  rcases boundaryLe.eq_or_lt with equal | strict
  · exact .sourceBoundary equal.symm
  · exact .strict (oldBoundaryLower.trans strict) projectedBounds.2 strict

end PairCoverSeamRefinementQueryCases
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
