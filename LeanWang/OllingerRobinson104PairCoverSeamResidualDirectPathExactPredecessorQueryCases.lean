/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamRefinementQueryCases
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorHierarchy

/-!
# Query cases for exact inherited residual sources

The coordinate trichotomy is paired with the orientation preserved by the
exact source predecessor.  This is the case interface consumed by target
recursion.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorQueryCases

open RedShadeCycles PairCoverSeamArithmetic
  PairCoverSeamRefinementQueryCases
  PairCoverSeamResidualDirectPathExactPredecessorHierarchy
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A horizontal fine query projects to an ordinary south/north query or to
the corresponding lower-edge/source-boundary stopping case. -/
theorem HorizontalExactInheritedSource.projectedQuery
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {parentX parentY column row boundary : Nat}
    (source : HorizontalExactInheritedSource phase depth grid
      parentX parentY column boundary)
    (rowLower : quarterSouth (successorWest phase (depth + 1) parentY) < row)
    (rowUpper : row < quarterNorth (successorEast phase (depth + 1) parentY))
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
          (quadrantAt column boundary) = some .north)) :
    (ProjectedBelow
        (quarterSouth (successorWest phase depth parentY))
        (quarterNorth (successorEast phase depth parentY))
        (coarseCoordinate row) source.oldBoundary ∧
      Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          (coarseCoordinate column) source.oldBoundary)
        (quadrantAt (coarseCoordinate column) source.oldBoundary) =
          some .south) ∨
    (ProjectedAbove
        (quarterSouth (successorWest phase depth parentY))
        (quarterNorth (successorEast phase depth parentY))
        (coarseCoordinate row) source.oldBoundary ∧
      Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          (coarseCoordinate column) source.oldBoundary)
        (quadrantAt (coarseCoordinate column) source.oldBoundary) =
          some .north) := by
  rcases wrongFacing with south | north
  · left
    constructor
    · simpa only [quarterSouth, quarterWest, quarterNorth, quarterEast] using
        projectedBelow_sparseBoundary
          (by simpa only [quarterSouth, quarterWest] using rowLower)
          (by simpa only [quarterNorth, quarterEast] using rowUpper)
          source.boundarySparse south.1
    · exact source.orientationEq.trans south.2
  · right
    constructor
    · simpa only [quarterSouth, quarterWest, quarterNorth, quarterEast] using
        projectedAbove_sparseBoundary
          (by simpa only [quarterSouth, quarterWest] using rowLower)
          (by simpa only [quarterNorth, quarterEast] using rowUpper)
          (by simpa only [quarterSouth, quarterWest] using
            source.oldBoundaryStrictBounds.1)
          source.boundarySparse north.1
    · exact source.orientationEq.trans north.2

/-- Vertical dual of `HorizontalExactInheritedSource.projectedQuery`. -/
theorem VerticalExactInheritedSource.projectedQuery
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {parentX parentY column row boundary : Nat}
    (source : VerticalExactInheritedSource phase depth grid
      parentX parentY boundary row)
    (columnLower :
      quarterWest (successorWest phase (depth + 1) parentX) < column)
    (columnUpper : column <
      quarterEast (successorEast phase (depth + 1) parentX))
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
          (quadrantAt boundary row) = some .east)) :
    (ProjectedBelow
        (quarterWest (successorWest phase depth parentX))
        (quarterEast (successorEast phase depth parentX))
        (coarseCoordinate column) source.oldBoundary ∧
      Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          source.oldBoundary (coarseCoordinate row))
        (quadrantAt source.oldBoundary (coarseCoordinate row)) = some .west) ∨
    (ProjectedAbove
        (quarterWest (successorWest phase depth parentX))
        (quarterEast (successorEast phase depth parentX))
        (coarseCoordinate column) source.oldBoundary ∧
      Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 1) grid)
          source.oldBoundary (coarseCoordinate row))
        (quadrantAt source.oldBoundary (coarseCoordinate row)) = some .east) := by
  rcases wrongFacing with west | east
  · exact Or.inl ⟨projectedBelow_sparseBoundary columnLower columnUpper
      source.boundarySparse west.1, source.orientationEq.trans west.2⟩
  · exact Or.inr ⟨projectedAbove_sparseBoundary columnLower columnUpper
      source.oldBoundaryStrictBounds.1 source.boundarySparse east.1,
      source.orientationEq.trans east.2⟩

end PairCoverSeamResidualDirectPathExactPredecessorQueryCases
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
