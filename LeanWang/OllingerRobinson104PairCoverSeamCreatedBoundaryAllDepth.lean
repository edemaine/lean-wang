/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedBoundaryFar

/-!
# Created-boundary paths at every depth

Two coordinates lie in the same depth-two macrocell, adjacent macrocells, or
have a complete macrocell between them.  The local and pair certificates cover
the first two cases; the query-facing parallel-target certificate covers the
third.  Consequently created-boundary paths require no hierarchy induction.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundaryAllDepth

open PairCoverSeamCreatedBoundaryPaths ShadedFreeLineRecurrence

/-- Created-boundary seam paths hold at an arbitrary hierarchy phase and
depth. -/
theorem atDepth (phase : Phase) (depth : Nat) :
    CreatedBoundaryPathsAt phase depth := by
  constructor
  · intro grid parentX parentY column row boundary
      columnWest columnEast _rowSouth _rowNorth _boundarySouth _boundaryNorth
      wrongFacing _notFits createdBoundary
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
    exact PairCoverSeamCreatedBoundaryFar.vertical
      phase depth grid parentX parentY wrongFacing createdBoundary far
  · intro grid parentX parentY column row boundary
      _columnWest _columnEast rowSouth rowNorth _boundaryWest _boundaryEast
      wrongFacing _notFits createdBoundary
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
    exact PairCoverSeamCreatedBoundaryFar.horizontal
      phase depth grid parentX parentY wrongFacing createdBoundary far

theorem allDepth (phase : Phase) :
    ∀ depth, CreatedBoundaryPathsAt phase depth :=
  atDepth phase

theorem even : ∀ depth, CreatedBoundaryPathsAt .even depth :=
  allDepth .even

theorem odd : ∀ depth, CreatedBoundaryPathsAt .odd depth :=
  allDepth .odd

end PairCoverSeamCreatedBoundaryAllDepth
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
