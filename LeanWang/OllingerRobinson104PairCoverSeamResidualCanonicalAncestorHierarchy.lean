/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBaseTransport
import LeanWang.OllingerRobinson104PairCoverSeamRefinementCoordinates
import LeanWang.OllingerRobinson104SparseFreeLinePlaneLocalStep

/-!
# Canonical residual-source ancestors at every hierarchy depth

The transported even/odd base and the two-substitution recurrence give named
cycle ancestors in every successor board of every arbitrary coarse grid.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalAncestorHierarchy

open RedCycles RedShadeCycles PairCoverSeamArithmetic
  PairCoverSeamRefinementCoordinates
  PairCoverSeamResidualCanonicalAncestorRecurrence
  PairCoverSeamResidualCanonicalAncestorBaseAudit
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem stepAt
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {blockX blockY : Nat}
    (old : SourceAncestorsIn (refinedGrid phase (depth + 1) grid)
      (successorWest phase depth blockX)
      (successorEast phase depth blockX)
      (successorWest phase depth blockY)
      (successorEast phase depth blockY)) :
    SourceAncestorsIn (refinedGrid phase (depth + 2) grid)
      (successorWest phase (depth + 1) blockX)
      (successorEast phase (depth + 1) blockX)
      (successorWest phase (depth + 1) blockY)
      (successorEast phase (depth + 1) blockY) := by
  let currentDepth := refinementDepth phase (depth + 1)
  let root := iterateRefine (currentDepth - 1) grid
  have currentDepth_pos : 0 < currentDepth := by
    dsimp [currentDepth]
    simp [refinementDepth]
  have oldGrid : iterateRefine 1 root =
      refinedGrid phase (depth + 1) grid := by
    dsimp [root, currentDepth]
    rw [PlaneRedBoards.iterateRefine_add]
    unfold refinedGrid
    congr 1
    omega
  have newGrid : iterateRefine 3 root =
      refinedGrid phase (depth + 2) grid := by
    dsimp [root, currentDepth]
    rw [PlaneRedBoards.iterateRefine_add]
    unfold refinedGrid
    congr 1
    simp [refinementDepth]
    omega
  have lifted := PairCoverSeamResidualCanonicalAncestorRecurrence.step root
    (by simpa only [oldGrid] using old)
  rw [newGrid] at lifted
  simpa only [successorWest_succ, successorEast_succ] using lifted

theorem sourceAncestorsAt (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (blockX blockY : Nat) :
    SourceAncestorsIn (refinedGrid phase (depth + 1) grid)
      (successorWest phase depth blockX)
      (successorEast phase depth blockX)
      (successorWest phase depth blockY)
      (successorEast phase depth blockY) := by
  induction depth with
  | zero =>
      have base :=
        PairCoverSeamResidualCanonicalAncestorBaseTransport.sourceAncestorsIn
          phase grid blockX blockY
      cases phase <;>
        simpa [refinedGrid, levels, largeLevel, largeWest, largeEast,
          successorWest, successorEast, west, east, scale, refinementDepth,
          Phase.factor, Phase.extra] using base
  | succ depth ih =>
      exact stepAt ih

/-- Compatibility with the original factorized residual-source interface.
The named hierarchy theorem is stronger: it also handles created boundaries. -/
theorem residualSourceAncestorsAt (phase : Phase) (depth : Nat) :
    PairCoverSeamResidualCycleBridges.ResidualSourceAncestorsAt phase depth := by
  constructor
  · intro grid parentX parentY column boundary
      columnWest columnEast boundarySouth boundaryNorth interior _
    have hierarchy := sourceAncestorsAt phase (depth + 1)
      grid parentX parentY
    have interior' : Signals.horizontalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) column boundary)
        (quadrantAt column boundary) ≠ none := by
      rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      exact interior
    have named := hierarchy.horizontal
      (by
        constructor
        · unfold quarterWest at columnWest ⊢
          omega
        · exact columnEast)
      (by
        constructor
        · unfold quarterSouth at boundarySouth
          unfold quarterWest
          omega
        · simpa [quarterNorth, quarterEast] using boundaryNorth)
      interior'
    have result := named.toCycleAncestor
    simpa only [SparseFreeLinePlaneLocalStep.refinedGrid_succ] using result
  · intro grid parentX parentY boundary row
      boundaryWest boundaryEast rowSouth rowNorth interior _
    have hierarchy := sourceAncestorsAt phase (depth + 1)
      grid parentX parentY
    have interior' : Signals.verticalInterior?
        (componentAt (refinedGrid phase (depth + 2) grid) boundary row)
        (quadrantAt boundary row) ≠ none := by
      rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      exact interior
    have named := hierarchy.vertical
      (by
        constructor
        · unfold quarterWest at boundaryWest ⊢
          omega
        · exact boundaryEast)
      (by
        constructor
        · unfold quarterSouth at rowSouth
          unfold quarterWest
          omega
        · simpa [quarterNorth, quarterEast] using rowNorth)
      interior'
    have result := named.toCycleAncestor
    simpa only [SparseFreeLinePlaneLocalStep.refinedGrid_succ] using result

end PairCoverSeamResidualCanonicalAncestorHierarchy
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
