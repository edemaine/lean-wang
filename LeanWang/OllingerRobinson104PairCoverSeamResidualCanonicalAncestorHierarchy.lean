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

/-- Canonical cycle level of the successor board at a recurrence depth. -/
def outerLevel (phase : Phase) (depth : Nat) : Nat :=
  2 * (depth + 1) + phase.extra

/-- The successor board's west side is the west side of its canonical cycle. -/
theorem successorWest_eq_canonical
    (phase : Phase) (depth block : Nat) :
    successorWest phase depth block =
      2 ^ outerLevel phase depth * (4 * block + 1) := by
  have power := two_pow_refinementLevel_eq_scale phase (depth + 1)
  have power' : 2 ^ outerLevel phase depth = west phase (depth + 1) := by
    simpa [outerLevel, west] using power
  rw [successorWest, two_pow_refinementDepth_eq_four_mul_west]
  change 4 * west phase (depth + 1) * block + west phase (depth + 1) = _
  rw [power']
  ring

/-- The successor board's east side is the east side of its canonical cycle. -/
theorem successorEast_eq_canonical
    (phase : Phase) (depth block : Nat) :
    successorEast phase depth block =
      2 ^ outerLevel phase depth * (4 * block + 3) := by
  have power := two_pow_refinementLevel_eq_scale phase (depth + 1)
  have power' : 2 ^ outerLevel phase depth = west phase (depth + 1) := by
    simpa [outerLevel, west] using power
  rw [successorEast, two_pow_refinementDepth_eq_four_mul_west]
  change 4 * west phase (depth + 1) * block +
      3 * west phase (depth + 1) = _
  rw [power']
  ring

private theorem stepWithinAt
    {phase : Phase} {depth : Nat} {grid : Nat → Nat → Index}
    {blockX blockY : Nat}
    (old : SourceAncestorsWithin (refinedGrid phase (depth + 1) grid)
      (outerLevel phase depth) blockX blockY
      (successorWest phase depth blockX)
      (successorEast phase depth blockX)
      (successorWest phase depth blockY)
      (successorEast phase depth blockY)) :
    SourceAncestorsWithin (refinedGrid phase (depth + 2) grid)
      (outerLevel phase (depth + 1)) blockX blockY
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
  have lifted := PairCoverSeamResidualCanonicalAncestorRecurrence.stepWithin root
    (successorWest_eq_canonical phase depth blockX)
    (successorEast_eq_canonical phase depth blockX)
    (successorWest_eq_canonical phase depth blockY)
    (successorEast_eq_canonical phase depth blockY)
    (by simpa only [oldGrid] using old)
  rw [newGrid] at lifted
  have levelEq : outerLevel phase depth + 2 =
      outerLevel phase (depth + 1) := by
    simp [outerLevel]
    omega
  simpa only [levelEq, successorWest_succ, successorEast_succ] using lifted

/-- Every successor-board source reaches a canonical cycle whose hierarchy
address lies under that successor board. -/
theorem sourceAncestorsWithinAt (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (blockX blockY : Nat) :
    SourceAncestorsWithin (refinedGrid phase (depth + 1) grid)
      (outerLevel phase depth) blockX blockY
      (successorWest phase depth blockX)
      (successorEast phase depth blockX)
      (successorWest phase depth blockY)
      (successorEast phase depth blockY) := by
  induction depth with
  | zero =>
      have base :=
        PairCoverSeamResidualCanonicalAncestorBaseTransport.sourceAncestorsWithin
          phase grid blockX blockY
      cases phase <;>
        simpa [outerLevel, refinedGrid, levels, largeLevel, largeWest, largeEast,
          successorWest, successorEast, west, east, scale, refinementDepth,
          Phase.factor, Phase.extra] using base
  | succ depth ih =>
      exact stepWithinAt ih

/-- Forgetting hierarchy containment recovers the previous all-depth theorem. -/
theorem sourceAncestorsAt (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (blockX blockY : Nat) :
    SourceAncestorsIn (refinedGrid phase (depth + 1) grid)
      (successorWest phase depth blockX)
      (successorEast phase depth blockX)
      (successorWest phase depth blockY)
      (successorEast phase depth blockY) :=
  (sourceAncestorsWithinAt phase depth grid blockX blockY).toSourceAncestorsIn

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
