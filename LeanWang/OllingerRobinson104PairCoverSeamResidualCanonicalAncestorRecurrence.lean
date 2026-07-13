/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestors
import LeanWang.OllingerRobinson104PairCoverSeamResidualCyclePredecessorTransport

/-!
# Recurrence for canonical residual-source ancestors

The stable collar begins one quarter before a hierarchy board and excludes its
east or north endpoint.  Under two substitutions this collar projects into
itself.  Sparse selected boundaries use the certified even predecessor;
created selected boundaries terminate at the local hierarchy cycle.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamResidualCanonicalAncestorRecurrence

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamShadePaths PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCyclePredecessorTransport
  PairCoverSeamResidualCanonicalAncestors
  RefinedCoordinateProjection Signals.FreeCellLocal

set_option maxRecDepth 20000

def InCollar (west east coordinate : Nat) : Prop :=
  quarterWest west - 1 ≤ coordinate ∧ coordinate < quarterEast east

/-- Every live horizontal or vertical selector in one hierarchy collar has a
named canonical cycle ancestor. -/
structure SourceAncestorsIn
    (grid : Nat → Nat → Index) (west east south north : Nat) : Prop where
  horizontal : ∀ {column boundary : Nat},
    InCollar west east column →
    InCollar south north boundary →
    Signals.horizontalInterior?
      (componentAt grid column boundary) (quadrantAt column boundary) ≠ none →
    CanonicalCycleAncestor grid (horizontalPort grid column boundary)
  vertical : ∀ {boundary row : Nat},
    InCollar west east boundary →
    InCollar south north row →
    Signals.verticalInterior?
      (componentAt grid boundary row) (quadrantAt boundary row) ≠ none →
    CanonicalCycleAncestor grid (verticalPort grid boundary row)

/-- Source ancestry retaining the relationship between every reached cycle
and the enclosing canonical hierarchy block. -/
structure SourceAncestorsWithin
    (grid : Nat → Nat → Index)
    (outerLevel outerBlockX outerBlockY west east south north : Nat) : Prop where
  horizontal : ∀ {column boundary : Nat},
    InCollar west east column →
    InCollar south north boundary →
    Signals.horizontalInterior?
      (componentAt grid column boundary) (quadrantAt column boundary) ≠ none →
    CanonicalCycleAncestorWithin grid (horizontalPort grid column boundary)
      outerLevel outerBlockX outerBlockY
  vertical : ∀ {boundary row : Nat},
    InCollar west east boundary →
    InCollar south north row →
    Signals.verticalInterior?
      (componentAt grid boundary row) (quadrantAt boundary row) ≠ none →
    CanonicalCycleAncestorWithin grid (verticalPort grid boundary row)
      outerLevel outerBlockX outerBlockY

theorem SourceAncestorsWithin.toSourceAncestorsIn
    {grid : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY west east south north : Nat}
    (ancestors : SourceAncestorsWithin grid outerLevel outerBlockX outerBlockY
      west east south north) :
    SourceAncestorsIn grid west east south north where
  horizontal columnBounds boundaryBounds interior :=
    (ancestors.horizontal columnBounds boundaryBounds interior).toCanonical
  vertical boundaryBounds rowBounds interior :=
    (ancestors.vertical boundaryBounds rowBounds interior).toCanonical

set_option maxHeartbeats 3000000 in
-- Both selector endpoints depend on the equality between nested refinements.
/-- One two-substitution step preserves source ancestry in the scaled collar. -/
theorem step
    (root : Nat → Nat → Index) {west east south north : Nat}
    (old : SourceAncestorsIn (iterateRefine 1 root)
      west east south north) :
    SourceAncestorsIn (iterateRefine 3 root)
      (4 * west) (4 * east) (4 * south) (4 * north) := by
  have hgrid : iterateRefine 2 (iterateRefine 1 root) =
      iterateRefine 3 root := by
    simpa using PlaneRedBoards.iterateRefine_add 2 1 root
  constructor
  · intro column boundary columnBounds boundaryBounds interior
    by_cases sparseBoundary : IsSparseCoordinate boundary
    · have interior' : Signals.horizontalInterior?
          (componentAt (iterateRefine 2 (iterateRefine 1 root))
            column boundary) (quadrantAt column boundary) ≠ none := by
        rw [hgrid]
        exact interior
      rcases horizontalPredecessor (iterateRefine 1 root)
          column boundary sparseBoundary interior' with
        ⟨oldColumn, oldBoundary, sameColumnBlock, boundarySparse,
          oldInterior, connector⟩
      have oldColumnBounds : InCollar west east oldColumn :=
        predecessor_in_collar_of_collar sameColumnBlock
          columnBounds.1 columnBounds.2
      have oldBoundaryBounds : InCollar south north oldBoundary :=
        sparse_preimage_in_collar boundarySparse
          boundaryBounds.1 boundaryBounds.2
      have ancestor := old.horizontal oldColumnBounds oldBoundaryBounds
        oldInterior
      have sourceLive := horizontalPort_present_of_interior oldInterior
      have fineAncestor := ancestor.refineSparse sourceLive
      have result := fineAncestor.of_evenPath connector
      simpa [hgrid] using result
    · exact PairCoverSeamResidualCanonicalAncestors.horizontalCreated
        root column boundary sparseBoundary interior
  · intro boundary row boundaryBounds rowBounds interior
    by_cases sparseBoundary : IsSparseCoordinate boundary
    · have interior' : Signals.verticalInterior?
          (componentAt (iterateRefine 2 (iterateRefine 1 root))
            boundary row) (quadrantAt boundary row) ≠ none := by
        rw [hgrid]
        exact interior
      rcases verticalPredecessor (iterateRefine 1 root)
          boundary row sparseBoundary interior' with
        ⟨oldBoundary, oldRow, sameRowBlock, boundarySparse,
          oldInterior, connector⟩
      have oldBoundaryBounds : InCollar west east oldBoundary :=
        sparse_preimage_in_collar boundarySparse
          boundaryBounds.1 boundaryBounds.2
      have oldRowBounds : InCollar south north oldRow :=
        predecessor_in_collar_of_collar sameRowBlock
          rowBounds.1 rowBounds.2
      have ancestor := old.vertical oldBoundaryBounds oldRowBounds oldInterior
      have sourceLive := verticalPort_present_of_interior oldInterior
      have fineAncestor := ancestor.refineSparse sourceLive
      have result := fineAncestor.of_evenPath connector
      simpa [hgrid] using result
    · exact PairCoverSeamResidualCanonicalAncestors.verticalCreated
        root boundary row sparseBoundary interior

end PairCoverSeamResidualCanonicalAncestorRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
