/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedConsecutiveFreeGrid
import LeanWang.Robinson.Closed104.HierarchyRecurrence
import LeanWang.Robinson.Closed104.ShadedObstructionGeometryCover

/-!
# Forward forcing for the shaded routed scaffold

The finite obstruction audit and the unbounded free-grid construction meet at
one hierarchy-localization property.  Once every selected boundary in a light
Robinson board can be covered by one audited subboard, the routed corridors
carry arbitrarily large fixed-corner payload squares.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedRoutedScaffoldForward

open HierarchyEmbedding OrientedRedCycles RedCycles RedShadeCycles
  ShadedConsecutiveFreeGrid ShadedObstructionGeometryCover

set_option maxRecDepth 20000

/-- Every selected boundary in either canonical light board used at a requested
size is localized by an audited obstruction-geometry board. -/
def LightBoardPairCovers : Prop :=
  forall {T : TileSet} {seed : WangTile}
      {x : Int × Int -> TileIn
        (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)},
    forall (decoded : ShadedRoutedPlaneDecode.Decoded x)
      (size : Nat) (coarseOrigin : Int × Int),
      let level := 2 * (1 + size)
      let coarse := ShadedPlaneShadeGrid.coarseGrid decoded
        (level + 2) coarseOrigin
      let state := ShadedPlaneShadeGrid.stateGrid decoded
        (ShadedPlaneShadeGrid.fineParentOrigin decoded
          (level + 2) coarseOrigin)
      (CycleShade state
          (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) .light ->
        PairCover (iterateRefine (level + 2) coarse) state
          (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)) ∧
      (CycleShade state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) .light ->
        PairCover (iterateRefine (level + 2) coarse) state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)))

set_option maxHeartbeats 1000000 in
-- The two dependent grid branches repeatedly unfold the routed payload proof.
/-- The hierarchy pair-cover invariant supplies the forward half of the routed
scaffold equivalence. -/
theorem forcesRoutedFixedCornerSquares
    (covers : LightBoardPairCovers) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold := by
  intro T seed htiles size hsize
  rcases htiles with ⟨x, hx⟩
  let decoded := ShadedRoutedPlaneDecode.decode hx
  let level := 2 * (1 + size)
  obtain ⟨coarseOrigin, coarseOrigin_zero⟩ :=
    HierarchyRecurrence.every_type_occurs decoded.tower
      (level + 2) (0, 0) 0
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded
    (level + 2) coarseOrigin
  have coarseRoot : coarse 0 0 = 0 := by
    simpa [coarse, ShadedPlaneShadeGrid.coarseGrid,
      HierarchyEmbedding.natGridAt, Desubstitution.shift] using
        coarseOrigin_zero
  let parentOrigin := ShadedPlaneShadeGrid.fineParentOrigin decoded
    (level + 2) coarseOrigin
  have parentGrid :
      natGridAt decoded.parent parentOrigin =
        iterateRefine (level + 2) coarse := by
    exact ShadedPlaneShadeGrid.parentGrid_eq_iterateRefine
      decoded (level + 2) coarseOrigin
  have pairCovers := covers decoded size coarseOrigin
  rcases unboundedConsecutiveMarkedFreeGrid_with_light
      decoded size coarseOrigin coarseRoot with
    ⟨cycle, shaded, ⟨grid⟩⟩ | ⟨cycle, shaded, ⟨grid⟩⟩
  · have pairCover := pairCovers.1 shaded
    rw [← parentGrid] at cycle grid pairCover
    have crossing := pairCover.localCover
      |>.crossingObstruction (ShadedPlaneSignalGrid.valid decoded parentOrigin)
    exact tileableFixedCornerSquare_crop hsize (by omega)
      (ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive
        decoded parentOrigin grid cycle shaded crossing)
  · have pairCover := pairCovers.2 shaded
    rw [← parentGrid] at cycle grid pairCover
    have crossing := pairCover.localCover
      |>.crossingObstruction (ShadedPlaneSignalGrid.valid decoded parentOrigin)
    exact tileableFixedCornerSquare_crop hsize (by omega)
      (ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive
        decoded parentOrigin grid cycle shaded crossing)

end ShadedRoutedScaffoldForward
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
