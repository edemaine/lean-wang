/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedConsecutiveFreeGrid
import LeanWang.OllingerRobinson104ShadedObstructionGeometryCover

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

/-- Every selected boundary in every decoded light board is localized by an
audited obstruction-geometry board. -/
def LightBoardPairCovers : Prop :=
  forall {T : TileSet} {seed : WangTile}
      {x : Int × Int -> TileIn
        (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)},
    forall (decoded : ShadedRoutedPlaneDecode.Decoded x)
      (parentOrigin : Int × Int) (west east south north : Nat),
      CycleOn (natGridAt decoded.parent parentOrigin)
          west east south north ->
        CycleShade (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
          west east south north .light ->
        PairCover (natGridAt decoded.parent parentOrigin)
          (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
          west east south north

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
  let coarseOrigin : Int × Int := (0, 0)
  let level := 2 * (1 + size)
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded
    (level + 2) coarseOrigin
  let parentOrigin := ShadedPlaneShadeGrid.fineParentOrigin decoded
    (level + 2) coarseOrigin
  have parentGrid :
      natGridAt decoded.parent parentOrigin =
        iterateRefine (level + 2) coarse := by
    exact ShadedPlaneShadeGrid.parentGrid_eq_iterateRefine
      decoded (level + 2) coarseOrigin
  rcases unboundedConsecutiveMarkedFreeGrid_with_light
      decoded size coarseOrigin with
    ⟨cycle, shaded, ⟨grid⟩⟩ | ⟨cycle, shaded, ⟨grid⟩⟩
  · rw [← parentGrid] at cycle grid
    have crossing := (covers decoded parentOrigin _ _ _ _ cycle shaded).localCover
      |>.crossingObstruction (ShadedPlaneSignalGrid.valid decoded parentOrigin)
    exact tileableFixedCornerSquare_crop hsize (by omega)
      (ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive
        decoded parentOrigin grid cycle shaded crossing)
  · rw [← parentGrid] at cycle grid
    have crossing := (covers decoded parentOrigin _ _ _ _ cycle shaded).localCover
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
