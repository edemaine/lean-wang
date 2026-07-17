/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.HierarchyRecurrence
import LeanWang.Robinson.Closed104.OrientedLightGeometry

/-!
# Forward forcing from oriented light-wire geometry

Every sufficiently large decoded Robinson hierarchy contains a consecutive
grid of free rows and columns inside a light board.  The light-wire height
argument supplies the crossing obstructions needed to route the payload at
that grid, directly and without intermediate pair-cover certificates.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightForward

open HierarchyEmbedding OrientedRedCycles RedCycles RedShadeCycles
  ShadedConsecutiveFreeGrid ShadedObstructionGeometry

set_option maxRecDepth 20000
/-- The oriented light-wire height invariant supplies the forward half of the
routed scaffold equivalence. -/
theorem closed104_forcesRoutedFixedCornerSquares :
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
  have valid := ShadedPlaneSignalGrid.valid decoded parentOrigin
  rcases unboundedConsecutiveMarkedFreeGrid_with_light
      decoded size coarseOrigin coarseRoot with
    ⟨cycle, shaded, ⟨grid⟩⟩ | ⟨cycle, shaded, ⟨grid⟩⟩
  · rw [← parentGrid] at cycle grid
    have geometry := OrientedLightGeometry.CycleShade.geometry
      shaded cycle valid.shadeValid
    have crossing := geometry.crossingObstruction valid
    exact tileableFixedCornerSquare_crop hsize (by omega)
      (ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive
        decoded parentOrigin grid cycle shaded crossing)
  · rw [← parentGrid] at cycle grid
    have geometry := OrientedLightGeometry.CycleShade.geometry
      shaded cycle valid.shadeValid
    have crossing := geometry.crossingObstruction valid
    exact tileableFixedCornerSquare_crop hsize (by omega)
      (ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive
        decoded parentOrigin grid cycle shaded crossing)

end OrientedLightForward
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
