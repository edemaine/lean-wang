/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104QuarterRegrouping

/-!
Decode ordinary corrected quarter-tile planes and recover a valid parent plane.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace QuarterPlaneDecode

open Desubstitution ParentPlane Quarters QuarterRegrouping

set_option maxRecDepth 20000

/-- Boundary matches between macroblocks reflect to their corrected parents. -/
theorem macroPlane_valid {z : QuarterPlane} (hz : ValidQuarterPlane z)
    {origin : Int × Int} (horigin : phaseAt z origin = .southwest) :
    ValidIndexPlane (macroPlane z origin) := by
  constructor
  · intro k
    have hk := block_spec hz horigin k
    have he := block_spec hz horigin (k.1 + 1, k.2)
    have hmatch := hz.1 (shift (blockOrigin origin k) 1 0)
    have hmatch' : WangTile.HMatches
        (quarterTile (z (shift (blockOrigin origin k) 1 0)))
        (quarterTile (z (blockOrigin origin (k.1 + 1, k.2)))) := by
      simpa only [shift_east, Int.reduceAdd, blockOrigin_east] using hmatch
    rw [hk.2.1, he.1] at hmatch'
    exact (TileSubdivision.hMatches_subdivideTileAt_iff
      (tile (components (macroPlane z origin k)))
      (tile (components (macroPlane z origin (k.1 + 1, k.2))))
      .southeast .southwest).1 hmatch'
  · intro k
    have hk := block_spec hz horigin k
    have hn := block_spec hz horigin (k.1, k.2 + 1)
    have hmatch := hz.2 (shift (blockOrigin origin k) 0 1)
    have hmatch' : WangTile.VMatches
        (quarterTile (z (shift (blockOrigin origin k) 0 1)))
        (quarterTile (z (blockOrigin origin (k.1, k.2 + 1)))) := by
      simpa only [shift_north, Int.reduceAdd, blockOrigin_north] using hmatch
    rw [hk.2.2.1, hn.1] at hmatch'
    exact (TileSubdivision.vMatches_subdivideTileAt_iff
      (tile (components (macroPlane z origin k)))
      (tile (components (macroPlane z origin (k.1, k.2 + 1))))
      .northwest .southwest).1 hmatch'


end QuarterPlaneDecode
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
