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

/-- Decode each ordinary quarter Wang tile to its typed site. -/
@[irreducible] def indexPlane
    (x : Int × Int → TileIn Quarters.tileSet) : QuarterPlane :=
  fun p => decode (x p).1

theorem indexPlane_apply (x : Int × Int → TileIn Quarters.tileSet)
    (p : Int × Int) :
    indexPlane x p = decode (x p).1 := by
  unfold indexPlane
  rfl

@[simp]
theorem quarterTile_indexPlane (x : Int × Int → TileIn Quarters.tileSet)
    (p : Int × Int) :
    quarterTile (indexPlane x p) = (x p).1 :=
  by
    rw [indexPlane_apply]
    exact quarterTile_decode_of_mem (x p).2

theorem indexPlane_valid {x : Int × Int → TileIn Quarters.tileSet}
    (hx : ValidPlaneTiling Quarters.tileSet x) :
    ValidQuarterPlane (indexPlane x) := by
  constructor
  · intro p
    simpa only [quarterTile_indexPlane] using hx.1 p
  · intro p
    simpa only [quarterTile_indexPlane] using hx.2 p

/-- Complete typed regrouping data extracted from an ordinary quarter tiling. -/
structure Regrouping (x : Int × Int → TileIn Quarters.tileSet) where
  origin : Int × Int
  phase : phaseAt (indexPlane x) origin = .southwest
  parent : IndexPlane
  parent_eq : parent = macroPlane (indexPlane x) origin
  parent_valid : ValidIndexPlane parent
  blocks : ∀ k : Int × Int,
    indexPlane x (blockOrigin origin k) = (parent k, .southwest) ∧
      indexPlane x (shift (blockOrigin origin k) 1 0) =
        (parent k, .southeast) ∧
      indexPlane x (shift (blockOrigin origin k) 0 1) =
        (parent k, .northwest) ∧
      indexPlane x (shift (blockOrigin origin k) 1 1) =
        (parent k, .northeast)

/-- Every valid ordinary quarter tiling regroups into a valid corrected parent plane. -/
noncomputable def regroup {x : Int × Int → TileIn Quarters.tileSet}
    (hx : ValidPlaneTiling Quarters.tileSet x) : Regrouping x := by
  let z := indexPlane x
  have hz : ValidQuarterPlane z := indexPlane_valid hx
  let origin := Classical.choose (exists_southwest_origin hz)
  have horigin : phaseAt z origin = .southwest :=
    Classical.choose_spec (exists_southwest_origin hz)
  exact {
    origin := origin
    phase := horigin
    parent := macroPlane z origin
    parent_eq := rfl
    parent_valid := macroPlane_valid hz horigin
    blocks := block_spec hz horigin
  }

end QuarterPlaneDecode
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
