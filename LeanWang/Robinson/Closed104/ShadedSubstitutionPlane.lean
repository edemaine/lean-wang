/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Compactness
import LeanWang.Robinson.Closed104.ShadedSignalRoutingScaffold
import LeanWang.Robinson.Closed104.ShadedSubstitutionSupertiles
import LeanWang.Robinson.Closed104.ShadedSignalRectangle

/-!
# Plane tilings from shaded substitution supertiles

The finite-state shade substitution supplies compatible corrected parent tiles
and shade blocks.  Flattening each block into four quarters preserves the
corrected Wang edges, and the independent signal-flow construction supplies the
outer signal edges.  Thus every substitution depth gives a genuine finite
`ShadedSignals.tileSet` square.  Their cofinal side lengths give a plane tiling
by compactness.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSubstitutionPlane

open Signals.FreeCellLocal
open ShadedSubstitution

set_option maxRecDepth 20000

/-- The corrected quarter tiles match horizontally in every bounded
substitution supertile. -/
theorem quarter_hmatch (level : Nat) (root : Node) (x y : Nat)
    (hx : x + 1 < 2 * 4 ^ level) (hy : y < 2 * 4 ^ level) :
    WangTile.HMatches
      (Quarters.quarterTile
        (supertileIndexGrid level root (x / 2) (y / 2), quadrantAt x y))
      (Quarters.quarterTile
        (supertileIndexGrid level root ((x + 1) / 2) (y / 2),
          quadrantAt (x + 1) y)) := by
  have hyParent : y / 2 < 4 ^ level := by omega
  have hxMod : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have hyMod : y % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hboundary : x % 2 = 1
  · have hnextDiv : (x + 1) / 2 = x / 2 + 1 := by omega
    have hnextMod : (x + 1) % 2 = 0 := by omega
    have hxParent : x / 2 + 1 < 4 ^ level := by omega
    have parentMatch :=
      (supertileNodeGrid_compatible level root).hmatch
        (x / 2) (y / 2) hxParent hyParent |>.1
    have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hyCases with hyZero | hyOne
    · simpa [Quarters.quarterTile, supertileIndexGrid, quadrantAt,
        Quadrant.ofBits,
        hboundary, hnextDiv, hnextMod, hyZero] using
        TileSubdivision.hMatches_southeast_southwest_of_hMatches parentMatch
    · simpa [Quarters.quarterTile, supertileIndexGrid, quadrantAt,
        Quadrant.ofBits,
        hboundary, hnextDiv, hnextMod, hyOne] using
        TileSubdivision.hMatches_northeast_northwest_of_hMatches parentMatch
  · have hxZero : x % 2 = 0 := by omega
    have hnextDiv : (x + 1) / 2 = x / 2 := by omega
    have hnextMod : (x + 1) % 2 = 1 := by omega
    have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hyCases with hyZero | hyOne
    · simpa [Quarters.quarterTile, quadrantAt, Quadrant.ofBits,
        hxZero, hnextDiv,
        hnextMod, hyZero] using
        TileSubdivision.hMatches_southwest_southeast
          (tile (components
            (supertileIndexGrid level root (x / 2) (y / 2))))
    · simpa [Quarters.quarterTile, quadrantAt, Quadrant.ofBits,
        hxZero, hnextDiv,
        hnextMod, hyOne] using
        TileSubdivision.hMatches_northwest_northeast
          (tile (components
            (supertileIndexGrid level root (x / 2) (y / 2))))

/-- The corrected quarter tiles match vertically in every bounded substitution
supertile. -/
theorem quarter_vmatch (level : Nat) (root : Node) (x y : Nat)
    (hx : x < 2 * 4 ^ level) (hy : y + 1 < 2 * 4 ^ level) :
    WangTile.VMatches
      (Quarters.quarterTile
        (supertileIndexGrid level root (x / 2) (y / 2), quadrantAt x y))
      (Quarters.quarterTile
        (supertileIndexGrid level root (x / 2) ((y + 1) / 2),
          quadrantAt x (y + 1))) := by
  have hxParent : x / 2 < 4 ^ level := by omega
  have hxMod : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have hyMod : y % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hboundary : y % 2 = 1
  · have hnextDiv : (y + 1) / 2 = y / 2 + 1 := by omega
    have hnextMod : (y + 1) % 2 = 0 := by omega
    have hyParent : y / 2 + 1 < 4 ^ level := by omega
    have parentMatch :=
      (supertileNodeGrid_compatible level root).vmatch
        (x / 2) (y / 2) hxParent hyParent |>.1
    have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hxCases with hxZero | hxOne
    · simpa [Quarters.quarterTile, supertileIndexGrid, quadrantAt,
        Quadrant.ofBits,
        hboundary, hnextDiv, hnextMod, hxZero] using
        TileSubdivision.vMatches_northwest_southwest_of_vMatches parentMatch
    · simpa [Quarters.quarterTile, supertileIndexGrid, quadrantAt,
        Quadrant.ofBits,
        hboundary, hnextDiv, hnextMod, hxOne] using
        TileSubdivision.vMatches_northeast_southeast_of_vMatches parentMatch
  · have hyZero : y % 2 = 0 := by omega
    have hnextDiv : (y + 1) / 2 = y / 2 := by omega
    have hnextMod : (y + 1) % 2 = 1 := by omega
    have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hxCases with hxZero | hxOne
    · simpa [Quarters.quarterTile, quadrantAt, Quadrant.ofBits,
        hyZero, hnextDiv,
        hnextMod, hxZero] using
        TileSubdivision.vMatches_southwest_northwest
          (tile (components
            (supertileIndexGrid level root (x / 2) (y / 2))))
    · simpa [Quarters.quarterTile, quadrantAt, Quadrant.ofBits,
        hyZero, hnextDiv,
        hnextMod, hxOne] using
        TileSubdivision.vMatches_southeast_northeast
          (tile (components
            (supertileIndexGrid level root (x / 2) (y / 2))))

/-- Side length, in quarter tiles, of a level-`level` shaded supertile. -/
def side (level : Nat) : Nat := 2 * 4 ^ level

/-- Selected vertical-border orientation seen along one quarter-tile row. -/
def rowInterior (level : Nat) (root : Node) (x y : Nat) : Option Bool :=
  ShadedSignalRectangle.horizontalInterior
    (supertileIndexGrid level root) (supertileShadeGrid level root) x y

/-- Selected horizontal-border orientation seen along one quarter-tile column. -/
def columnInterior (level : Nat) (root : Node) (x y : Nat) : Option Bool :=
  ShadedSignalRectangle.verticalInterior
    (supertileIndexGrid level root) (supertileShadeGrid level root) x y

private noncomputable def signals (level : Nat) (root : Node) :
    Nat → Nat → Signals.State :=
  ShadedSignalRectangle.signalGrid
    (supertileIndexGrid level root) (supertileShadeGrid level root)
    (side level) (side level)

/-- The fully decorated site at a quarter coordinate of a shaded supertile. -/
def site (level : Nat) (root : Node) (x y : Nat) : ShadedSignals.Site :=
  (((supertileIndexGrid level root (x / 2) (y / 2), quadrantAt x y),
      supertileShadeGrid level root x y),
    signals level root x y)

@[simp] theorem site_signal_west (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.west =
      ShadedSignalRectangle.intervalEdge
        (fun x => rowInterior level root x y) (side level) x := by
  rfl

@[simp] theorem site_signal_east (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.east =
      ShadedSignalRectangle.intervalEdge
        (fun x => rowInterior level root x y) (side level) (x + 1) := by
  rfl

@[simp] theorem site_signal_south (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.south =
      ShadedSignalRectangle.intervalEdge
        (fun y => columnInterior level root x y) (side level) y := by
  rfl

@[simp] theorem site_signal_north (level : Nat) (root : Node) (x y : Nat) :
    (site level root x y).2.north =
      ShadedSignalRectangle.intervalEdge
        (fun y => columnInterior level root x y) (side level) (y + 1) := by
  rfl

private theorem validSignals (level : Nat) (root : Node) :
    ShadedSignalRectangle.ValidSignalRectangle
      (supertileIndexGrid level root) (supertileShadeGrid level root)
      (signals level root) (side level) (side level) := by
  exact ShadedSignalRectangle.validSignalRectangle
    (supertileIndexGrid level root) (supertileShadeGrid level root)
    (side level) (side level)
    (supertile_validShadeRectangle level root)

/-- The concrete Wang rectangle underlying a decorated shaded supertile. -/
def tileRectangle (level : Nat) (root : Node) :
    Rectangle (side level) (side level) :=
  fun i j => ShadedSignals.tile (site level root i j)

/-- Every concrete decorated shaded supertile is a valid Wang rectangle. -/
theorem validTileRectangle (level : Nat) (root : Node) :
    ValidRectangle ShadedSignals.tileSet (tileRectangle level root) := by
  have valid := validSignals level root
  constructor
  · intro i j
    apply ShadedSignals.tile_mem
    · exact valid.shadeValid.allowed i j i.isLt j.isLt
    · exact valid.signalAllowed i j i.isLt j.isLt
  constructor
  · intro i j hi
    change WangTile.HMatches
      (ShadedSignals.tile (site level root i j))
      (ShadedSignals.tile
        (site level root (i.val + 1) j))
    simp only [ShadedSignals.tile, WangTile.HMatches_product_iff,
      RedShades.tile]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact quarter_hmatch level root i j hi j.isLt
    · simpa [RedShades.State.tile, WangTile.HMatches, site] using
        congrArg RedShades.State.edgeCode
          (valid.shadeValid.hmatch i j hi j.isLt)
    · simpa [Signals.State.tile, WangTile.HMatches, site] using
        congrArg Signals.Flow.code (valid.hmatch i j hi j.isLt)
  · intro i j hj
    change WangTile.VMatches
      (ShadedSignals.tile (site level root i j))
      (ShadedSignals.tile
        (site level root i (j.val + 1)))
    simp only [ShadedSignals.tile, WangTile.VMatches_product_iff,
      RedShades.tile]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact quarter_vmatch level root i j i.isLt hj
    · simpa [RedShades.State.tile, WangTile.VMatches, site] using
        congrArg RedShades.State.edgeCode
          (valid.shadeValid.vmatch i j i.isLt hj)
    · simpa [Signals.State.tile, WangTile.VMatches, site] using
        congrArg Signals.Flow.code (valid.vmatch i j i.isLt hj)

/-- The concrete rectangle viewed directly as a routed-scaffold tiling. -/
theorem validRoutedTileRectangle (level : Nat) (root : Node) :
    ValidRectangle ShadedSignals.routedScaffold.tiles
      (tileRectangle level root) := by
  simpa using validTileRectangle level root

@[simp] theorem routedRole_tileRectangle (level : Nat) (root : Node)
    (i j : Fin (side level)) :
    ShadedSignals.routedScaffold.role (tileRectangle level root i j) =
      ShadedSignals.routeRole (ShadedSignals.tile (site level root i j)) := by
  simp [tileRectangle]

/-- Every certified shaded substitution supertile, with its obstruction-signal
decoration, is a valid finite Wang square. -/
theorem tileableSquare (level : Nat) (root : Node) :
    TileableSquare ShadedSignals.tileSet (side level) :=
  ⟨tileRectangle level root, validTileRectangle level root⟩

theorem level_le_side (level : Nat) : level ≤ side level := by
  induction level with
  | zero => simp [side]
  | succ level ih =>
      have ih' : level ≤ 2 * 4 ^ level := by simpa [side] using ih
      have hpositive : 0 < 2 * 4 ^ level :=
        Nat.mul_pos (by decide) (pow_pos (by decide) _)
      rw [side, pow_succ]
      change level + 1 ≤ 2 * (4 ^ level * 4)
      omega

/-- The concrete shaded obstruction tileset tiles the plane, independently of
any payload. -/
theorem tilesPlane : TilesPlane ShadedSignals.tileSet := by
  apply tilesPlane_of_cofinal_tileableSquares
  intro n
  exact ⟨side n, level_le_side n, tileableSquare n seedNode⟩

end ShadedSubstitutionPlane
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
