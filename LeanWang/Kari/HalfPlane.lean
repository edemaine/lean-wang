/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Compactness

/-!
# Upper-half-plane tilings

Kari's construction first produces tilings of an upper half-plane, with each
successive row representing a further step of a partial dynamical system.  For
ordinary Wang tiles, existence of such a tiling is equivalent to existence of
a tiling of the whole plane.

The forward implication is the compactness step used in Section 5.4.2 of
Jeandel and Vanier, *The Undecidability of the Domino Problem* (2020): translate
arbitrarily large finite regions of an upper-half-plane tiling downward, then
apply finite-box compactness.  The reverse implication is restriction.
-/

namespace LeanWang
namespace Kari

/-- Validity of a Wang tiling of the upper half-plane `Int × Nat`. -/
def ValidUpperHalfTiling (T : TileSet) (x : Int × Nat → TileIn T) : Prop :=
  (∀ p : Int × Nat,
      WangTile.HMatches (x p).1 (x (p.1 + 1, p.2)).1) ∧
    (∀ p : Int × Nat,
      WangTile.VMatches (x p).1 (x (p.1, p.2 + 1)).1)

/-- A finite tileset tiles the upper half-plane. -/
def TilesUpperHalf (T : TileSet) : Prop :=
  ∃ x : Int × Nat → TileIn T, ValidUpperHalfTiling T x

/-- A plane tiling restricts to an upper-half-plane tiling. -/
theorem tilesUpperHalf_of_tilesPlane {T : TileSet} :
    TilesPlane T → TilesUpperHalf T := by
  rintro ⟨x, hxH, hxV⟩
  let y : Int × Nat → TileIn T := fun p => x (p.1, (p.2 : Int))
  refine ⟨y, ?_, ?_⟩
  · intro p
    exact hxH (p.1, (p.2 : Int))
  · intro p
    simpa [y] using hxV (p.1, (p.2 : Int))

/-- An upper-half-plane tiling supplies every centered finite box by vertical translation. -/
theorem tileableBox_of_tilesUpperHalf {T : TileSet} :
    TilesUpperHalf T → ∀ r : Nat, TileableBox T r := by
  rintro ⟨x, hxH, hxV⟩ r
  let y : BoxPattern T r := fun p => x (p.1.1, boxCoord r p.1.2)
  refine ⟨y, ?_, ?_⟩
  · intro p hp
    exact hxH (p.1.1, boxCoord r p.1.2)
  · intro p hp
    have hsucc : boxCoord r (p.1.2 + 1) = boxCoord r p.1.2 + 1 :=
      boxCoord_succ p.2.2.2.1
    simpa [y, hsucc] using hxV (p.1.1, boxCoord r p.1.2)

/-- An upper-half-plane tiling extends to a plane tiling by compactness. -/
theorem tilesPlane_of_tilesUpperHalf {T : TileSet} :
    TilesUpperHalf T → TilesPlane T := by
  intro h
  exact tilesPlane_of_all_tileableBoxes (tileableBox_of_tilesUpperHalf h)

/-- A finite Wang tileset tiles the upper half-plane exactly when it tiles the plane. -/
theorem tilesUpperHalf_iff_tilesPlane (T : TileSet) :
    TilesUpperHalf T ↔ TilesPlane T :=
  ⟨tilesPlane_of_tilesUpperHalf, tilesUpperHalf_of_tilesPlane⟩

end Kari
end LeanWang
