/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13
import LeanWang.OllingerRobinsonTranscription

/-!
Bridge from the raw Figure 13 Wang tiles to the role-transcription interface.

The geometric proof determines which raw scaffold tiles are inactive, channels,
active cells, and the distinguished fixed-corner cell.  This module keeps that
choice as an explicit 92-entry role list and proves that a complete role list
does not change the underlying Figure 13 tileset.
-/

namespace LeanWang
namespace OllingerRobinson

/--
Attach a list of roles to a list of Wang tiles.  If the lists have different
lengths, extra entries on either side are ignored; the completeness lemma below
is the intended way to use this with `fig13Tiles`.
-/
def roleSpecsOfTiles : TileSet → List CellRole → List RoleTileSpec
  | tile :: tiles, role :: roles =>
      { tile := tile, role := role } :: roleSpecsOfTiles tiles roles
  | _, _ => []

@[simp]
theorem roleSpecsOfTiles_nil_left (roles : List CellRole) :
    roleSpecsOfTiles [] roles = [] := by
  cases roles <;> rfl

@[simp]
theorem roleSpecsOfTiles_nil_right (tiles : TileSet) :
    roleSpecsOfTiles tiles [] = [] := by
  cases tiles <;> rfl

@[simp]
theorem roleSpecsOfTiles_cons_cons
    (tile : WangTile) (tiles : TileSet) (role : CellRole) (roles : List CellRole) :
    roleSpecsOfTiles (tile :: tiles) (role :: roles) =
      { tile := tile, role := role } :: roleSpecsOfTiles tiles roles :=
  rfl

theorem tilesOfSpecs_roleSpecsOfTiles_eq_left
    {tiles : TileSet} {roles : List CellRole}
    (hlen : roles.length = tiles.length) :
    tilesOfSpecs (roleSpecsOfTiles tiles roles) = tiles := by
  revert roles
  induction tiles with
  | nil =>
      intro roles hlen
      cases roles <;> simp [tilesOfSpecs] at hlen ⊢
  | cons tile tiles ih =>
      intro roles hlen
      cases roles with
      | nil =>
          simp at hlen
      | cons role roles =>
          simp only [List.length_cons] at hlen
          have htail : roles.length = tiles.length := Nat.succ.inj hlen
          simpa only [roleSpecsOfTiles_cons_cons, tilesOfSpecs, List.map_cons]
            using congrArg (List.cons tile) (ih htail)

theorem roleSpecsOfTiles_length_eq_left
    {tiles : TileSet} {roles : List CellRole}
    (hlen : roles.length = tiles.length) :
    (roleSpecsOfTiles tiles roles).length = tiles.length := by
  revert roles
  induction tiles with
  | nil =>
      intro roles hlen
      cases roles <;> simp at hlen ⊢
  | cons tile tiles ih =>
      intro roles hlen
      cases roles with
      | nil =>
          simp at hlen
      | cons role roles =>
          simp only [List.length_cons] at hlen
          have htail : roles.length = tiles.length := Nat.succ.inj hlen
          simp [ih htail]

/-- Figure 13 tile data with an explicit role list attached. -/
def fig13RoleSpecs (roles : List CellRole) : List RoleTileSpec :=
  roleSpecsOfTiles fig13Tiles roles

theorem fig13RoleSpecs_tiles
    {roles : List CellRole} (hlen : roles.length = 92) :
    tilesOfSpecs (fig13RoleSpecs roles) = fig13Tiles := by
  exact tilesOfSpecs_roleSpecsOfTiles_eq_left (by simpa using hlen)

theorem fig13RoleSpecs_length
    {roles : List CellRole} (hlen : roles.length = 92) :
    (fig13RoleSpecs roles).length = 92 := by
  simpa [fig13RoleSpecs] using
    roleSpecsOfTiles_length_eq_left (tiles := fig13Tiles) (roles := roles)
      (by simpa using hlen)

theorem fig13RoleSpecs_nodupTilesBool
    {roles : List CellRole} (hlen : roles.length = 92) :
    nodupTilesBool (fig13RoleSpecs roles) = true := by
  apply decide_eq_true
  rw [fig13RoleSpecs_tiles hlen]
  exact fig13Tiles_nodup

end OllingerRobinson
end LeanWang
