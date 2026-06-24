/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonFigure13
import LeanWang.OllingerRobinsonTranscription
import LeanWang.TileSubdivision

/-!
Bridge from the raw Figure 13 Wang tiles to the role-transcription interface.

The geometric proof determines which raw scaffold tiles are inactive, channels,
active cells, and the distinguished fixed-corner cell.  This module keeps that
choice as an explicit 92-entry role list and proves that a complete role list
does not change the underlying Figure 13 tileset.
-/

namespace LeanWang
namespace OllingerRobinson

/-- Roles attached to the four quadrants of one raw scaffold tile. -/
structure TileQuarterRoles where
  southwest : CellRole
  southeast : CellRole
  northwest : CellRole
  northeast : CellRole
deriving DecidableEq, Repr

namespace TileQuarterRoles

def roleAt (roles : TileQuarterRoles) : Quadrant → CellRole
  | .southwest => roles.southwest
  | .southeast => roles.southeast
  | .northwest => roles.northwest
  | .northeast => roles.northeast

/-- Expand one raw tile with quadrant roles into four role specs. -/
def toRoleSpecs (tile : WangTile) (roles : TileQuarterRoles) : List RoleTileSpec :=
  Quadrant.all.map fun q =>
    { tile := TileSubdivision.subdivideTileAt tile q, role := roles.roleAt q }

@[simp]
theorem toRoleSpecs_length (tile : WangTile) (roles : TileQuarterRoles) :
    (toRoleSpecs tile roles).length = 4 := by
  simp [toRoleSpecs]

@[simp]
theorem tilesOfSpecs_toRoleSpecs (tile : WangTile) (roles : TileQuarterRoles) :
    tilesOfSpecs (toRoleSpecs tile roles) =
      TileSubdivision.subdivideTile tile := by
  simp [toRoleSpecs, TileSubdivision.subdivideTile, tilesOfSpecs]

end TileQuarterRoles

/--
Expand raw tiles and one four-quadrant role record per raw tile into ordinary
role specs for the subdivided tileset.
-/
def quarterRoleSpecsOfTiles : TileSet → List TileQuarterRoles → List RoleTileSpec
  | tile :: tiles, roles :: roleRows =>
      roles.toRoleSpecs tile ++ quarterRoleSpecsOfTiles tiles roleRows
  | _, _ => []

@[simp]
theorem quarterRoleSpecsOfTiles_nil_left (roles : List TileQuarterRoles) :
    quarterRoleSpecsOfTiles [] roles = [] := by
  cases roles <;> rfl

@[simp]
theorem quarterRoleSpecsOfTiles_nil_right (tiles : TileSet) :
    quarterRoleSpecsOfTiles tiles [] = [] := by
  cases tiles <;> rfl

@[simp]
theorem quarterRoleSpecsOfTiles_cons_cons
    (tile : WangTile) (tiles : TileSet)
    (roles : TileQuarterRoles) (roleRows : List TileQuarterRoles) :
    quarterRoleSpecsOfTiles (tile :: tiles) (roles :: roleRows) =
      roles.toRoleSpecs tile ++ quarterRoleSpecsOfTiles tiles roleRows :=
  rfl

theorem tilesOfSpecs_quarterRoleSpecsOfTiles_eq_subdivideTileSet
    {tiles : TileSet} {roleRows : List TileQuarterRoles}
    (hlen : roleRows.length = tiles.length) :
    tilesOfSpecs (quarterRoleSpecsOfTiles tiles roleRows) =
      TileSubdivision.subdivideTileSet tiles := by
  revert roleRows
  induction tiles with
  | nil =>
      intro roleRows hlen
      cases roleRows <;> simp [tilesOfSpecs] at hlen ⊢
  | cons tile tiles ih =>
      intro roleRows hlen
      cases roleRows with
      | nil =>
          simp at hlen
      | cons roles roleRows =>
          simp only [List.length_cons] at hlen
          have htail : roleRows.length = tiles.length := Nat.succ.inj hlen
          change tilesOfSpecs (roles.toRoleSpecs tile) ++
              tilesOfSpecs (quarterRoleSpecsOfTiles tiles roleRows) =
            TileSubdivision.subdivideTile tile ++
              TileSubdivision.subdivideTileSet tiles
          rw [TileQuarterRoles.tilesOfSpecs_toRoleSpecs, ih htail]

theorem quarterRoleSpecsOfTiles_length_eq_four_mul
    {tiles : TileSet} {roleRows : List TileQuarterRoles}
    (hlen : roleRows.length = tiles.length) :
    (quarterRoleSpecsOfTiles tiles roleRows).length = 4 * tiles.length := by
  revert roleRows
  induction tiles with
  | nil =>
      intro roleRows hlen
      cases roleRows <;> simp at hlen ⊢
  | cons tile tiles ih =>
      intro roleRows hlen
      cases roleRows with
      | nil =>
          simp at hlen
      | cons roles roleRows =>
          simp only [List.length_cons] at hlen
          have htail : roleRows.length = tiles.length := Nat.succ.inj hlen
          simp [ih htail, Nat.mul_succ, Nat.add_comm]

/-- Figure 13 subdivided into quadrant role specs. -/
def fig13QuarterRoleSpecs (roleRows : List TileQuarterRoles) :
    List RoleTileSpec :=
  quarterRoleSpecsOfTiles fig13Tiles roleRows

theorem fig13QuarterRoleSpecs_tiles
    {roleRows : List TileQuarterRoles} (hlen : roleRows.length = 92) :
    tilesOfSpecs (fig13QuarterRoleSpecs roleRows) =
      TileSubdivision.subdivideTileSet fig13Tiles := by
  exact tilesOfSpecs_quarterRoleSpecsOfTiles_eq_subdivideTileSet
    (by simpa using hlen)

theorem fig13QuarterRoleSpecs_length
    {roleRows : List TileQuarterRoles} (hlen : roleRows.length = 92) :
    (fig13QuarterRoleSpecs roleRows).length = 368 := by
  simpa [fig13QuarterRoleSpecs] using
    quarterRoleSpecsOfTiles_length_eq_four_mul
      (tiles := fig13Tiles) (roleRows := roleRows) (by simpa using hlen)

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
