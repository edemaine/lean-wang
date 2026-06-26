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

def const (role : CellRole) : TileQuarterRoles where
  southwest := role
  southeast := role
  northwest := role
  northeast := role

def ofQuadrants
    (southwest southeast northwest northeast : CellRole) : TileQuarterRoles where
  southwest := southwest
  southeast := southeast
  northwest := northwest
  northeast := northeast

def inactive : TileQuarterRoles :=
  const CellRole.inactive

def channel : TileQuarterRoles :=
  const CellRole.channel

def active : TileQuarterRoles :=
  const CellRole.active

def roleAt (roles : TileQuarterRoles) : Quadrant → CellRole
  | .southwest => roles.southwest
  | .southeast => roles.southeast
  | .northwest => roles.northwest
  | .northeast => roles.northeast

@[simp]
theorem roleAt_const (role : CellRole) (q : Quadrant) :
    (const role).roleAt q = role := by
  cases q <;> rfl

@[simp]
theorem roleAt_ofQuadrants_southwest
    (southwest southeast northwest northeast : CellRole) :
    (ofQuadrants southwest southeast northwest northeast).roleAt
      Quadrant.southwest = southwest :=
  rfl

@[simp]
theorem roleAt_ofQuadrants_southeast
    (southwest southeast northwest northeast : CellRole) :
    (ofQuadrants southwest southeast northwest northeast).roleAt
      Quadrant.southeast = southeast :=
  rfl

@[simp]
theorem roleAt_ofQuadrants_northwest
    (southwest southeast northwest northeast : CellRole) :
    (ofQuadrants southwest southeast northwest northeast).roleAt
      Quadrant.northwest = northwest :=
  rfl

@[simp]
theorem roleAt_ofQuadrants_northeast
    (southwest southeast northwest northeast : CellRole) :
    (ofQuadrants southwest southeast northwest northeast).roleAt
      Quadrant.northeast = northeast :=
  rfl

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

theorem mem_toRoleSpecs (tile : WangTile) (roles : TileQuarterRoles)
    (q : Quadrant) :
    ({ tile := TileSubdivision.subdivideTileAt tile q
       role := roles.roleAt q } : RoleTileSpec) ∈ roles.toRoleSpecs tile := by
  unfold toRoleSpecs
  exact List.mem_map.2 ⟨q, Quadrant.mem_all q, rfl⟩

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

set_option linter.flexible false in
theorem mem_quarterRoleSpecsOfTiles_of_getElem?
    {tiles : TileSet} {roleRows : List TileQuarterRoles}
    {i : Nat} {tile : WangTile} {roles : TileQuarterRoles} (q : Quadrant)
    (htile : tiles[i]? = some tile)
    (hroles : roleRows[i]? = some roles) :
    ({ tile := TileSubdivision.subdivideTileAt tile q
       role := roles.roleAt q } : RoleTileSpec) ∈
      quarterRoleSpecsOfTiles tiles roleRows := by
  revert roleRows i
  induction tiles with
  | nil =>
      intro roleRows i htile hroles
      simp at htile
  | cons head tiles ih =>
      intro roleRows i htile hroles
      cases roleRows with
      | nil =>
          cases i <;> simp at hroles
      | cons headRoles roleRows =>
          cases i with
          | zero =>
              simp at htile hroles
              subst head
              subst headRoles
              exact List.mem_append_left _
                (TileQuarterRoles.mem_toRoleSpecs tile roles q)
          | succ i =>
              simp at htile hroles
              exact List.mem_append_right _ (ih htile hroles)

theorem exists_of_mem_quarterRoleSpecsOfTiles
    {tiles : TileSet} {roleRows : List TileQuarterRoles} {spec : RoleTileSpec}
    (hspec : spec ∈ quarterRoleSpecsOfTiles tiles roleRows) :
    ∃ (i : Nat) (tile : WangTile) (roles : TileQuarterRoles) (q : Quadrant),
      tiles[i]? = some tile ∧
        roleRows[i]? = some roles ∧
        spec.tile = TileSubdivision.subdivideTileAt tile q ∧
        spec.role = TileQuarterRoles.roleAt roles q := by
  induction tiles generalizing roleRows with
  | nil =>
      cases roleRows <;> simp at hspec
  | cons head tiles ih =>
      cases roleRows with
      | nil =>
          simp at hspec
      | cons headRoles roleRows =>
          rw [quarterRoleSpecsOfTiles_cons_cons, List.mem_append] at hspec
          rcases hspec with hhead | htail
          · unfold TileQuarterRoles.toRoleSpecs at hhead
            rcases List.mem_map.1 hhead with ⟨q, _hq, hspecq⟩
            refine ⟨0, head, headRoles, q, ?_, ?_, ?_, ?_⟩
            · rfl
            · rfl
            · exact congrArg RoleTileSpec.tile hspecq.symm
            · exact congrArg RoleTileSpec.role hspecq.symm
          · rcases ih htail with
              ⟨i, tile, roles, q, htile, hroles, hspecTile, hspecRole⟩
            refine ⟨i + 1, tile, roles, q, ?_, ?_, hspecTile, hspecRole⟩
            · simpa using htile
            · simpa using hroles

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

theorem fig13SubdividedTiles_nodup :
    (TileSubdivision.subdivideTileSet fig13Tiles).Nodup :=
  TileSubdivision.subdivideTileSet_nodup_of_nodup fig13Tiles_nodup

theorem fig13QuarterRoleSpecs_nodupTilesBool
    {roleRows : List TileQuarterRoles} (hlen : roleRows.length = 92) :
    nodupTilesBool (fig13QuarterRoleSpecs roleRows) = true := by
  apply decide_eq_true
  rw [fig13QuarterRoleSpecs_tiles hlen]
  exact fig13SubdividedTiles_nodup

/-- The `i`th raw Figure 13 tile, using the scanned Figure 13 order. -/
def fig13Tile (i : Fin 92) : WangTile :=
  fig13Tiles.get ⟨i.val, by simp [fig13Tiles_length, i.isLt]⟩

theorem fig13Tile_primrec : Primrec fig13Tile := by
  let defaultTile : WangTile := { n := 0, s := 0, e := 0, w := 0 }
  have hgetD : Primrec (fun i : Fin 92 => fig13Tiles.getD i.val defaultTile) := by
    exact (Primrec.list_getD defaultTile).comp
      (Primrec.const fig13Tiles) Primrec.encode
  exact hgetD.of_eq fun i => by
    unfold fig13Tile
    rw [List.getD_eq_getElem (hn := by simp [fig13Tiles_length, i.isLt])]
    rfl

theorem fig13Tile_injective : Function.Injective fig13Tile := by
  intro i j h
  unfold fig13Tile at h
  apply Fin.ext
  have hidx :
      (⟨i.val, by simp [fig13Tiles_length, i.isLt]⟩ :
          Fin fig13Tiles.length) =
        ⟨j.val, by simp [fig13Tiles_length, j.isLt]⟩ := by
    exact (List.Nodup.get_inj_iff fig13Tiles_nodup).1 h
  exact congrArg Fin.val hidx

theorem fig13Tile_eq_iff (i j : Fin 92) :
    fig13Tile i = fig13Tile j ↔ i = j :=
  ⟨fun h => fig13Tile_injective h, fun h => h ▸ rfl⟩

/-- A named quadrant tile in the subdivided Figure 13 scaffold. -/
def fig13QuarterTile (i : Fin 92) (q : Quadrant) : WangTile :=
  TileSubdivision.subdivideTileAt (fig13Tile i) q

theorem fig13QuarterTile_eq_iff (i j : Fin 92) (q r : Quadrant) :
    fig13QuarterTile i q = fig13QuarterTile j r ↔ i = j ∧ q = r := by
  unfold fig13QuarterTile fig13Tile
  constructor
  · intro h
    have hparts := TileSubdivision.subdivideTileAt_eq_iff
      (fig13Tiles.get ⟨i.val, by simp [fig13Tiles_length, i.isLt]⟩)
      (fig13Tiles.get ⟨j.val, by simp [fig13Tiles_length, j.isLt]⟩)
      q r |>.1 h
    constructor
    · apply Fin.ext
      have hidx :
          (⟨i.val, by simp [fig13Tiles_length, i.isLt]⟩ :
              Fin fig13Tiles.length) =
            ⟨j.val, by simp [fig13Tiles_length, j.isLt]⟩ := by
        exact (List.Nodup.get_inj_iff fig13Tiles_nodup).1 hparts.1
      exact congrArg Fin.val hidx
    · exact hparts.2
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A single quadrant site in the Figure 18 interpretation of Figure 13. -/
structure Figure18Site where
  index : Fin 92
  quadrant : Quadrant
deriving DecidableEq, Repr

namespace Figure18Site

def toPair (site : Figure18Site) : Fin 92 × Quadrant :=
  (site.index, site.quadrant)

def ofPair (p : Fin 92 × Quadrant) : Figure18Site where
  index := p.1
  quadrant := p.2

def equivPair : Figure18Site ≃ Fin 92 × Quadrant where
  toFun := toPair
  invFun := ofPair
  left_inv := by
    intro site
    cases site
    rfl
  right_inv := by
    intro p
    rcases p with ⟨i, q⟩
    rfl

instance instPrimcodable : Primcodable Figure18Site :=
  Primcodable.ofEquiv (Fin 92 × Quadrant) equivPair

theorem toPair_primrec : Primrec toPair := by
  simpa [equivPair] using
    (Primrec.of_equiv (e := equivPair) : Primrec equivPair)

theorem ofPair_primrec : Primrec ofPair := by
  simpa [equivPair] using
    (Primrec.of_equiv_symm (e := equivPair) : Primrec equivPair.symm)

theorem index_primrec : Primrec Figure18Site.index :=
  Primrec.fst.comp toPair_primrec

theorem quadrant_primrec : Primrec Figure18Site.quadrant :=
  Primrec.snd.comp toPair_primrec

def tile (site : Figure18Site) : WangTile :=
  fig13QuarterTile site.index site.quadrant

def rawTile (site : Figure18Site) : WangTile :=
  fig13Tile site.index

theorem tile_primrec : Primrec tile := by
  unfold tile fig13QuarterTile
  exact TileSubdivision.subdivideTileAt_primrec₂.comp
    (fig13Tile_primrec.comp index_primrec) quadrant_primrec

theorem rawTile_primrec : Primrec rawTile :=
  fig13Tile_primrec.comp index_primrec

@[simp]
theorem tile_eq_subdivideTileAt_rawTile (site : Figure18Site) :
    site.tile = TileSubdivision.subdivideTileAt site.rawTile site.quadrant := by
  rfl

/--
Finite east-neighbor relation between Figure 18 sites.

The true cases are exactly the two internal west/east seams of one Figure 13
tile and the two east-boundary crossings between horizontally matching raw
Figure 13 tiles.
-/
def hCompatible (left right : Figure18Site) : Bool :=
  match left.quadrant, right.quadrant with
  | .southwest, .southeast => decide (left.index = right.index)
  | .northwest, .northeast => decide (left.index = right.index)
  | .southeast, .southwest => decide (WangTile.HMatches left.rawTile right.rawTile)
  | .northeast, .northwest => decide (WangTile.HMatches left.rawTile right.rawTile)
  | _, _ => false

/--
Finite north-neighbor relation between Figure 18 sites.

The true cases are exactly the two internal south/north seams of one Figure 13
tile and the two north-boundary crossings between vertically matching raw
Figure 13 tiles.
-/
def vCompatible (lower upper : Figure18Site) : Bool :=
  match lower.quadrant, upper.quadrant with
  | .southwest, .northwest => decide (lower.index = upper.index)
  | .southeast, .northeast => decide (lower.index = upper.index)
  | .northwest, .southwest => decide (WangTile.VMatches lower.rawTile upper.rawTile)
  | .northeast, .southeast => decide (WangTile.VMatches lower.rawTile upper.rawTile)
  | _, _ => false

set_option linter.flexible false in
theorem hMatches_of_hCompatible {left right : Figure18Site}
    (h : hCompatible left right = true) :
    WangTile.HMatches left.tile right.tile := by
  rcases left with ⟨li, lq⟩
  rcases right with ⟨ri, rq⟩
  cases lq <;> cases rq <;>
    simp [hCompatible, tile, rawTile, fig13QuarterTile] at h ⊢
  · subst ri
    exact TileSubdivision.hMatches_southwest_southeast (fig13Tile li)
  · exact TileSubdivision.hMatches_southeast_southwest_of_hMatches h
  · subst ri
    exact TileSubdivision.hMatches_northwest_northeast (fig13Tile li)
  · exact TileSubdivision.hMatches_northeast_northwest_of_hMatches h

set_option linter.flexible false in
theorem hCompatible_of_hMatches {left right : Figure18Site}
    (h : WangTile.HMatches left.tile right.tile) :
    hCompatible left right = true := by
  rcases left with ⟨li, lq⟩
  rcases right with ⟨ri, rq⟩
  cases lq <;> cases rq <;>
    simp [hCompatible, tile, rawTile, fig13QuarterTile,
      TileSubdivision.hMatches_subdivideTileAt_iff,
      fig13Tile_eq_iff] at h ⊢
  all_goals exact h

set_option linter.flexible false in
theorem vMatches_of_vCompatible {lower upper : Figure18Site}
    (h : vCompatible lower upper = true) :
    WangTile.VMatches lower.tile upper.tile := by
  rcases lower with ⟨li, lq⟩
  rcases upper with ⟨ri, rq⟩
  cases lq <;> cases rq <;>
    simp [vCompatible, tile, rawTile, fig13QuarterTile] at h ⊢
  · subst ri
    exact TileSubdivision.vMatches_southwest_northwest (fig13Tile li)
  · subst ri
    exact TileSubdivision.vMatches_southeast_northeast (fig13Tile li)
  · exact TileSubdivision.vMatches_northwest_southwest_of_vMatches h
  · exact TileSubdivision.vMatches_northeast_southeast_of_vMatches h

set_option linter.flexible false in
theorem vCompatible_of_vMatches {lower upper : Figure18Site}
    (h : WangTile.VMatches lower.tile upper.tile) :
    vCompatible lower upper = true := by
  rcases lower with ⟨li, lq⟩
  rcases upper with ⟨ri, rq⟩
  cases lq <;> cases rq <;>
    simp [vCompatible, tile, rawTile, fig13QuarterTile,
      TileSubdivision.vMatches_subdivideTileAt_iff,
      fig13Tile_eq_iff] at h ⊢
  all_goals exact h

/-- All Figure 18 quadrant sites, ordered by Figure 13 tile index then quadrant. -/
def all : List Figure18Site :=
  (List.finRange 92).flatMap fun i =>
    Quadrant.all.map fun q => ({ index := i, quadrant := q } : Figure18Site)

def ofTile? (tile : WangTile) : Option Figure18Site :=
  all.find? fun site => site.tile = tile

/-- Index of the first Figure 18 site with the given tile, or `all.length`. -/
def tileIndex (tile : WangTile) : Nat :=
  all.findIdx fun site => decide (site.tile = tile)

theorem tileIndex_primrec : Primrec tileIndex := by
  let pred : WangTile → Figure18Site → Bool := fun tile site => decide (site.tile = tile)
  have hleft : Primrec (fun p : WangTile × Figure18Site => (p.2).tile) :=
    tile_primrec.comp (Primrec.snd (α := WangTile) (β := Figure18Site))
  have hright : Primrec (fun p : WangTile × Figure18Site => p.1) :=
    Primrec.fst
  have hpredUncurried : Primrec (fun p : WangTile × Figure18Site => pred p.1 p.2) := by
    exact Primrec.eq.decide.comp hleft hright
  have hpred : Primrec₂ pred := Primrec₂.mk hpredUncurried
  exact (Primrec.list_findIdx₁ hpred all).of_eq fun tile => by
    rfl

@[simp]
theorem all_length : all.length = 368 := by
  simp [all, Quadrant.all]

@[simp]
theorem all_tiles_length : (all.map tile).length = 368 := by
  simp [all, Quadrant.all]

@[simp]
theorem tile_mk (index : Fin 92) (quadrant : Quadrant) :
    ({ index := index, quadrant := quadrant } : Figure18Site).tile =
      fig13QuarterTile index quadrant :=
  rfl

theorem tile_eq_iff (site other : Figure18Site) :
    site.tile = other.tile ↔ site = other := by
  cases site
  cases other
  simp [tile, fig13QuarterTile_eq_iff]

theorem tile_injective :
    Function.Injective tile := by
  intro site other htile
  exact (tile_eq_iff site other).1 htile

theorem mem_all (site : Figure18Site) : site ∈ all := by
  rcases site with ⟨i, q⟩
  unfold all
  exact List.mem_flatMap.2 ⟨i, List.mem_finRange i,
    List.mem_map.2 ⟨q, Quadrant.mem_all q, rfl⟩⟩

theorem tile_mem_all_tiles (site : Figure18Site) :
    site.tile ∈ all.map tile :=
  List.mem_map.2 ⟨site, site.mem_all, rfl⟩

theorem tileIndex_lt_length_of_mem_all_tiles {tile : WangTile}
    (hmem : tile ∈ all.map Figure18Site.tile) :
    tileIndex tile < all.length := by
  unfold tileIndex
  rcases List.mem_map.1 hmem with ⟨site, hsite, htile⟩
  exact List.findIdx_lt_length_of_exists ⟨site, hsite, decide_eq_true htile⟩

/--
Recover the Figure 18 site for a tile known to belong to the finite site tile
list, using the primitive-recursive numeric search `tileIndex`.
-/
def siteOfTile (tile : WangTile) (hmem : tile ∈ all.map Figure18Site.tile) :
    Figure18Site :=
  all[tileIndex tile]'(tileIndex_lt_length_of_mem_all_tiles hmem)

theorem siteOfTile_mem_all {tile : WangTile}
    (hmem : tile ∈ all.map Figure18Site.tile) :
    siteOfTile tile hmem ∈ all := by
  unfold siteOfTile
  exact List.getElem_mem (tileIndex_lt_length_of_mem_all_tiles hmem)

theorem siteOfTile_tile {tile : WangTile}
    (hmem : tile ∈ all.map Figure18Site.tile) :
    (siteOfTile tile hmem).tile = tile := by
  unfold siteOfTile tileIndex
  exact of_decide_eq_true (List.findIdx_getElem
    (xs := all) (p := fun site : Figure18Site => decide (site.tile = tile))
    (w := tileIndex_lt_length_of_mem_all_tiles hmem))

theorem siteOfTile_getElem? {tile : WangTile}
    (hmem : tile ∈ all.map Figure18Site.tile) :
    all[tileIndex tile]? = some (siteOfTile tile hmem) := by
  unfold siteOfTile
  exact List.getElem?_eq_getElem (tileIndex_lt_length_of_mem_all_tiles hmem)

theorem ofTile?_eq_some_tile {tile : WangTile} {site : Figure18Site}
    (h : ofTile? tile = some site) :
    site.tile = tile := by
  unfold ofTile? at h
  exact of_decide_eq_true
    (List.find?_some (p := fun site : Figure18Site => site.tile = tile) h)

theorem ofTile?_eq_some_mem {tile : WangTile} {site : Figure18Site}
    (h : ofTile? tile = some site) :
    site ∈ all := by
  unfold ofTile? at h
  exact List.mem_of_find?_eq_some h

theorem ofTile?_isSome_of_mem_all_tiles {tile : WangTile}
    (hmem : tile ∈ all.map Figure18Site.tile) :
    (ofTile? tile).isSome = true := by
  unfold ofTile?
  rw [List.find?_isSome]
  rcases List.mem_map.1 hmem with ⟨site, hsite, htile⟩
  exact ⟨site, hsite, decide_eq_true htile⟩

theorem exists_ofTile?_eq_some_of_mem_all_tiles {tile : WangTile}
    (hmem : tile ∈ all.map Figure18Site.tile) :
    ∃ site : Figure18Site,
      ofTile? tile = some site ∧ site ∈ all ∧ site.tile = tile := by
  have hsome := ofTile?_isSome_of_mem_all_tiles hmem
  cases hfind : ofTile? tile with
  | none =>
      simp [hfind] at hsome
  | some site =>
      exact ⟨site, rfl, ofTile?_eq_some_mem hfind,
        ofTile?_eq_some_tile hfind⟩

/-- Offset of a quadrant in the flat Figure 18 role transcription order. -/
def quadrantOffset : Quadrant → Nat
  | .southwest => 0
  | .southeast => 1
  | .northwest => 2
  | .northeast => 3

/-- Index of a Figure 18 site in the flat role transcription order. -/
def flatIndex (site : Figure18Site) : Nat :=
  4 * site.index.val + quadrantOffset site.quadrant

@[simp]
theorem flatIndex_mk_southwest (i : Fin 92) :
    ({ index := i, quadrant := Quadrant.southwest } : Figure18Site).flatIndex =
      4 * i.val := by
  rfl

@[simp]
theorem flatIndex_mk_southeast (i : Fin 92) :
    ({ index := i, quadrant := Quadrant.southeast } : Figure18Site).flatIndex =
      4 * i.val + 1 := by
  rfl

@[simp]
theorem flatIndex_mk_northwest (i : Fin 92) :
    ({ index := i, quadrant := Quadrant.northwest } : Figure18Site).flatIndex =
      4 * i.val + 2 := by
  rfl

@[simp]
theorem flatIndex_mk_northeast (i : Fin 92) :
    ({ index := i, quadrant := Quadrant.northeast } : Figure18Site).flatIndex =
      4 * i.val + 3 := by
  rfl

def quadrantOfFlatOffset (offset : Nat) : Quadrant :=
  match offset with
  | 0 => Quadrant.southwest
  | 1 => Quadrant.southeast
  | 2 => Quadrant.northwest
  | _ => Quadrant.northeast

def siteOfFlatIndex (k : Fin 368) : Figure18Site where
  index := ⟨k.val / 4, by omega⟩
  quadrant := quadrantOfFlatOffset (k.val % 4)

theorem flatIndex_lt (site : Figure18Site) : site.flatIndex < 368 := by
  rcases site with ⟨i, q⟩
  cases q <;> simp [flatIndex, quadrantOffset] <;> omega

theorem siteOfFlatIndex_flatIndex (site : Figure18Site) :
    siteOfFlatIndex ⟨site.flatIndex, site.flatIndex_lt⟩ = site := by
  rcases site with ⟨i, q⟩
  cases q <;>
    simp [siteOfFlatIndex, flatIndex, quadrantOffset, quadrantOfFlatOffset,
      Nat.mul_add_div, Nat.mul_add_mod_self_left, Nat.div_eq_of_lt,
      Nat.mod_eq_of_lt]

theorem mk_eq_iff (i : Fin 92) (q : Quadrant) (site : Figure18Site) :
    ({ index := i, quadrant := q } : Figure18Site) = site ↔
      i = site.index ∧ q = site.quadrant := by
  cases site
  simp

/-- Decode an ordinary natural-number tile index and quadrant as a Figure 18 site. -/
def ofNat? (i : Nat) (q : Quadrant) : Option Figure18Site :=
  if h : i < 92 then some ({ index := ⟨i, h⟩, quadrant := q } : Figure18Site)
  else none

@[simp]
theorem ofNat?_eq_some_of_lt {i : Nat} (q : Quadrant) (h : i < 92) :
    ofNat? i q = some ({ index := ⟨i, h⟩, quadrant := q } : Figure18Site) := by
  simp [ofNat?, h]

@[simp]
theorem ofNat?_eq_none_of_not_lt {i : Nat} (q : Quadrant) (h : ¬ i < 92) :
    ofNat? i q = none := by
  simp [ofNat?, h]

/--
Decode a list of ordinary indexed quadrant specs.

Concrete Figure 18 data should pair this with `natSpecsValidBool`, so that an
out-of-range raw tile index is caught by a small finite check.
-/
def sitesOfNatSpecs : List (Nat × Quadrant) → List Figure18Site
  | [] => []
  | (i, q) :: specs =>
      match ofNat? i q with
      | some site => site :: sitesOfNatSpecs specs
      | none => sitesOfNatSpecs specs

/-- Finite check that all raw Figure 18 site specs use valid Figure 13 indices. -/
def natSpecsValidBool (specs : List (Nat × Quadrant)) : Bool :=
  specs.all fun spec => decide (spec.1 < 92)

theorem natSpecsValidBool_cons {i : Nat} {q : Quadrant}
    {specs : List (Nat × Quadrant)}
    (hcheck : natSpecsValidBool ((i, q) :: specs) = true) :
    i < 92 ∧ natSpecsValidBool specs = true := by
  simpa [natSpecsValidBool] using hcheck

theorem length_sitesOfNatSpecs_of_natSpecsValidBool
    {specs : List (Nat × Quadrant)}
    (hcheck : natSpecsValidBool specs = true) :
    (sitesOfNatSpecs specs).length = specs.length := by
  induction specs with
  | nil =>
      rfl
  | cons spec specs ih =>
      rcases spec with ⟨i, q⟩
      rcases natSpecsValidBool_cons (i := i) (q := q) hcheck with
        ⟨hi, htail⟩
      simp [sitesOfNatSpecs, ofNat?_eq_some_of_lt q hi, ih htail]

theorem mem_sitesOfNatSpecs_of_mem
    {specs : List (Nat × Quadrant)} {i : Nat} {q : Quadrant}
    (hcheck : natSpecsValidBool specs = true)
    (hmem : (i, q) ∈ specs) :
    ∃ h : i < 92,
      ({ index := ⟨i, h⟩, quadrant := q } : Figure18Site) ∈
        sitesOfNatSpecs specs := by
  induction specs with
  | nil =>
      simp at hmem
  | cons spec specs ih =>
      rcases spec with ⟨j, r⟩
      rcases natSpecsValidBool_cons (i := j) (q := r) hcheck with
        ⟨hj, htail⟩
      rcases List.mem_cons.1 hmem with hhead | htailMem
      · cases hhead
        exact ⟨hj, by simp [sitesOfNatSpecs, ofNat?_eq_some_of_lt q hj]⟩
      · rcases ih htail htailMem with ⟨hi, hsite⟩
        exact ⟨hi, by
          simp [sitesOfNatSpecs, ofNat?_eq_some_of_lt r hj, hsite]⟩

theorem mem_spec_of_mem_sitesOfNatSpecs
    {specs : List (Nat × Quadrant)} {site : Figure18Site}
    (hcheck : natSpecsValidBool specs = true)
    (hmem : site ∈ sitesOfNatSpecs specs) :
    (site.index.val, site.quadrant) ∈ specs := by
  induction specs with
  | nil =>
      simp [sitesOfNatSpecs] at hmem
  | cons spec specs ih =>
      rcases spec with ⟨i, q⟩
      rcases natSpecsValidBool_cons (i := i) (q := q) hcheck with
        ⟨hi, htail⟩
      simp only [sitesOfNatSpecs, ofNat?_eq_some_of_lt q hi,
        List.mem_cons] at hmem ⊢
      rcases hmem with hsite | htailMem
      · left
        cases hsite
        rfl
      · right
        exact ih htail htailMem

theorem mem_sitesOfNatSpecs_iff_of_natSpecsValidBool
    {specs : List (Nat × Quadrant)}
    (hcheck : natSpecsValidBool specs = true) (site : Figure18Site) :
    site ∈ sitesOfNatSpecs specs ↔
      (site.index.val, site.quadrant) ∈ specs := by
  constructor
  · exact mem_spec_of_mem_sitesOfNatSpecs hcheck
  · intro hmem
    rcases mem_sitesOfNatSpecs_of_mem hcheck hmem with ⟨hi, hsite⟩
    simpa using hsite

/-- Checked raw data for a finite list of Figure 18 sites. -/
structure CheckedNatSpecs where
  specs : List (Nat × Quadrant)
  valid : natSpecsValidBool specs = true

namespace CheckedNatSpecs

def sites (data : CheckedNatSpecs) : List Figure18Site :=
  sitesOfNatSpecs data.specs

theorem sites_length (data : CheckedNatSpecs) :
    data.sites.length = data.specs.length :=
  length_sitesOfNatSpecs_of_natSpecsValidBool data.valid

theorem mem_sites_of_mem_specs
    (data : CheckedNatSpecs) {i : Nat} {q : Quadrant}
    (hmem : (i, q) ∈ data.specs) :
    ∃ h : i < 92,
      ({ index := ⟨i, h⟩, quadrant := q } : Figure18Site) ∈
        data.sites :=
  mem_sitesOfNatSpecs_of_mem data.valid hmem

theorem mem_specs_of_mem_sites
    (data : CheckedNatSpecs) {site : Figure18Site}
    (hmem : site ∈ data.sites) :
    (site.index.val, site.quadrant) ∈ data.specs :=
  mem_spec_of_mem_sitesOfNatSpecs data.valid hmem

theorem mem_sites_iff (data : CheckedNatSpecs) (site : Figure18Site) :
    site ∈ data.sites ↔
      (site.index.val, site.quadrant) ∈ data.specs :=
  mem_sitesOfNatSpecs_iff_of_natSpecsValidBool data.valid site

end CheckedNatSpecs

end Figure18Site

/-- Role lookup entries for a complete quadrant role transcription. -/
def fig13QuarterRoleEntries (roleRows : List TileQuarterRoles) :
    List (WangTile × CellRole) :=
  roleEntriesOfSpecs (fig13QuarterRoleSpecs roleRows)

/--
Read the role row at a Figure 13 index from a complete 92-row role table.

This wrapper keeps later concrete-data proofs from having to carry the
`roleRows.length = 92` index proof by hand.
-/
def fig13QuarterRoleRow
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (i : Fin 92) : TileQuarterRoles :=
  roleRows.get ⟨i.val, by rw [hlen]; exact i.isLt⟩

theorem fig13QuarterRoleRow_getElem?
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (i : Fin 92) :
    roleRows[i.val]? = some (fig13QuarterRoleRow roleRows hlen i) := by
  unfold fig13QuarterRoleRow
  exact List.getElem?_eq_getElem (by rw [hlen]; exact i.isLt)

theorem mem_fig13QuarterRoleSpecs_of_getElem?
    {roleRows : List TileQuarterRoles} {i : Fin 92}
    {roles : TileQuarterRoles} (q : Quadrant)
    (hroles : roleRows[i.val]? = some roles) :
    ({ tile := fig13QuarterTile i q
       role := roles.roleAt q } : RoleTileSpec) ∈
      fig13QuarterRoleSpecs roleRows := by
  unfold fig13QuarterRoleSpecs fig13QuarterTile fig13Tile
  exact mem_quarterRoleSpecsOfTiles_of_getElem? q
    (List.getElem?_eq_getElem (by simp [fig13Tiles_length, i.isLt]))
    hroles

theorem fig13QuarterRoleEntries_lookup_of_getElem?
    {roleRows : List TileQuarterRoles} (hlen : roleRows.length = 92)
    {i : Fin 92} {roles : TileQuarterRoles} {q : Quadrant}
    (hroles : roleRows[i.val]? = some roles) :
    lookupRole (fig13QuarterRoleEntries roleRows) (fig13QuarterTile i q) =
      roles.roleAt q := by
  have hmem := mem_fig13QuarterRoleSpecs_of_getElem? (roleRows := roleRows)
    (i := i) (roles := roles) q hroles
  exact lookupRole_eq_role_of_mem_of_nodupTilesBool
    (fig13QuarterRoleSpecs_nodupTilesBool hlen) hmem

theorem fig13QuarterRoleEntries_lookup_corner_of_getElem?
    {roleRows : List TileQuarterRoles} (hlen : roleRows.length = 92)
    {i : Fin 92} {roles : TileQuarterRoles} {q : Quadrant}
    (hroles : roleRows[i.val]? = some roles)
    (hcorner : roles.roleAt q = CellRole.corner) :
    lookupRole (fig13QuarterRoleEntries roleRows) (fig13QuarterTile i q) =
      CellRole.corner := by
  rw [fig13QuarterRoleEntries_lookup_of_getElem? hlen hroles, hcorner]

/--
Finite boolean check that the given indexed quadrant is the only quadrant role
marked as the distinguished corner in a complete 92-row Figure 13 role table.
-/
def fig13QuarterCornerPositionUniqueBool
    (roleRows : List TileQuarterRoles)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant) : Bool :=
  (List.range 92).all fun i =>
    Quadrant.all.all fun q =>
      match roleRows[i]? with
      | some roles =>
          decide (roles.roleAt q = CellRole.corner) ==
            decide (i = cornerIndex.val ∧ q = cornerQuadrant)
      | none => false

theorem fig13QuarterCornerPositionUnique_of_bool
    {roleRows : List TileQuarterRoles}
    {cornerIndex : Fin 92} {cornerQuadrant : Quadrant}
    (hcheck :
      fig13QuarterCornerPositionUniqueBool
        roleRows cornerIndex cornerQuadrant = true) :
    ∀ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles →
        (roles.roleAt q = CellRole.corner ↔
          i = cornerIndex ∧ q = cornerQuadrant) := by
  intro i roles q hroles
  unfold fig13QuarterCornerPositionUniqueBool at hcheck
  have hrow := List.all_eq_true.1 hcheck i.val (List.mem_range.2 i.isLt)
  have hrow' :
      ∀ x ∈ Quadrant.all,
        decide (roles.roleAt x = CellRole.corner) =
          decide (i.val = cornerIndex.val ∧ x = cornerQuadrant) := by
    simpa [hroles] using hrow
  have hq := hrow' q (Quadrant.mem_all q)
  have hdec :
      decide (roles.roleAt q = CellRole.corner) =
        decide (i.val = cornerIndex.val ∧ q = cornerQuadrant) :=
    hq
  constructor
  · intro hrole
    have hleft : decide (roles.roleAt q = CellRole.corner) = true :=
      decide_eq_true hrole
    have hright :
        decide (i.val = cornerIndex.val ∧ q = cornerQuadrant) = true := by
      simpa [hleft] using hdec.symm
    rcases of_decide_eq_true hright with ⟨hi, hqcorner⟩
    exact ⟨Fin.ext hi, hqcorner⟩
  · rintro ⟨hi, hqcorner⟩
    have hright :
        decide (i.val = cornerIndex.val ∧ q = cornerQuadrant) = true :=
      decide_eq_true ⟨congrArg Fin.val hi, hqcorner⟩
    have hleft : decide (roles.roleAt q = CellRole.corner) = true := by
      simpa [hright] using hdec
    exact of_decide_eq_true hleft

theorem fig13QuarterCornerRole_of_positionUniqueBool
    {roleRows : List TileQuarterRoles} (hlen : roleRows.length = 92)
    {cornerIndex : Fin 92} {cornerQuadrant : Quadrant}
    (hcheck :
      fig13QuarterCornerPositionUniqueBool
        roleRows cornerIndex cornerQuadrant = true) :
    (fig13QuarterRoleRow roleRows hlen cornerIndex).roleAt cornerQuadrant =
      CellRole.corner := by
  exact (fig13QuarterCornerPositionUnique_of_bool hcheck
    cornerIndex (fig13QuarterRoleRow roleRows hlen cornerIndex) cornerQuadrant
    (fig13QuarterRoleRow_getElem? roleRows hlen cornerIndex)).2 ⟨rfl, rfl⟩

theorem exists_of_mem_fig13QuarterRoleSpecs
    {roleRows : List TileQuarterRoles} {spec : RoleTileSpec}
    (hspec : spec ∈ fig13QuarterRoleSpecs roleRows) :
    ∃ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles ∧
        spec.tile = fig13QuarterTile i q ∧
        spec.role = roles.roleAt q := by
  unfold fig13QuarterRoleSpecs at hspec
  rcases exists_of_mem_quarterRoleSpecsOfTiles hspec with
    ⟨i, tile, roles, q, htile, hroles, hspecTile, hspecRole⟩
  rcases List.getElem?_eq_some_iff.1 htile with ⟨hi, hget⟩
  refine ⟨⟨i, by simpa [fig13Tiles_length] using hi⟩, roles, q, hroles, ?_, hspecRole⟩
  unfold fig13QuarterTile fig13Tile
  have htile' : tile = fig13Tiles.get ⟨i, by simpa [fig13Tiles_length] using hi⟩ := by
    simpa [List.get_eq_getElem] using hget.symm
  simpa [htile'] using hspecTile

theorem fig13QuarterRoleSpecs_cornerRoleUniqueBool_of_forall_getElem?
    {roleRows : List TileQuarterRoles}
    {cornerIndex : Fin 92} {cornerQuadrant : Quadrant}
    (hunique : ∀ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles →
        (roles.roleAt q = CellRole.corner ↔
          i = cornerIndex ∧ q = cornerQuadrant)) :
    cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
      (fig13QuarterTile cornerIndex cornerQuadrant) = true := by
  apply cornerRoleUniqueBool_of_forall_mem
  intro spec hspec
  rcases exists_of_mem_fig13QuarterRoleSpecs hspec with
    ⟨i, roles, q, hroles, hspecTile, hspecRole⟩
  constructor
  · intro hrole
    rcases (hunique i roles q hroles).1 (hspecRole.symm.trans hrole) with
      ⟨rfl, rfl⟩
    exact hspecTile
  · intro htile
    have hparts :
        fig13QuarterTile i q = fig13QuarterTile cornerIndex cornerQuadrant := by
      exact hspecTile.symm.trans htile
    unfold fig13QuarterTile fig13Tile at hparts
    have hp := TileSubdivision.subdivideTileAt_eq_iff
      (fig13Tiles.get ⟨i.val, by simp [fig13Tiles_length, i.isLt]⟩)
      (fig13Tiles.get ⟨cornerIndex.val, by simp [fig13Tiles_length, cornerIndex.isLt]⟩)
      q cornerQuadrant |>.1 hparts
    have hq : q = cornerQuadrant := hp.2
    have hi : i = cornerIndex := by
      apply Fin.ext
      have htileEq := hp.1
      have hnodup := fig13Tiles_nodup
      have hidx :
          (⟨i.val, by simp [fig13Tiles_length, i.isLt]⟩ :
              Fin fig13Tiles.length) =
            ⟨cornerIndex.val,
              by simp [fig13Tiles_length, cornerIndex.isLt]⟩ := by
        exact (List.Nodup.get_inj_iff hnodup).1 htileEq
      exact congrArg Fin.val hidx
    exact hspecRole.trans ((hunique i roles q hroles).2 ⟨hi, hq⟩)

/--
Package complete Figure 13 quadrant roles as finite checked scaffold data from
the two corner checks that depend on the concrete role assignment.
-/
def fig13QuarterFiniteCheckedTranscription
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerTile : WangTile)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows) cornerTile = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows) cornerTile = true) :
    FiniteCheckedTranscription :=
  finiteCheckedTranscriptionOfSpecChecks
    (fig13QuarterRoleSpecs roleRows) cornerTile hcorner
    (fig13QuarterRoleSpecs_nodupTilesBool hlen) hunique

/--
Package complete Figure 13 quadrant roles when the distinguished corner is
specified by raw tile index and quadrant.
-/
def fig13QuarterFiniteCheckedTranscriptionAt
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = true) :
    FiniteCheckedTranscription :=
  fig13QuarterFiniteCheckedTranscription roleRows hlen
    (fig13QuarterTile cornerIndex cornerQuadrant) hcorner hunique

/--
Package complete Figure 13 quadrant roles from indexed corner facts.

This is the intended constructor for the concrete role table: prove that the
chosen indexed quadrant is a corner, and prove that no other indexed quadrant
has role `corner`.
-/
def fig13QuarterFiniteCheckedTranscriptionOfPositionChecks
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    {cornerRoles : TileQuarterRoles}
    (hcornerRow : roleRows[cornerIndex.val]? = some cornerRoles)
    (hcornerRole : cornerRoles.roleAt cornerQuadrant = CellRole.corner)
    (hunique : ∀ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles →
        (roles.roleAt q = CellRole.corner ↔
          i = cornerIndex ∧ q = cornerQuadrant)) :
    FiniteCheckedTranscription :=
  fig13QuarterFiniteCheckedTranscriptionAt roleRows hlen
    cornerIndex cornerQuadrant
    (fig13QuarterRoleEntries_lookup_corner_of_getElem?
      hlen hcornerRow hcornerRole)
    (fig13QuarterRoleSpecs_cornerRoleUniqueBool_of_forall_getElem? hunique)

/--
Package complete Figure 13 quadrant roles from a single finite boolean
unique-corner check.

For the concrete Figure 13/Figure 18 table, this is the intended end point:
the row length and boolean check should both be discharged by `decide`.
-/
def fig13QuarterFiniteCheckedTranscriptionOfUniqueBool
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcheck :
      fig13QuarterCornerPositionUniqueBool
        roleRows cornerIndex cornerQuadrant = true) :
    FiniteCheckedTranscription :=
  fig13QuarterFiniteCheckedTranscriptionOfPositionChecks
    roleRows hlen cornerIndex cornerQuadrant
    (fig13QuarterRoleRow_getElem? roleRows hlen cornerIndex)
    (fig13QuarterCornerRole_of_positionUniqueBool hlen hcheck)
    (fig13QuarterCornerPositionUnique_of_bool hcheck)

@[simp]
theorem fig13QuarterFiniteCheckedTranscription_specs
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerTile : WangTile)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows) cornerTile = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows) cornerTile = true) :
    (fig13QuarterFiniteCheckedTranscription roleRows hlen cornerTile hcorner hunique).specs =
      fig13QuarterRoleSpecs roleRows :=
  rfl

@[simp]
theorem fig13QuarterFiniteCheckedTranscription_cornerTile
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerTile : WangTile)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows) cornerTile = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows) cornerTile = true) :
    (fig13QuarterFiniteCheckedTranscription roleRows hlen cornerTile hcorner hunique).cornerTile =
      cornerTile :=
  rfl

theorem fig13QuarterFiniteCheckedTranscription_presentation_tiles
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerTile : WangTile)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows) cornerTile = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows) cornerTile = true) :
    (fig13QuarterFiniteCheckedTranscription
      roleRows hlen cornerTile hcorner hunique).presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles := by
  simp [FiniteCheckedTranscription.presentation, fig13QuarterRoleSpecs_tiles hlen]

@[simp]
theorem fig13QuarterFiniteCheckedTranscriptionAt_specs
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = true) :
    (fig13QuarterFiniteCheckedTranscriptionAt
      roleRows hlen cornerIndex cornerQuadrant hcorner hunique).specs =
      fig13QuarterRoleSpecs roleRows :=
  rfl

@[simp]
theorem fig13QuarterFiniteCheckedTranscriptionAt_cornerTile
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = true) :
    (fig13QuarterFiniteCheckedTranscriptionAt
      roleRows hlen cornerIndex cornerQuadrant hcorner hunique).cornerTile =
      fig13QuarterTile cornerIndex cornerQuadrant :=
  rfl

theorem fig13QuarterFiniteCheckedTranscriptionAt_presentation_tiles
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = true) :
    (fig13QuarterFiniteCheckedTranscriptionAt
      roleRows hlen cornerIndex cornerQuadrant hcorner hunique).presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  fig13QuarterFiniteCheckedTranscription_presentation_tiles
    roleRows hlen (fig13QuarterTile cornerIndex cornerQuadrant) hcorner hunique

theorem fig13QuarterFiniteCheckedTranscriptionAt_nodup
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = true) :
    (fig13QuarterFiniteCheckedTranscriptionAt
      roleRows hlen cornerIndex cornerQuadrant hcorner hunique).nodup =
      fig13QuarterRoleSpecs_nodupTilesBool hlen :=
  rfl

theorem fig13QuarterFiniteCheckedTranscriptionAt_sanity
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcorner :
      lookupRole (fig13QuarterRoleEntries roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = CellRole.corner)
    (hunique :
      cornerRoleUniqueBool (fig13QuarterRoleSpecs roleRows)
        (fig13QuarterTile cornerIndex cornerQuadrant) = true) :
    (fig13QuarterFiniteCheckedTranscriptionAt
      roleRows hlen cornerIndex cornerQuadrant hcorner hunique).sanity =
      sanityBool_of_specChecks hcorner
        (fig13QuarterRoleSpecs_nodupTilesBool hlen) hunique :=
  rfl

@[simp]
theorem fig13QuarterFiniteCheckedTranscriptionOfPositionChecks_specs
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    {cornerRoles : TileQuarterRoles}
    (hcornerRow : roleRows[cornerIndex.val]? = some cornerRoles)
    (hcornerRole : cornerRoles.roleAt cornerQuadrant = CellRole.corner)
    (hunique : ∀ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles →
        (roles.roleAt q = CellRole.corner ↔
          i = cornerIndex ∧ q = cornerQuadrant)) :
    (fig13QuarterFiniteCheckedTranscriptionOfPositionChecks
      roleRows hlen cornerIndex cornerQuadrant hcornerRow hcornerRole hunique).specs =
      fig13QuarterRoleSpecs roleRows :=
  rfl

@[simp]
theorem fig13QuarterFiniteCheckedTranscriptionOfPositionChecks_cornerTile
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    {cornerRoles : TileQuarterRoles}
    (hcornerRow : roleRows[cornerIndex.val]? = some cornerRoles)
    (hcornerRole : cornerRoles.roleAt cornerQuadrant = CellRole.corner)
    (hunique : ∀ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles →
        (roles.roleAt q = CellRole.corner ↔
          i = cornerIndex ∧ q = cornerQuadrant)) :
    (fig13QuarterFiniteCheckedTranscriptionOfPositionChecks
      roleRows hlen cornerIndex cornerQuadrant hcornerRow hcornerRole hunique).cornerTile =
      fig13QuarterTile cornerIndex cornerQuadrant :=
  rfl

theorem fig13QuarterFiniteCheckedTranscriptionOfPositionChecks_presentation_tiles
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    {cornerRoles : TileQuarterRoles}
    (hcornerRow : roleRows[cornerIndex.val]? = some cornerRoles)
    (hcornerRole : cornerRoles.roleAt cornerQuadrant = CellRole.corner)
    (hunique : ∀ (i : Fin 92) (roles : TileQuarterRoles) (q : Quadrant),
      roleRows[i.val]? = some roles →
        (roles.roleAt q = CellRole.corner ↔
          i = cornerIndex ∧ q = cornerQuadrant)) :
    (fig13QuarterFiniteCheckedTranscriptionOfPositionChecks
      roleRows hlen cornerIndex cornerQuadrant hcornerRow hcornerRole
        hunique).presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  fig13QuarterFiniteCheckedTranscriptionAt_presentation_tiles
    roleRows hlen cornerIndex cornerQuadrant
    (fig13QuarterRoleEntries_lookup_corner_of_getElem?
      hlen hcornerRow hcornerRole)
    (fig13QuarterRoleSpecs_cornerRoleUniqueBool_of_forall_getElem? hunique)

@[simp]
theorem fig13QuarterFiniteCheckedTranscriptionOfUniqueBool_specs
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcheck :
      fig13QuarterCornerPositionUniqueBool
        roleRows cornerIndex cornerQuadrant = true) :
    (fig13QuarterFiniteCheckedTranscriptionOfUniqueBool
      roleRows hlen cornerIndex cornerQuadrant hcheck).specs =
      fig13QuarterRoleSpecs roleRows :=
  fig13QuarterFiniteCheckedTranscriptionOfPositionChecks_specs
    roleRows hlen cornerIndex cornerQuadrant
    (fig13QuarterRoleRow_getElem? roleRows hlen cornerIndex)
    (fig13QuarterCornerRole_of_positionUniqueBool hlen hcheck)
    (fig13QuarterCornerPositionUnique_of_bool hcheck)

@[simp]
theorem fig13QuarterFiniteCheckedTranscriptionOfUniqueBool_cornerTile
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcheck :
      fig13QuarterCornerPositionUniqueBool
        roleRows cornerIndex cornerQuadrant = true) :
    (fig13QuarterFiniteCheckedTranscriptionOfUniqueBool
      roleRows hlen cornerIndex cornerQuadrant hcheck).cornerTile =
      fig13QuarterTile cornerIndex cornerQuadrant :=
  fig13QuarterFiniteCheckedTranscriptionOfPositionChecks_cornerTile
    roleRows hlen cornerIndex cornerQuadrant
    (fig13QuarterRoleRow_getElem? roleRows hlen cornerIndex)
    (fig13QuarterCornerRole_of_positionUniqueBool hlen hcheck)
    (fig13QuarterCornerPositionUnique_of_bool hcheck)

theorem fig13QuarterFiniteCheckedTranscriptionOfUniqueBool_presentation_tiles
    (roleRows : List TileQuarterRoles) (hlen : roleRows.length = 92)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hcheck :
      fig13QuarterCornerPositionUniqueBool
        roleRows cornerIndex cornerQuadrant = true) :
    (fig13QuarterFiniteCheckedTranscriptionOfUniqueBool
      roleRows hlen cornerIndex cornerQuadrant hcheck).presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  fig13QuarterFiniteCheckedTranscriptionOfPositionChecks_presentation_tiles
    roleRows hlen cornerIndex cornerQuadrant
    (fig13QuarterRoleRow_getElem? roleRows hlen cornerIndex)
    (fig13QuarterCornerRole_of_positionUniqueBool hlen hcheck)
    (fig13QuarterCornerPositionUnique_of_bool hcheck)

/--
Concrete finite target for the Figure 18 interpretation of Figure 13.

The rows are ordered like `fig13Tiles`; each row assigns roles to the four
quarter-tiles of that raw tile.  The boolean certificate states that the
declared indexed quadrant is exactly the unique `corner` quadrant.  Filling this
structure with the paper-derived role table is the finite-data step before the
geometric `forces`/`realizes` proofs.
-/
structure Figure18RoleTable where
  roleRows : List TileQuarterRoles
  cornerIndex : Fin 92
  cornerQuadrant : Quadrant
  length_eq : roleRows.length = 92
  uniqueCorner :
    fig13QuarterCornerPositionUniqueBool
      roleRows cornerIndex cornerQuadrant = true

namespace Figure18RoleTable

def row (table : Figure18RoleTable) (i : Fin 92) : TileQuarterRoles :=
  fig13QuarterRoleRow table.roleRows table.length_eq i

def roleAt (table : Figure18RoleTable) (i : Fin 92) (q : Quadrant) :
    CellRole :=
  (table.row i).roleAt q

def roleAtSite (table : Figure18RoleTable) (site : Figure18Site) :
    CellRole :=
  table.roleAt site.index site.quadrant

def cornerTile (table : Figure18RoleTable) : WangTile :=
  fig13QuarterTile table.cornerIndex table.cornerQuadrant

def cornerSite (table : Figure18RoleTable) : Figure18Site where
  index := table.cornerIndex
  quadrant := table.cornerQuadrant

def finiteCheckedTranscription (table : Figure18RoleTable) :
    FiniteCheckedTranscription :=
  fig13QuarterFiniteCheckedTranscriptionOfUniqueBool
    table.roleRows table.length_eq table.cornerIndex table.cornerQuadrant
    table.uniqueCorner

def presentation (table : Figure18RoleTable) : ScaffoldPresentation :=
  table.finiteCheckedTranscription.presentation

@[simp]
theorem finiteCheckedTranscription_specs (table : Figure18RoleTable) :
    table.finiteCheckedTranscription.specs =
      fig13QuarterRoleSpecs table.roleRows :=
  fig13QuarterFiniteCheckedTranscriptionOfUniqueBool_specs
    table.roleRows table.length_eq table.cornerIndex table.cornerQuadrant
    table.uniqueCorner

@[simp]
theorem finiteCheckedTranscription_cornerTile (table : Figure18RoleTable) :
    table.finiteCheckedTranscription.cornerTile = table.cornerTile :=
  fig13QuarterFiniteCheckedTranscriptionOfUniqueBool_cornerTile
    table.roleRows table.length_eq table.cornerIndex table.cornerQuadrant
    table.uniqueCorner

theorem finiteCheckedTranscription_presentation_tiles
    (table : Figure18RoleTable) :
    table.finiteCheckedTranscription.presentation.tiles =
      TileSubdivision.subdivideTileSet fig13Tiles :=
  fig13QuarterFiniteCheckedTranscriptionOfUniqueBool_presentation_tiles
    table.roleRows table.length_eq table.cornerIndex table.cornerQuadrant
    table.uniqueCorner

theorem presentation_tiles (table : Figure18RoleTable) :
    table.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  table.finiteCheckedTranscription_presentation_tiles

theorem presentation_tiles_nodup (table : Figure18RoleTable) :
    table.presentation.tiles.Nodup := by
  rw [table.presentation_tiles]
  exact fig13SubdividedTiles_nodup

theorem row_getElem? (table : Figure18RoleTable) (i : Fin 92) :
    table.roleRows[i.val]? = some (table.row i) :=
  fig13QuarterRoleRow_getElem? table.roleRows table.length_eq i

theorem presentation_mem_fig13QuarterTile
    (table : Figure18RoleTable) (i : Fin 92) (q : Quadrant) :
    fig13QuarterTile i q ∈ table.presentation.tiles := by
  rw [table.presentation_tiles]
  have hspec := mem_fig13QuarterRoleSpecs_of_getElem? (roleRows := table.roleRows)
    (i := i) (roles := table.row i) q (table.row_getElem? i)
  have hmem : fig13QuarterTile i q ∈
      tilesOfSpecs (fig13QuarterRoleSpecs table.roleRows) := by
    exact mem_tilesOfSpecs.2 ⟨
      ({ tile := fig13QuarterTile i q
         role := (table.row i).roleAt q } : RoleTileSpec),
      hspec, rfl⟩
  simpa [fig13QuarterRoleSpecs_tiles table.length_eq] using hmem

theorem presentation_mem_site
    (table : Figure18RoleTable) (site : Figure18Site) :
    site.tile ∈ table.presentation.tiles :=
  table.presentation_mem_fig13QuarterTile site.index site.quadrant

theorem exists_fig13QuarterTile_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    ∃ i : Fin 92, ∃ q : Quadrant, tile = fig13QuarterTile i q := by
  have htile' : tile ∈ tilesOfSpecs (fig13QuarterRoleSpecs table.roleRows) := by
    rw [fig13QuarterRoleSpecs_tiles table.length_eq]
    simpa [table.presentation_tiles] using htile
  rcases mem_tilesOfSpecs.1 htile' with ⟨spec, hspec, hspecTile⟩
  rcases exists_of_mem_fig13QuarterRoleSpecs hspec with
    ⟨i, _roles, q, _hroles, hspecQuarter, _hspecRole⟩
  exact ⟨i, q, hspecTile.symm.trans hspecQuarter⟩

theorem presentation_mem_iff_exists_fig13QuarterTile
    (table : Figure18RoleTable) (tile : WangTile) :
    tile ∈ table.presentation.tiles ↔
      ∃ i : Fin 92, ∃ q : Quadrant, tile = fig13QuarterTile i q := by
  constructor
  · exact table.exists_fig13QuarterTile_of_mem_presentation
  · rintro ⟨i, q, rfl⟩
    exact table.presentation_mem_fig13QuarterTile i q

theorem exists_site_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    ∃ site : Figure18Site, site ∈ Figure18Site.all ∧ tile = site.tile := by
  rcases table.exists_fig13QuarterTile_of_mem_presentation htile with
    ⟨i, q, htileSite⟩
  let site : Figure18Site := { index := i, quadrant := q }
  exact ⟨site, Figure18Site.mem_all site, htileSite⟩

theorem presentation_mem_iff_exists_site
    (table : Figure18RoleTable) (tile : WangTile) :
    tile ∈ table.presentation.tiles ↔
      ∃ site : Figure18Site, site ∈ Figure18Site.all ∧ tile = site.tile := by
  constructor
  · exact table.exists_site_of_mem_presentation
  · rintro ⟨site, _hsite, rfl⟩
    exact table.presentation_mem_site site

theorem presentation_mem_iff_mem_site_tiles
    (table : Figure18RoleTable) (tile : WangTile) :
    tile ∈ table.presentation.tiles ↔
      tile ∈ Figure18Site.all.map Figure18Site.tile := by
  constructor
  · intro htile
    rcases table.exists_site_of_mem_presentation htile with
      ⟨site, hsite, htileSite⟩
    exact List.mem_map.2 ⟨site, hsite, htileSite.symm⟩
  · intro htile
    rcases List.mem_map.1 htile with ⟨site, _hsite, htileSite⟩
    exact htileSite ▸ table.presentation_mem_site site

/--
Decode a scaffold presentation tile back to its Figure 18 site using the
finite numeric site search.
-/
def siteOfPresentationTile
    (table : Figure18RoleTable) (tile : WangTile)
    (htile : tile ∈ table.presentation.tiles) : Figure18Site :=
  Figure18Site.siteOfTile tile
    ((table.presentation_mem_iff_mem_site_tiles tile).1 htile)

theorem siteOfPresentationTile_mem_all
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    table.siteOfPresentationTile tile htile ∈ Figure18Site.all :=
  Figure18Site.siteOfTile_mem_all
    ((table.presentation_mem_iff_mem_site_tiles tile).1 htile)

theorem siteOfPresentationTile_tile
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    (table.siteOfPresentationTile tile htile).tile = tile :=
  Figure18Site.siteOfTile_tile
    ((table.presentation_mem_iff_mem_site_tiles tile).1 htile)

theorem siteOfPresentationTile_getElem?
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    Figure18Site.all[Figure18Site.tileIndex tile]? =
      some (table.siteOfPresentationTile tile htile) :=
  Figure18Site.siteOfTile_getElem?
    ((table.presentation_mem_iff_mem_site_tiles tile).1 htile)

theorem siteOfTile?_isSome_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    (Figure18Site.ofTile? tile).isSome = true :=
  Figure18Site.ofTile?_isSome_of_mem_all_tiles
    ((table.presentation_mem_iff_mem_site_tiles tile).1 htile)

/--
Decode the scaffold layer of one tile in a scaffold/payload product.

This is a single-cell helper for the Figure 18 geometric extraction: membership
in `combineWithScaffold` gives some presentation tile and payload whose product
is the observed combined tile.
-/
theorem exists_base_payload_of_mem_combineWithScaffold
    (table : Figure18RoleTable) {T : TileSet} {seed tile : WangTile}
    (htile : tile ∈ combineWithScaffold table.presentation.toScaffold T seed) :
    ∃ base : WangTile, base ∈ table.presentation.tiles ∧
      ∃ payload : WangTile, WangTile.product base payload = tile := by
  rcases mem_combineWithScaffold_iff.1 htile with
    ⟨base, hbase, payload, _hactiveMem, _hinactive, hproduct⟩
  exact ⟨base, hbase, payload, hproduct⟩

noncomputable def combinedBaseTile
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    WangTile :=
  Classical.choose
    (table.exists_base_payload_of_mem_combineWithScaffold tile.2)

theorem combinedBaseTile_mem
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    table.combinedBaseTile tile ∈ table.presentation.tiles :=
  (Classical.choose_spec
    (table.exists_base_payload_of_mem_combineWithScaffold tile.2)).1

theorem combinedBaseTile_product
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    ∃ payload : WangTile,
      WangTile.product (table.combinedBaseTile tile) payload = tile.1 :=
  (Classical.choose_spec
    (table.exists_base_payload_of_mem_combineWithScaffold tile.2)).2

noncomputable def combinedSite
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    Figure18Site :=
  table.siteOfPresentationTile
    (table.combinedBaseTile tile) (table.combinedBaseTile_mem tile)

theorem combinedSite_tile
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    (table.combinedSite tile).tile = table.combinedBaseTile tile :=
  table.siteOfPresentationTile_tile (table.combinedBaseTile_mem tile)

theorem combinedSite_mem_all
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    table.combinedSite tile ∈ Figure18Site.all :=
  table.siteOfPresentationTile_mem_all (table.combinedBaseTile_mem tile)

theorem combinedSite_product
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    ∃ payload : WangTile,
      WangTile.product (table.combinedSite tile).tile payload = tile.1 := by
  rcases table.combinedBaseTile_product tile with ⟨payload, hproduct⟩
  refine ⟨payload, ?_⟩
  rw [table.combinedSite_tile tile]
  exact hproduct

theorem combinedSite_hCompatible_of_validPlaneTiling
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    {x : Int × Int →
      TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling
      (combineWithScaffold table.presentation.toScaffold T seed) x)
    (p : Int × Int) :
    Figure18Site.hCompatible
      (table.combinedSite (x p))
      (table.combinedSite (x (p.1 + 1, p.2))) = true := by
  rcases table.combinedSite_product (x p) with
    ⟨payloadLeft, hleft⟩
  rcases table.combinedSite_product (x (p.1 + 1, p.2)) with
    ⟨payloadRight, hright⟩
  apply Figure18Site.hCompatible_of_hMatches
  have hproduct : WangTile.HMatches
      (WangTile.product (table.combinedSite (x p)).tile payloadLeft)
      (WangTile.product
        (table.combinedSite (x (p.1 + 1, p.2))).tile payloadRight) := by
    simpa [← hleft, ← hright] using hx.1 p
  exact (WangTile.HMatches_product_iff
    (table.combinedSite (x p)).tile payloadLeft
    (table.combinedSite (x (p.1 + 1, p.2))).tile payloadRight).1
      hproduct |>.1

theorem combinedSite_vCompatible_of_validPlaneTiling
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    {x : Int × Int →
      TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling
      (combineWithScaffold table.presentation.toScaffold T seed) x)
    (p : Int × Int) :
    Figure18Site.vCompatible
      (table.combinedSite (x p))
      (table.combinedSite (x (p.1, p.2 + 1))) = true := by
  rcases table.combinedSite_product (x p) with
    ⟨payloadLower, hlower⟩
  rcases table.combinedSite_product (x (p.1, p.2 + 1)) with
    ⟨payloadUpper, hupper⟩
  apply Figure18Site.vCompatible_of_vMatches
  have hproduct : WangTile.VMatches
      (WangTile.product (table.combinedSite (x p)).tile payloadLower)
      (WangTile.product
        (table.combinedSite (x (p.1, p.2 + 1))).tile payloadUpper) := by
    simpa [← hlower, ← hupper] using hx.2 p
  exact (WangTile.VMatches_product_iff
    (table.combinedSite (x p)).tile payloadLower
    (table.combinedSite (x (p.1, p.2 + 1))).tile payloadUpper).1
      hproduct |>.1

theorem combinedSite_hCompatible_of_selectedCoords
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    {x : Int × Int →
      TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling
      (combineWithScaffold table.presentation.toScaffold T seed) x)
    {n : Nat}
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
      horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1)
    (i : Fin n) (j : Fin n) (hi : i.val + 1 < n) :
    Figure18Site.hCompatible
      (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
      (table.combinedSite
        (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) = true := by
  have hcompat :=
    table.combinedSite_hCompatible_of_validPlaneTiling hx
      (horizontalCoord i, verticalCoord j)
  simpa [horizontalCoord_succ i hi] using hcompat

theorem combinedSite_vCompatible_of_selectedCoords
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    {x : Int × Int →
      TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling
      (combineWithScaffold table.presentation.toScaffold T seed) x)
    {n : Nat}
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1)
    (i : Fin n) (j : Fin n) (hj : j.val + 1 < n) :
    Figure18Site.vCompatible
      (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
      (table.combinedSite
        (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) = true := by
  have vcompat :=
    table.combinedSite_vCompatible_of_validPlaneTiling hx
      (horizontalCoord i, verticalCoord j)
  simpa [verticalCoord_succ j hj] using vcompat

theorem presentation_role_fig13QuarterTile
    (table : Figure18RoleTable) (i : Fin 92) (q : Quadrant) :
    table.presentation.role (fig13QuarterTile i q) = table.roleAt i q := by
  simpa [presentation, finiteCheckedTranscription,
    FiniteCheckedTranscription.presentation, presentationOfSpecs,
    fig13QuarterRoleEntries, roleAt] using
    fig13QuarterRoleEntries_lookup_of_getElem?
      table.length_eq (table.row_getElem? i) (q := q)

theorem presentation_role_site
    (table : Figure18RoleTable) (site : Figure18Site) :
    table.presentation.role site.tile = table.roleAtSite site :=
  table.presentation_role_fig13QuarterTile site.index site.quadrant

theorem presentation_role_of_eq_site
    (table : Figure18RoleTable) {tile : WangTile} {site : Figure18Site}
    (htile : tile = site.tile) :
    table.presentation.role tile = table.roleAtSite site := by
  rw [htile, table.presentation_role_site]

theorem presentation_active_of_eq_site
    (table : Figure18RoleTable) {tile : WangTile} {site : Figure18Site}
    (htile : tile = site.tile) :
    CellRole.isActive (table.presentation.role tile) =
      CellRole.isActive (table.roleAtSite site) := by
  rw [htile, table.presentation_role_site]

theorem presentation_role_siteOfPresentationTile
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    table.presentation.role tile =
      table.roleAtSite (table.siteOfPresentationTile tile htile) :=
  table.presentation_role_of_eq_site
    (table.siteOfPresentationTile_tile htile).symm

theorem presentation_active_siteOfPresentationTile
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    CellRole.isActive (table.presentation.role tile) =
      CellRole.isActive
        (table.roleAtSite (table.siteOfPresentationTile tile htile)) := by
  rw [table.presentation_role_siteOfPresentationTile htile]

theorem presentation_role_combinedBaseTile
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    table.presentation.role (table.combinedBaseTile tile) =
      table.roleAtSite (table.combinedSite tile) :=
  table.presentation_role_siteOfPresentationTile (table.combinedBaseTile_mem tile)

theorem presentation_active_combinedBaseTile
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    CellRole.isActive (table.presentation.role (table.combinedBaseTile tile)) =
      CellRole.isActive (table.roleAtSite (table.combinedSite tile)) := by
  rw [table.presentation_role_combinedBaseTile tile]

theorem hMatches_of_siteOfPresentationTile_hCompatible
    (table : Figure18RoleTable) {left right : WangTile}
    (hleft : left ∈ table.presentation.tiles)
    (hright : right ∈ table.presentation.tiles)
    (hcompat : Figure18Site.hCompatible
      (table.siteOfPresentationTile left hleft)
      (table.siteOfPresentationTile right hright) = true) :
    WangTile.HMatches left right := by
  have hmatch := Figure18Site.hMatches_of_hCompatible hcompat
  rwa [table.siteOfPresentationTile_tile hleft,
    table.siteOfPresentationTile_tile hright] at hmatch

theorem vMatches_of_siteOfPresentationTile_vCompatible
    (table : Figure18RoleTable) {lower upper : WangTile}
    (hlower : lower ∈ table.presentation.tiles)
    (hupper : upper ∈ table.presentation.tiles)
    (hcompat : Figure18Site.vCompatible
      (table.siteOfPresentationTile lower hlower)
      (table.siteOfPresentationTile upper hupper) = true) :
    WangTile.VMatches lower upper := by
  have hmatch := Figure18Site.vMatches_of_vCompatible hcompat
  rwa [table.siteOfPresentationTile_tile hlower,
    table.siteOfPresentationTile_tile hupper] at hmatch

theorem exists_fig13QuarterTile_role_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    ∃ i : Fin 92, ∃ q : Quadrant,
      tile = fig13QuarterTile i q ∧
        table.presentation.role tile = table.roleAt i q := by
  rcases table.exists_fig13QuarterTile_of_mem_presentation htile with
    ⟨i, q, rfl⟩
  exact ⟨i, q, rfl, table.presentation_role_fig13QuarterTile i q⟩

theorem exists_site_role_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    ∃ site : Figure18Site, site ∈ Figure18Site.all ∧
      tile = site.tile ∧
        table.presentation.role tile = table.roleAtSite site := by
  rcases table.exists_site_of_mem_presentation htile with
    ⟨site, hsite, htileSite⟩
  exact ⟨site, hsite, htileSite,
    table.presentation_role_of_eq_site htileSite⟩

theorem exists_siteOfTile?_role_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    ∃ site : Figure18Site,
      Figure18Site.ofTile? tile = some site ∧
        site ∈ Figure18Site.all ∧
          tile = site.tile ∧
            table.presentation.role tile = table.roleAtSite site := by
  rcases Figure18Site.exists_ofTile?_eq_some_of_mem_all_tiles
      ((table.presentation_mem_iff_mem_site_tiles tile).1 htile) with
    ⟨site, hdecode, hsite, hsiteTile⟩
  exact ⟨site, hdecode, hsite, hsiteTile.symm,
    table.presentation_role_of_eq_site hsiteTile.symm⟩

theorem exists_site_active_of_mem_presentation
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles) :
    ∃ site : Figure18Site, site ∈ Figure18Site.all ∧
      tile = site.tile ∧
        CellRole.isActive (table.presentation.role tile) =
          CellRole.isActive (table.roleAtSite site) := by
  rcases table.exists_site_of_mem_presentation htile with
    ⟨site, hsite, htileSite⟩
  exact ⟨site, hsite, htileSite,
    table.presentation_active_of_eq_site htileSite⟩

theorem roleAt_corner (table : Figure18RoleTable) :
    table.roleAt table.cornerIndex table.cornerQuadrant = CellRole.corner := by
  exact fig13QuarterCornerRole_of_positionUniqueBool
    table.length_eq table.uniqueCorner

theorem roleAtSite_corner (table : Figure18RoleTable) :
    table.roleAtSite table.cornerSite = CellRole.corner :=
  table.roleAt_corner

theorem presentation_role_cornerTile (table : Figure18RoleTable) :
    table.presentation.role table.cornerTile = CellRole.corner := by
  rw [cornerTile, presentation_role_fig13QuarterTile, roleAt_corner]

theorem presentation_active_fig13QuarterTile
    (table : Figure18RoleTable) (i : Fin 92) (q : Quadrant) :
    CellRole.isActive (table.presentation.role (fig13QuarterTile i q)) =
      CellRole.isActive (table.roleAt i q) := by
  rw [presentation_role_fig13QuarterTile]

theorem presentation_active_site
    (table : Figure18RoleTable) (site : Figure18Site) :
    CellRole.isActive (table.presentation.role site.tile) =
      CellRole.isActive (table.roleAtSite site) := by
  rw [presentation_role_site]

theorem presentation_active_cornerTile (table : Figure18RoleTable) :
    CellRole.isActive (table.presentation.role table.cornerTile) = true := by
  rw [presentation_role_cornerTile]
  rfl

theorem roleAt_corner_iff (table : Figure18RoleTable)
    (i : Fin 92) (q : Quadrant) :
    table.roleAt i q = CellRole.corner ↔
      i = table.cornerIndex ∧ q = table.cornerQuadrant := by
  exact fig13QuarterCornerPositionUnique_of_bool table.uniqueCorner
    i (table.row i) q (table.row_getElem? i)

theorem roleAtSite_corner_iff (table : Figure18RoleTable)
    (site : Figure18Site) :
    table.roleAtSite site = CellRole.corner ↔ site = table.cornerSite := by
  cases site with
  | mk i q =>
      simp [roleAtSite, cornerSite, roleAt_corner_iff]

theorem site_eq_cornerSite_of_presentation_role_corner
    (table : Figure18RoleTable) {tile : WangTile} {site : Figure18Site}
    (htile : tile = site.tile)
    (hrole : table.presentation.role tile = CellRole.corner) :
    site = table.cornerSite := by
  have hsiteRole : table.roleAtSite site = CellRole.corner := by
    rw [← table.presentation_role_of_eq_site htile]
    exact hrole
  exact (table.roleAtSite_corner_iff site).1 hsiteRole

theorem siteOfPresentationTile_eq_cornerSite_of_role_corner
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles)
    (hrole : table.presentation.role tile = CellRole.corner) :
    table.siteOfPresentationTile tile htile = table.cornerSite :=
  table.site_eq_cornerSite_of_presentation_role_corner
    (table.siteOfPresentationTile_tile htile).symm hrole

theorem exists_cornerSite_of_mem_presentation_role_corner
    (table : Figure18RoleTable) {tile : WangTile}
    (htile : tile ∈ table.presentation.tiles)
    (hrole : table.presentation.role tile = CellRole.corner) :
    ∃ site : Figure18Site, site ∈ Figure18Site.all ∧
      tile = site.tile ∧ site = table.cornerSite := by
  rcases table.exists_site_of_mem_presentation htile with
    ⟨site, hsite, htileSite⟩
  exact ⟨site, hsite, htileSite,
    table.site_eq_cornerSite_of_presentation_role_corner htileSite hrole⟩

theorem cornerTile_eq_cornerSite_tile (table : Figure18RoleTable) :
    table.cornerTile = table.cornerSite.tile :=
  rfl

end Figure18RoleTable

namespace Figure18RoleTable

/--
Convert a flat quarter-role transcription into the 92 raw-tile rows expected by
`Figure18RoleTable`.

The flat order is the same as `fig13QuarterRoleSpecs`: for each raw Figure 13
tile in scan order, list southwest, southeast, northwest, then northeast.  The
`getD` default is only for totality; `ofFlatRoles` below separately requires
the intended length `368`.
-/
def rowsOfFlatRoles (flat : List CellRole) : List TileQuarterRoles :=
  (List.range 92).map fun i =>
    TileQuarterRoles.ofQuadrants
      (flat.getD (4 * i) CellRole.inactive)
      (flat.getD (4 * i + 1) CellRole.inactive)
      (flat.getD (4 * i + 2) CellRole.inactive)
      (flat.getD (4 * i + 3) CellRole.inactive)

@[simp]
theorem rowsOfFlatRoles_length (flat : List CellRole) :
    (rowsOfFlatRoles flat).length = 92 := by
  simp [rowsOfFlatRoles]

/--
Build a `Figure18RoleTable` from a flat quarter-role transcription.

This is the intended constructor for a transcription read directly from the
quarter-level Figure 18 picture: prove the flat list has exactly 368 entries and
let the existing finite checker prove the unique-corner condition.
-/
def ofFlatRoles
    (flat : List CellRole) (_hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true) :
    Figure18RoleTable where
  roleRows := rowsOfFlatRoles flat
  cornerIndex := cornerIndex
  cornerQuadrant := cornerQuadrant
  length_eq := rowsOfFlatRoles_length flat
  uniqueCorner := hunique

theorem rowsOfFlatRoles_getElem?
    (flat : List CellRole) (i : Fin 92) :
    (rowsOfFlatRoles flat)[i.val]? =
      some (TileQuarterRoles.ofQuadrants
        (flat.getD (4 * i.val) CellRole.inactive)
        (flat.getD (4 * i.val + 1) CellRole.inactive)
        (flat.getD (4 * i.val + 2) CellRole.inactive)
        (flat.getD (4 * i.val + 3) CellRole.inactive)) := by
  unfold rowsOfFlatRoles
  simp [i.isLt]

theorem ofFlatRoles_row
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (i : Fin 92) :
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).row i =
      TileQuarterRoles.ofQuadrants
        (flat.getD (4 * i.val) CellRole.inactive)
        (flat.getD (4 * i.val + 1) CellRole.inactive)
        (flat.getD (4 * i.val + 2) CellRole.inactive)
        (flat.getD (4 * i.val + 3) CellRole.inactive) := by
  have hrow :=
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).row_getElem? i
  change (rowsOfFlatRoles flat)[i.val]? =
      some ((ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).row i) at hrow
  rw [rowsOfFlatRoles_getElem? flat i] at hrow
  exact Option.some.inj hrow.symm

theorem ofFlatRoles_roleAt_southwest
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (i : Fin 92) :
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).roleAt
        i Quadrant.southwest =
      flat.getD (4 * i.val) CellRole.inactive := by
  simp [Figure18RoleTable.roleAt, ofFlatRoles_row]

theorem ofFlatRoles_roleAt_southeast
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (i : Fin 92) :
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).roleAt
        i Quadrant.southeast =
      flat.getD (4 * i.val + 1) CellRole.inactive := by
  simp [Figure18RoleTable.roleAt, ofFlatRoles_row]

theorem ofFlatRoles_roleAt_northwest
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (i : Fin 92) :
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).roleAt
        i Quadrant.northwest =
      flat.getD (4 * i.val + 2) CellRole.inactive := by
  simp [Figure18RoleTable.roleAt, ofFlatRoles_row]

theorem ofFlatRoles_roleAt_northeast
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (i : Fin 92) :
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).roleAt
        i Quadrant.northeast =
      flat.getD (4 * i.val + 3) CellRole.inactive := by
  simp [Figure18RoleTable.roleAt, ofFlatRoles_row]

/-- Role lookup in a flat Figure 18 transcription, indexed by concrete site. -/
def flatRoleAt (flat : List CellRole) (site : Figure18Site) : CellRole :=
  flat.getD site.flatIndex CellRole.inactive

theorem rowsOfFlatRoles_roleAt
    (flat : List CellRole) (i : Fin 92) (q : Quadrant) :
    (fig13QuarterRoleRow (rowsOfFlatRoles flat)
        (rowsOfFlatRoles_length flat) i).roleAt q =
      flatRoleAt flat ({ index := i, quadrant := q } : Figure18Site) := by
  have hrow := fig13QuarterRoleRow_getElem?
    (rowsOfFlatRoles flat) (rowsOfFlatRoles_length flat) i
  rw [rowsOfFlatRoles_getElem? flat i] at hrow
  have hrowEq := Option.some.inj hrow.symm
  rw [hrowEq]
  cases q <;> rfl

theorem ofFlatRoles_roleAtSite
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (site : Figure18Site) :
    (ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique).roleAtSite site =
      flatRoleAt flat site := by
  rcases site with ⟨i, q⟩
  cases q <;>
    simp [Figure18RoleTable.roleAtSite, flatRoleAt,
      ofFlatRoles_roleAt_southwest, ofFlatRoles_roleAt_southeast,
      ofFlatRoles_roleAt_northwest, ofFlatRoles_roleAt_northeast]

theorem ofFlatRoles_flatRoleAt_corner_iff
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (site : Figure18Site) :
    flatRoleAt flat site = CellRole.corner ↔
      site = ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site) := by
  let table : Figure18RoleTable :=
    ofFlatRoles flat hflat cornerIndex cornerQuadrant hunique
  have hrole : table.roleAtSite site = flatRoleAt flat site :=
    ofFlatRoles_roleAtSite flat hflat cornerIndex cornerQuadrant hunique site
  rw [← hrole]
  simpa [table, Figure18RoleTable.cornerSite, ofFlatRoles] using
    table.roleAtSite_corner_iff site

theorem ofFlatRoles_flatRoleAt_corner
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true) :
    flatRoleAt flat
        ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site) =
      CellRole.corner := by
  exact (ofFlatRoles_flatRoleAt_corner_iff
    flat hflat cornerIndex cornerQuadrant hunique
    ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site)).2 rfl

theorem ofFlatRoles_isCorner_flatRoleAt_iff
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (site : Figure18Site) :
    CellRole.isCorner (flatRoleAt flat site) = true ↔
      site = ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site) := by
  rw [CellRole.isCorner_eq_true_iff]
  exact ofFlatRoles_flatRoleAt_corner_iff
    flat hflat cornerIndex cornerQuadrant hunique site

/--
The active Figure 18 sites selected by a flat role transcription.

This is a finite data view used by the concrete scaffold proof: after the paper
role table is transcribed, this list exposes exactly the sites where payload
tiles may be read.
-/
def activeFlatSites (flat : List CellRole) : List Figure18Site :=
  Figure18Site.all.filter fun site =>
    CellRole.isActive (flatRoleAt flat site)

def cornerFlatSites (flat : List CellRole) : List Figure18Site :=
  Figure18Site.all.filter fun site =>
    CellRole.isCorner (flatRoleAt flat site)

theorem mem_activeFlatSites {flat : List CellRole} {site : Figure18Site} :
    site ∈ activeFlatSites flat ↔
      site ∈ Figure18Site.all ∧
        CellRole.isActive (flatRoleAt flat site) = true := by
  simp [activeFlatSites]

theorem mem_cornerFlatSites {flat : List CellRole} {site : Figure18Site} :
    site ∈ cornerFlatSites flat ↔
      site ∈ Figure18Site.all ∧
        CellRole.isCorner (flatRoleAt flat site) = true := by
  simp [cornerFlatSites]

theorem mem_cornerFlatSites_ofFlatRoles_iff
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true)
    (site : Figure18Site) :
    site ∈ cornerFlatSites flat ↔
      site = ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site) := by
  rw [mem_cornerFlatSites,
    ofFlatRoles_isCorner_flatRoleAt_iff flat hflat cornerIndex cornerQuadrant hunique]
  constructor
  · exact And.right
  · intro hsite
    exact ⟨Figure18Site.mem_all site, hsite⟩

theorem corner_mem_activeFlatSites_ofFlatRoles
    (flat : List CellRole) (hflat : flat.length = 368)
    (cornerIndex : Fin 92) (cornerQuadrant : Quadrant)
    (hunique :
      fig13QuarterCornerPositionUniqueBool
        (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true) :
    ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site) ∈
      activeFlatSites flat := by
  rw [mem_activeFlatSites]
  exact ⟨Figure18Site.mem_all
      ({ index := cornerIndex, quadrant := cornerQuadrant } : Figure18Site),
    by
      rw [ofFlatRoles_flatRoleAt_corner flat hflat cornerIndex cornerQuadrant hunique]
      rfl⟩

/--
Role assignment generated from a finite list of active Figure 18 sites and a
distinguished corner site.

The corner test comes first, so including the corner in `activeSites` is
harmless.
-/
def roleOfActiveSites
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    CellRole :=
  if site = cornerSite then CellRole.corner
  else if site ∈ activeSites then CellRole.active
  else CellRole.inactive

@[simp]
theorem roleOfActiveSites_corner
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    roleOfActiveSites activeSites cornerSite cornerSite = CellRole.corner := by
  simp [roleOfActiveSites]

theorem roleOfActiveSites_of_mem_of_ne
    {activeSites : List Figure18Site} {cornerSite site : Figure18Site}
    (hmem : site ∈ activeSites) (hne : site ≠ cornerSite) :
    roleOfActiveSites activeSites cornerSite site = CellRole.active := by
  simp [roleOfActiveSites, hne, hmem]

theorem roleOfActiveSites_of_not_mem_of_ne
    {activeSites : List Figure18Site} {cornerSite site : Figure18Site}
    (hmem : site ∉ activeSites) (hne : site ≠ cornerSite) :
    roleOfActiveSites activeSites cornerSite site = CellRole.inactive := by
  simp [roleOfActiveSites, hne, hmem]

theorem roleOfActiveSites_eq_corner_iff
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    roleOfActiveSites activeSites cornerSite site = CellRole.corner ↔
      site = cornerSite := by
  by_cases hcorner : site = cornerSite
  · subst hcorner
    simp [roleOfActiveSites]
  · by_cases hmem : site ∈ activeSites
    · simp [roleOfActiveSites_of_mem_of_ne hmem hcorner, hcorner]
    · simp [roleOfActiveSites_of_not_mem_of_ne hmem hcorner, hcorner]

theorem isActive_roleOfActiveSites_iff
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    CellRole.isActive (roleOfActiveSites activeSites cornerSite site) = true ↔
      site = cornerSite ∨ site ∈ activeSites := by
  by_cases hcorner : site = cornerSite
  · subst hcorner
    simp
  · by_cases hmem : site ∈ activeSites
    · simp [roleOfActiveSites_of_mem_of_ne hmem hcorner, hmem,
        CellRole.isActive]
    · simp [roleOfActiveSites_of_not_mem_of_ne hmem hcorner, hcorner, hmem,
        CellRole.isActive]

/--
Flat 368-entry role transcription generated from a finite active-site list.

This is the intended concrete-data shape for the Figure 18 scaffold: transcribe
only the active sites and the distinguished corner, then let this definition
expand them into the flat role list consumed by `FlatRoleTable`.
-/
def flatRolesOfActiveSites
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    List CellRole :=
  List.ofFn fun k : Fin 368 =>
    roleOfActiveSites activeSites cornerSite (Figure18Site.siteOfFlatIndex k)

@[simp]
theorem flatRolesOfActiveSites_length
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    (flatRolesOfActiveSites activeSites cornerSite).length = 368 := by
  rw [flatRolesOfActiveSites]
  exact List.length_ofFn

theorem flatRoleAt_flatRolesOfActiveSites
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    flatRoleAt (flatRolesOfActiveSites activeSites cornerSite) site =
      roleOfActiveSites activeSites cornerSite site := by
  unfold flatRoleAt flatRolesOfActiveSites
  rw [List.getD_eq_getElem]
  · rw [List.getElem_ofFn]
    exact congrArg (roleOfActiveSites activeSites cornerSite)
      (Figure18Site.siteOfFlatIndex_flatIndex site)
  · rw [List.length_ofFn]
    exact site.flatIndex_lt

theorem mem_activeFlatSites_flatRolesOfActiveSites_iff
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    site ∈ activeFlatSites (flatRolesOfActiveSites activeSites cornerSite) ↔
      site = cornerSite ∨ site ∈ activeSites := by
  rw [mem_activeFlatSites, flatRoleAt_flatRolesOfActiveSites,
    isActive_roleOfActiveSites_iff]
  constructor
  · exact And.right
  · intro hsite
    exact ⟨Figure18Site.mem_all site, hsite⟩

theorem flatRolesOfActiveSites_uniqueCorner
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    fig13QuarterCornerPositionUniqueBool
      (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))
      cornerSite.index cornerSite.quadrant = true := by
  unfold fig13QuarterCornerPositionUniqueBool
  apply List.all_eq_true.2
  intro i hi
  apply List.all_eq_true.2
  intro q _hq
  have hiLt : i < 92 := List.mem_range.1 hi
  let fi : Fin 92 := ⟨i, hiLt⟩
  have hrow := fig13QuarterRoleRow_getElem?
    (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))
    (rowsOfFlatRoles_length (flatRolesOfActiveSites activeSites cornerSite)) fi
  change (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))[i]? =
    some (fig13QuarterRoleRow
      (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))
      (rowsOfFlatRoles_length (flatRolesOfActiveSites activeSites cornerSite))
      fi) at hrow
  rw [hrow]
  have hiff :
      (fig13QuarterRoleRow
          (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))
          (rowsOfFlatRoles_length
            (flatRolesOfActiveSites activeSites cornerSite)) fi).roleAt q =
          CellRole.corner ↔
        i = cornerSite.index.val ∧ q = cornerSite.quadrant := by
    rw [rowsOfFlatRoles_roleAt, flatRoleAt_flatRolesOfActiveSites,
      roleOfActiveSites_eq_corner_iff, Figure18Site.mk_eq_iff]
    constructor
    · rintro ⟨hindex, hquadrant⟩
      exact ⟨congrArg Fin.val hindex, hquadrant⟩
    · rintro ⟨hindex, hquadrant⟩
      exact ⟨Fin.ext hindex, hquadrant⟩
  have hdec :
      decide ((fig13QuarterRoleRow
          (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))
          (rowsOfFlatRoles_length
            (flatRolesOfActiveSites activeSites cornerSite)) fi).roleAt q =
          CellRole.corner) =
        decide (i = cornerSite.index.val ∧ q = cornerSite.quadrant) := by
    by_cases hleft :
        (fig13QuarterRoleRow
          (rowsOfFlatRoles (flatRolesOfActiveSites activeSites cornerSite))
          (rowsOfFlatRoles_length
            (flatRolesOfActiveSites activeSites cornerSite)) fi).roleAt q =
          CellRole.corner
    · have hright := hiff.1 hleft
      rw [decide_eq_true hleft, decide_eq_true hright]
    · have hright : ¬(i = cornerSite.index.val ∧ q = cornerSite.quadrant) := by
        intro hright
        exact hleft (hiff.2 hright)
      rw [decide_eq_false hleft, decide_eq_false hright]
  simp [hdec]

/--
First-class flat Figure 18 role transcription.

This is the intended finite-data container for the paper-derived 368-entry role
list. The `uniqueCorner` field is the mechanical checker that the declared
corner site is exactly the unique `corner` role in the flat transcription.
-/
structure FlatRoleTable where
  flat : List CellRole
  cornerIndex : Fin 92
  cornerQuadrant : Quadrant
  length_eq : flat.length = 368
  uniqueCorner :
    fig13QuarterCornerPositionUniqueBool
      (rowsOfFlatRoles flat) cornerIndex cornerQuadrant = true

namespace FlatRoleTable

def toRoleTable (table : FlatRoleTable) : Figure18RoleTable :=
  ofFlatRoles table.flat table.length_eq table.cornerIndex
    table.cornerQuadrant table.uniqueCorner

def cornerSite (table : FlatRoleTable) : Figure18Site where
  index := table.cornerIndex
  quadrant := table.cornerQuadrant

def activeSites (table : FlatRoleTable) : List Figure18Site :=
  activeFlatSites table.flat

def cornerSites (table : FlatRoleTable) : List Figure18Site :=
  cornerFlatSites table.flat

def ofActiveSites
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    FlatRoleTable where
  flat := flatRolesOfActiveSites activeSites cornerSite
  cornerIndex := cornerSite.index
  cornerQuadrant := cornerSite.quadrant
  length_eq := flatRolesOfActiveSites_length activeSites cornerSite
  uniqueCorner := flatRolesOfActiveSites_uniqueCorner activeSites cornerSite

set_option maxRecDepth 4096 in
theorem ofActiveSites_flat
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    (ofActiveSites activeSites cornerSite).flat =
      flatRolesOfActiveSites activeSites cornerSite :=
  rfl

set_option maxRecDepth 4096 in
theorem ofActiveSites_cornerSite
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    (ofActiveSites activeSites cornerSite).cornerSite = cornerSite := by
  rfl

@[simp]
theorem toRoleTable_roleRows (table : FlatRoleTable) :
    table.toRoleTable.roleRows = rowsOfFlatRoles table.flat :=
  rfl

@[simp]
theorem toRoleTable_cornerIndex (table : FlatRoleTable) :
    table.toRoleTable.cornerIndex = table.cornerIndex :=
  rfl

@[simp]
theorem toRoleTable_cornerQuadrant (table : FlatRoleTable) :
    table.toRoleTable.cornerQuadrant = table.cornerQuadrant :=
  rfl

@[simp]
theorem toRoleTable_cornerSite (table : FlatRoleTable) :
    table.toRoleTable.cornerSite = table.cornerSite :=
  rfl

theorem roleAtSite_eq_flatRoleAt
    (table : FlatRoleTable) (site : Figure18Site) :
    table.toRoleTable.roleAtSite site = flatRoleAt table.flat site :=
  ofFlatRoles_roleAtSite table.flat table.length_eq table.cornerIndex
    table.cornerQuadrant table.uniqueCorner site

theorem flatRoleAt_corner_iff
    (table : FlatRoleTable) (site : Figure18Site) :
    flatRoleAt table.flat site = CellRole.corner ↔ site = table.cornerSite :=
  ofFlatRoles_flatRoleAt_corner_iff table.flat table.length_eq
    table.cornerIndex table.cornerQuadrant table.uniqueCorner site

theorem isCorner_flatRoleAt_iff
    (table : FlatRoleTable) (site : Figure18Site) :
    CellRole.isCorner (flatRoleAt table.flat site) = true ↔
      site = table.cornerSite :=
  ofFlatRoles_isCorner_flatRoleAt_iff table.flat table.length_eq
    table.cornerIndex table.cornerQuadrant table.uniqueCorner site

theorem mem_cornerSites_iff
    (table : FlatRoleTable) (site : Figure18Site) :
    site ∈ table.cornerSites ↔ site = table.cornerSite :=
  mem_cornerFlatSites_ofFlatRoles_iff table.flat table.length_eq
    table.cornerIndex table.cornerQuadrant table.uniqueCorner site

theorem mem_activeSites_iff
    (table : FlatRoleTable) (site : Figure18Site) :
    site ∈ table.activeSites ↔
      site ∈ Figure18Site.all ∧
        CellRole.isActive (table.toRoleTable.roleAtSite site) = true := by
  rw [FlatRoleTable.activeSites, mem_activeFlatSites,
    table.roleAtSite_eq_flatRoleAt]

theorem isActive_toRoleTable_of_mem_activeSites
    (table : FlatRoleTable) {site : Figure18Site}
    (hmem : site ∈ table.activeSites) :
    CellRole.isActive (table.toRoleTable.roleAtSite site) = true :=
  (table.mem_activeSites_iff site).1 hmem |>.2

theorem corner_mem_activeSites (table : FlatRoleTable) :
    table.cornerSite ∈ table.activeSites :=
  corner_mem_activeFlatSites_ofFlatRoles table.flat table.length_eq
    table.cornerIndex table.cornerQuadrant table.uniqueCorner

theorem ofActiveSites_roleAtSite
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    (ofActiveSites activeSites cornerSite).toRoleTable.roleAtSite site =
      roleOfActiveSites activeSites cornerSite site := by
  rw [roleAtSite_eq_flatRoleAt, ofActiveSites_flat,
    flatRoleAt_flatRolesOfActiveSites activeSites cornerSite site]

theorem mem_ofActiveSites_activeSites_iff
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    site ∈ (ofActiveSites activeSites cornerSite).activeSites ↔
      site = cornerSite ∨ site ∈ activeSites := by
  rw [FlatRoleTable.activeSites, ofActiveSites_flat,
    mem_activeFlatSites_flatRolesOfActiveSites_iff]

theorem mem_ofActiveSites_activeSites_of_mem
    {activeSites : List Figure18Site} {cornerSite site : Figure18Site}
    (hmem : site ∈ activeSites) :
    site ∈ (ofActiveSites activeSites cornerSite).activeSites := by
  exact (mem_ofActiveSites_activeSites_iff
    activeSites cornerSite site).2 (Or.inr hmem)

theorem corner_mem_ofActiveSites_activeSites
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    cornerSite ∈ (ofActiveSites activeSites cornerSite).activeSites := by
  exact (mem_ofActiveSites_activeSites_iff
    activeSites cornerSite cornerSite).2 (Or.inl rfl)

end FlatRoleTable

/--
Smoke-test data for the finite Figure 18 table checker.

This is deliberately not the Ollinger/Robinson scaffold interpretation: it marks
only one quadrant as `corner` and leaves every other quadrant inactive.  Its role
is to exercise the finite `Figure18RoleTable` path with concrete data before the
paper-derived role table is transcribed.
-/
def smokeRoleRows : List TileQuarterRoles :=
  TileQuarterRoles.ofQuadrants
      CellRole.corner CellRole.inactive CellRole.inactive CellRole.inactive ::
    List.replicate 91 TileQuarterRoles.inactive

@[simp]
theorem smokeRoleRows_length : smokeRoleRows.length = 92 := by
  decide

def smokeCornerIndex : Fin 92 :=
  ⟨0, by decide⟩

def smokeCornerQuadrant : Quadrant :=
  Quadrant.southwest

def smokeCornerSite : Figure18Site where
  index := smokeCornerIndex
  quadrant := smokeCornerQuadrant

def smokeActiveSiteSpecs : List (Nat × Quadrant) :=
  []

def smokeActiveSiteData : Figure18Site.CheckedNatSpecs where
  specs := smokeActiveSiteSpecs
  valid := rfl

def smokeActiveSites : List Figure18Site :=
  smokeActiveSiteData.sites

theorem smokeActiveSites_length :
    smokeActiveSites.length = smokeActiveSiteSpecs.length :=
  smokeActiveSiteData.sites_length

theorem smokeUniqueCorner :
    fig13QuarterCornerPositionUniqueBool
      smokeRoleRows smokeCornerIndex smokeCornerQuadrant = true := by
  decide

/--
Concrete finite smoke table for the checker.  It is useful for regression
testing the finite transcription pipeline, but it has no geometric certificate.
-/
def smoke : Figure18RoleTable where
  roleRows := smokeRoleRows
  cornerIndex := smokeCornerIndex
  cornerQuadrant := smokeCornerQuadrant
  length_eq := smokeRoleRows_length
  uniqueCorner := smokeUniqueCorner

def smokeFlat : FlatRoleTable :=
  FlatRoleTable.ofActiveSites smokeActiveSites smokeCornerSite

@[simp]
theorem smoke_roleAt_corner :
    smoke.roleAt smokeCornerIndex smokeCornerQuadrant = CellRole.corner :=
  smoke.roleAt_corner

theorem smoke_presentation_tiles :
    smoke.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  smoke.presentation_tiles

@[simp]
theorem smoke_cornerSite :
    smoke.cornerSite = smokeCornerSite :=
  rfl

@[simp]
theorem smokeFlat_cornerSite :
    smokeFlat.cornerSite = smokeCornerSite :=
  rfl

theorem smoke_flatRoleAt_corner :
    flatRoleAt smokeFlat.flat smoke.cornerSite = CellRole.corner := by
  rw [smoke_cornerSite, smokeFlat, FlatRoleTable.ofActiveSites_flat,
    flatRoleAt_flatRolesOfActiveSites]
  rfl

theorem smoke_flatRoleAt_second_site :
    flatRoleAt smokeFlat.flat
      ({ index := ⟨0, by decide⟩, quadrant := Quadrant.southeast } : Figure18Site) =
        CellRole.inactive := by
  rw [smokeFlat, FlatRoleTable.ofActiveSites_flat,
    flatRoleAt_flatRolesOfActiveSites]
  rfl

theorem smokeFlat_corner_mem_activeSites :
    smokeFlat.cornerSite ∈ smokeFlat.activeSites :=
  FlatRoleTable.corner_mem_ofActiveSites_activeSites smokeActiveSites smokeCornerSite

end Figure18RoleTable

/-- The concrete Figure 18 scaffold tile set: quarters of the Figure 13 tiles. -/
def figure18ScaffoldTiles : TileSet :=
  TileSubdivision.subdivideTileSet fig13Tiles

theorem figure18ScaffoldTiles_nodup : figure18ScaffoldTiles.Nodup := by
  exact TileSubdivision.subdivideTileSet_nodup_of_nodup fig13Tiles_nodup

theorem mem_figure18ScaffoldTiles_iff {tile : WangTile} :
    tile ∈ figure18ScaffoldTiles ↔
      tile ∈ Figure18Site.all.map Figure18Site.tile := by
  constructor
  · intro htile
    rw [figure18ScaffoldTiles, TileSubdivision.subdivideTileSet,
      List.mem_flatMap] at htile
    rcases htile with ⟨raw, hraw, hsub⟩
    rcases List.mem_iff_get.1 hraw with ⟨k, hrawk⟩
    have hk : k.val < 92 := by
      simpa [fig13Tiles_length] using k.isLt
    let i : Fin 92 := ⟨k.val, hk⟩
    have hraw_eq : raw = fig13Tile i := by
      unfold fig13Tile i
      simpa [List.get_eq_getElem] using hrawk.symm
    rw [TileSubdivision.subdivideTile] at hsub
    rcases List.mem_map.1 hsub with ⟨q, hq, htileq⟩
    exact List.mem_map.2
      ⟨({ index := i, quadrant := q } : Figure18Site),
        Figure18Site.mem_all _, by
          simpa [Figure18Site.tile, fig13QuarterTile, hraw_eq] using htileq⟩
  · intro htile
    rcases List.mem_map.1 htile with ⟨site, _hsite, htileSite⟩
    rw [figure18ScaffoldTiles, TileSubdivision.subdivideTileSet,
      List.mem_flatMap]
    refine ⟨site.rawTile, ?_, ?_⟩
    · unfold Figure18Site.rawTile fig13Tile
      exact List.getElem_mem _
    · rw [TileSubdivision.subdivideTile]
      exact List.mem_map.2
        ⟨site.quadrant, Quadrant.mem_all site.quadrant, by
          simpa [Figure18Site.tile_eq_subdivideTileAt_rawTile] using htileSite⟩

theorem mem_figure18ScaffoldTiles_of_site (site : Figure18Site) :
    site.tile ∈ figure18ScaffoldTiles :=
  mem_figure18ScaffoldTiles_iff.2 site.tile_mem_all_tiles

theorem exists_site_of_mem_figure18ScaffoldTiles {tile : WangTile}
    (htile : tile ∈ figure18ScaffoldTiles) :
    ∃ site : Figure18Site, site ∈ Figure18Site.all ∧ site.tile = tile := by
  rcases List.mem_map.1 (mem_figure18ScaffoldTiles_iff.1 htile) with
    ⟨site, hsite, htileSite⟩
  exact ⟨site, hsite, htileSite⟩

/--
Role-table-indexed active square window for the Figure 18 scaffold.

This is a concrete local target for the free-square part of the
Ollinger/Robinson argument: instead of producing arbitrary scaffold tiles, the
geometric proof may identify each cell by a raw Figure 13 tile index and one of
its four Figure 18 quadrants.  The conversion below turns this indexed witness
into the presentation-level window expected by the abstract scaffold interface.
-/
structure Figure18IndexedActiveCornerWindow
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  origin : Int × Int
  indexRect : Fin n → Fin n → Fin 92
  quadrantRect : Fin n → Fin n → Quadrant
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (table.roleAt (indexRect i j) (quadrantRect i j)) = true
  corner :
    table.roleAt (indexRect ⟨0, hn⟩ ⟨0, hn⟩)
      (quadrantRect ⟨0, hn⟩ ⟨0, hn⟩) = CellRole.corner
  product : ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
    WangTile.product (fig13QuarterTile (indexRect i j) (quadrantRect i j)) payload =
      (x (origin.1 + Int.ofNat i.val, origin.2 + Int.ofNat j.val)).1

namespace Figure18IndexedActiveCornerWindow

def baseRect
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn) :
    Rectangle n n :=
  fun i j => fig13QuarterTile (window.indexRect i j) (window.quadrantRect i j)

theorem baseRect_eq
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn)
    (i : Fin n) (j : Fin n) :
    window.baseRect i j =
      fig13QuarterTile (window.indexRect i j) (window.quadrantRect i j) :=
  rfl

def toPresentedActiveCornerWindow
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedActiveCornerWindow table x n hn) :
    PresentedActiveCornerWindow table.presentation x n hn where
  origin := window.origin
  baseRect := window.baseRect
  mem := by
    intro i j
    exact table.presentation_mem_fig13QuarterTile
      (window.indexRect i j) (window.quadrantRect i j)
  active := by
    intro i j
    rw [window.baseRect_eq i j, table.presentation_role_fig13QuarterTile]
    exact window.active i j
  corner := by
    rw [window.baseRect_eq ⟨0, hn⟩ ⟨0, hn⟩,
      table.presentation_role_fig13QuarterTile]
    exact window.corner
  product := by
    intro i j
    simpa [baseRect_eq] using window.product i j

end Figure18IndexedActiveCornerWindow

/--
Every combined plane tiling contains arbitrarily large active-corner windows
whose scaffold cells are identified by Figure 13 indices and Figure 18
quadrants.
-/
def HasFigure18IndexedActiveCornerWindows (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18IndexedActiveCornerWindow table x n hn)

theorem hasPresentedRecognizableFreeSquares_of_figure18Indexed
    {table : Figure18RoleTable}
    (hwindow : HasFigure18IndexedActiveCornerWindows table) :
    HasPresentedRecognizableFreeSquares table.presentation := by
  intro T seed x hx n hn
  rcases hwindow x hx n hn with ⟨window⟩
  exact ⟨window.toPresentedActiveCornerWindow⟩

theorem hasRecognizableFreeSquares_of_figure18Indexed
    {table : Figure18RoleTable}
    (hwindow : HasFigure18IndexedActiveCornerWindows table) :
    HasRecognizableFreeSquares table.presentation.toScaffold := by
  exact hasRecognizableFreeSquares_of_presented
    (hasPresentedRecognizableFreeSquares_of_figure18Indexed hwindow)
    (by
      simpa [Figure18RoleTable.presentation] using
        table.finiteCheckedTranscription.sanityProp.corner_unique)

theorem forcesActiveCornerSquares_of_figure18Indexed
    {table : Figure18RoleTable}
    (hwindow : HasFigure18IndexedActiveCornerWindows table) :
    ForcesActiveCornerSquares table.presentation.toScaffold := by
  exact forcesActiveCornerSquares_of_planeTilingForcesActiveCornerWindows
    (planeTilingForcesActiveCornerWindows_of_hasActiveCornerBaseWindows
      (planeTilingHasActiveCornerBaseWindows_of_hasRecognizableFreeSquares
        (hasRecognizableFreeSquares_of_figure18Indexed hwindow)))

theorem forcesFixedCornerSquares_of_figure18Indexed
    {table : Figure18RoleTable}
    (hwindow : HasFigure18IndexedActiveCornerWindows table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_forcesActiveCornerSquares
    (forcesActiveCornerSquares_of_figure18Indexed hwindow)

/--
Payload square extracted from the routed Figure 18 free coordinates.

The paper's free square is described by selected horizontal coordinates `H` and
vertical coordinates `V` inside a scaffold square.  The payload cells need not be
a contiguous rectangle of scaffold cells; the missing adjacencies are routed
through obstructed rows and columns.  This structure records the resulting
payload rectangle together with the scaffold sites from which it is read.
-/
structure Figure18RoutedFixedCornerSquare
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  baseRect : Rectangle n n
  payloadRect : Rectangle n n
  mem : ∀ i : Fin n, ∀ j : Fin n, baseRect i j ∈ table.presentation.tiles
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (table.presentation.role (baseRect i j)) = true
  cornerRole :
    table.presentation.role (baseRect ⟨0, hn⟩ ⟨0, hn⟩) = CellRole.corner
  product : ∀ i : Fin n, ∀ j : Fin n,
    WangTile.product (baseRect i j) (payloadRect i j) =
      (x (horizontalCoord i, verticalCoord j)).1
  hmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j)
  vmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩)

namespace Figure18RoutedFixedCornerSquare

theorem payload_mem
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18RoutedFixedCornerSquare table x n hn)
    (i : Fin n) (j : Fin n) :
    window.payloadRect i j ∈ T := by
  apply payload_mem_of_active_product_mem_combineWithScaffold
    (S := table.presentation.toScaffold)
    (base := window.baseRect i j)
  · exact window.active i j
  · rw [window.product i j]
    exact (x (window.horizontalCoord i, window.verticalCoord j)).2

theorem base_corner
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18RoutedFixedCornerSquare table x n hn) :
    window.baseRect ⟨0, hn⟩ ⟨0, hn⟩ = table.presentation.toScaffold.corner := by
  change window.baseRect ⟨0, hn⟩ ⟨0, hn⟩ = table.presentation.cornerTile
  exact table.finiteCheckedTranscription.sanityProp.corner_unique
    (window.baseRect ⟨0, hn⟩ ⟨0, hn⟩)
    (window.mem ⟨0, hn⟩ ⟨0, hn⟩)
    window.cornerRole

theorem payload_corner_of_product
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18RoutedFixedCornerSquare table x n hn) :
    window.payloadRect ⟨0, hn⟩ ⟨0, hn⟩ = seed := by
  apply payload_eq_seed_of_active_corner_product_mem_combineWithScaffold
    (S := table.presentation.toScaffold)
    (base := window.baseRect ⟨0, hn⟩ ⟨0, hn⟩)
  · exact window.active ⟨0, hn⟩ ⟨0, hn⟩
  · exact window.base_corner
  · rw [window.product ⟨0, hn⟩ ⟨0, hn⟩]
    exact (x (window.horizontalCoord ⟨0, hn⟩,
      window.verticalCoord ⟨0, hn⟩)).2

theorem payload_valid
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18RoutedFixedCornerSquare table x n hn) :
    ValidRectangle T window.payloadRect := by
  constructor
  · intro i j
    exact window.payload_mem i j
  constructor
  · exact window.hmatch
  · exact window.vmatch

theorem tileable
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18RoutedFixedCornerSquare table x n hn) :
    TileableFixedCornerSquare T seed n :=
  ⟨hn, window.payloadRect, window.payload_valid, window.payload_corner_of_product⟩

/--
Build a routed fixed-corner square from the geometric routing data.

The local Figure 18 proof should supply the selected coordinates, scaffold
sites, payload decoding, and routed horizontal/vertical payload matches. Payload
membership and the lower-left seed condition are then consequences of the
combined scaffold tileset and the corner-role uniqueness check.
-/
def ofRoutedMatches
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} (hn : 0 < n)
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (baseRect payloadRect : Rectangle n n)
    (mem : ∀ i : Fin n, ∀ j : Fin n, baseRect i j ∈ table.presentation.tiles)
    (active : ∀ i : Fin n, ∀ j : Fin n,
      CellRole.isActive (table.presentation.role (baseRect i j)) = true)
    (cornerRole :
      table.presentation.role (baseRect ⟨0, hn⟩ ⟨0, hn⟩) = CellRole.corner)
    (product : ∀ i : Fin n, ∀ j : Fin n,
      WangTile.product (baseRect i j) (payloadRect i j) =
        (x (horizontalCoord i, verticalCoord j)).1)
    (hmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j))
    (vmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩)) :
    Figure18RoutedFixedCornerSquare table x n hn where
  horizontalCoord := horizontalCoord
  verticalCoord := verticalCoord
  baseRect := baseRect
  payloadRect := payloadRect
  mem := mem
  active := active
  cornerRole := cornerRole
  product := product
  hmatch := hmatch
  vmatch := vmatch

end Figure18RoutedFixedCornerSquare

/--
Indexed version of `Figure18RoutedFixedCornerSquare`.

This is the finite-data-facing target for the Figure 18 geometric argument:
each scaffold site is identified by its raw Figure 13 tile index and quadrant,
so role facts can be discharged by lookup in the concrete role table.
-/
structure Figure18IndexedRoutedFixedCornerSquare
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  siteRect : Fin n → Fin n → Figure18Site
  payloadRect : Rectangle n n
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerRole :
    table.roleAtSite (siteRect ⟨0, hn⟩ ⟨0, hn⟩) = CellRole.corner
  product : ∀ i : Fin n, ∀ j : Fin n,
    WangTile.product (siteRect i j).tile (payloadRect i j) =
      (x (horizontalCoord i, verticalCoord j)).1
  hmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j)
  vmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩)

namespace Figure18IndexedRoutedFixedCornerSquare

def baseRect
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    Rectangle n n :=
  fun i j => (window.siteRect i j).tile

theorem baseRect_eq
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (i : Fin n) (j : Fin n) :
    window.baseRect i j = (window.siteRect i j).tile :=
  rfl

theorem corner_site
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    window.siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite :=
  (table.roleAtSite_corner_iff (window.siteRect ⟨0, hn⟩ ⟨0, hn⟩)).1
    window.cornerRole

theorem base_corner
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    window.baseRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerTile := by
  rw [window.baseRect_eq, window.corner_site]
  exact table.cornerTile_eq_cornerSite_tile.symm

/--
Reindex a routed fixed-corner square by decoding each scaffold base tile back
to its concrete Figure 18 site.
-/
def ofRoutedFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18RoutedFixedCornerSquare table x n hn) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  siteRect := fun i j =>
    table.siteOfPresentationTile (window.baseRect i j) (window.mem i j)
  payloadRect := window.payloadRect
  active := by
    intro i j
    rw [← table.presentation_active_siteOfPresentationTile (window.mem i j)]
    exact window.active i j
  cornerRole := by
    rw [← table.presentation_role_siteOfPresentationTile
      (window.mem ⟨0, hn⟩ ⟨0, hn⟩)]
    exact window.cornerRole
  product := by
    intro i j
    rw [table.siteOfPresentationTile_tile (window.mem i j)]
    exact window.product i j
  hmatch := window.hmatch
  vmatch := window.vmatch

def toRoutedFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    Figure18RoutedFixedCornerSquare table x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  baseRect := window.baseRect
  payloadRect := window.payloadRect
  mem := by
    intro i j
    exact table.presentation_mem_site (window.siteRect i j)
  active := by
    intro i j
    rw [window.baseRect_eq i j, table.presentation_role_site]
    exact window.active i j
  cornerRole := by
    rw [window.baseRect_eq ⟨0, hn⟩ ⟨0, hn⟩,
      table.presentation_role_site]
    exact window.cornerRole
  product := by
    intro i j
    simpa [baseRect_eq] using window.product i j
  hmatch := window.hmatch
  vmatch := window.vmatch

theorem payload_mem
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn)
    (i : Fin n) (j : Fin n) :
    window.payloadRect i j ∈ T :=
  window.toRoutedFixedCornerSquare.payload_mem i j

theorem payload_corner_of_product
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    window.payloadRect ⟨0, hn⟩ ⟨0, hn⟩ = seed :=
  window.toRoutedFixedCornerSquare.payload_corner_of_product

theorem payload_valid
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    ValidRectangle T window.payloadRect :=
  window.toRoutedFixedCornerSquare.payload_valid

theorem tileable
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18IndexedRoutedFixedCornerSquare table x n hn) :
    TileableFixedCornerSquare T seed n :=
  window.toRoutedFixedCornerSquare.tileable

theorem payload_hMatches_of_validPlaneTiling
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x)
    {p : Int × Int} {leftSite rightSite : Figure18Site}
    {payloadLeft payloadRight : WangTile}
    (hcompat : Figure18Site.hCompatible leftSite rightSite = true)
    (hleft :
      WangTile.product leftSite.tile payloadLeft = (x p).1)
    (hright :
      WangTile.product rightSite.tile payloadRight = (x (p.1 + 1, p.2)).1) :
    WangTile.HMatches payloadLeft payloadRight := by
  have _hbase : WangTile.HMatches leftSite.tile rightSite.tile :=
    Figure18Site.hMatches_of_hCompatible hcompat
  have hproduct : WangTile.HMatches
      (WangTile.product leftSite.tile payloadLeft)
      (WangTile.product rightSite.tile payloadRight) := by
    simpa [← hleft, ← hright] using hx.1 p
  exact (WangTile.HMatches_product_iff
    leftSite.tile payloadLeft rightSite.tile payloadRight).1 hproduct |>.2

theorem payload_vMatches_of_validPlaneTiling
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x)
    {p : Int × Int} {lowerSite upperSite : Figure18Site}
    {payloadLower payloadUpper : WangTile}
    (hcompat : Figure18Site.vCompatible lowerSite upperSite = true)
    (hlower :
      WangTile.product lowerSite.tile payloadLower = (x p).1)
    (hupper :
      WangTile.product upperSite.tile payloadUpper = (x (p.1, p.2 + 1)).1) :
    WangTile.VMatches payloadLower payloadUpper := by
  have _hbase : WangTile.VMatches lowerSite.tile upperSite.tile :=
    Figure18Site.vMatches_of_vCompatible hcompat
  have hproduct : WangTile.VMatches
      (WangTile.product lowerSite.tile payloadLower)
      (WangTile.product upperSite.tile payloadUpper) := by
    simpa [← hlower, ← hupper] using hx.2 p
  exact (WangTile.VMatches_product_iff
    lowerSite.tile payloadLower upperSite.tile payloadUpper).1 hproduct |>.2

/--
Build an indexed routed fixed-corner square when the geometric proof identifies
the lower-left site as the table's distinguished corner site directly.
-/
def ofSiteMatches
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} (hn : 0 < n)
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (siteRect : Fin n → Fin n → Figure18Site)
    (payloadRect : Rectangle n n)
    (active : ∀ i : Fin n, ∀ j : Fin n,
      CellRole.isActive (table.roleAtSite (siteRect i j)) = true)
    (cornerSite :
      siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite)
    (product : ∀ i : Fin n, ∀ j : Fin n,
      WangTile.product (siteRect i j).tile (payloadRect i j) =
        (x (horizontalCoord i, verticalCoord j)).1)
    (hmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j))
    (vmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩)) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn where
  horizontalCoord := horizontalCoord
  verticalCoord := verticalCoord
  siteRect := siteRect
  payloadRect := payloadRect
  active := active
  cornerRole := by
    rw [cornerSite]
    exact table.roleAtSite_corner
  product := product
  hmatch := hmatch
  vmatch := vmatch

/--
Build an indexed routed fixed-corner square from adjacent selected coordinates.

Here the geometric proof supplies compatible Figure 18 base sites at adjacent
selected plane coordinates. The payload horizontal and vertical matches are then
forced by validity of the combined tiling and the product decomposition.
-/
def ofAdjacentCompatibleSites
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x)
    {n : Nat} (hn : 0 < n)
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (siteRect : Fin n → Fin n → Figure18Site)
    (payloadRect : Rectangle n n)
    (horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
      horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1)
    (verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1)
    (hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true)
    (vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)
    (active : ∀ i : Fin n, ∀ j : Fin n,
      CellRole.isActive (table.roleAtSite (siteRect i j)) = true)
    (cornerSite :
      siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite)
    (product : ∀ i : Fin n, ∀ j : Fin n,
      WangTile.product (siteRect i j).tile (payloadRect i j) =
        (x (horizontalCoord i, verticalCoord j)).1) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn :=
  ofSiteMatches hn horizontalCoord verticalCoord siteRect payloadRect
    active cornerSite product
    (by
      intro i j hi
      exact payload_hMatches_of_validPlaneTiling hx
        (p := (horizontalCoord i, verticalCoord j))
        (hcompatible i j hi)
        (product i j)
        (by
          simpa [horizontalCoord_succ i hi] using
            product ⟨i.val + 1, hi⟩ j))
    (by
      intro i j hj
      exact payload_vMatches_of_validPlaneTiling hx
        (p := (horizontalCoord i, verticalCoord j))
        (vcompatible i j hj)
        (product i j)
        (by
          simpa [verticalCoord_succ j hj] using
            product i ⟨j.val + 1, hj⟩))

end Figure18IndexedRoutedFixedCornerSquare

/--
Adjacent-compatible selected-coordinate square for the Figure 18 scaffold.

This is the scaffold-instantiation target closest to the local geometric
argument: identify selected horizontal and vertical coordinates, decode the
Figure 18 site at each selected crossing, prove adjacent selected coordinates
are actual neighbors in the plane, and verify Figure 18 site compatibility.
Payload edge matches are deliberately not fields; they are derived from these
facts and the validity of the combined tiling.
-/
structure Figure18AdjacentCompatibleFixedCornerSquare
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  siteRect : Fin n → Fin n → Figure18Site
  payloadRect : Rectangle n n
  horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1
  verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1
  hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    Figure18Site.hCompatible (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true
  vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    Figure18Site.vCompatible (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite
  product : ∀ i : Fin n, ∀ j : Fin n,
    WangTile.product (siteRect i j).tile (payloadRect i j) =
      (x (horizontalCoord i, verticalCoord j)).1

/--
Adjacent-compatible selected-coordinate square with pointwise payload
decompositions instead of a preassembled payload rectangle.

This is the most direct local extraction target from a combined tiling: for
each selected coordinate, identify the Figure 18 base site and show that the
combined tile has some payload component over that site.  The payload rectangle
is chosen later when converting to `Figure18AdjacentCompatibleFixedCornerSquare`.
-/
structure Figure18AdjacentProductWitnessFixedCornerSquare
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  siteRect : Fin n → Fin n → Figure18Site
  horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1
  verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1
  hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    Figure18Site.hCompatible (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true
  vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    Figure18Site.vCompatible (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite
  productWitness : ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
    WangTile.product (siteRect i j).tile payload =
      (x (horizontalCoord i, verticalCoord j)).1

namespace Figure18AdjacentCompatibleFixedCornerSquare

/--
Build an adjacent-compatible fixed-corner square from pointwise payload
decompositions.

This is the shape a geometric scaffold proof naturally gets after selecting
the relevant Figure 18 sites in a combined tiling: each selected site has some
payload component.  The constructor packages those witnesses into the
`payloadRect` field expected by the routed-square interface.
-/
noncomputable def ofProductWitnesses
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} (hn : 0 < n)
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (siteRect : Fin n → Fin n → Figure18Site)
    (horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
      horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1)
    (verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1)
    (hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true)
    (vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)
    (active : ∀ i : Fin n, ∀ j : Fin n,
      CellRole.isActive (table.roleAtSite (siteRect i j)) = true)
    (cornerSite :
      siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite)
    (productWitness : ∀ i : Fin n, ∀ j : Fin n, ∃ payload : WangTile,
      WangTile.product (siteRect i j).tile payload =
        (x (horizontalCoord i, verticalCoord j)).1) :
    Figure18AdjacentCompatibleFixedCornerSquare table x n hn where
  horizontalCoord := horizontalCoord
  verticalCoord := verticalCoord
  siteRect := siteRect
  payloadRect := fun i j => Classical.choose (productWitness i j)
  horizontalCoord_succ := horizontalCoord_succ
  verticalCoord_succ := verticalCoord_succ
  hcompatible := hcompatible
  vcompatible := vcompatible
  active := active
  cornerSite := cornerSite
  product := by
    intro i j
    exact Classical.choose_spec (productWitness i j)

def toIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18AdjacentCompatibleFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn :=
  Figure18IndexedRoutedFixedCornerSquare.ofAdjacentCompatibleSites hx hn
    window.horizontalCoord window.verticalCoord window.siteRect window.payloadRect
    window.horizontalCoord_succ window.verticalCoord_succ
    window.hcompatible window.vcompatible window.active
    window.cornerSite window.product

theorem tileable
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18AdjacentCompatibleFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x) :
    TileableFixedCornerSquare T seed n :=
  (window.toIndexedRoutedFixedCornerSquare hx).tileable

end Figure18AdjacentCompatibleFixedCornerSquare

/--
Every combined plane tiling contains arbitrarily large routed payload squares
with the requested lower-left seed.
-/
def HasFigure18RoutedFixedCornerSquares (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18RoutedFixedCornerSquare table x n hn)

/--
Finite-coordinate form of `HasFigure18RoutedFixedCornerSquares`.

This is usually the most convenient target for a concrete Figure 18 proof: it
avoids arbitrary presentation tiles by naming each routed scaffold cell with a
Figure 13 index and quadrant.
-/
def HasFigure18IndexedRoutedFixedCornerSquares
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18IndexedRoutedFixedCornerSquare table x n hn)

/--
Finite selected-coordinate form of `HasFigure18IndexedRoutedFixedCornerSquares`.

This is the preferred target for the local Figure 18 scaffold proof when the
selected coordinates are adjacent in the ambient plane. It avoids asking the
geometric proof to provide payload edge matches directly.
-/
def HasFigure18AdjacentCompatibleFixedCornerSquares
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18AdjacentCompatibleFixedCornerSquare table x n hn)

/--
Pointwise-payload-witness form of `HasFigure18AdjacentCompatibleFixedCornerSquares`.

This is the intended statement for the local Figure 18 geometric extraction
when payload components are obtained cell by cell from membership in the
combined tileset.
-/
def HasFigure18AdjacentProductWitnessFixedCornerSquares
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18AdjacentProductWitnessFixedCornerSquare table x n hn)

/--
Decoded-site form of `HasFigure18AdjacentProductWitnessFixedCornerSquares`.

This is the intended finite geometric target for the concrete Figure 18
scaffold.  The selected combined-tiling coordinates are checked by decoding
their scaffold component to a `Figure18Site`; the payload witness then follows
from membership in the combined tileset.
-/
def HasFigure18DecodedSiteFixedCornerSquares
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ horizontalCoord : Fin n → Int, ∃ verticalCoord : Fin n → Int,
          (∀ i : Fin n, ∀ hi : i.val + 1 < n,
            horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1) ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n,
            verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1) ∧
          (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
            Figure18Site.hCompatible
              (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
              (table.combinedSite
                (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) =
              true) ∧
          (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
            Figure18Site.vCompatible
              (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
              (table.combinedSite
                (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) =
              true) ∧
          (∀ i : Fin n, ∀ j : Fin n,
            CellRole.isActive
              (table.roleAtSite
                (table.combinedSite (x (horizontalCoord i, verticalCoord j)))) =
              true) ∧
          table.combinedSite
              (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
            table.cornerSite

/--
Flat-table decoded-site form of the Figure 18 square obligation.

This is the finite-data target for a concrete 368-entry role transcription:
the geometric proof only has to show that selected decoded scaffold sites lie
in the flat table's active-site list, with the lower-left site equal to the
flat table's distinguished corner.  Role lookup is handled by the conversion to
`HasFigure18DecodedSiteFixedCornerSquares`.
-/
def HasFigure18FlatDecodedSiteFixedCornerSquares
    (table : Figure18RoleTable.FlatRoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int →
      TileIn (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)),
    ValidPlaneTiling
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ horizontalCoord : Fin n → Int, ∃ verticalCoord : Fin n → Int,
          (∀ i : Fin n, ∀ hi : i.val + 1 < n,
            horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1) ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n,
            verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1) ∧
          (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
            Figure18Site.hCompatible
              (table.toRoleTable.combinedSite
                (x (horizontalCoord i, verticalCoord j)))
              (table.toRoleTable.combinedSite
                (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) =
              true) ∧
          (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
            Figure18Site.vCompatible
              (table.toRoleTable.combinedSite
                (x (horizontalCoord i, verticalCoord j)))
              (table.toRoleTable.combinedSite
                (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) =
              true) ∧
          (∀ i : Fin n, ∀ j : Fin n,
            table.toRoleTable.combinedSite
              (x (horizontalCoord i, verticalCoord j)) ∈ table.activeSites) ∧
          table.toRoleTable.combinedSite
              (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
            table.cornerSite

/--
Flat active-site form of the Figure 18 square obligation.

This is the smallest current target for the geometric scaffold proof.  Once
the selected coordinates are adjacent in the ambient plane, the decoded
horizontal and vertical site compatibility follows from `ValidPlaneTiling`;
the concrete proof only has to identify active decoded sites and the
distinguished lower-left corner.
-/
def HasFigure18FlatActiveSiteFixedCornerSquares
    (table : Figure18RoleTable.FlatRoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int →
      TileIn (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)),
    ValidPlaneTiling
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ horizontalCoord : Fin n → Int, ∃ verticalCoord : Fin n → Int,
          (∀ i : Fin n, ∀ hi : i.val + 1 < n,
            horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1) ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n,
            verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1) ∧
          (∀ i : Fin n, ∀ j : Fin n,
            table.toRoleTable.combinedSite
              (x (horizontalCoord i, verticalCoord j)) ∈ table.activeSites) ∧
          table.toRoleTable.combinedSite
              (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
            table.cornerSite

/--
Listed active-site form for flat tables generated by
`Figure18RoleTable.FlatRoleTable.ofActiveSites`.

This is the intended proof target for a direct transcription of Figure 18:
the geometric proof names the finite list of usable quarter-sites and only has
to show that each selected decoded site is either the distinguished corner or
is in that list.  The conversion below turns this into the existing
`table.activeSites` obligation for the generated flat role table.
-/
def HasFigure18ListedActiveSiteFixedCornerSquares
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  let table := Figure18RoleTable.FlatRoleTable.ofActiveSites activeSites cornerSite
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int →
      TileIn (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)),
    ValidPlaneTiling
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        ∃ horizontalCoord : Fin n → Int, ∃ verticalCoord : Fin n → Int,
          (∀ i : Fin n, ∀ hi : i.val + 1 < n,
            horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1) ∧
          (∀ j : Fin n, ∀ hj : j.val + 1 < n,
            verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1) ∧
          (∀ i : Fin n, ∀ j : Fin n,
            table.toRoleTable.combinedSite
              (x (horizontalCoord i, verticalCoord j)) = cornerSite ∨
            table.toRoleTable.combinedSite
              (x (horizontalCoord i, verticalCoord j)) ∈ activeSites) ∧
          table.toRoleTable.combinedSite
              (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
            cornerSite

/--
Structured witness for one listed-active Figure 18 fixed-corner square.

This packages the free-subsquare data that Figure 18 supplies: adjacent
horizontal and vertical coordinates, every decoded quarter-site either equal to
the distinguished corner or belonging to the listed active sites, and the
lower-left decoded site equal to the corner.  The unstructured proposition
`HasFigure18ListedActiveSiteFixedCornerSquares` is kept as the public certificate
field; this structure is the Lean-friendly target for constructing one witness at
a time from the free-subsquare geometry.
-/
structure Figure18ListedActiveSiteFixedCornerSquare
    (table : Figure18RoleTable)
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) : Type where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1
  verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1
  listedActive : ∀ i : Fin n, ∀ j : Fin n,
    table.combinedSite
      (x (horizontalCoord i, verticalCoord j)) = cornerSite ∨
    table.combinedSite
      (x (horizontalCoord i, verticalCoord j)) ∈ activeSites
  corner : table.combinedSite
      (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
      cornerSite

namespace Figure18ListedActiveSiteFixedCornerSquare

theorem exists_witness
    {table : Figure18RoleTable}
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window :
      Figure18ListedActiveSiteFixedCornerSquare
        table activeSites cornerSite x n hn) :
    ∃ horizontalCoord : Fin n → Int, ∃ verticalCoord : Fin n → Int,
      (∀ i : Fin n, ∀ hi : i.val + 1 < n,
        horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1) ∧
      (∀ j : Fin n, ∀ hj : j.val + 1 < n,
        verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1) ∧
      (∀ i : Fin n, ∀ j : Fin n,
        table.combinedSite
          (x (horizontalCoord i, verticalCoord j)) = cornerSite ∨
        table.combinedSite
          (x (horizontalCoord i, verticalCoord j)) ∈ activeSites) ∧
      table.combinedSite
          (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
        cornerSite :=
  ⟨window.horizontalCoord, window.verticalCoord, window.horizontalCoord_succ,
    window.verticalCoord_succ, window.listedActive, window.corner⟩

end Figure18ListedActiveSiteFixedCornerSquare

/--
Structured form of `HasFigure18ListedActiveSiteFixedCornerSquares`.

This is often the more convenient proof target: after selecting the Figure 18
free-subsquare coordinates, construct one
`Figure18ListedActiveSiteFixedCornerSquare` witness for each `n`.
-/
def HasFigure18ListedActiveSiteFixedCornerSquareWindows
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18ListedActiveSiteFixedCornerSquare
          (Figure18RoleTable.FlatRoleTable.ofActiveSites
            activeSites cornerSite).toRoleTable
          activeSites cornerSite x n hn)

theorem hasFigure18ListedActiveSiteFixedCornerSquares_of_windows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSites cornerSite) :
    HasFigure18ListedActiveSiteFixedCornerSquares activeSites cornerSite := by
  intro T seed x hx n hn
  rcases hwindows x hx n hn with ⟨window⟩
  exact window.exists_witness

theorem hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_exists
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hlisted :
      HasFigure18ListedActiveSiteFixedCornerSquares activeSites cornerSite) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindows
      activeSites cornerSite := by
  intro T seed x hx n hn
  rcases hlisted x hx n hn with
    ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
      verticalCoord_succ, listedActive, corner⟩
  exact ⟨{
    horizontalCoord := horizontalCoord
    verticalCoord := verticalCoord
    horizontalCoord_succ := horizontalCoord_succ
    verticalCoord_succ := verticalCoord_succ
    listedActive := listedActive
    corner := corner
  }⟩

theorem hasFigure18FlatActiveSiteFixedCornerSquares_of_listedActiveSite
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hlisted :
      HasFigure18ListedActiveSiteFixedCornerSquares activeSites cornerSite) :
    HasFigure18FlatActiveSiteFixedCornerSquares
      (Figure18RoleTable.FlatRoleTable.ofActiveSites activeSites cornerSite) := by
  intro T seed x hx n hn
  rcases hlisted x hx n hn with
    ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
      verticalCoord_succ, listedActive, corner⟩
  refine ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
    verticalCoord_succ, ?_, ?_⟩
  · intro i j
    let table := Figure18RoleTable.FlatRoleTable.ofActiveSites activeSites cornerSite
    let site := table.toRoleTable.combinedSite
        (x (horizontalCoord i, verticalCoord j))
    exact (Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_iff
      activeSites cornerSite site).2 (listedActive i j)
  · exact corner

namespace Figure18AdjacentProductWitnessFixedCornerSquare

/--
Build a product-witness square directly from the Figure 18 sites decoded at the
selected combined-tiling coordinates.

This is the closest interface to the geometric extraction: once selected
coordinates are known, the base site and payload witness at each coordinate are
read from the combined tile itself.
-/
noncomputable def ofCombinedSites
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} (hn : 0 < n)
    (horizontalCoord : Fin n → Int) (verticalCoord : Fin n → Int)
    (horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
      horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1)
    (verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1)
    (hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
      Figure18Site.hCompatible
        (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
        (table.combinedSite
          (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) = true)
    (vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Figure18Site.vCompatible
        (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
        (table.combinedSite
          (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) = true)
    (active : ∀ i : Fin n, ∀ j : Fin n,
      CellRole.isActive
        (table.roleAtSite
          (table.combinedSite (x (horizontalCoord i, verticalCoord j)))) = true)
    (cornerSite :
      table.combinedSite
          (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
        table.cornerSite) :
    Figure18AdjacentProductWitnessFixedCornerSquare table x n hn where
  horizontalCoord := horizontalCoord
  verticalCoord := verticalCoord
  siteRect := fun i j =>
    table.combinedSite (x (horizontalCoord i, verticalCoord j))
  horizontalCoord_succ := horizontalCoord_succ
  verticalCoord_succ := verticalCoord_succ
  hcompatible := hcompatible
  vcompatible := vcompatible
  active := active
  cornerSite := cornerSite
  productWitness := by
    intro i j
    exact table.combinedSite_product (x (horizontalCoord i, verticalCoord j))

noncomputable def toAdjacentCompatibleFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18AdjacentProductWitnessFixedCornerSquare table x n hn) :
    Figure18AdjacentCompatibleFixedCornerSquare table x n hn :=
  Figure18AdjacentCompatibleFixedCornerSquare.ofProductWitnesses hn
    window.horizontalCoord window.verticalCoord window.siteRect
    window.horizontalCoord_succ window.verticalCoord_succ
    window.hcompatible window.vcompatible window.active
    window.cornerSite window.productWitness

theorem tileable
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18AdjacentProductWitnessFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x) :
    TileableFixedCornerSquare T seed n :=
  window.toAdjacentCompatibleFixedCornerSquare.tileable hx

end Figure18AdjacentProductWitnessFixedCornerSquare

theorem hasFigure18AdjacentCompatibleFixedCornerSquares_of_productWitness
    {table : Figure18RoleTable}
    (hproduct : HasFigure18AdjacentProductWitnessFixedCornerSquares table) :
    HasFigure18AdjacentCompatibleFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hproduct x hx n hn with ⟨window⟩
  exact ⟨window.toAdjacentCompatibleFixedCornerSquare⟩

theorem hasFigure18AdjacentProductWitnessFixedCornerSquares_of_decodedSite
    {table : Figure18RoleTable}
    (hdecoded : HasFigure18DecodedSiteFixedCornerSquares table) :
    HasFigure18AdjacentProductWitnessFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hdecoded x hx n hn with
    ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
      verticalCoord_succ, hcompatible, vcompatible, active, cornerSite⟩
  exact ⟨Figure18AdjacentProductWitnessFixedCornerSquare.ofCombinedSites hn
    horizontalCoord verticalCoord horizontalCoord_succ verticalCoord_succ
    hcompatible vcompatible active cornerSite⟩

theorem hasFigure18DecodedSiteFixedCornerSquares_of_flatDecodedSite
    {table : Figure18RoleTable.FlatRoleTable}
    (hflat : HasFigure18FlatDecodedSiteFixedCornerSquares table) :
    HasFigure18DecodedSiteFixedCornerSquares table.toRoleTable := by
  intro T seed x hx n hn
  rcases hflat x hx n hn with
    ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
      verticalCoord_succ, hcompatible, vcompatible, activeSites,
      cornerSite⟩
  refine ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
    verticalCoord_succ, hcompatible, vcompatible, ?_, ?_⟩
  · intro i j
    exact table.isActive_toRoleTable_of_mem_activeSites (activeSites i j)
  · simpa using cornerSite

theorem hasFigure18FlatDecodedSiteFixedCornerSquares_of_activeSite
    {table : Figure18RoleTable.FlatRoleTable}
    (hactive : HasFigure18FlatActiveSiteFixedCornerSquares table) :
    HasFigure18FlatDecodedSiteFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hactive x hx n hn with
    ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
      verticalCoord_succ, activeSites, cornerSite⟩
  refine ⟨horizontalCoord, verticalCoord, horizontalCoord_succ,
    verticalCoord_succ, ?_, ?_, activeSites, cornerSite⟩
  · intro i j hi
    exact table.toRoleTable.combinedSite_hCompatible_of_selectedCoords
      hx horizontalCoord verticalCoord horizontalCoord_succ i j hi
  · intro i j hj
    exact table.toRoleTable.combinedSite_vCompatible_of_selectedCoords
      hx horizontalCoord verticalCoord verticalCoord_succ i j hj

theorem hasFigure18IndexedRoutedFixedCornerSquares_of_adjacentCompatible
    {table : Figure18RoleTable}
    (hadjacent : HasFigure18AdjacentCompatibleFixedCornerSquares table) :
    HasFigure18IndexedRoutedFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hadjacent x hx n hn with ⟨window⟩
  exact ⟨window.toIndexedRoutedFixedCornerSquare hx⟩

theorem hasFigure18IndexedRoutedFixedCornerSquares_of_routed
    {table : Figure18RoleTable}
    (hrouted : HasFigure18RoutedFixedCornerSquares table) :
    HasFigure18IndexedRoutedFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hrouted x hx n hn with ⟨window⟩
  exact ⟨Figure18IndexedRoutedFixedCornerSquare.ofRoutedFixedCornerSquare window⟩

theorem hasFigure18RoutedFixedCornerSquares_of_indexed
    {table : Figure18RoleTable}
    (hindexed : HasFigure18IndexedRoutedFixedCornerSquares table) :
    HasFigure18RoutedFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hindexed x hx n hn with ⟨window⟩
  exact ⟨window.toRoutedFixedCornerSquare⟩

theorem forcesFixedCornerSquares_of_figure18Routed
    {table : Figure18RoleTable}
    (hrouted : HasFigure18RoutedFixedCornerSquares table) :
    ForcesFixedCornerSquares table.presentation.toScaffold := by
  intro T seed htiles n hn
  rcases htiles with ⟨x, hx⟩
  rcases hrouted x hx n hn with ⟨window⟩
  exact window.tileable

theorem forcesFixedCornerSquares_of_figure18IndexedRouted
    {table : Figure18RoleTable}
    (hindexed : HasFigure18IndexedRoutedFixedCornerSquares table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18Routed
    (hasFigure18RoutedFixedCornerSquares_of_indexed hindexed)

theorem forcesFixedCornerSquares_of_figure18AdjacentCompatible
    {table : Figure18RoleTable}
    (hadjacent : HasFigure18AdjacentCompatibleFixedCornerSquares table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18IndexedRouted
    (hasFigure18IndexedRoutedFixedCornerSquares_of_adjacentCompatible hadjacent)

theorem forcesFixedCornerSquares_of_figure18AdjacentProductWitness
    {table : Figure18RoleTable}
    (hproduct : HasFigure18AdjacentProductWitnessFixedCornerSquares table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18AdjacentCompatible
    (hasFigure18AdjacentCompatibleFixedCornerSquares_of_productWitness hproduct)

theorem forcesFixedCornerSquares_of_figure18DecodedSite
    {table : Figure18RoleTable}
    (hdecoded : HasFigure18DecodedSiteFixedCornerSquares table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18AdjacentProductWitness
    (hasFigure18AdjacentProductWitnessFixedCornerSquares_of_decodedSite
      hdecoded)

theorem forcesFixedCornerSquares_of_figure18FlatDecodedSite
    {table : Figure18RoleTable.FlatRoleTable}
    (hflat : HasFigure18FlatDecodedSiteFixedCornerSquares table) :
    ForcesFixedCornerSquares table.toRoleTable.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18DecodedSite
    (hasFigure18DecodedSiteFixedCornerSquares_of_flatDecodedSite hflat)

theorem forcesFixedCornerSquares_of_figure18FlatActiveSite
    {table : Figure18RoleTable.FlatRoleTable}
    (hactive : HasFigure18FlatActiveSiteFixedCornerSquares table) :
    ForcesFixedCornerSquares table.toRoleTable.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18FlatDecodedSite
    (hasFigure18FlatDecodedSiteFixedCornerSquares_of_activeSite hactive)

/--
Geometric obligations for a concrete Figure 18 role table using the direct
recognizable-free-square route.

This is stronger and more structured than `Figure18FlexibleCertificate`: it is
the right target if the Ollinger/Robinson free-square proof can identify a
literal indexed active block.
-/
structure Figure18Certificate (table : Figure18RoleTable) : Prop where
  indexedRecognizable : HasFigure18IndexedActiveCornerWindows table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

namespace Figure18Certificate

def toPresentedCertificate
    {table : Figure18RoleTable} (certificate : Figure18Certificate table) :
    PresentedCertificate table.presentation where
  recognizable :=
    hasPresentedRecognizableFreeSquares_of_figure18Indexed
      certificate.indexedRecognizable
  corner_unique := by
    simpa [Figure18RoleTable.presentation] using
      table.finiteCheckedTranscription.sanityProp.corner_unique
  realizes := certificate.realizes

def toCertificate
    {table : Figure18RoleTable} (certificate : Figure18Certificate table) :
    Certificate table.presentation.toScaffold :=
  certificate_of_presentedCertificate certificate.toPresentedCertificate

theorem isScaffold
    {table : Figure18RoleTable} (certificate : Figure18Certificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_certificate certificate.toCertificate

end Figure18Certificate

/--
Geometric obligations for a concrete Figure 18 role table.

The finite data and sanity checks live in `Figure18RoleTable`; these are the
two non-finite scaffold facts still supplied by the Ollinger/Robinson argument.
-/
structure Figure18FlexibleCertificate (table : Figure18RoleTable) : Prop where
  forces : ForcesFixedCornerSquares table.presentation.toScaffold
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

/--
Geometric obligations for a concrete Figure 18 role table using the routed
payload-square extraction from the paper's selected free coordinates.
-/
structure Figure18RoutedCertificate (table : Figure18RoleTable) : Prop where
  routedForces : HasFigure18RoutedFixedCornerSquares table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

/--
Geometric obligations for a concrete Figure 18 role table using the indexed
routed payload-square extraction.

This is the preferred finite-data target: the free-coordinate proof names every
routed scaffold site by Figure 13 index and quadrant, then converts through the
ordinary routed certificate.
-/
structure Figure18IndexedRoutedCertificate (table : Figure18RoleTable) : Prop where
  indexedRoutedForces : HasFigure18IndexedRoutedFixedCornerSquares table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

/--
Geometric obligations for a concrete Figure 18 role table using adjacent
selected coordinates and finite Figure 18 site compatibility.
-/
structure Figure18AdjacentCompatibleCertificate (table : Figure18RoleTable) : Prop where
  adjacentForces : HasFigure18AdjacentCompatibleFixedCornerSquares table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

/--
Geometric obligations for a concrete Figure 18 role table using adjacent
selected coordinates and pointwise payload witnesses.
-/
structure Figure18AdjacentProductWitnessCertificate (table : Figure18RoleTable) : Prop where
  productForces : HasFigure18AdjacentProductWitnessFixedCornerSquares table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

/--
Geometric obligations for a concrete Figure 18 role table using decoded
combined-tiling sites.
-/
structure Figure18DecodedSiteCertificate (table : Figure18RoleTable) : Prop where
  decodedForces : HasFigure18DecodedSiteFixedCornerSquares table
  realizes : RealizesActiveCornerSquares table.presentation.toScaffold

/--
Geometric obligations for a concrete flat Figure 18 table using decoded
combined-tiling sites.
-/
structure Figure18FlatDecodedSiteCertificate
    (table : Figure18RoleTable.FlatRoleTable) : Prop where
  flatDecodedForces : HasFigure18FlatDecodedSiteFixedCornerSquares table
  realizes : RealizesActiveCornerSquares
    table.toRoleTable.presentation.toScaffold

/--
Geometric obligations for a concrete Figure 18 active-site list.

This is the most direct finite-data target for a transcription of Figure 18:
the flat role table is generated from a listed set of usable quarter-sites and
a distinguished corner site.
-/
structure Figure18ListedActiveSiteCertificate
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop where
  listedActiveForces :
    HasFigure18ListedActiveSiteFixedCornerSquares activeSites cornerSite
  realizes : RealizesActiveCornerSquares
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable.presentation.toScaffold

/--
Geometric obligations for a concrete flat Figure 18 table using selected
decoded active sites.
-/
structure Figure18FlatActiveSiteCertificate
    (table : Figure18RoleTable.FlatRoleTable) : Prop where
  flatActiveForces : HasFigure18FlatActiveSiteFixedCornerSquares table
  realizes : RealizesActiveCornerSquares
    table.toRoleTable.presentation.toScaffold

namespace Figure18Certificate

def toFlexibleCertificate
    {table : Figure18RoleTable} (certificate : Figure18Certificate table) :
    Figure18FlexibleCertificate table where
  forces := forcesFixedCornerSquares_of_figure18Indexed
    certificate.indexedRecognizable
  realizes := certificate.realizes

end Figure18Certificate

namespace Figure18RoutedCertificate

def toFlexibleCertificate
    {table : Figure18RoleTable} (certificate : Figure18RoutedCertificate table) :
    Figure18FlexibleCertificate table where
  forces := forcesFixedCornerSquares_of_figure18Routed certificate.routedForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable} (certificate : Figure18RoutedCertificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18Routed certificate.routedForces
    realizes := certificate.realizes
  }

end Figure18RoutedCertificate

namespace Figure18IndexedRoutedCertificate

def toRoutedCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18IndexedRoutedCertificate table) :
    Figure18RoutedCertificate table where
  routedForces :=
    hasFigure18RoutedFixedCornerSquares_of_indexed
      certificate.indexedRoutedForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18IndexedRoutedCertificate table) :
    Figure18FlexibleCertificate table where
  forces := forcesFixedCornerSquares_of_figure18IndexedRouted
    certificate.indexedRoutedForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable}
    (certificate : Figure18IndexedRoutedCertificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18IndexedRouted
      certificate.indexedRoutedForces
    realizes := certificate.realizes
  }

end Figure18IndexedRoutedCertificate

namespace Figure18AdjacentCompatibleCertificate

def toIndexedRoutedCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18AdjacentCompatibleCertificate table) :
    Figure18IndexedRoutedCertificate table where
  indexedRoutedForces :=
    hasFigure18IndexedRoutedFixedCornerSquares_of_adjacentCompatible
      certificate.adjacentForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18AdjacentCompatibleCertificate table) :
    Figure18FlexibleCertificate table where
  forces := forcesFixedCornerSquares_of_figure18AdjacentCompatible
    certificate.adjacentForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable}
    (certificate : Figure18AdjacentCompatibleCertificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18AdjacentCompatible
      certificate.adjacentForces
    realizes := certificate.realizes
  }

end Figure18AdjacentCompatibleCertificate

namespace Figure18AdjacentProductWitnessCertificate

def toAdjacentCompatibleCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18AdjacentProductWitnessCertificate table) :
    Figure18AdjacentCompatibleCertificate table where
  adjacentForces :=
    hasFigure18AdjacentCompatibleFixedCornerSquares_of_productWitness
      certificate.productForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18AdjacentProductWitnessCertificate table) :
    Figure18FlexibleCertificate table where
  forces := forcesFixedCornerSquares_of_figure18AdjacentProductWitness
    certificate.productForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable}
    (certificate : Figure18AdjacentProductWitnessCertificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18AdjacentProductWitness
      certificate.productForces
    realizes := certificate.realizes
  }

end Figure18AdjacentProductWitnessCertificate

namespace Figure18DecodedSiteCertificate

def toAdjacentProductWitnessCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18DecodedSiteCertificate table) :
    Figure18AdjacentProductWitnessCertificate table where
  productForces :=
    hasFigure18AdjacentProductWitnessFixedCornerSquares_of_decodedSite
      certificate.decodedForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {table : Figure18RoleTable}
    (certificate : Figure18DecodedSiteCertificate table) :
    Figure18FlexibleCertificate table where
  forces := forcesFixedCornerSquares_of_figure18DecodedSite
    certificate.decodedForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable}
    (certificate : Figure18DecodedSiteCertificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18DecodedSite
      certificate.decodedForces
    realizes := certificate.realizes
  }

end Figure18DecodedSiteCertificate

namespace Figure18FlatDecodedSiteCertificate

def toDecodedSiteCertificate
    {table : Figure18RoleTable.FlatRoleTable}
    (certificate : Figure18FlatDecodedSiteCertificate table) :
    Figure18DecodedSiteCertificate table.toRoleTable where
  decodedForces :=
    hasFigure18DecodedSiteFixedCornerSquares_of_flatDecodedSite
      certificate.flatDecodedForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {table : Figure18RoleTable.FlatRoleTable}
    (certificate : Figure18FlatDecodedSiteCertificate table) :
    Figure18FlexibleCertificate table.toRoleTable where
  forces := forcesFixedCornerSquares_of_figure18FlatDecodedSite
    certificate.flatDecodedForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable.FlatRoleTable}
    (certificate : Figure18FlatDecodedSiteCertificate table) :
    IsScaffold table.toRoleTable.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18FlatDecodedSite
      certificate.flatDecodedForces
    realizes := certificate.realizes
  }

end Figure18FlatDecodedSiteCertificate

namespace Figure18ListedActiveSiteCertificate

def toFlatActiveSiteCertificate
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (certificate :
      Figure18ListedActiveSiteCertificate activeSites cornerSite) :
    Figure18FlatActiveSiteCertificate
      (Figure18RoleTable.FlatRoleTable.ofActiveSites activeSites cornerSite) where
  flatActiveForces :=
    hasFigure18FlatActiveSiteFixedCornerSquares_of_listedActiveSite
      certificate.listedActiveForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (certificate :
      Figure18ListedActiveSiteCertificate activeSites cornerSite) :
    Figure18FlexibleCertificate
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable where
  forces := forcesFixedCornerSquares_of_figure18FlatActiveSite
    (hasFigure18FlatActiveSiteFixedCornerSquares_of_listedActiveSite
      certificate.listedActiveForces)
  realizes := certificate.realizes

theorem isScaffold
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (certificate :
      Figure18ListedActiveSiteCertificate activeSites cornerSite) :
    IsScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18FlatActiveSite
      (hasFigure18FlatActiveSiteFixedCornerSquares_of_listedActiveSite
        certificate.listedActiveForces)
    realizes := certificate.realizes
  }

end Figure18ListedActiveSiteCertificate

namespace Figure18FlatActiveSiteCertificate

def toFlatDecodedSiteCertificate
    {table : Figure18RoleTable.FlatRoleTable}
    (certificate : Figure18FlatActiveSiteCertificate table) :
    Figure18FlatDecodedSiteCertificate table where
  flatDecodedForces :=
    hasFigure18FlatDecodedSiteFixedCornerSquares_of_activeSite
      certificate.flatActiveForces
  realizes := certificate.realizes

def toFlexibleCertificate
    {table : Figure18RoleTable.FlatRoleTable}
    (certificate : Figure18FlatActiveSiteCertificate table) :
    Figure18FlexibleCertificate table.toRoleTable where
  forces := forcesFixedCornerSquares_of_figure18FlatActiveSite
    certificate.flatActiveForces
  realizes := certificate.realizes

theorem isScaffold
    {table : Figure18RoleTable.FlatRoleTable}
    (certificate : Figure18FlatActiveSiteCertificate table) :
    IsScaffold table.toRoleTable.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := forcesFixedCornerSquares_of_figure18FlatActiveSite
      certificate.flatActiveForces
    realizes := certificate.realizes
  }

end Figure18FlatActiveSiteCertificate

/--
Concrete Figure 18 scaffold package: a checked finite role table together with
the geometric flexible scaffold certificate.
-/
structure Figure18FlexibleInstance where
  table : Figure18RoleTable
  certificate : Figure18FlexibleCertificate table

/--
Concrete Figure 18 scaffold package using the routed payload-square certificate.
-/
structure Figure18RoutedInstance where
  table : Figure18RoleTable
  certificate : Figure18RoutedCertificate table

/--
Concrete Figure 18 scaffold package using the indexed routed payload-square
certificate.
-/
structure Figure18IndexedRoutedInstance where
  table : Figure18RoleTable
  certificate : Figure18IndexedRoutedCertificate table

/--
Concrete Figure 18 scaffold package using adjacent selected coordinates and
finite Figure 18 site compatibility.
-/
structure Figure18AdjacentCompatibleInstance where
  table : Figure18RoleTable
  certificate : Figure18AdjacentCompatibleCertificate table

/--
Concrete Figure 18 scaffold package using adjacent selected coordinates and
pointwise payload witnesses.
-/
structure Figure18AdjacentProductWitnessInstance where
  table : Figure18RoleTable
  certificate : Figure18AdjacentProductWitnessCertificate table

/--
Concrete Figure 18 scaffold package using decoded combined-tiling sites.
-/
structure Figure18DecodedSiteInstance where
  table : Figure18RoleTable
  certificate : Figure18DecodedSiteCertificate table

/--
Concrete Figure 18 scaffold package using a flat role transcription and decoded
combined-tiling sites.
-/
structure Figure18FlatDecodedSiteInstance where
  table : Figure18RoleTable.FlatRoleTable
  certificate : Figure18FlatDecodedSiteCertificate table

/--
Concrete Figure 18 scaffold package using a flat role transcription and
selected decoded active sites.
-/
structure Figure18FlatActiveSiteInstance where
  table : Figure18RoleTable.FlatRoleTable
  certificate : Figure18FlatActiveSiteCertificate table

/--
Concrete Figure 18 scaffold package generated from a finite list of active
quarter-sites and a distinguished corner site.
-/
structure Figure18ListedActiveSiteInstance where
  activeSites : List Figure18Site
  cornerSite : Figure18Site
  certificate : Figure18ListedActiveSiteCertificate activeSites cornerSite

/--
Concrete Figure 18 scaffold package generated from checked Nat-indexed
active-site specs and a distinguished corner site.
-/
structure Figure18CheckedListedActiveSiteInstance where
  activeSiteData : Figure18Site.CheckedNatSpecs
  cornerSite : Figure18Site
  certificate :
    Figure18ListedActiveSiteCertificate activeSiteData.sites cornerSite

/--
Concrete Figure 18 scaffold data before the geometric proof is supplied.

This is the Lean-facing target for transcribing Figure 18 from the paper: a
checked finite list of usable active quarter-sites, together with the
distinguished lower-left corner quarter-site.  The local free-square invariant
and the realization invariant below are the two remaining non-finite scaffold
facts needed to turn this data into `Figure18CheckedListedActiveSiteInstance`.
-/
structure Figure18ScaffoldData where
  activeSiteData : Figure18Site.CheckedNatSpecs
  cornerSite : Figure18Site

namespace Figure18ScaffoldData

def activeSites (D : Figure18ScaffoldData) : List Figure18Site :=
  D.activeSiteData.sites

def table (D : Figure18ScaffoldData) :
    Figure18RoleTable.FlatRoleTable :=
  Figure18RoleTable.FlatRoleTable.ofActiveSites D.activeSites D.cornerSite

def finite (D : Figure18ScaffoldData) :
    FiniteCheckedTranscription :=
  D.table.toRoleTable.finiteCheckedTranscription

def presentation (D : Figure18ScaffoldData) :
    ScaffoldPresentation :=
  D.table.toRoleTable.presentation

def scaffold (D : Figure18ScaffoldData) : Scaffold :=
  D.presentation.toScaffold

def tiles (D : Figure18ScaffoldData) : TileSet :=
  D.presentation.tiles

def HasLocalFreeSquareInvariant (D : Figure18ScaffoldData) : Prop :=
  HasFigure18ListedActiveSiteFixedCornerSquares D.activeSites D.cornerSite

def HasRealizationInvariant (D : Figure18ScaffoldData) : Prop :=
  RealizesActiveCornerSquares D.scaffold

/--
The two geometric facts still needed after the finite Figure 18 active-site
data has been transcribed.
-/
structure Certificate (D : Figure18ScaffoldData) : Prop where
  localFreeSquares : D.HasLocalFreeSquareInvariant
  realizes : D.HasRealizationInvariant

theorem activeSites_length (D : Figure18ScaffoldData) :
    D.activeSites.length = D.activeSiteData.specs.length :=
  D.activeSiteData.sites_length

@[simp]
theorem table_cornerSite (D : Figure18ScaffoldData) :
    D.table.cornerSite = D.cornerSite :=
  rfl

theorem presentation_tiles (D : Figure18ScaffoldData) :
    D.presentation.tiles = figure18ScaffoldTiles := by
  simpa [presentation, figure18ScaffoldTiles] using
    D.table.toRoleTable.presentation_tiles

theorem scaffold_tiles (D : Figure18ScaffoldData) :
    D.scaffold.tiles = figure18ScaffoldTiles := by
  simpa [scaffold] using D.presentation_tiles

theorem tiles_eq (D : Figure18ScaffoldData) :
    D.tiles = figure18ScaffoldTiles :=
  D.presentation_tiles

theorem corner_mem_table_activeSites (D : Figure18ScaffoldData) :
    D.cornerSite ∈ D.table.activeSites :=
  Figure18RoleTable.FlatRoleTable.corner_mem_ofActiveSites_activeSites
    D.activeSites D.cornerSite

theorem activeSite_mem_table_activeSites_of_mem
    {D : Figure18ScaffoldData} {site : Figure18Site}
    (hmem : site ∈ D.activeSites) :
    site ∈ D.table.activeSites :=
  Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_of_mem hmem

def Certificate.toListedActiveSiteCertificate
    {D : Figure18ScaffoldData} (certificate : D.Certificate) :
    Figure18ListedActiveSiteCertificate D.activeSites D.cornerSite where
  listedActiveForces := certificate.localFreeSquares
  realizes := by
    simpa [HasRealizationInvariant, scaffold, presentation, table]
      using certificate.realizes

def toCheckedListedActiveSiteInstance
    (D : Figure18ScaffoldData) (certificate : D.Certificate) :
    Figure18CheckedListedActiveSiteInstance where
  activeSiteData := D.activeSiteData
  cornerSite := D.cornerSite
  certificate := by
    simpa [activeSites] using certificate.toListedActiveSiteCertificate

@[simp]
theorem toCheckedListedActiveSiteInstance_activeSiteData
    (D : Figure18ScaffoldData) (certificate : D.Certificate) :
    (D.toCheckedListedActiveSiteInstance certificate).activeSiteData =
      D.activeSiteData :=
  rfl

@[simp]
theorem toCheckedListedActiveSiteInstance_cornerSite
    (D : Figure18ScaffoldData) (certificate : D.Certificate) :
    (D.toCheckedListedActiveSiteInstance certificate).cornerSite =
      D.cornerSite :=
  rfl

end Figure18ScaffoldData

/--
Concrete Figure 18 scaffold package using the direct indexed free-square
certificate.
-/
structure Figure18Instance where
  table : Figure18RoleTable
  certificate : Figure18Certificate table

namespace Figure18Instance

def finite (I : Figure18Instance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18Instance) : ScaffoldPresentation :=
  I.table.presentation

def checkedTranscription (I : Figure18Instance) :
    CheckedTranscription where
  finite := I.finite
  recognizable := I.certificate.toPresentedCertificate.recognizable
  realizes := I.certificate.realizes

def toPresentedInstance (I : Figure18Instance) :
    PresentedInstance :=
  {
    presentation := I.presentation
    certificate := I.certificate.toPresentedCertificate
  }

@[simp]
theorem checkedTranscription_finite (I : Figure18Instance) :
    I.checkedTranscription.finite = I.finite :=
  rfl

@[simp]
theorem checkedTranscription_presentation (I : Figure18Instance) :
    I.checkedTranscription.presentation = I.presentation :=
  rfl

theorem presentation_tiles (I : Figure18Instance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18Instance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

def toFlexibleInstance (I : Figure18Instance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFlexibleCertificate

end Figure18Instance

namespace Figure18RoutedInstance

def finite (I : Figure18RoutedInstance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18RoutedInstance) : ScaffoldPresentation :=
  I.table.presentation

def toFlexibleInstance (I : Figure18RoutedInstance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toFlexibleInstance_table (I : Figure18RoutedInstance) :
    I.toFlexibleInstance.table = I.table :=
  rfl

theorem presentation_tiles (I : Figure18RoutedInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18RoutedInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18RoutedInstance

namespace Figure18IndexedRoutedInstance

def finite (I : Figure18IndexedRoutedInstance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18IndexedRoutedInstance) : ScaffoldPresentation :=
  I.table.presentation

def toRoutedInstance (I : Figure18IndexedRoutedInstance) :
    Figure18RoutedInstance where
  table := I.table
  certificate := I.certificate.toRoutedCertificate

def toFlexibleInstance (I : Figure18IndexedRoutedInstance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toRoutedInstance_table (I : Figure18IndexedRoutedInstance) :
    I.toRoutedInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table (I : Figure18IndexedRoutedInstance) :
    I.toFlexibleInstance.table = I.table :=
  rfl

theorem presentation_tiles (I : Figure18IndexedRoutedInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18IndexedRoutedInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18IndexedRoutedInstance

namespace Figure18AdjacentCompatibleInstance

def finite (I : Figure18AdjacentCompatibleInstance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18AdjacentCompatibleInstance) : ScaffoldPresentation :=
  I.table.presentation

def toIndexedRoutedInstance (I : Figure18AdjacentCompatibleInstance) :
    Figure18IndexedRoutedInstance where
  table := I.table
  certificate := I.certificate.toIndexedRoutedCertificate

def toFlexibleInstance (I : Figure18AdjacentCompatibleInstance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toIndexedRoutedInstance_table (I : Figure18AdjacentCompatibleInstance) :
    I.toIndexedRoutedInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table (I : Figure18AdjacentCompatibleInstance) :
    I.toFlexibleInstance.table = I.table :=
  rfl

theorem presentation_tiles (I : Figure18AdjacentCompatibleInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18AdjacentCompatibleInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18AdjacentCompatibleInstance

namespace Figure18AdjacentProductWitnessInstance

def finite (I : Figure18AdjacentProductWitnessInstance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18AdjacentProductWitnessInstance) : ScaffoldPresentation :=
  I.table.presentation

def toAdjacentCompatibleInstance (I : Figure18AdjacentProductWitnessInstance) :
    Figure18AdjacentCompatibleInstance where
  table := I.table
  certificate := I.certificate.toAdjacentCompatibleCertificate

def toFlexibleInstance (I : Figure18AdjacentProductWitnessInstance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toAdjacentCompatibleInstance_table
    (I : Figure18AdjacentProductWitnessInstance) :
    I.toAdjacentCompatibleInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table (I : Figure18AdjacentProductWitnessInstance) :
    I.toFlexibleInstance.table = I.table :=
  rfl

theorem presentation_tiles (I : Figure18AdjacentProductWitnessInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18AdjacentProductWitnessInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18AdjacentProductWitnessInstance

namespace Figure18DecodedSiteInstance

def finite (I : Figure18DecodedSiteInstance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18DecodedSiteInstance) : ScaffoldPresentation :=
  I.table.presentation

def toAdjacentProductWitnessInstance (I : Figure18DecodedSiteInstance) :
    Figure18AdjacentProductWitnessInstance where
  table := I.table
  certificate := I.certificate.toAdjacentProductWitnessCertificate

def toFlexibleInstance (I : Figure18DecodedSiteInstance) :
    Figure18FlexibleInstance where
  table := I.table
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toAdjacentProductWitnessInstance_table
    (I : Figure18DecodedSiteInstance) :
    I.toAdjacentProductWitnessInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table (I : Figure18DecodedSiteInstance) :
    I.toFlexibleInstance.table = I.table :=
  rfl

theorem presentation_tiles (I : Figure18DecodedSiteInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18DecodedSiteInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18DecodedSiteInstance

namespace Figure18FlatDecodedSiteInstance

def finite (I : Figure18FlatDecodedSiteInstance) : FiniteCheckedTranscription :=
  I.table.toRoleTable.finiteCheckedTranscription

def presentation (I : Figure18FlatDecodedSiteInstance) :
    ScaffoldPresentation :=
  I.table.toRoleTable.presentation

def toDecodedSiteInstance (I : Figure18FlatDecodedSiteInstance) :
    Figure18DecodedSiteInstance where
  table := I.table.toRoleTable
  certificate := I.certificate.toDecodedSiteCertificate

def toFlexibleInstance (I : Figure18FlatDecodedSiteInstance) :
    Figure18FlexibleInstance where
  table := I.table.toRoleTable
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toDecodedSiteInstance_table (I : Figure18FlatDecodedSiteInstance) :
    I.toDecodedSiteInstance.table = I.table.toRoleTable :=
  rfl

@[simp]
theorem toFlexibleInstance_table (I : Figure18FlatDecodedSiteInstance) :
    I.toFlexibleInstance.table = I.table.toRoleTable :=
  rfl

theorem presentation_tiles (I : Figure18FlatDecodedSiteInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.toRoleTable.presentation_tiles

theorem isScaffold (I : Figure18FlatDecodedSiteInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18FlatDecodedSiteInstance

namespace Figure18FlatActiveSiteInstance

def finite (I : Figure18FlatActiveSiteInstance) : FiniteCheckedTranscription :=
  I.table.toRoleTable.finiteCheckedTranscription

def presentation (I : Figure18FlatActiveSiteInstance) :
    ScaffoldPresentation :=
  I.table.toRoleTable.presentation

def toFlatDecodedSiteInstance (I : Figure18FlatActiveSiteInstance) :
    Figure18FlatDecodedSiteInstance where
  table := I.table
  certificate := I.certificate.toFlatDecodedSiteCertificate

def toFlexibleInstance (I : Figure18FlatActiveSiteInstance) :
    Figure18FlexibleInstance where
  table := I.table.toRoleTable
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toFlatDecodedSiteInstance_table (I : Figure18FlatActiveSiteInstance) :
    I.toFlatDecodedSiteInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table (I : Figure18FlatActiveSiteInstance) :
    I.toFlexibleInstance.table = I.table.toRoleTable :=
  rfl

theorem presentation_tiles (I : Figure18FlatActiveSiteInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.toRoleTable.presentation_tiles

theorem isScaffold (I : Figure18FlatActiveSiteInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18FlatActiveSiteInstance

namespace Figure18ListedActiveSiteInstance

def table (I : Figure18ListedActiveSiteInstance) :
    Figure18RoleTable.FlatRoleTable :=
  Figure18RoleTable.FlatRoleTable.ofActiveSites I.activeSites I.cornerSite

def finite (I : Figure18ListedActiveSiteInstance) : FiniteCheckedTranscription :=
  I.table.toRoleTable.finiteCheckedTranscription

def presentation (I : Figure18ListedActiveSiteInstance) :
    ScaffoldPresentation :=
  I.table.toRoleTable.presentation

def toFlatActiveSiteInstance (I : Figure18ListedActiveSiteInstance) :
    Figure18FlatActiveSiteInstance where
  table := I.table
  certificate := I.certificate.toFlatActiveSiteCertificate

def toFlexibleInstance (I : Figure18ListedActiveSiteInstance) :
    Figure18FlexibleInstance where
  table := I.table.toRoleTable
  certificate := I.certificate.toFlexibleCertificate

@[simp]
theorem toFlatActiveSiteInstance_table
    (I : Figure18ListedActiveSiteInstance) :
    I.toFlatActiveSiteInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table
    (I : Figure18ListedActiveSiteInstance) :
    I.toFlexibleInstance.table = I.table.toRoleTable :=
  rfl

theorem presentation_tiles (I : Figure18ListedActiveSiteInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.toRoleTable.presentation_tiles

theorem isScaffold (I : Figure18ListedActiveSiteInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18ListedActiveSiteInstance

namespace Figure18CheckedListedActiveSiteInstance

def activeSites (I : Figure18CheckedListedActiveSiteInstance) :
    List Figure18Site :=
  I.activeSiteData.sites

def table (I : Figure18CheckedListedActiveSiteInstance) :
    Figure18RoleTable.FlatRoleTable :=
  Figure18RoleTable.FlatRoleTable.ofActiveSites I.activeSites I.cornerSite

def finite (I : Figure18CheckedListedActiveSiteInstance) :
    FiniteCheckedTranscription :=
  I.table.toRoleTable.finiteCheckedTranscription

def presentation (I : Figure18CheckedListedActiveSiteInstance) :
    ScaffoldPresentation :=
  I.table.toRoleTable.presentation

def toListedActiveSiteInstance
    (I : Figure18CheckedListedActiveSiteInstance) :
    Figure18ListedActiveSiteInstance where
  activeSites := I.activeSites
  cornerSite := I.cornerSite
  certificate := I.certificate

def toFlatActiveSiteInstance
    (I : Figure18CheckedListedActiveSiteInstance) :
    Figure18FlatActiveSiteInstance :=
  I.toListedActiveSiteInstance.toFlatActiveSiteInstance

def toFlexibleInstance
    (I : Figure18CheckedListedActiveSiteInstance) :
    Figure18FlexibleInstance :=
  I.toListedActiveSiteInstance.toFlexibleInstance

@[simp]
theorem toListedActiveSiteInstance_activeSites
    (I : Figure18CheckedListedActiveSiteInstance) :
    I.toListedActiveSiteInstance.activeSites = I.activeSites :=
  rfl

@[simp]
theorem toListedActiveSiteInstance_cornerSite
    (I : Figure18CheckedListedActiveSiteInstance) :
    I.toListedActiveSiteInstance.cornerSite = I.cornerSite :=
  rfl

@[simp]
theorem toFlatActiveSiteInstance_table
    (I : Figure18CheckedListedActiveSiteInstance) :
    I.toFlatActiveSiteInstance.table = I.table :=
  rfl

@[simp]
theorem toFlexibleInstance_table
    (I : Figure18CheckedListedActiveSiteInstance) :
    I.toFlexibleInstance.table = I.table.toRoleTable :=
  rfl

theorem presentation_tiles (I : Figure18CheckedListedActiveSiteInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.toRoleTable.presentation_tiles

theorem isScaffold (I : Figure18CheckedListedActiveSiteInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.certificate.isScaffold

end Figure18CheckedListedActiveSiteInstance

namespace Figure18ScaffoldData

theorem Certificate.isScaffold
    {D : Figure18ScaffoldData} (certificate : D.Certificate) :
    IsScaffold D.scaffold := by
  simpa [toCheckedListedActiveSiteInstance, activeSites, scaffold, presentation, table,
    Figure18CheckedListedActiveSiteInstance.presentation,
    Figure18CheckedListedActiveSiteInstance.table,
    Figure18CheckedListedActiveSiteInstance.activeSites,
    Figure18ListedActiveSiteInstance.presentation,
    Figure18ListedActiveSiteInstance.table]
    using (D.toCheckedListedActiveSiteInstance certificate).isScaffold

end Figure18ScaffoldData

namespace Figure18FlexibleInstance

def finite (I : Figure18FlexibleInstance) : FiniteCheckedTranscription :=
  I.table.finiteCheckedTranscription

def presentation (I : Figure18FlexibleInstance) : ScaffoldPresentation :=
  I.table.presentation

def checkedFlexibleTranscription (I : Figure18FlexibleInstance) :
    CheckedFlexibleTranscription where
  finite := I.finite
  forces := I.certificate.forces
  realizes := I.certificate.realizes

def toPresentedFlexibleInstance (I : Figure18FlexibleInstance) :
    PresentedFlexibleInstance :=
  I.checkedFlexibleTranscription.toPresentedFlexibleInstance

@[simp]
theorem checkedFlexibleTranscription_finite
    (I : Figure18FlexibleInstance) :
    I.checkedFlexibleTranscription.finite = I.finite :=
  rfl

@[simp]
theorem checkedFlexibleTranscription_presentation
    (I : Figure18FlexibleInstance) :
    I.checkedFlexibleTranscription.presentation = I.presentation :=
  rfl

theorem presentation_tiles (I : Figure18FlexibleInstance) :
    I.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  I.table.presentation_tiles

theorem isScaffold (I : Figure18FlexibleInstance) :
    IsScaffold I.presentation.toScaffold :=
  I.checkedFlexibleTranscription.isScaffold

end Figure18FlexibleInstance

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
