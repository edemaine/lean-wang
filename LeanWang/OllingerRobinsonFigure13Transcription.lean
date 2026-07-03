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

/-- A raw Figure 13 tile-list member decoded to its scanned Figure 13 index. -/
theorem exists_fig13Tile_eq_of_mem_fig13Tiles {tile : WangTile}
    (hmem : tile ∈ fig13Tiles) :
    ∃ index : Fin 92, fig13Tile index = tile := by
  have hidx : fig13Tiles.idxOf tile < fig13Tiles.length :=
    List.idxOf_lt_length_of_mem hmem
  refine ⟨⟨fig13Tiles.idxOf tile, by simpa [fig13Tiles_length] using hidx⟩, ?_⟩
  unfold fig13Tile
  have hget : fig13Tiles[fig13Tiles.idxOf tile]? = some tile :=
    List.getElem?_idxOf hmem
  have hgetSome : some fig13Tiles[fig13Tiles.idxOf tile] = some tile := by
    rw [List.getElem?_eq_getElem hidx] at hget
    exact hget
  exact Option.some.inj hgetSome

/-- Boolean raw horizontal compatibility for two indexed Figure 13 tiles. -/
def fig13RawHCompatiblePairBool (left right : Fin 92) : Bool :=
  decide (WangTile.HMatches (fig13Tile left) (fig13Tile right))

/-- Boolean raw vertical compatibility for two indexed Figure 13 tiles. -/
def fig13RawVCompatiblePairBool (lower upper : Fin 92) : Bool :=
  decide (WangTile.VMatches (fig13Tile lower) (fig13Tile upper))

/-- All pairs of raw Figure 13 tile indices. -/
def fig13RawIndexPairs : List (Fin 92 × Fin 92) :=
  (List.finRange 92).product (List.finRange 92)

theorem mem_fig13RawIndexPairs (pair : Fin 92 × Fin 92) :
    pair ∈ fig13RawIndexPairs := by
  rcases pair with ⟨left, right⟩
  simp [fig13RawIndexPairs]

/-- Horizontally compatible indexed raw Figure 13 tile pairs. -/
def fig13RawHCompatiblePairs : List (Fin 92 × Fin 92) :=
  fig13RawIndexPairs.filter fun pair =>
    fig13RawHCompatiblePairBool pair.1 pair.2

theorem mem_fig13RawHCompatiblePairs_iff
    {pair : Fin 92 × Fin 92} :
    pair ∈ fig13RawHCompatiblePairs ↔
      fig13RawHCompatiblePairBool pair.1 pair.2 = true := by
  simp [fig13RawHCompatiblePairs, mem_fig13RawIndexPairs pair]

/--
Fast finite check for a raw Figure 13 `2 × 2` square.

The raw Figure 13 tiles are superimposed macro tiles, not a standalone plane
tileset.  This checker first enumerates the small list of horizontally
compatible rows and then tests whether two such rows can be stacked.
-/
def fig13RawTwoByTwoSquareBool : Bool :=
  fig13RawHCompatiblePairs.any fun bottom =>
    fig13RawHCompatiblePairs.any fun top =>
      fig13RawVCompatiblePairBool bottom.1 top.1 &&
        fig13RawVCompatiblePairBool bottom.2 top.2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000 in
-- The indexed check computes all raw horizontal pairs among 92 tiles once,
-- then checks the resulting small row list for a stackable `2 × 2` witness.
/--
Diagnostic obstruction: the raw Figure 13 macro-tile list does not tile a
`2 × 2` square by itself.

The proof-facing scaffold route must therefore use the subdivided Figure 18
site compatibility / board-free-line interfaces, not raw `TilesPlane
fig13Tiles` as a standalone target.
-/
theorem fig13RawTwoByTwoSquareBool_eq_false :
    fig13RawTwoByTwoSquareBool = false := by
  decide

theorem fig13RawTwoByTwoSquareBool_eq_true_of_indices
    {southwest southeast northwest northeast : Fin 92}
    (hbottom :
      WangTile.HMatches (fig13Tile southwest) (fig13Tile southeast))
    (htop :
      WangTile.HMatches (fig13Tile northwest) (fig13Tile northeast))
    (hleft :
      WangTile.VMatches (fig13Tile southwest) (fig13Tile northwest))
    (hright :
      WangTile.VMatches (fig13Tile southeast) (fig13Tile northeast)) :
    fig13RawTwoByTwoSquareBool = true := by
  unfold fig13RawTwoByTwoSquareBool
  apply List.any_eq_true.2
  refine ⟨(southwest, southeast), ?_, ?_⟩
  · rw [mem_fig13RawHCompatiblePairs_iff]
    exact decide_eq_true hbottom
  · apply List.any_eq_true.2
    refine ⟨(northwest, northeast), ?_, ?_⟩
    · rw [mem_fig13RawHCompatiblePairs_iff]
      exact decide_eq_true htop
    · simp [fig13RawVCompatiblePairBool, hleft, hright]

/-- The raw Figure 13 macro-tile list cannot tile a `2 × 2` square. -/
theorem not_tileableSquare_fig13Tiles_two :
    ¬ TileableSquare fig13Tiles 2 := by
  rintro ⟨x, hx⟩
  let west : Fin 2 := ⟨0, by decide⟩
  let east : Fin 2 := ⟨1, by decide⟩
  let south : Fin 2 := ⟨0, by decide⟩
  let north : Fin 2 := ⟨1, by decide⟩
  rcases exists_fig13Tile_eq_of_mem_fig13Tiles (hx.1 west south) with
    ⟨southwest, hsw⟩
  rcases exists_fig13Tile_eq_of_mem_fig13Tiles (hx.1 east south) with
    ⟨southeast, hse⟩
  rcases exists_fig13Tile_eq_of_mem_fig13Tiles (hx.1 west north) with
    ⟨northwest, hnw⟩
  rcases exists_fig13Tile_eq_of_mem_fig13Tiles (hx.1 east north) with
    ⟨northeast, hne⟩
  have hbottom : WangTile.HMatches (fig13Tile southwest) (fig13Tile southeast) := by
    rw [hsw, hse]
    exact hx.2.1 west south (by decide)
  have htop : WangTile.HMatches (fig13Tile northwest) (fig13Tile northeast) := by
    rw [hnw, hne]
    exact hx.2.1 west north (by decide)
  have hleft : WangTile.VMatches (fig13Tile southwest) (fig13Tile northwest) := by
    rw [hsw, hnw]
    exact hx.2.2 west south (by decide)
  have hright : WangTile.VMatches (fig13Tile southeast) (fig13Tile northeast) := by
    rw [hse, hne]
    exact hx.2.2 east south (by decide)
  have htrue := fig13RawTwoByTwoSquareBool_eq_true_of_indices
    hbottom htop hleft hright
  rw [fig13RawTwoByTwoSquareBool_eq_false] at htrue
  contradiction

/-- The raw Figure 13 macro-tile list is not a standalone plane tileset. -/
theorem not_tilesPlane_fig13Tiles :
    ¬ TilesPlane fig13Tiles := by
  intro hplane
  exact not_tileableSquare_fig13Tiles_two
    (tileableSquare_of_tilesPlane hplane 2)

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

/--
All length-`n` row tails that can be appended to a fixed Figure 18 site.

The first element of each returned tail is a valid east neighbor of `left`,
and consecutive entries in the tail are also east-compatible.
-/
def rowTailsAfter (left : Figure18Site) : Nat → List (List Figure18Site)
  | 0 => [[]]
  | n + 1 =>
      all.flatMap fun right =>
        if hCompatible left right then
          (rowTailsAfter right n).map fun tail => right :: tail
        else
          []

/-- All horizontally compatible Figure 18 site rows of the requested width. -/
def compatibleRows : Nat → List (List Figure18Site)
  | 0 => [[]]
  | n + 1 =>
      all.flatMap fun first =>
        (rowTailsAfter first n).map fun tail => first :: tail

/-- Pointwise vertical compatibility of two Figure 18 site rows. -/
def rowsVCompatible : List Figure18Site → List Figure18Site → Bool
  | [], [] => true
  | lower :: lowers, upper :: uppers =>
      vCompatible lower upper && rowsVCompatible lowers uppers
  | _, _ => false

/--
Possible top rows after stacking `height + 1` compatible rows of fixed width.

This dynamic program is used only for finite diagnostics; it avoids enumerating
all rectangles explicitly.
-/
def rowStackTops (width : Nat) : Nat → List (List Figure18Site)
  | 0 => compatibleRows width
  | height + 1 =>
      let rows := compatibleRows width
      (rowStackTops width height).flatMap fun lower =>
        rows.filter fun upper => rowsVCompatible lower upper

/-- Fast row-DP existence check for a Figure 18 site rectangle of the given size. -/
def hasRectangleStackBool (width height : Nat) : Bool :=
  match height with
  | 0 => true
  | depth + 1 => !(rowStackTops width depth).isEmpty

set_option linter.style.nativeDecide false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000 in
-- Native evaluation keeps this finite diagnostic from forcing a huge kernel reduction.
/--
Diagnostic obstruction: the subdivided Figure 18 site graph does not contain a
compatible `3 × 3` square.

Thus `HasCompatibleFigure18ScaffoldSquares` is also too strong as a standalone
scaffold-plane target.  The remaining scaffold proof must use the routed
active-corner/board invariant rather than plane tileability of all subdivided
Figure 13 scaffold sites.
-/
theorem hasRectangleStackBool_three_three_eq_false :
    hasRectangleStackBool 3 3 = false := by
  native_decide

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

/-- Encode a typed Figure 18 site as the raw Nat-indexed form used for data entry. -/
def toNatSpec (site : Figure18Site) : Nat × Quadrant :=
  (site.index.val, site.quadrant)

/-- Encode typed Figure 18 sites as raw Nat-indexed specs. -/
def natSpecsOfSites (sites : List Figure18Site) : List (Nat × Quadrant) :=
  sites.map toNatSpec

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

theorem natSpecsValidBool_natSpecsOfSites (sites : List Figure18Site) :
    natSpecsValidBool (natSpecsOfSites sites) = true := by
  induction sites with
  | nil =>
      rfl
  | cons site sites ih =>
      rcases site with ⟨i, q⟩
      simp [natSpecsOfSites, toNatSpec, natSpecsValidBool, i.isLt]

theorem sitesOfNatSpecs_natSpecsOfSites (sites : List Figure18Site) :
    sitesOfNatSpecs (natSpecsOfSites sites) = sites := by
  induction sites with
  | nil =>
      rfl
  | cons site sites ih =>
      rcases site with ⟨i, q⟩
      change sitesOfNatSpecs ((i.val, q) :: natSpecsOfSites sites) =
        ({ index := i, quadrant := q } : Figure18Site) :: sites
      simp [sitesOfNatSpecs, ofNat?, i.isLt, ih]

/-- Checked raw data for a finite list of Figure 18 sites. -/
structure CheckedNatSpecs where
  specs : List (Nat × Quadrant)
  valid : natSpecsValidBool specs = true

namespace CheckedNatSpecs

def ofSites (sites : List Figure18Site) : CheckedNatSpecs where
  specs := natSpecsOfSites sites
  valid := natSpecsValidBool_natSpecsOfSites sites

def sites (data : CheckedNatSpecs) : List Figure18Site :=
  sitesOfNatSpecs data.specs

@[simp]
theorem ofSites_specs (sites : List Figure18Site) :
    (ofSites sites).specs = natSpecsOfSites sites :=
  rfl

@[simp]
theorem ofSites_sites (sites : List Figure18Site) :
    (ofSites sites).sites = sites :=
  sitesOfNatSpecs_natSpecsOfSites sites

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

theorem presentation_sanity (table : Figure18RoleTable) :
    table.presentation.Sanity := by
  simpa [presentation] using table.finiteCheckedTranscription.sanityProp

theorem scaffold_corner_mem (table : Figure18RoleTable) :
    table.presentation.toScaffold.corner ∈ table.presentation.toScaffold.tiles :=
  ScaffoldPresentation.toScaffold_corner_mem_of_sanity table.presentation_sanity

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

noncomputable def combinedPayload
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    WangTile :=
  Classical.choose (table.combinedSite_product tile)

theorem combinedPayload_product
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed)) :
    WangTile.product (table.combinedSite tile).tile
      (table.combinedPayload tile) = tile.1 :=
  Classical.choose_spec (table.combinedSite_product tile)

theorem combinedSite_eq_of_product_site
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (tile : TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (site : Figure18Site) (payload : WangTile)
    (hproduct : WangTile.product site.tile payload = tile.1) :
    table.combinedSite tile = site := by
  rcases table.combinedSite_product tile with
    ⟨combinedPayload, hcombined⟩
  apply Figure18Site.tile_injective
  exact (product_eq_iff.1 (hcombined.trans hproduct.symm)).1

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

def activeSiteData (table : FlatRoleTable) :
    Figure18Site.CheckedNatSpecs :=
  Figure18Site.CheckedNatSpecs.ofSites table.activeSites

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

@[simp]
theorem activeSiteData_sites (table : FlatRoleTable) :
    table.activeSiteData.sites = table.activeSites :=
  Figure18Site.CheckedNatSpecs.ofSites_sites table.activeSites

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

theorem roleOfActiveSites_ofActiveSites_activeSites
    (activeSites : List Figure18Site) (cornerSite site : Figure18Site) :
    roleOfActiveSites
        (ofActiveSites activeSites cornerSite).activeSites cornerSite site =
      roleOfActiveSites activeSites cornerSite site := by
  by_cases hcorner : site = cornerSite
  · subst hcorner
    simp [roleOfActiveSites]
  · by_cases hmem : site ∈ activeSites
    · have hmem' :
          site ∈ (ofActiveSites activeSites cornerSite).activeSites :=
        (mem_ofActiveSites_activeSites_iff
          activeSites cornerSite site).2 (Or.inr hmem)
      simp [roleOfActiveSites, hcorner, hmem, hmem']
    · have hmem' :
          site ∉ (ofActiveSites activeSites cornerSite).activeSites := by
        intro hsite
        rcases (mem_ofActiveSites_activeSites_iff
          activeSites cornerSite site).1 hsite with hsite | hsite
        · exact hcorner hsite
        · exact hmem hsite
      simp [roleOfActiveSites, hcorner, hmem, hmem']

theorem flatRolesOfActiveSites_ofActiveSites_activeSites
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    flatRolesOfActiveSites
        (ofActiveSites activeSites cornerSite).activeSites cornerSite =
      flatRolesOfActiveSites activeSites cornerSite := by
  unfold flatRolesOfActiveSites
  rw [List.ofFn_inj]
  funext k
  exact roleOfActiveSites_ofActiveSites_activeSites
    activeSites cornerSite (Figure18Site.siteOfFlatIndex k)

theorem ofActiveSites_activeSites_roleAtSite
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    (ofActiveSites
        (ofActiveSites activeSites cornerSite).activeSites cornerSite).toRoleTable.roleAtSite =
      (ofActiveSites activeSites cornerSite).toRoleTable.roleAtSite := by
  funext site
  rw [ofActiveSites_roleAtSite, ofActiveSites_roleAtSite,
    roleOfActiveSites_ofActiveSites_activeSites]

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

theorem tilesPlane_figure18ScaffoldTiles_of_tilesPlane_fig13Tiles :
    TilesPlane fig13Tiles → TilesPlane figure18ScaffoldTiles := by
  simpa [figure18ScaffoldTiles] using
    (TileSubdivision.tilesPlane_subdivideTileSet_of_tilesPlane
      (T := fig13Tiles))

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

/-- Enlarge the listed active-site set for a fixed decoded-window witness. -/
def mono_activeSites
    {table : Figure18RoleTable}
    {activeSites activeSites' : List Figure18Site}
    {cornerSite : Figure18Site}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (hsubset :
      ∀ site : Figure18Site, site ∈ activeSites → site ∈ activeSites')
    (window :
      Figure18ListedActiveSiteFixedCornerSquare
        table activeSites cornerSite x n hn) :
    Figure18ListedActiveSiteFixedCornerSquare
      table activeSites' cornerSite x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  horizontalCoord_succ := window.horizontalCoord_succ
  verticalCoord_succ := window.verticalCoord_succ
  listedActive := by
    intro i j
    rcases window.listedActive i j with hcorner | hactive
    · exact Or.inl hcorner
    · exact Or.inr (hsubset _ hactive)
  corner := window.corner

/--
View a listed-active witness against the generated flat table's computed active
site list.
-/
def toGeneratedActiveSites
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSites cornerSite).toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window :
      Figure18ListedActiveSiteFixedCornerSquare
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSites cornerSite).toRoleTable
        activeSites cornerSite x n hn) :
    Figure18ListedActiveSiteFixedCornerSquare
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).activeSites
      cornerSite x n hn :=
  window.mono_activeSites (by
    intro site hsite
    exact Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_of_mem
      hsite)

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

/-!
Robinson square sizes used by the board/free-grid proof.

The original recursive argument produces forced squares of side
`1, 3, 7, 15, ...`.  The Figure 18 routed-board interface uses the coarser
board scale `4^level - 1`; its free rows and columns give a virtual payload
grid of side `2^level + 1`.
-/
namespace RobinsonSquare

/-- Side length of Robinson's forced `level`-square: `1, 3, 7, ...`. -/
def forcedSide (level : Nat) : Nat :=
  2 ^ (level + 1) - 1

/-- Side length of a red border at a routed-board level. -/
def redBorderSide (level : Nat) : Nat :=
  4 ^ level

/-- Side length of the Figure 18 board at a routed-board level. -/
def boardSide (level : Nat) : Nat :=
  4 ^ level - 1

/-- Number of free rows/columns available in a routed board of this level. -/
def freeGridSide (level : Nat) : Nat :=
  2 ^ level + 1

@[simp] theorem forcedSide_zero : forcedSide 0 = 1 := by
  decide

@[simp] theorem forcedSide_one : forcedSide 1 = 3 := by
  decide

@[simp] theorem forcedSide_two : forcedSide 2 = 7 := by
  decide

@[simp] theorem forcedSide_three : forcedSide 3 = 15 := by
  decide

@[simp] theorem redBorderSide_zero : redBorderSide 0 = 1 := by
  decide

@[simp] theorem redBorderSide_one : redBorderSide 1 = 4 := by
  decide

@[simp] theorem redBorderSide_two : redBorderSide 2 = 16 := by
  decide

@[simp] theorem redBorderSide_three : redBorderSide 3 = 64 := by
  decide

@[simp] theorem boardSide_zero : boardSide 0 = 0 := by
  decide

@[simp] theorem boardSide_one : boardSide 1 = 3 := by
  decide

@[simp] theorem boardSide_two : boardSide 2 = 15 := by
  decide

@[simp] theorem boardSide_three : boardSide 3 = 63 := by
  decide

@[simp] theorem freeGridSide_zero : freeGridSide 0 = 2 := by
  decide

@[simp] theorem freeGridSide_one : freeGridSide 1 = 3 := by
  decide

@[simp] theorem freeGridSide_two : freeGridSide 2 = 5 := by
  decide

@[simp] theorem freeGridSide_three : freeGridSide 3 = 9 := by
  decide

theorem one_le_two_pow (level : Nat) : 1 ≤ 2 ^ level := by
  induction level with
  | zero =>
      simp
  | succ level ih =>
      rw [pow_succ]
      omega

theorem le_two_pow (level : Nat) : level ≤ 2 ^ level := by
  induction level with
  | zero =>
      simp
  | succ level ih =>
      have hone : 1 ≤ 2 ^ level := one_le_two_pow level
      calc
        level + 1 ≤ 2 ^ level + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ level + 2 ^ level := Nat.add_le_add_left hone (2 ^ level)
        _ = 2 ^ (level + 1) := by
          rw [pow_succ]
          omega

theorem self_le_freeGridSide (level : Nat) :
    level ≤ freeGridSide level := by
  unfold freeGridSide
  exact Nat.le_trans (le_two_pow level) (Nat.le.intro rfl)

theorem freeGridSide_pos (level : Nat) : 0 < freeGridSide level := by
  unfold freeGridSide
  exact Nat.succ_pos (2 ^ level)

/--
Robinson's Section 7 closed form for the number of free rows or columns in the
red-board of a given level.
-/
theorem freeGridSide_eq_two_pow_add_one (level : Nat) :
    freeGridSide level = 2 ^ level + 1 := by
  rfl

/--
The shifted positive-board interface uses the first nondegenerate red board at
`level + 1`, whose free grid has side `2^(level+1) + 1`.
-/
theorem positiveBoardFreeGridSide_eq_two_pow_add_one (level : Nat) :
    freeGridSide (level + 1) = 2 ^ (level + 1) + 1 := by
  rfl

theorem redBorderSide_pos (level : Nat) : 0 < redBorderSide level := by
  unfold redBorderSide
  exact pow_pos (by decide : 0 < 4) level

theorem boardSide_eq_redBorderSide_sub_one (level : Nat) :
    boardSide level = redBorderSide level - 1 := by
  rfl

theorem redBorderSide_succ (level : Nat) :
    redBorderSide (level + 1) = 4 * redBorderSide level := by
  unfold redBorderSide
  rw [pow_succ]
  omega

theorem boardSide_succ (level : Nat) :
    boardSide (level + 1) = 4 * boardSide level + 3 := by
  unfold boardSide
  have hpos : 0 < 4 ^ level := pow_pos (by decide : 0 < 4) level
  rw [pow_succ]
  omega

theorem freeGridSide_succ (level : Nat) :
    freeGridSide (level + 1) = 2 * freeGridSide level - 1 := by
  unfold freeGridSide
  rw [pow_succ]
  omega

/--
Robinson's Section 7 count recurrence for the number of free rows or columns
on a board: the next board repeats the old free-line pattern twice, sharing the
center line.
-/
theorem freeGridSide_succ_eq_double_sub_one (level : Nat) :
    freeGridSide (level + 1) = freeGridSide level + freeGridSide level - 1 := by
  rw [freeGridSide_succ]
  omega

theorem freeGridSide_le_boardSide_add_two (level : Nat) :
    freeGridSide level ≤ boardSide level + 2 := by
  unfold freeGridSide boardSide
  induction level with
  | zero =>
      simp
  | succ level ih =>
      rw [pow_succ, pow_succ]
      have hpos : 0 < 4 ^ level := pow_pos (by decide : 0 < 4) level
      omega

/--
Any requested finite payload square fits in the free grid of some Robinson
board level.  The concrete geometric proof may use a sharper level, but choosing
`level = n` is enough for the abstract routed-grid obligation.
-/
theorem exists_level_with_payload_capacity (n : Nat) :
    ∃ level : Nat, n ≤ freeGridSide level :=
  ⟨n, self_le_freeGridSide n⟩

/-- Last index in the virtual free-line grid at a Robinson board level. -/
def freeGridLast (level : Nat) : Fin (freeGridSide level) :=
  ⟨freeGridSide level - 1, by
    have hpos := freeGridSide_pos level
    omega⟩

/--
Left copy of a level's free-line indices inside the next level's overlapping
`F_{n+1} = 2F_n - 1` recurrence.
-/
def freeLineLeftEmbedding (level : Nat) :
    Fin (freeGridSide level) → Fin (freeGridSide (level + 1)) :=
  fun i =>
    ⟨i.val, by
      have hle : freeGridSide level ≤ freeGridSide (level + 1) := by
        rw [freeGridSide_succ]
        have hpos := freeGridSide_pos level
        omega
      exact Nat.lt_of_lt_of_le i.isLt hle⟩

/--
Right copy of a level's free-line indices inside the next level's overlapping
`F_{n+1} = 2F_n - 1` recurrence.
-/
def freeLineRightEmbedding (level : Nat) :
    Fin (freeGridSide level) → Fin (freeGridSide (level + 1)) :=
  fun i =>
    ⟨i.val + (freeGridSide level - 1), by
      rw [freeGridSide_succ]
      have hpos := freeGridSide_pos level
      have hi := i.isLt
      omega⟩

@[simp]
theorem freeGridLast_val (level : Nat) :
    (freeGridLast level).val = freeGridSide level - 1 :=
  rfl

@[simp]
theorem freeLineLeftEmbedding_val (level : Nat)
    (i : Fin (freeGridSide level)) :
    (freeLineLeftEmbedding level i).val = i.val :=
  rfl

@[simp]
theorem freeLineRightEmbedding_val (level : Nat)
    (i : Fin (freeGridSide level)) :
    (freeLineRightEmbedding level i).val =
      i.val + (freeGridSide level - 1) :=
  rfl

/--
The two recursive copies share exactly the old last/free-center index: the
right copy's first line is the left copy's last line.
-/
theorem freeLineEmbedding_overlap (level : Nat) :
    freeLineLeftEmbedding level (freeGridLast level) =
      freeLineRightEmbedding level ⟨0, freeGridSide_pos level⟩ := by
  apply Fin.ext
  simp [freeLineLeftEmbedding, freeLineRightEmbedding, freeGridLast]

/-- The left copy of free-line indices is injective. -/
theorem freeLineLeftEmbedding_injective (level : Nat) :
    Function.Injective (freeLineLeftEmbedding level) := by
  intro i j h
  apply Fin.ext
  simpa [freeLineLeftEmbedding] using congrArg Fin.val h

/-- The right copy of free-line indices is injective. -/
theorem freeLineRightEmbedding_injective (level : Nat) :
    Function.Injective (freeLineRightEmbedding level) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa [freeLineRightEmbedding] using hval

/--
The overlap between the two recursive copies is unique: it is the old last
index in the left copy and the old first index in the right copy.
-/
theorem freeLineEmbedding_eq_iff (level : Nat)
    (i j : Fin (freeGridSide level)) :
    freeLineLeftEmbedding level i = freeLineRightEmbedding level j ↔
      i = freeGridLast level ∧ j = ⟨0, freeGridSide_pos level⟩ := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    have hpos := freeGridSide_pos level
    have hi := i.isLt
    have hj := j.isLt
    constructor
    · apply Fin.ext
      simp [freeLineLeftEmbedding, freeLineRightEmbedding,
        freeGridLast] at hval ⊢
      omega
    · apply Fin.ext
      simp [freeLineLeftEmbedding, freeLineRightEmbedding] at hval
      change j.val = 0
      omega
  · rintro ⟨rfl, rfl⟩
    exact freeLineEmbedding_overlap level

/--
Every next-level virtual free-line index lies in the left copy, or in the
right copy, of the previous level's free-line indices. The shared line belongs
to both copies.
-/
theorem freeLineEmbedding_cover (level : Nat)
    (i : Fin (freeGridSide (level + 1))) :
    (∃ j : Fin (freeGridSide level), freeLineLeftEmbedding level j = i) ∨
      ∃ j : Fin (freeGridSide level), freeLineRightEmbedding level j = i := by
  by_cases hleft : i.val < freeGridSide level
  · left
    refine ⟨⟨i.val, hleft⟩, ?_⟩
    apply Fin.ext
    simp [freeLineLeftEmbedding]
  · right
    have hpos := freeGridSide_pos level
    have hnext : freeGridSide (level + 1) = 2 * freeGridSide level - 1 :=
      freeGridSide_succ level
    have hlt : i.val - (freeGridSide level - 1) < freeGridSide level := by
      have hi := i.isLt
      omega
    refine ⟨⟨i.val - (freeGridSide level - 1), hlt⟩, ?_⟩
    apply Fin.ext
    simp [freeLineRightEmbedding]
    omega

/-- Which recursive copy contains a next-level free-line index. -/
inductive FreeLineSide where
  | left
  | right
deriving DecidableEq, Repr

/--
Deterministic predecessor data for a next-level free-line index in Robinson's
overlapping recurrence.

The shared overlap line is assigned to the left copy; the symmetric overlap
identity is still available from `freeLineEmbedding_overlap` and
`freeLineEmbedding_eq_iff`.
-/
structure FreeLinePreimage (level : Nat)
    (i : Fin (freeGridSide (level + 1))) where
  side : FreeLineSide
  index : Fin (freeGridSide level)
  maps :
    match side with
    | .left => freeLineLeftEmbedding level index = i
    | .right => freeLineRightEmbedding level index = i

namespace FreeLinePreimage

/-- Reapply a predecessor to recover the original next-level index. -/
def child {level : Nat} {i : Fin (freeGridSide (level + 1))}
    (p : FreeLinePreimage level i) : Fin (freeGridSide (level + 1)) :=
  match p.side with
  | .left => freeLineLeftEmbedding level p.index
  | .right => freeLineRightEmbedding level p.index

@[simp]
theorem child_eq {level : Nat} {i : Fin (freeGridSide (level + 1))}
    (p : FreeLinePreimage level i) : p.child = i := by
  cases p with
  | mk side index maps =>
      cases side <;> exact maps

end FreeLinePreimage

/--
Canonical predecessor for a next-level free-line index.  Indices in the
left copy, including the overlap line, choose `.left`; the remaining indices
choose `.right`.
-/
def freeLinePreimage (level : Nat)
    (i : Fin (freeGridSide (level + 1))) :
    FreeLinePreimage level i := by
  by_cases hleft : i.val < freeGridSide level
  · exact
      { side := FreeLineSide.left
        index := ⟨i.val, hleft⟩
        maps := by
          apply Fin.ext
          simp [freeLineLeftEmbedding] }
  · have hpos := freeGridSide_pos level
    have hlt : i.val - (freeGridSide level - 1) < freeGridSide level := by
      have hi : i.val < 2 * freeGridSide level - 1 := by
        simpa [freeGridSide_succ] using i.isLt
      omega
    exact
      { side := FreeLineSide.right
        index := ⟨i.val - (freeGridSide level - 1), hlt⟩
        maps := by
          apply Fin.ext
          simp [freeLineRightEmbedding]
          omega }

@[simp]
theorem freeLinePreimage_child (level : Nat)
    (i : Fin (freeGridSide (level + 1))) :
    (freeLinePreimage level i).child = i :=
  FreeLinePreimage.child_eq (freeLinePreimage level i)

theorem freeLinePreimage_side_left_of_lt (level : Nat)
    (i : Fin (freeGridSide (level + 1)))
    (hleft : i.val < freeGridSide level) :
    (freeLinePreimage level i).side = FreeLineSide.left := by
  simp [freeLinePreimage, hleft]

theorem freeLinePreimage_side_right_of_not_lt (level : Nat)
    (i : Fin (freeGridSide (level + 1)))
    (hleft : ¬ i.val < freeGridSide level) :
    (freeLinePreimage level i).side = FreeLineSide.right := by
  simp [freeLinePreimage, hleft]

/--
Coordinate form of Robinson's free-line recurrence.

The next-level free-line coordinates are obtained from two translated copies
of the previous level's coordinates, overlapping at one line.  The actual
translation offsets are left abstract here; the geometric red-board proof is
responsible for supplying them.
-/
structure FreeLineCoordinateStep (level : Nat)
    (parent : Fin (freeGridSide level) → Int)
    (child : Fin (freeGridSide (level + 1)) → Int) : Type where
  leftOffset : Int
  rightOffset : Int
  left :
    ∀ i : Fin (freeGridSide level),
      child (freeLineLeftEmbedding level i) = parent i + leftOffset
  right :
    ∀ i : Fin (freeGridSide level),
      child (freeLineRightEmbedding level i) = parent i + rightOffset

namespace FreeLineCoordinateStep

/--
The two offsets agree at the unique overlap line after accounting for the
parent coordinates used by the two copies.
-/
theorem overlap
    {level : Nat}
    {parent : Fin (freeGridSide level) → Int}
    {child : Fin (freeGridSide (level + 1)) → Int}
    (step : FreeLineCoordinateStep level parent child) :
    parent (freeGridLast level) + step.leftOffset =
      parent ⟨0, freeGridSide_pos level⟩ + step.rightOffset := by
  calc
    parent (freeGridLast level) + step.leftOffset
        = child (freeLineLeftEmbedding level (freeGridLast level)) := by
          rw [step.left]
    _ = child (freeLineRightEmbedding level ⟨0, freeGridSide_pos level⟩) := by
          rw [freeLineEmbedding_overlap]
    _ = parent ⟨0, freeGridSide_pos level⟩ + step.rightOffset := by
          rw [step.right]

/-- Coordinate value of a child free line from its canonical predecessor. -/
theorem child_eq_preimage
    {level : Nat}
    {parent : Fin (freeGridSide level) → Int}
    {child : Fin (freeGridSide (level + 1)) → Int}
    (step : FreeLineCoordinateStep level parent child)
    (i : Fin (freeGridSide (level + 1))) :
    child i =
      match (freeLinePreimage level i).side with
      | .left =>
          parent (freeLinePreimage level i).index + step.leftOffset
      | .right =>
          parent (freeLinePreimage level i).index + step.rightOffset := by
  have hchild := FreeLinePreimage.child_eq (freeLinePreimage level i)
  cases hside : (freeLinePreimage level i).side
  · simp only [FreeLinePreimage.child, hside] at hchild
    change child i =
      parent (freeLinePreimage level i).index + step.leftOffset
    calc
      child i = child (freeLineLeftEmbedding level
          (freeLinePreimage level i).index) := by rw [hchild]
      _ = parent (freeLinePreimage level i).index + step.leftOffset :=
          step.left (freeLinePreimage level i).index
  · simp only [FreeLinePreimage.child, hside] at hchild
    change child i =
      parent (freeLinePreimage level i).index + step.rightOffset
    calc
      child i = child (freeLineRightEmbedding level
          (freeLinePreimage level i).index) := by rw [hchild]
      _ = parent (freeLinePreimage level i).index + step.rightOffset :=
          step.right (freeLinePreimage level i).index

end FreeLineCoordinateStep

end RobinsonSquare

/--
Adjacent-coordinate specialization of the Robinson-board free-grid obligation.

This is useful if a later geometric proof extracts a literal adjacent block of
active Figure 18 sites.  Robinson's board argument more naturally gives routed
coordinates, so `Figure18RobinsonBoardRoutedFreeGrid` below is the preferred
target for the Section 7 proof.
-/
structure Figure18RobinsonBoardAdjacentFreeGrid
    (table : Figure18RoleTable)
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) : Type where
  freeColumnCoord : Fin n → Int
  freeRowCoord : Fin n → Int
  freeColumnCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    freeColumnCoord ⟨i.val + 1, hi⟩ = freeColumnCoord i + 1
  freeRowCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    freeRowCoord ⟨j.val + 1, hj⟩ = freeRowCoord j + 1
  freeCrossingRole : ∀ i : Fin n, ∀ j : Fin n,
    table.combinedSite
      (x (freeColumnCoord i, freeRowCoord j)) = cornerSite ∨
    table.combinedSite
      (x (freeColumnCoord i, freeRowCoord j)) ∈ activeSites
  lowerLeftCorner : table.combinedSite
      (x (freeColumnCoord ⟨0, hn⟩, freeRowCoord ⟨0, hn⟩)) =
      cornerSite

namespace Figure18RobinsonBoardAdjacentFreeGrid

/--
Forget the Robinson-board terminology once the free-grid coordinates have been
selected; the abstract scaffold reduction only needs the listed-active window.
-/
def toListedActiveSiteFixedCornerSquare
    {table : Figure18RoleTable}
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (grid :
      Figure18RobinsonBoardAdjacentFreeGrid
        table activeSites cornerSite x n hn) :
    Figure18ListedActiveSiteFixedCornerSquare
      table activeSites cornerSite x n hn where
  horizontalCoord := grid.freeColumnCoord
  verticalCoord := grid.freeRowCoord
  horizontalCoord_succ := grid.freeColumnCoord_succ
  verticalCoord_succ := grid.freeRowCoord_succ
  listedActive := grid.freeCrossingRole
  corner := grid.lowerLeftCorner

end Figure18RobinsonBoardAdjacentFreeGrid

/--
Adjacent-coordinate Robinson-board/free-grid version of the concrete Figure 18
invariant.
-/
def HasFigure18RobinsonBoardAdjacentFreeGrids
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18RobinsonBoardAdjacentFreeGrid
          (Figure18RoleTable.FlatRoleTable.ofActiveSites
            activeSites cornerSite).toRoleTable
          activeSites cornerSite x n hn)

theorem hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_robinsonBoardAdjacentFreeGrids
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hgrids :
      HasFigure18RobinsonBoardAdjacentFreeGrids activeSites cornerSite) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindows
      activeSites cornerSite := by
  intro T seed x hx n hn
  rcases hgrids x hx n hn with ⟨grid⟩
  exact ⟨grid.toListedActiveSiteFixedCornerSquare⟩

/--
Routed Robinson-board form of the Figure 18 forcing obligation.

Robinson's proof uses red borders to define boards and obstruction signals to
single out the free rows and columns.  Those free rows and columns are not
usually adjacent in the ambient plane; the board instead transmits payload
signals through the intervening scaffold cells.  This structure records the
selected free crossings, their decoded Figure 18 sites, and the routed payload
edge matches needed by `Figure18IndexedRoutedFixedCornerSquare`.
-/
structure Figure18RobinsonBoardRoutedFreeGrid
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) : Type where
  freeColumnCoord : Fin n → Int
  freeRowCoord : Fin n → Int
  siteRect : Fin n → Fin n → Figure18Site
  payloadRect : Rectangle n n
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, hn⟩ ⟨0, hn⟩ = table.cornerSite
  product : ∀ i : Fin n, ∀ j : Fin n,
    WangTile.product (siteRect i j).tile (payloadRect i j) =
      (x (freeColumnCoord i, freeRowCoord j)).1
  hmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    WangTile.HMatches (payloadRect i j) (payloadRect ⟨i.val + 1, hi⟩ j)
  vmatch : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    WangTile.VMatches (payloadRect i j) (payloadRect i ⟨j.val + 1, hj⟩)

namespace Figure18RobinsonBoardRoutedFreeGrid

/--
Finite Figure 18 site compatibility of neighboring virtual payload cells in a
routed Robinson free grid.
-/
def SiteCompatible
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x n hn) :
    Prop :=
  (∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    Figure18Site.hCompatible
      (grid.siteRect i j) (grid.siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
  (∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    Figure18Site.vCompatible
      (grid.siteRect i j) (grid.siteRect i ⟨j.val + 1, hj⟩) = true)

/-- Forget the board terminology after the routed free-grid data is selected. -/
def toIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x n hn) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn :=
  Figure18IndexedRoutedFixedCornerSquare.ofSiteMatches hn
    grid.freeColumnCoord
    grid.freeRowCoord
    grid.siteRect
    grid.payloadRect
    grid.active
    grid.cornerSite
    grid.product
    grid.hmatch
    grid.vmatch

/-- A routed Robinson free grid directly yields the extracted payload square. -/
theorem tileable
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x n hn) :
    TileableFixedCornerSquare T seed n :=
  grid.toIndexedRoutedFixedCornerSquare.tileable

/-- Restrict a routed free grid to its lower-left `n × n` subgrid. -/
def restrict
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n m : Nat} {hm : 0 < m} (hn : 0 < n) (hcap : n ≤ m)
    (grid : Figure18RobinsonBoardRoutedFreeGrid table x m hm) :
    Figure18RobinsonBoardRoutedFreeGrid table x n hn where
  freeColumnCoord := fun i => grid.freeColumnCoord (Fin.castLE hcap i)
  freeRowCoord := fun j => grid.freeRowCoord (Fin.castLE hcap j)
  siteRect := fun i j =>
    grid.siteRect (Fin.castLE hcap i) (Fin.castLE hcap j)
  payloadRect := fun i j =>
    grid.payloadRect (Fin.castLE hcap i) (Fin.castLE hcap j)
  active := by
    intro i j
    exact grid.active (Fin.castLE hcap i) (Fin.castLE hcap j)
  cornerSite := by
    simpa [Fin.castLE] using grid.cornerSite
  product := by
    intro i j
    exact grid.product (Fin.castLE hcap i) (Fin.castLE hcap j)
  hmatch := by
    intro i j hi
    have hiBig : (Fin.castLE hcap i).val + 1 < m :=
      Nat.lt_of_lt_of_le hi hcap
    simpa [Fin.castLE] using
      grid.hmatch (Fin.castLE hcap i) (Fin.castLE hcap j) hiBig
  vmatch := by
    intro i j hj
    have hjBig : (Fin.castLE hcap j).val + 1 < m :=
      Nat.lt_of_lt_of_le hj hcap
    simpa [Fin.castLE] using
      grid.vmatch (Fin.castLE hcap i) (Fin.castLE hcap j) hjBig

/-- Local site compatibility is inherited by lower-left restrictions. -/
theorem SiteCompatible.restrict
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {n m : Nat} {hm : 0 < m}
    {grid : Figure18RobinsonBoardRoutedFreeGrid table x m hm}
    (hsite : grid.SiteCompatible) (hn : 0 < n) (hcap : n ≤ m) :
    (grid.restrict hn hcap).SiteCompatible := by
  rcases hsite with ⟨hh, hv⟩
  constructor
  · intro i j hi
    have hiBig : (Fin.castLE hcap i).val + 1 < m :=
      Nat.lt_of_lt_of_le hi hcap
    change Figure18Site.hCompatible
        (grid.siteRect (Fin.castLE hcap i) (Fin.castLE hcap j))
        (grid.siteRect (Fin.castLE hcap ⟨i.val + 1, hi⟩)
          (Fin.castLE hcap j)) = true
    simpa [Fin.castLE] using
      hh (Fin.castLE hcap i) (Fin.castLE hcap j) hiBig
  · intro i j hj
    have hjBig : (Fin.castLE hcap j).val + 1 < m :=
      Nat.lt_of_lt_of_le hj hcap
    change Figure18Site.vCompatible
        (grid.siteRect (Fin.castLE hcap i) (Fin.castLE hcap j))
        (grid.siteRect (Fin.castLE hcap i)
          (Fin.castLE hcap ⟨j.val + 1, hj⟩)) = true
    simpa [Fin.castLE] using
      hv (Fin.castLE hcap i) (Fin.castLE hcap j) hjBig

end Figure18RobinsonBoardRoutedFreeGrid

/--
Robinson Section 7 board geometry at one red-board level.

This is the obstruction-only part of the argument: the free rows and columns
are enumerated, lie on the board, and are exactly the board rows/columns with no
obstruction signal crossing them.  It deliberately does not mention Figure 18
sites, payload tiles, or combined tilings.
-/
structure RobinsonBoardSignalGeometry (level : Nat) : Type where
  freeColumnCoord :
    Fin (RobinsonSquare.freeGridSide level) → Int
  freeRowCoord :
    Fin (RobinsonSquare.freeGridSide level) → Int
  isBoardColumn : Int → Prop
  isBoardRow : Int → Prop
  isFreeColumn : Int → Prop
  isFreeRow : Int → Prop
  hasHorizontalObstruction : Int → Int → Prop
  hasVerticalObstruction : Int → Int → Prop
  freeRow_iff_noHorizontalObstruction :
    ∀ y : Int, isBoardRow y →
      (isFreeRow y ↔
        ∀ x : Int, isBoardColumn x → ¬ hasHorizontalObstruction x y)
  freeColumn_iff_noVerticalObstruction :
    ∀ x : Int, isBoardColumn x →
      (isFreeColumn x ↔
        ∀ y : Int, isBoardRow y → ¬ hasVerticalObstruction x y)
  freeColumnCoord_board :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      isBoardColumn (freeColumnCoord i)
  freeRowCoord_board :
    ∀ j : Fin (RobinsonSquare.freeGridSide level),
      isBoardRow (freeRowCoord j)
  freeColumnCoord_free :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      isFreeColumn (freeColumnCoord i)
  freeRowCoord_free :
    ∀ j : Fin (RobinsonSquare.freeGridSide level),
      isFreeRow (freeRowCoord j)
  freeColumnCoord_complete :
    ∀ x : Int, isFreeColumn x →
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        freeColumnCoord i = x
  freeRowCoord_complete :
    ∀ y : Int, isFreeRow y →
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        freeRowCoord j = y
  freeColumnCoord_injective :
    Function.Injective freeColumnCoord
  freeRowCoord_injective :
    Function.Injective freeRowCoord

namespace RobinsonBoardSignalGeometry

/-- A board coordinate pair lying at the intersection of a free column and row. -/
def IsFreeCrossing {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) (column row : Int) : Prop :=
  geometry.isFreeColumn column ∧ geometry.isFreeRow row

/--
A board coordinate pair whose full column and row carry no obstruction signal.

This is Robinson's obstruction-signal description of a free crossing: the
predicate is phrased in terms of the signals emitted and absorbed by borders,
rather than in terms of the already-enumerated free rows and columns.
-/
def IsClearCrossing {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) (column row : Int) : Prop :=
  geometry.isBoardColumn column ∧ geometry.isBoardRow row ∧
    (∀ y : Int, geometry.isBoardRow y →
      ¬ geometry.hasVerticalObstruction column y) ∧
    (∀ x : Int, geometry.isBoardColumn x →
      ¬ geometry.hasHorizontalObstruction x row)

/-- The free columns are exactly the columns enumerated by the geometry. -/
theorem isFreeColumn_iff_exists_freeColumnCoord
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (column : Int) :
    geometry.isFreeColumn column ↔
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        geometry.freeColumnCoord i = column := by
  constructor
  · exact geometry.freeColumnCoord_complete column
  · rintro ⟨i, rfl⟩
    exact geometry.freeColumnCoord_free i

/-- The free rows are exactly the rows enumerated by the geometry. -/
theorem isFreeRow_iff_exists_freeRowCoord
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (row : Int) :
    geometry.isFreeRow row ↔
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        geometry.freeRowCoord j = row := by
  constructor
  · exact geometry.freeRowCoord_complete row
  · rintro ⟨j, rfl⟩
    exact geometry.freeRowCoord_free j

/-- Free crossings are exactly products of the enumerated free columns and rows. -/
theorem isFreeCrossing_iff_exists_freeCoords
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (column row : Int) :
    geometry.IsFreeCrossing column row ↔
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        ∃ j : Fin (RobinsonSquare.freeGridSide level),
          geometry.freeColumnCoord i = column ∧
            geometry.freeRowCoord j = row := by
  constructor
  · rintro ⟨hcolumnFree, hrowFree⟩
    rcases geometry.freeColumnCoord_complete column hcolumnFree with
      ⟨i, hcolumn⟩
    rcases geometry.freeRowCoord_complete row hrowFree with ⟨j, hrow⟩
    exact ⟨i, j, hcolumn, hrow⟩
  · rintro ⟨i, j, hcolumn, hrow⟩
    exact ⟨hcolumn ▸ geometry.freeColumnCoord_free i,
      hrow ▸ geometry.freeRowCoord_free j⟩

/--
A board coordinate pair is a free crossing exactly when its whole column has no
vertical obstruction and its whole row has no horizontal obstruction.
-/
theorem isFreeCrossing_iff_clearLines
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column row : Int}
    (hcolumn : geometry.isBoardColumn column)
    (hrow : geometry.isBoardRow row) :
    geometry.IsFreeCrossing column row ↔
      (∀ y : Int, geometry.isBoardRow y →
        ¬ geometry.hasVerticalObstruction column y) ∧
      (∀ x : Int, geometry.isBoardColumn x →
        ¬ geometry.hasHorizontalObstruction x row) := by
  constructor
  · rintro ⟨hcolumnFree, hrowFree⟩
    exact ⟨
      (geometry.freeColumn_iff_noVerticalObstruction column hcolumn).1
        hcolumnFree,
      (geometry.freeRow_iff_noHorizontalObstruction row hrow).1 hrowFree⟩
  · rintro ⟨hclearColumn, hclearRow⟩
    exact ⟨
      (geometry.freeColumn_iff_noVerticalObstruction column hcolumn).2
        hclearColumn,
      (geometry.freeRow_iff_noHorizontalObstruction row hrow).2 hclearRow⟩

/-- Every free column is a board column. -/
theorem isBoardColumn_of_isFreeColumn
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column : Int} (hfree : geometry.isFreeColumn column) :
    geometry.isBoardColumn column := by
  rcases geometry.freeColumnCoord_complete column hfree with ⟨i, hcoord⟩
  rw [← hcoord]
  exact geometry.freeColumnCoord_board i

/-- Every free row is a board row. -/
theorem isBoardRow_of_isFreeRow
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {row : Int} (hfree : geometry.isFreeRow row) :
    geometry.isBoardRow row := by
  rcases geometry.freeRowCoord_complete row hfree with ⟨j, hcoord⟩
  rw [← hcoord]
  exact geometry.freeRowCoord_board j

/--
Robinson's obstruction-signal predicate is equivalent to the enumerated free
crossing predicate.
-/
theorem isClearCrossing_iff_isFreeCrossing
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (column row : Int) :
    geometry.IsClearCrossing column row ↔
      geometry.IsFreeCrossing column row := by
  constructor
  · intro hclear
    exact (geometry.isFreeCrossing_iff_clearLines hclear.1 hclear.2.1).2
      ⟨hclear.2.2.1, hclear.2.2.2⟩
  · intro hfree
    have hcolumn := geometry.isBoardColumn_of_isFreeColumn hfree.1
    have hrow := geometry.isBoardRow_of_isFreeRow hfree.2
    have hclear := (geometry.isFreeCrossing_iff_clearLines hcolumn hrow).1 hfree
    exact ⟨hcolumn, hrow, hclear.1, hclear.2⟩

/--
Robinson's obstruction-signal characterization, in enumerated-grid form:
inside a board, a coordinate pair is represented in the free grid exactly when
its full column and row carry no obstruction signal.
-/
theorem exists_freeCoords_iff_clearLines
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column row : Int}
    (hcolumn : geometry.isBoardColumn column)
    (hrow : geometry.isBoardRow row) :
    (∃ i : Fin (RobinsonSquare.freeGridSide level),
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        geometry.freeColumnCoord i = column ∧
          geometry.freeRowCoord j = row) ↔
      (∀ y : Int, geometry.isBoardRow y →
        ¬ geometry.hasVerticalObstruction column y) ∧
      (∀ x : Int, geometry.isBoardColumn x →
        ¬ geometry.hasHorizontalObstruction x row) := by
  rw [← geometry.isFreeCrossing_iff_exists_freeCoords column row]
  exact geometry.isFreeCrossing_iff_clearLines hcolumn hrow

/-- Enumerated free-column/free-row coordinates form free crossings. -/
theorem isFreeCrossing_freeCoord
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    geometry.IsFreeCrossing
      (geometry.freeColumnCoord i) (geometry.freeRowCoord j) :=
  ⟨geometry.freeColumnCoord_free i, geometry.freeRowCoord_free j⟩

/-- Any free crossing has no obstruction signal through the crossing cell. -/
theorem noObstruction_of_isFreeCrossing
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column row : Int}
    (hcolumn : geometry.isBoardColumn column)
    (hrow : geometry.isBoardRow row)
    (hcross : geometry.IsFreeCrossing column row) :
    (¬ geometry.hasHorizontalObstruction column row) ∧
      ¬ geometry.hasVerticalObstruction column row := by
  have hclear := (geometry.isFreeCrossing_iff_clearLines
    hcolumn hrow).1 hcross
  exact ⟨hclear.2 column hcolumn, hclear.1 row hrow⟩

/-- A selected free row has no horizontal obstruction at any board column. -/
theorem noHorizontalObstruction_of_freeRowCoord
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (column : Int) (hcolumn : geometry.isBoardColumn column)
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    ¬ geometry.hasHorizontalObstruction column
      (geometry.freeRowCoord j) := by
  have hrow := geometry.freeRow_iff_noHorizontalObstruction
    (geometry.freeRowCoord j) (geometry.freeRowCoord_board j)
  exact (hrow.1 (geometry.freeRowCoord_free j)) column hcolumn

/-- A selected free column has no vertical obstruction at any board row. -/
theorem noVerticalObstruction_of_freeColumnCoord
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (row : Int) (hrow : geometry.isBoardRow row) :
    ¬ geometry.hasVerticalObstruction
      (geometry.freeColumnCoord i) row := by
  have hcolumn := geometry.freeColumn_iff_noVerticalObstruction
    (geometry.freeColumnCoord i) (geometry.freeColumnCoord_board i)
  exact (hcolumn.1 (geometry.freeColumnCoord_free i)) row hrow

/-- A horizontal obstruction through a board row prevents that row from being free. -/
theorem not_freeRow_of_horizontalObstruction
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column row : Int}
    (hrow : geometry.isBoardRow row)
    (hcolumn : geometry.isBoardColumn column)
    (hobs : geometry.hasHorizontalObstruction column row) :
    ¬ geometry.isFreeRow row := by
  intro hfree
  exact (geometry.freeRow_iff_noHorizontalObstruction row hrow).1 hfree
    column hcolumn hobs

/-- A vertical obstruction through a board column prevents that column from being free. -/
theorem not_freeColumn_of_verticalObstruction
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column row : Int}
    (hcolumn : geometry.isBoardColumn column)
    (hrow : geometry.isBoardRow row)
    (hobs : geometry.hasVerticalObstruction column row) :
    ¬ geometry.isFreeColumn column := by
  intro hfree
  exact (geometry.freeColumn_iff_noVerticalObstruction column hcolumn).1
    hfree row hrow hobs

/-- Every non-free board row has a horizontal obstruction at some board column. -/
theorem exists_horizontalObstruction_of_boardRow_not_free
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {row : Int}
    (hrow : geometry.isBoardRow row)
    (hnotFree : ¬ geometry.isFreeRow row) :
    ∃ column : Int,
      geometry.isBoardColumn column ∧
        geometry.hasHorizontalObstruction column row := by
  by_contra hnone
  apply hnotFree
  refine (geometry.freeRow_iff_noHorizontalObstruction row hrow).2 ?_
  intro column hcolumn hobs
  exact hnone ⟨column, hcolumn, hobs⟩

/-- Every non-free board column has a vertical obstruction at some board row. -/
theorem exists_verticalObstruction_of_boardColumn_not_free
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    {column : Int}
    (hcolumn : geometry.isBoardColumn column)
    (hnotFree : ¬ geometry.isFreeColumn column) :
    ∃ row : Int,
      geometry.isBoardRow row ∧
        geometry.hasVerticalObstruction column row := by
  by_contra hnone
  apply hnotFree
  refine (geometry.freeColumn_iff_noVerticalObstruction column hcolumn).2 ?_
  intro row hrow hobs
  exact hnone ⟨row, hrow, hobs⟩

/--
At a selected free-row/free-column crossing, neither obstruction signal is
present.
-/
theorem noObstruction_at_freeCrossing
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (¬ geometry.hasHorizontalObstruction
        (geometry.freeColumnCoord i) (geometry.freeRowCoord j)) ∧
      ¬ geometry.hasVerticalObstruction
        (geometry.freeColumnCoord i) (geometry.freeRowCoord j) := by
  constructor
  · exact geometry.noHorizontalObstruction_of_freeRowCoord
      (geometry.freeColumnCoord i) (geometry.freeColumnCoord_board i) j
  · exact geometry.noVerticalObstruction_of_freeColumnCoord
      i (geometry.freeRowCoord j) (geometry.freeRowCoord_board j)

/--
The free columns selected by a Robinson board geometry are exactly the finite
index set of size `freeGridSide level`.
-/
noncomputable def freeColumnEquivFin
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { column : Int // geometry.isFreeColumn column } ≃
      Fin (RobinsonSquare.freeGridSide level) where
  toFun column :=
    Classical.choose
      (geometry.freeColumnCoord_complete column.1 column.2)
  invFun i :=
    ⟨geometry.freeColumnCoord i, geometry.freeColumnCoord_free i⟩
  left_inv column := by
    apply Subtype.ext
    exact Classical.choose_spec
      (geometry.freeColumnCoord_complete column.1 column.2)
  right_inv i := by
    apply geometry.freeColumnCoord_injective
    exact Classical.choose_spec
      (geometry.freeColumnCoord_complete
        (geometry.freeColumnCoord i) (geometry.freeColumnCoord_free i))

/--
The free rows selected by a Robinson board geometry are exactly the finite index
set of size `freeGridSide level`.
-/
noncomputable def freeRowEquivFin
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { row : Int // geometry.isFreeRow row } ≃
      Fin (RobinsonSquare.freeGridSide level) where
  toFun row :=
    Classical.choose
      (geometry.freeRowCoord_complete row.1 row.2)
  invFun j :=
    ⟨geometry.freeRowCoord j, geometry.freeRowCoord_free j⟩
  left_inv row := by
    apply Subtype.ext
    exact Classical.choose_spec
      (geometry.freeRowCoord_complete row.1 row.2)
  right_inv j := by
    apply geometry.freeRowCoord_injective
    exact Classical.choose_spec
      (geometry.freeRowCoord_complete
        (geometry.freeRowCoord j) (geometry.freeRowCoord_free j))

/--
Robinson's horizontal obstruction criterion selects exactly `freeGridSide level`
unobstructed board rows.
-/
noncomputable def unobstructedRowEquivFin
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { row : Int //
        geometry.isBoardRow row ∧
          ∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column row } ≃
      Fin (RobinsonSquare.freeGridSide level) where
  toFun row :=
    Classical.choose
      (geometry.freeRowCoord_complete row.1
        ((geometry.freeRow_iff_noHorizontalObstruction
          row.1 row.2.1).2 row.2.2))
  invFun j :=
    ⟨geometry.freeRowCoord j,
      geometry.freeRowCoord_board j,
      fun column hcolumn =>
        geometry.noHorizontalObstruction_of_freeRowCoord column hcolumn j⟩
  left_inv row := by
    apply Subtype.ext
    exact Classical.choose_spec
      (geometry.freeRowCoord_complete row.1
        ((geometry.freeRow_iff_noHorizontalObstruction
          row.1 row.2.1).2 row.2.2))
  right_inv j := by
    apply geometry.freeRowCoord_injective
    exact Classical.choose_spec
      (geometry.freeRowCoord_complete
        (geometry.freeRowCoord j)
        ((geometry.freeRow_iff_noHorizontalObstruction
          (geometry.freeRowCoord j) (geometry.freeRowCoord_board j)).2
          (fun column hcolumn =>
            geometry.noHorizontalObstruction_of_freeRowCoord column hcolumn j)))

/--
Robinson's vertical obstruction criterion selects exactly `freeGridSide level`
unobstructed board columns.
-/
noncomputable def unobstructedColumnEquivFin
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { column : Int //
        geometry.isBoardColumn column ∧
          ∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction column row } ≃
      Fin (RobinsonSquare.freeGridSide level) where
  toFun column :=
    Classical.choose
      (geometry.freeColumnCoord_complete column.1
        ((geometry.freeColumn_iff_noVerticalObstruction
          column.1 column.2.1).2 column.2.2))
  invFun i :=
    ⟨geometry.freeColumnCoord i,
      geometry.freeColumnCoord_board i,
      fun row hrow =>
        geometry.noVerticalObstruction_of_freeColumnCoord i row hrow⟩
  left_inv column := by
    apply Subtype.ext
    exact Classical.choose_spec
      (geometry.freeColumnCoord_complete column.1
        ((geometry.freeColumn_iff_noVerticalObstruction
          column.1 column.2.1).2 column.2.2))
  right_inv i := by
    apply geometry.freeColumnCoord_injective
    exact Classical.choose_spec
      (geometry.freeColumnCoord_complete
        (geometry.freeColumnCoord i)
        ((geometry.freeColumn_iff_noVerticalObstruction
          (geometry.freeColumnCoord i) (geometry.freeColumnCoord_board i)).2
          (fun row hrow =>
            geometry.noVerticalObstruction_of_freeColumnCoord i row hrow)))

@[reducible]
noncomputable def freeColumnFintype
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    Fintype { column : Int // geometry.isFreeColumn column } :=
  Fintype.ofEquiv (Fin (RobinsonSquare.freeGridSide level))
    (geometry.freeColumnEquivFin.symm)

@[reducible]
noncomputable def freeRowFintype
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    Fintype { row : Int // geometry.isFreeRow row } :=
  Fintype.ofEquiv (Fin (RobinsonSquare.freeGridSide level))
    (geometry.freeRowEquivFin.symm)

@[reducible]
noncomputable def unobstructedRowFintype
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    Fintype
      { row : Int //
        geometry.isBoardRow row ∧
          ∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column row } :=
  Fintype.ofEquiv (Fin (RobinsonSquare.freeGridSide level))
    (geometry.unobstructedRowEquivFin.symm)

@[reducible]
noncomputable def unobstructedColumnFintype
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    Fintype
      { column : Int //
        geometry.isBoardColumn column ∧
          ∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction column row } :=
  Fintype.ofEquiv (Fin (RobinsonSquare.freeGridSide level))
    (geometry.unobstructedColumnEquivFin.symm)

/--
Robinson's Section 7 count: the free columns of a level-`n` board form a
finite set of size `freeGridSide n`.
-/
theorem freeColumn_card_eq_freeGridSide
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { column : Int // geometry.isFreeColumn column }
      (geometry.freeColumnFintype) = RobinsonSquare.freeGridSide level := by
  letI := geometry.freeColumnFintype
  rw [← Fintype.card_fin (RobinsonSquare.freeGridSide level)]
  exact Fintype.card_congr (geometry.freeColumnEquivFin)

/--
Robinson's Section 7 count: the free rows of a level-`n` board form a finite
set of size `freeGridSide n`.
-/
theorem freeRow_card_eq_freeGridSide
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { row : Int // geometry.isFreeRow row }
      (geometry.freeRowFintype) = RobinsonSquare.freeGridSide level := by
  letI := geometry.freeRowFintype
  rw [← Fintype.card_fin (RobinsonSquare.freeGridSide level)]
  exact Fintype.card_congr (geometry.freeRowEquivFin)

/--
Robinson's obstruction criterion selects exactly `freeGridSide n`
unobstructed board rows.
-/
theorem unobstructedRow_card_eq_freeGridSide
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card
      { row : Int //
        geometry.isBoardRow row ∧
          ∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column row }
      (geometry.unobstructedRowFintype) = RobinsonSquare.freeGridSide level := by
  letI := geometry.unobstructedRowFintype
  rw [← Fintype.card_fin (RobinsonSquare.freeGridSide level)]
  exact Fintype.card_congr (geometry.unobstructedRowEquivFin)

/--
Robinson's obstruction criterion selects exactly `freeGridSide n`
unobstructed board columns.
-/
theorem unobstructedColumn_card_eq_freeGridSide
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card
      { column : Int //
        geometry.isBoardColumn column ∧
          ∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction column row }
      (geometry.unobstructedColumnFintype) =
        RobinsonSquare.freeGridSide level := by
  letI := geometry.unobstructedColumnFintype
  rw [← Fintype.card_fin (RobinsonSquare.freeGridSide level)]
  exact Fintype.card_congr (geometry.unobstructedColumnEquivFin)

theorem freeColumn_card_eq_two_pow_add_one
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { column : Int // geometry.isFreeColumn column }
      (geometry.freeColumnFintype) = 2 ^ level + 1 := by
  rw [geometry.freeColumn_card_eq_freeGridSide,
    RobinsonSquare.freeGridSide_eq_two_pow_add_one]

theorem freeRow_card_eq_two_pow_add_one
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { row : Int // geometry.isFreeRow row }
      (geometry.freeRowFintype) = 2 ^ level + 1 := by
  rw [geometry.freeRow_card_eq_freeGridSide,
    RobinsonSquare.freeGridSide_eq_two_pow_add_one]

theorem unobstructedRow_card_eq_two_pow_add_one
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card
      { row : Int //
        geometry.isBoardRow row ∧
          ∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column row }
      (geometry.unobstructedRowFintype) = 2 ^ level + 1 := by
  rw [geometry.unobstructedRow_card_eq_freeGridSide,
    RobinsonSquare.freeGridSide_eq_two_pow_add_one]

theorem unobstructedColumn_card_eq_two_pow_add_one
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card
      { column : Int //
        geometry.isBoardColumn column ∧
          ∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction column row }
      (geometry.unobstructedColumnFintype) = 2 ^ level + 1 := by
  rw [geometry.unobstructedColumn_card_eq_freeGridSide,
    RobinsonSquare.freeGridSide_eq_two_pow_add_one]

/--
Free crossings form the product of the enumerated free columns and free rows.
This is the finite-set version of Robinson's statement that the selected board
lines act as a contiguous square.
-/
noncomputable def freeCrossingEquivFinProd
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { p : Int × Int // geometry.IsFreeCrossing p.1 p.2 } ≃
      Fin (RobinsonSquare.freeGridSide level) ×
        Fin (RobinsonSquare.freeGridSide level) where
  toFun p :=
    (geometry.freeColumnEquivFin ⟨p.1.1, p.2.1⟩,
      geometry.freeRowEquivFin ⟨p.1.2, p.2.2⟩)
  invFun ij :=
    ⟨(geometry.freeColumnCoord ij.1, geometry.freeRowCoord ij.2),
      geometry.isFreeCrossing_freeCoord ij.1 ij.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have h := geometry.freeColumnEquivFin.left_inv ⟨p.1.1, p.2.1⟩
      exact congrArg Subtype.val h
    · have h := geometry.freeRowEquivFin.left_inv ⟨p.1.2, p.2.2⟩
      exact congrArg Subtype.val h
  right_inv ij := by
    apply Prod.ext
    · exact geometry.freeColumnEquivFin.right_inv ij.1
    · exact geometry.freeRowEquivFin.right_inv ij.2

@[reducible]
noncomputable def freeCrossingFintype
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    Fintype { p : Int × Int // geometry.IsFreeCrossing p.1 p.2 } :=
  Fintype.ofEquiv
    (Fin (RobinsonSquare.freeGridSide level) ×
      Fin (RobinsonSquare.freeGridSide level))
    (geometry.freeCrossingEquivFinProd.symm)

theorem freeCrossing_card_eq_freeGridSide_mul_freeGridSide
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { p : Int × Int // geometry.IsFreeCrossing p.1 p.2 }
      (geometry.freeCrossingFintype) =
        RobinsonSquare.freeGridSide level *
          RobinsonSquare.freeGridSide level := by
  letI := geometry.freeCrossingFintype
  have h := Fintype.card_congr (geometry.freeCrossingEquivFinProd)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

theorem freeCrossing_card_eq_two_pow_add_one_mul
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { p : Int × Int // geometry.IsFreeCrossing p.1 p.2 }
      (geometry.freeCrossingFintype) =
        (2 ^ level + 1) * (2 ^ level + 1) := by
  rw [geometry.freeCrossing_card_eq_freeGridSide_mul_freeGridSide,
    RobinsonSquare.freeGridSide_eq_two_pow_add_one]

/-- Clear crossings and free crossings are the same finite subtype. -/
noncomputable def clearCrossingEquivFreeCrossing
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { p : Int × Int // geometry.IsClearCrossing p.1 p.2 } ≃
      { p : Int × Int // geometry.IsFreeCrossing p.1 p.2 } where
  toFun p :=
    ⟨p.1, (geometry.isClearCrossing_iff_isFreeCrossing p.1.1 p.1.2).1 p.2⟩
  invFun p :=
    ⟨p.1, (geometry.isClearCrossing_iff_isFreeCrossing p.1.1 p.1.2).2 p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
The obstruction-defined clear crossings form the same virtual square as the
enumerated free rows and columns.
-/
noncomputable def clearCrossingEquivFinProd
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    { p : Int × Int // geometry.IsClearCrossing p.1 p.2 } ≃
      Fin (RobinsonSquare.freeGridSide level) ×
        Fin (RobinsonSquare.freeGridSide level) :=
  (geometry.clearCrossingEquivFreeCrossing).trans
    geometry.freeCrossingEquivFinProd

@[reducible]
noncomputable def clearCrossingFintype
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    Fintype { p : Int × Int // geometry.IsClearCrossing p.1 p.2 } :=
  Fintype.ofEquiv
    (Fin (RobinsonSquare.freeGridSide level) ×
      Fin (RobinsonSquare.freeGridSide level))
    (geometry.clearCrossingEquivFinProd.symm)

theorem clearCrossing_card_eq_freeGridSide_mul_freeGridSide
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { p : Int × Int // geometry.IsClearCrossing p.1 p.2 }
      (geometry.clearCrossingFintype) =
        RobinsonSquare.freeGridSide level *
          RobinsonSquare.freeGridSide level := by
  letI := geometry.clearCrossingFintype
  have h := Fintype.card_congr (geometry.clearCrossingEquivFinProd)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

theorem clearCrossing_card_eq_two_pow_add_one_mul
    {level : Nat} (geometry : RobinsonBoardSignalGeometry level) :
    @Fintype.card { p : Int × Int // geometry.IsClearCrossing p.1 p.2 }
      (geometry.clearCrossingFintype) =
        (2 ^ level + 1) * (2 ^ level + 1) := by
  rw [geometry.clearCrossing_card_eq_freeGridSide_mul_freeGridSide,
    RobinsonSquare.freeGridSide_eq_two_pow_add_one]

/-- Column-coordinate recurrence between consecutive Robinson board geometries. -/
def ColumnCoordinateStep
    {level : Nat}
    (parent : RobinsonBoardSignalGeometry level)
    (child : RobinsonBoardSignalGeometry (level + 1)) :
    Type :=
  RobinsonSquare.FreeLineCoordinateStep level
    parent.freeColumnCoord child.freeColumnCoord

/-- Row-coordinate recurrence between consecutive Robinson board geometries. -/
def RowCoordinateStep
    {level : Nat}
    (parent : RobinsonBoardSignalGeometry level)
    (child : RobinsonBoardSignalGeometry (level + 1)) :
    Type :=
  RobinsonSquare.FreeLineCoordinateStep level
    parent.freeRowCoord child.freeRowCoord

/--
Both coordinate recurrences for the next-level Robinson board geometry.
-/
structure CoordinateStep
    {level : Nat}
    (parent : RobinsonBoardSignalGeometry level)
    (child : RobinsonBoardSignalGeometry (level + 1)) :
    Type where
  columns : ColumnCoordinateStep parent child
  rows : RowCoordinateStep parent child

/-- Column-coordinate overlap forced by the free-line recurrence. -/
theorem columnCoordinateStep_overlap
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : ColumnCoordinateStep parent child) :
    parent.freeColumnCoord (RobinsonSquare.freeGridLast level) +
        step.leftOffset =
      parent.freeColumnCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.overlap step

/-- Row-coordinate overlap forced by the free-line recurrence. -/
theorem rowCoordinateStep_overlap
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : RowCoordinateStep parent child) :
    parent.freeRowCoord (RobinsonSquare.freeGridLast level) +
        step.leftOffset =
      parent.freeRowCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.overlap step

/-- Child column coordinate from its canonical previous-level preimage. -/
theorem columnCoordinateStep_child_eq_preimage
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : ColumnCoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeColumnCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.leftOffset
      | .right =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.child_eq_preimage step i

/-- Child row coordinate from its canonical previous-level preimage. -/
theorem rowCoordinateStep_child_eq_preimage
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : RowCoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeRowCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.leftOffset
      | .right =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.child_eq_preimage step i

namespace CoordinateStep

/-- Column-coordinate overlap from a combined geometry coordinate step. -/
theorem column_overlap
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : CoordinateStep parent child) :
    parent.freeColumnCoord (RobinsonSquare.freeGridLast level) +
        step.columns.leftOffset =
      parent.freeColumnCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.columns.rightOffset :=
  columnCoordinateStep_overlap step.columns

/-- Row-coordinate overlap from a combined geometry coordinate step. -/
theorem row_overlap
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : CoordinateStep parent child) :
    parent.freeRowCoord (RobinsonSquare.freeGridLast level) +
        step.rows.leftOffset =
      parent.freeRowCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.rows.rightOffset :=
  rowCoordinateStep_overlap step.rows

/-- Child column coordinate from a combined geometry coordinate step. -/
theorem column_child_eq_preimage
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeColumnCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.columns.leftOffset
      | .right =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.columns.rightOffset :=
  columnCoordinateStep_child_eq_preimage step.columns i

/-- Child row coordinate from a combined geometry coordinate step. -/
theorem row_child_eq_preimage
    {level : Nat}
    {parent : RobinsonBoardSignalGeometry level}
    {child : RobinsonBoardSignalGeometry (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeRowCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rows.leftOffset
      | .right =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rows.rightOffset :=
  rowCoordinateStep_child_eq_preimage step.rows i

end CoordinateStep

/--
Canonical obstruction-only Robinson board geometry at one level.

This realizes the abstract Section 7 free-line recurrence without choosing any
payload routing: every integer coordinate is part of the board, the selected
free rows/columns are the enumerated coordinates `0, ..., freeGridSide - 1`,
and an obstruction signal is present exactly on non-free lines.
-/
def canonical (level : Nat) : RobinsonBoardSignalGeometry level where
  freeColumnCoord := fun i => i.val
  freeRowCoord := fun j => j.val
  isBoardColumn := fun _ => True
  isBoardRow := fun _ => True
  isFreeColumn := fun x =>
    ∃ i : Fin (RobinsonSquare.freeGridSide level), (i.val : Int) = x
  isFreeRow := fun y =>
    ∃ j : Fin (RobinsonSquare.freeGridSide level), (j.val : Int) = y
  hasHorizontalObstruction := fun _ y =>
    ¬ ∃ j : Fin (RobinsonSquare.freeGridSide level), (j.val : Int) = y
  hasVerticalObstruction := fun x _ =>
    ¬ ∃ i : Fin (RobinsonSquare.freeGridSide level), (i.val : Int) = x
  freeRow_iff_noHorizontalObstruction := by
    intro y _hrow
    constructor
    · intro hfree x _hcolumn hobs
      exact hobs hfree
    · intro hclear
      by_contra hnotFree
      exact hclear 0 True.intro hnotFree
  freeColumn_iff_noVerticalObstruction := by
    intro x _hcolumn
    constructor
    · intro hfree y _hrow hobs
      exact hobs hfree
    · intro hclear
      by_contra hnotFree
      exact hclear 0 True.intro hnotFree
  freeColumnCoord_board := fun _ => True.intro
  freeRowCoord_board := fun _ => True.intro
  freeColumnCoord_free := fun i => ⟨i, rfl⟩
  freeRowCoord_free := fun j => ⟨j, rfl⟩
  freeColumnCoord_complete := by
    intro x hfree
    exact hfree
  freeRowCoord_complete := by
    intro y hfree
    exact hfree
  freeColumnCoord_injective := by
    intro i j h
    apply Fin.ext
    exact Int.ofNat.inj h
  freeRowCoord_injective := by
    intro i j h
    apply Fin.ext
    exact Int.ofNat.inj h

@[simp]
theorem canonical_freeColumnCoord
    (level : Nat) (i : Fin (RobinsonSquare.freeGridSide level)) :
    (canonical level).freeColumnCoord i = i.val :=
  rfl

@[simp]
theorem canonical_freeRowCoord
    (level : Nat) (j : Fin (RobinsonSquare.freeGridSide level)) :
    (canonical level).freeRowCoord j = j.val :=
  rfl

theorem canonical_freeColumnCoord_succ
    (level : Nat) (i : Fin (RobinsonSquare.freeGridSide level))
    (hi : i.val + 1 < RobinsonSquare.freeGridSide level) :
    (canonical level).freeColumnCoord ⟨i.val + 1, hi⟩ =
      (canonical level).freeColumnCoord i + 1 := by
  norm_num [canonical]

theorem canonical_freeRowCoord_succ
    (level : Nat) (j : Fin (RobinsonSquare.freeGridSide level))
    (hj : j.val + 1 < RobinsonSquare.freeGridSide level) :
    (canonical level).freeRowCoord ⟨j.val + 1, hj⟩ =
      (canonical level).freeRowCoord j + 1 := by
  norm_num [canonical]

@[simp]
theorem canonical_isBoardColumn
    (level : Nat) (column : Int) :
    (canonical level).isBoardColumn column := by
  trivial

@[simp]
theorem canonical_isBoardRow
    (level : Nat) (row : Int) :
    (canonical level).isBoardRow row := by
  trivial

theorem canonical_isFreeColumn_iff_exists
    (level : Nat) (column : Int) :
    (canonical level).isFreeColumn column ↔
      ∃ i : Fin (RobinsonSquare.freeGridSide level), (i.val : Int) = column := by
  rfl

theorem canonical_isFreeRow_iff_exists
    (level : Nat) (row : Int) :
    (canonical level).isFreeRow row ↔
      ∃ j : Fin (RobinsonSquare.freeGridSide level), (j.val : Int) = row := by
  rfl

theorem canonical_hasHorizontalObstruction_iff_not_freeRow
    (level : Nat) (column row : Int) :
    (canonical level).hasHorizontalObstruction column row ↔
      ¬ (canonical level).isFreeRow row := by
  rfl

theorem canonical_hasVerticalObstruction_iff_not_freeColumn
    (level : Nat) (column row : Int) :
    (canonical level).hasVerticalObstruction column row ↔
      ¬ (canonical level).isFreeColumn column := by
  rfl

theorem canonical_noHorizontalObstruction_iff_freeRow
    (level : Nat) (column row : Int) :
    ¬ (canonical level).hasHorizontalObstruction column row ↔
      (canonical level).isFreeRow row := by
  rw [canonical_hasHorizontalObstruction_iff_not_freeRow]
  exact not_not

theorem canonical_noVerticalObstruction_iff_freeColumn
    (level : Nat) (column row : Int) :
    ¬ (canonical level).hasVerticalObstruction column row ↔
      (canonical level).isFreeColumn column := by
  rw [canonical_hasVerticalObstruction_iff_not_freeColumn]
  exact not_not

theorem canonical_freeColumn_bounds
    {level : Nat} {column : Int}
    (hfree : (canonical level).isFreeColumn column) :
    0 ≤ column ∧ column < RobinsonSquare.freeGridSide level := by
  rcases hfree with ⟨i, rfl⟩
  constructor
  · exact Int.natCast_nonneg i.val
  · exact_mod_cast i.isLt

theorem canonical_freeRow_bounds
    {level : Nat} {row : Int}
    (hfree : (canonical level).isFreeRow row) :
    0 ≤ row ∧ row < RobinsonSquare.freeGridSide level := by
  rcases hfree with ⟨j, rfl⟩
  constructor
  · exact Int.natCast_nonneg j.val
  · exact_mod_cast j.isLt

/-- In the canonical geometry, free columns are exactly the in-range columns. -/
theorem canonical_isFreeColumn_iff_bounds
    (level : Nat) (column : Int) :
    (canonical level).isFreeColumn column ↔
      0 ≤ column ∧ column < RobinsonSquare.freeGridSide level := by
  constructor
  · exact canonical_freeColumn_bounds
  · intro hbounds
    refine ⟨⟨column.toNat, ?_⟩, ?_⟩
    · have hcast : (column.toNat : Int) = column :=
        Int.toNat_of_nonneg hbounds.1
      omega
    · exact Int.toNat_of_nonneg hbounds.1

/-- In the canonical geometry, free rows are exactly the in-range rows. -/
theorem canonical_isFreeRow_iff_bounds
    (level : Nat) (row : Int) :
    (canonical level).isFreeRow row ↔
      0 ≤ row ∧ row < RobinsonSquare.freeGridSide level := by
  constructor
  · exact canonical_freeRow_bounds
  · intro hbounds
    refine ⟨⟨row.toNat, ?_⟩, ?_⟩
    · have hcast : (row.toNat : Int) = row :=
        Int.toNat_of_nonneg hbounds.1
      omega
    · exact Int.toNat_of_nonneg hbounds.1

/--
In the canonical geometry, a horizontal obstruction is present exactly on rows
outside the enumerated free-row range.
-/
theorem canonical_hasHorizontalObstruction_iff_row_out_of_bounds
    (level : Nat) (column row : Int) :
    (canonical level).hasHorizontalObstruction column row ↔
      row < 0 ∨ (RobinsonSquare.freeGridSide level : Int) ≤ row := by
  rw [canonical_hasHorizontalObstruction_iff_not_freeRow,
    canonical_isFreeRow_iff_bounds]
  omega

/--
In the canonical geometry, a vertical obstruction is present exactly on columns
outside the enumerated free-column range.
-/
theorem canonical_hasVerticalObstruction_iff_column_out_of_bounds
    (level : Nat) (column row : Int) :
    (canonical level).hasVerticalObstruction column row ↔
      column < 0 ∨ (RobinsonSquare.freeGridSide level : Int) ≤ column := by
  rw [canonical_hasVerticalObstruction_iff_not_freeColumn,
    canonical_isFreeColumn_iff_bounds]
  omega

/--
No horizontal obstruction in the canonical geometry is the same as being on an
enumerated free row.
-/
theorem canonical_noHorizontalObstruction_iff_row_bounds
    (level : Nat) (column row : Int) :
    ¬ (canonical level).hasHorizontalObstruction column row ↔
      0 ≤ row ∧ row < RobinsonSquare.freeGridSide level := by
  rw [canonical_noHorizontalObstruction_iff_freeRow,
    canonical_isFreeRow_iff_bounds]

/--
No vertical obstruction in the canonical geometry is the same as being on an
enumerated free column.
-/
theorem canonical_noVerticalObstruction_iff_column_bounds
    (level : Nat) (column row : Int) :
    ¬ (canonical level).hasVerticalObstruction column row ↔
      0 ≤ column ∧ column < RobinsonSquare.freeGridSide level := by
  rw [canonical_noVerticalObstruction_iff_freeColumn,
    canonical_isFreeColumn_iff_bounds]

theorem canonical_noObstruction_at_freeCrossing
    (level : Nat)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (¬ (canonical level).hasHorizontalObstruction
        ((canonical level).freeColumnCoord i)
        ((canonical level).freeRowCoord j)) ∧
      ¬ (canonical level).hasVerticalObstruction
        ((canonical level).freeColumnCoord i)
        ((canonical level).freeRowCoord j) :=
  (canonical level).noObstruction_at_freeCrossing i j

/-- Coordinate recurrence for the canonical Robinson board geometries. -/
def canonicalCoordinateStep (level : Nat) :
    CoordinateStep (canonical level) (canonical (level + 1)) where
  columns := {
    leftOffset := 0
    rightOffset := RobinsonSquare.freeGridSide level - 1
    left := by
      intro i
      norm_num [canonical, RobinsonSquare.freeLineLeftEmbedding_val]
    right := by
      intro i
      simp [canonical, RobinsonSquare.freeLineRightEmbedding_val]
      have hpos := RobinsonSquare.freeGridSide_pos level
      omega
  }
  rows := {
    leftOffset := 0
    rightOffset := RobinsonSquare.freeGridSide level - 1
    left := by
      intro i
      norm_num [canonical, RobinsonSquare.freeLineLeftEmbedding_val]
    right := by
      intro i
      simp [canonical, RobinsonSquare.freeLineRightEmbedding_val]
      have hpos := RobinsonSquare.freeGridSide_pos level
      omega
  }

end RobinsonBoardSignalGeometry

/--
Coherent Robinson Section 7 obstruction geometry across all red-board levels.

This is the pure geometry target: one obstruction/free-line geometry per level,
plus the repeated free-line coordinate recurrence between consecutive levels.
-/
structure RobinsonBoardSignalGeometryTower : Type where
  geometries : (level : Nat) → RobinsonBoardSignalGeometry level
  steps : ∀ level : Nat,
    RobinsonBoardSignalGeometry.CoordinateStep
      (geometries level) (geometries (level + 1))

/-- Existence of the pure Robinson Section 7 obstruction-geometry tower. -/
def HasRobinsonBoardSignalGeometryTower : Prop :=
  Nonempty RobinsonBoardSignalGeometryTower

/-- The canonical obstruction geometry at every level, with Robinson's recurrence. -/
def canonicalRobinsonBoardSignalGeometryTower :
    RobinsonBoardSignalGeometryTower where
  geometries := RobinsonBoardSignalGeometry.canonical
  steps := RobinsonBoardSignalGeometry.canonicalCoordinateStep

/-- The pure obstruction-geometry part of Robinson Section 7 is inhabited. -/
theorem hasRobinsonBoardSignalGeometryTower :
    HasRobinsonBoardSignalGeometryTower :=
  ⟨canonicalRobinsonBoardSignalGeometryTower⟩

/--
Robinson Section 7 certificate for one red board level.

The original argument identifies the free rows and columns by obstruction
signals: a row is free exactly when no horizontal obstruction signal crosses it,
and a column is free exactly when no vertical obstruction signal crosses it.
At crossings of selected free rows and columns, payload signals are routed
through the intervening board cells.  This structure keeps those obstruction
facts visible for the geometric proof while still carrying the routed payload
data expected by `Figure18RobinsonBoardRoutedFreeGrid`.
-/
structure Figure18RobinsonBoardSignalCertificate
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    (level : Nat) : Type where
  freeColumnCoord :
    Fin (RobinsonSquare.freeGridSide level) → Int
  freeRowCoord :
    Fin (RobinsonSquare.freeGridSide level) → Int
  isBoardColumn : Int → Prop
  isBoardRow : Int → Prop
  isFreeColumn : Int → Prop
  isFreeRow : Int → Prop
  hasHorizontalObstruction : Int → Int → Prop
  hasVerticalObstruction : Int → Int → Prop
  freeRow_iff_noHorizontalObstruction :
    ∀ y : Int, isBoardRow y →
      (isFreeRow y ↔
        ∀ x : Int, isBoardColumn x → ¬ hasHorizontalObstruction x y)
  freeColumn_iff_noVerticalObstruction :
    ∀ x : Int, isBoardColumn x →
      (isFreeColumn x ↔
        ∀ y : Int, isBoardRow y → ¬ hasVerticalObstruction x y)
  freeColumnCoord_board :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      isBoardColumn (freeColumnCoord i)
  freeRowCoord_board :
    ∀ j : Fin (RobinsonSquare.freeGridSide level),
      isBoardRow (freeRowCoord j)
  freeColumnCoord_free :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      isFreeColumn (freeColumnCoord i)
  freeRowCoord_free :
    ∀ j : Fin (RobinsonSquare.freeGridSide level),
      isFreeRow (freeRowCoord j)
  freeColumnCoord_complete :
    ∀ x : Int, isFreeColumn x →
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        freeColumnCoord i = x
  freeRowCoord_complete :
    ∀ y : Int, isFreeRow y →
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        freeRowCoord j = y
  freeColumnCoord_injective :
    Function.Injective freeColumnCoord
  freeRowCoord_injective :
    Function.Injective freeRowCoord
  siteRect :
    Fin (RobinsonSquare.freeGridSide level) →
      Fin (RobinsonSquare.freeGridSide level) → Figure18Site
  payloadRect :
    Rectangle (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide level)
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite
  product :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        WangTile.product (siteRect i j).tile (payloadRect i j) =
          (x (freeColumnCoord i, freeRowCoord j)).1
  hmatch :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.HMatches (payloadRect i j)
            (payloadRect ⟨i.val + 1, hi⟩ j)
  vmatch :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.VMatches (payloadRect i j)
            (payloadRect i ⟨j.val + 1, hj⟩)

namespace Figure18RobinsonBoardSignalCertificate

/-- Forget the Figure 18 payload-routing data and keep only board geometry. -/
def geometry
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    RobinsonBoardSignalGeometry level where
  freeColumnCoord := certificate.freeColumnCoord
  freeRowCoord := certificate.freeRowCoord
  isBoardColumn := certificate.isBoardColumn
  isBoardRow := certificate.isBoardRow
  isFreeColumn := certificate.isFreeColumn
  isFreeRow := certificate.isFreeRow
  hasHorizontalObstruction := certificate.hasHorizontalObstruction
  hasVerticalObstruction := certificate.hasVerticalObstruction
  freeRow_iff_noHorizontalObstruction :=
    certificate.freeRow_iff_noHorizontalObstruction
  freeColumn_iff_noVerticalObstruction :=
    certificate.freeColumn_iff_noVerticalObstruction
  freeColumnCoord_board := certificate.freeColumnCoord_board
  freeRowCoord_board := certificate.freeRowCoord_board
  freeColumnCoord_free := certificate.freeColumnCoord_free
  freeRowCoord_free := certificate.freeRowCoord_free
  freeColumnCoord_complete := certificate.freeColumnCoord_complete
  freeRowCoord_complete := certificate.freeRowCoord_complete
  freeColumnCoord_injective := certificate.freeColumnCoord_injective
  freeRowCoord_injective := certificate.freeRowCoord_injective

@[simp]
theorem geometry_freeColumnCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    certificate.geometry.freeColumnCoord = certificate.freeColumnCoord :=
  rfl

@[simp]
theorem geometry_freeColumnCoord_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (i : Fin (RobinsonSquare.freeGridSide level)) :
    certificate.geometry.freeColumnCoord i = certificate.freeColumnCoord i :=
  rfl

@[simp]
theorem geometry_freeRowCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    certificate.geometry.freeRowCoord = certificate.freeRowCoord :=
  rfl

@[simp]
theorem geometry_freeRowCoord_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (i : Fin (RobinsonSquare.freeGridSide level)) :
    certificate.geometry.freeRowCoord i = certificate.freeRowCoord i :=
  rfl

/-- A coordinate pair lying at a free crossing of the certificate board. -/
def IsFreeCrossing
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column row : Int) : Prop :=
  certificate.geometry.IsFreeCrossing column row

/-- A certificate coordinate pair whose full board row and column are clear. -/
def IsClearCrossing
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column row : Int) : Prop :=
  certificate.geometry.IsClearCrossing column row

/-- Certificate free crossings are free columns crossed with free rows. -/
theorem isFreeCrossing_iff
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column row : Int) :
    certificate.IsFreeCrossing column row ↔
      certificate.isFreeColumn column ∧ certificate.isFreeRow row := by
  rfl

/-- Certificate free crossings are exactly the enumerated free coordinates. -/
theorem isFreeCrossing_iff_exists_freeCoords
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column row : Int) :
    certificate.IsFreeCrossing column row ↔
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        ∃ j : Fin (RobinsonSquare.freeGridSide level),
          certificate.freeColumnCoord i = column ∧
            certificate.freeRowCoord j = row :=
  certificate.geometry.isFreeCrossing_iff_exists_freeCoords column row

/-- Certificate clear crossings are exactly certificate free crossings. -/
theorem isClearCrossing_iff_isFreeCrossing
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column row : Int) :
    certificate.IsClearCrossing column row ↔
      certificate.IsFreeCrossing column row :=
  certificate.geometry.isClearCrossing_iff_isFreeCrossing column row

/-- Certificate clear crossings are exactly the enumerated free coordinates. -/
theorem isClearCrossing_iff_exists_freeCoords
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column row : Int) :
    certificate.IsClearCrossing column row ↔
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        ∃ j : Fin (RobinsonSquare.freeGridSide level),
          certificate.freeColumnCoord i = column ∧
            certificate.freeRowCoord j = row := by
  rw [certificate.isClearCrossing_iff_isFreeCrossing,
    certificate.isFreeCrossing_iff_exists_freeCoords]

/-- Certificate free crossings form the virtual board square. -/
noncomputable def freeCrossingEquivFinProd
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    { p : Int × Int // certificate.IsFreeCrossing p.1 p.2 } ≃
      Fin (RobinsonSquare.freeGridSide level) ×
        Fin (RobinsonSquare.freeGridSide level) :=
  certificate.geometry.freeCrossingEquivFinProd

@[reducible]
noncomputable def freeCrossingFintype
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    Fintype { p : Int × Int // certificate.IsFreeCrossing p.1 p.2 } :=
  certificate.geometry.freeCrossingFintype

theorem freeCrossing_card_eq_two_pow_add_one_mul
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    @Fintype.card { p : Int × Int // certificate.IsFreeCrossing p.1 p.2 }
      (certificate.freeCrossingFintype) =
        (2 ^ level + 1) * (2 ^ level + 1) :=
  certificate.geometry.freeCrossing_card_eq_two_pow_add_one_mul

/-- Certificate clear crossings form the obstruction-defined virtual square. -/
noncomputable def clearCrossingEquivFinProd
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    { p : Int × Int // certificate.IsClearCrossing p.1 p.2 } ≃
      Fin (RobinsonSquare.freeGridSide level) ×
        Fin (RobinsonSquare.freeGridSide level) :=
  certificate.geometry.clearCrossingEquivFinProd

@[reducible]
noncomputable def clearCrossingFintype
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    Fintype { p : Int × Int // certificate.IsClearCrossing p.1 p.2 } :=
  certificate.geometry.clearCrossingFintype

theorem clearCrossing_card_eq_two_pow_add_one_mul
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    @Fintype.card { p : Int × Int // certificate.IsClearCrossing p.1 p.2 }
      (certificate.clearCrossingFintype) =
        (2 ^ level + 1) * (2 ^ level + 1) :=
  certificate.geometry.clearCrossing_card_eq_two_pow_add_one_mul

/-- The selected free-column/free-row coordinates are certificate free crossings. -/
theorem isFreeCrossing_freeCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    certificate.IsFreeCrossing
      (certificate.freeColumnCoord i) (certificate.freeRowCoord j) :=
  certificate.geometry.isFreeCrossing_freeCoord i j

/--
A certificate coordinate pair is a free crossing exactly when its board column
has no vertical obstruction and its board row has no horizontal obstruction.
-/
theorem isFreeCrossing_iff_clearLines
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column row : Int}
    (hcolumn : certificate.isBoardColumn column)
    (hrow : certificate.isBoardRow row) :
    certificate.IsFreeCrossing column row ↔
      (∀ y : Int, certificate.isBoardRow y →
        ¬ certificate.hasVerticalObstruction column y) ∧
      (∀ x : Int, certificate.isBoardColumn x →
        ¬ certificate.hasHorizontalObstruction x row) :=
  certificate.geometry.isFreeCrossing_iff_clearLines hcolumn hrow

/--
Certificate-level form of Robinson's obstruction-signal characterization:
clear board lines are exactly the coordinates that occur in the routed free
grid.
-/
theorem exists_freeCoords_iff_clearLines
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column row : Int}
    (hcolumn : certificate.isBoardColumn column)
    (hrow : certificate.isBoardRow row) :
    (∃ i : Fin (RobinsonSquare.freeGridSide level),
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        certificate.freeColumnCoord i = column ∧
          certificate.freeRowCoord j = row) ↔
      (∀ y : Int, certificate.isBoardRow y →
        ¬ certificate.hasVerticalObstruction column y) ∧
      (∀ x : Int, certificate.isBoardColumn x →
        ¬ certificate.hasHorizontalObstruction x row) :=
  certificate.geometry.exists_freeCoords_iff_clearLines hcolumn hrow

/-- Any certificate free crossing has no obstruction through the crossing cell. -/
theorem noObstruction_of_isFreeCrossing
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column row : Int}
    (hcolumn : certificate.isBoardColumn column)
    (hrow : certificate.isBoardRow row)
    (hcross : certificate.IsFreeCrossing column row) :
    (¬ certificate.hasHorizontalObstruction column row) ∧
      ¬ certificate.hasVerticalObstruction column row :=
  certificate.geometry.noObstruction_of_isFreeCrossing hcolumn hrow hcross

/--
If Robinson's obstruction signals show that a board column and row are clear,
then the corresponding plane coordinate is one of the routed active free-grid
cells, with the recorded scaffold/payload product tile.
-/
theorem activeProduct_of_clearLines
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column row : Int}
    (hcolumn : certificate.isBoardColumn column)
    (hrow : certificate.isBoardRow row)
    (hclear :
      (∀ y : Int, certificate.isBoardRow y →
        ¬ certificate.hasVerticalObstruction column y) ∧
      (∀ x : Int, certificate.isBoardColumn x →
        ¬ certificate.hasHorizontalObstruction x row)) :
    ∃ i : Fin (RobinsonSquare.freeGridSide level),
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        certificate.freeColumnCoord i = column ∧
          certificate.freeRowCoord j = row ∧
          CellRole.isActive (table.roleAtSite (certificate.siteRect i j)) =
            true ∧
          WangTile.product (certificate.siteRect i j).tile
              (certificate.payloadRect i j) =
            (x (column, row)).1 := by
  rcases (certificate.exists_freeCoords_iff_clearLines hcolumn hrow).2
      hclear with ⟨i, j, hcolumn_eq, hrow_eq⟩
  refine ⟨i, j, hcolumn_eq, hrow_eq, certificate.active i j, ?_⟩
  simpa [hcolumn_eq, hrow_eq] using certificate.product i j

/--
Build a full signal certificate from board obstruction geometry and the routed
Figure 18 payload data at the selected free crossings.
-/
def ofGeometry
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level)
    (siteRect :
      Fin (RobinsonSquare.freeGridSide level) →
        Fin (RobinsonSquare.freeGridSide level) → Figure18Site)
    (payloadRect :
      Rectangle (RobinsonSquare.freeGridSide level)
        (RobinsonSquare.freeGridSide level))
    (active :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          CellRole.isActive (table.roleAtSite (siteRect i j)) = true)
    (cornerSite :
      siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
        ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite)
    (product :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          WangTile.product (siteRect i j).tile (payloadRect i j) =
            (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)).1)
    (hmatch :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
            WangTile.HMatches (payloadRect i j)
              (payloadRect ⟨i.val + 1, hi⟩ j))
    (vmatch :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
            WangTile.VMatches (payloadRect i j)
              (payloadRect i ⟨j.val + 1, hj⟩)) :
    Figure18RobinsonBoardSignalCertificate table x level where
  freeColumnCoord := geometry.freeColumnCoord
  freeRowCoord := geometry.freeRowCoord
  isBoardColumn := geometry.isBoardColumn
  isBoardRow := geometry.isBoardRow
  isFreeColumn := geometry.isFreeColumn
  isFreeRow := geometry.isFreeRow
  hasHorizontalObstruction := geometry.hasHorizontalObstruction
  hasVerticalObstruction := geometry.hasVerticalObstruction
  freeRow_iff_noHorizontalObstruction :=
    geometry.freeRow_iff_noHorizontalObstruction
  freeColumn_iff_noVerticalObstruction :=
    geometry.freeColumn_iff_noVerticalObstruction
  freeColumnCoord_board := geometry.freeColumnCoord_board
  freeRowCoord_board := geometry.freeRowCoord_board
  freeColumnCoord_free := geometry.freeColumnCoord_free
  freeRowCoord_free := geometry.freeRowCoord_free
  freeColumnCoord_complete := geometry.freeColumnCoord_complete
  freeRowCoord_complete := geometry.freeRowCoord_complete
  freeColumnCoord_injective := geometry.freeColumnCoord_injective
  freeRowCoord_injective := geometry.freeRowCoord_injective
  siteRect := siteRect
  payloadRect := payloadRect
  active := active
  cornerSite := cornerSite
  product := product
  hmatch := hmatch
  vmatch := vmatch

/--
The Figure 18 sites selected by a Robinson signal certificate are locally
compatible as virtual neighbors in the payload grid.

This is the finite site-level condition needed by the generated layer-stack
checker.  It is deliberately separate from `hmatch` and `vmatch`, which record
payload-edge matches in the routed Wang square.
-/
def SiteCompatible
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    Prop :=
  (∀ i : Fin (RobinsonSquare.freeGridSide level),
    ∀ j : Fin (RobinsonSquare.freeGridSide level),
    ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
      Figure18Site.hCompatible
        (certificate.siteRect i j)
        (certificate.siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
  (∀ i : Fin (RobinsonSquare.freeGridSide level),
    ∀ j : Fin (RobinsonSquare.freeGridSide level),
    ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
      Figure18Site.vCompatible
        (certificate.siteRect i j)
        (certificate.siteRect i ⟨j.val + 1, hj⟩) = true)

/--
Figure 18 payload-routing data over one Robinson obstruction geometry.

The geometry fields say where the free rows and columns are; this routing data
adds the decoded Figure 18 site at each free crossing, the payload tile read
there, payload edge matches, and the finite local site-compatibility proof.
-/
structure Routing
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) : Type where
  siteRect :
    Fin (RobinsonSquare.freeGridSide level) →
      Fin (RobinsonSquare.freeGridSide level) → Figure18Site
  payloadRect :
    Rectangle (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide level)
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite
  product :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        WangTile.product (siteRect i j).tile (payloadRect i j) =
          (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)).1
  hmatch :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.HMatches (payloadRect i j)
            (payloadRect ⟨i.val + 1, hi⟩ j)
  vmatch :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.VMatches (payloadRect i j)
            (payloadRect i ⟨j.val + 1, hj⟩)
  siteCompatible :
    (ofGeometry geometry siteRect payloadRect active cornerSite product
      hmatch vmatch).SiteCompatible

/--
Product-witness form of Figure 18 routing over one Robinson obstruction
geometry.

This is closer to the data extracted from a combined tiling: at each selected
free crossing, identify the Figure 18 base site and exhibit some payload tile
whose product is the combined tile there.  The assembled `payloadRect` is
derived when converting to `Routing`.
-/
structure ProductWitnessRouting
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) : Type where
  siteRect :
    Fin (RobinsonSquare.freeGridSide level) →
      Fin (RobinsonSquare.freeGridSide level) → Figure18Site
  payloadWitness :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        { payload : WangTile //
          WangTile.product (siteRect i j).tile payload =
            (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)).1 }
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite
  hmatch :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.HMatches (payloadWitness i j).1
            (payloadWitness ⟨i.val + 1, hi⟩ j).1
  vmatch :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.VMatches (payloadWitness i j).1
            (payloadWitness i ⟨j.val + 1, hj⟩).1
  siteCompatible :
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.hCompatible
          (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.vCompatible
          (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)

namespace ProductWitnessRouting

/-- Payload rectangle assembled from pointwise product witnesses. -/
def payloadRect
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry) :
    Rectangle (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide level) :=
  fun i j => (routing.payloadWitness i j).1

theorem product
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    WangTile.product (routing.siteRect i j).tile
        (routing.payloadRect i j) =
      (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)).1 :=
  (routing.payloadWitness i j).2

/-- Convert product-witness routing into the theorem-facing routing package. -/
def toRouting
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry) :
    Routing table x geometry where
  siteRect := routing.siteRect
  payloadRect := routing.payloadRect
  active := routing.active
  cornerSite := routing.cornerSite
  product := routing.product
  hmatch := routing.hmatch
  vmatch := routing.vmatch
  siteCompatible := by
    simpa [Figure18RobinsonBoardSignalCertificate.SiteCompatible,
      Figure18RobinsonBoardSignalCertificate.ofGeometry] using
      routing.siteCompatible

@[simp]
theorem payloadRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.payloadRect i j = (routing.payloadWitness i j).1 :=
  rfl

@[simp]
theorem toRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toRouting.siteRect i j = routing.siteRect i j :=
  rfl

@[simp]
theorem toRouting_payloadRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toRouting.payloadRect i j = (routing.payloadWitness i j).1 :=
  rfl

@[simp]
theorem toRouting_product_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : ProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toRouting.product i j = routing.product i j :=
  rfl

end ProductWitnessRouting

/--
Product-witness routing where the payload edge matches are obtained by
transmission along unobstructed board rows and columns.

This is the form closest to Robinson's Section 7 description: obstruction
signals identify the free lines, and the remaining local tile rules transport
the simulated payload signals along those lines.  The constructor below turns
these transmission facts into the simpler `ProductWitnessRouting` interface.
-/
structure CorridorProductWitnessRouting
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) : Type where
  siteRect :
    Fin (RobinsonSquare.freeGridSide level) →
      Fin (RobinsonSquare.freeGridSide level) → Figure18Site
  payloadWitness :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        { payload : WangTile //
          WangTile.product (siteRect i j).tile payload =
            (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)).1 }
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite
  htransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          (∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column
              (geometry.freeRowCoord j)) →
            WangTile.HMatches (payloadWitness i j).1
              (payloadWitness ⟨i.val + 1, hi⟩ j).1
  vtransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          (∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction
              (geometry.freeColumnCoord i) row) →
            WangTile.VMatches (payloadWitness i j).1
              (payloadWitness i ⟨j.val + 1, hj⟩).1
  siteCompatible :
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.hCompatible
          (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.vCompatible
          (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)

namespace CorridorProductWitnessRouting

/--
Forget the explicit corridor-transmission hypotheses after using the
obstruction geometry to prove that selected rows and columns are unobstructed.
-/
def toProductWitnessRouting
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : CorridorProductWitnessRouting table x geometry) :
    ProductWitnessRouting table x geometry where
  siteRect := routing.siteRect
  payloadWitness := routing.payloadWitness
  active := routing.active
  cornerSite := routing.cornerSite
  hmatch := by
    intro i j hi
    exact routing.htransmit i j hi
      (fun column hcolumn =>
        geometry.noHorizontalObstruction_of_freeRowCoord column hcolumn j)
  vmatch := by
    intro i j hj
    exact routing.vtransmit i j hj
      (fun row hrow =>
        geometry.noVerticalObstruction_of_freeColumnCoord i row hrow)
  siteCompatible := routing.siteCompatible

@[simp]
theorem toProductWitnessRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : CorridorProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toProductWitnessRouting.siteRect i j = routing.siteRect i j :=
  rfl

@[simp]
theorem toProductWitnessRouting_payloadWitness_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : CorridorProductWitnessRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toProductWitnessRouting.payloadWitness i j =
      routing.payloadWitness i j :=
  rfl

/--
Build corridor routing from selected combined-tiling sites.

This removes the repetitive product-witness extraction from the concrete
Robinson proof: once the geometric argument has selected the free crossings,
shown that their decoded scaffold sites are active with the right corner, and
proved corridor transmission/site-compatibility, the payload witnesses are read
directly from the product decomposition of the combined tiling.
-/
noncomputable def ofCombinedSites
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (active :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          CellRole.isActive
            (table.roleAtSite
              (table.combinedSite
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord j)))) = true)
    (cornerSite :
      table.combinedSite
        (x (geometry.freeColumnCoord
          ⟨0, RobinsonSquare.freeGridSide_pos level⟩,
          geometry.freeRowCoord
            ⟨0, RobinsonSquare.freeGridSide_pos level⟩)) =
        table.cornerSite)
    (htransmit :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
            (∀ column : Int, geometry.isBoardColumn column →
              ¬ geometry.hasHorizontalObstruction column
                (geometry.freeRowCoord j)) →
              WangTile.HMatches
                (table.combinedPayload
                  (x (geometry.freeColumnCoord i,
                    geometry.freeRowCoord j)))
                (table.combinedPayload
                  (x (geometry.freeColumnCoord ⟨i.val + 1, hi⟩,
                    geometry.freeRowCoord j))))
    (vtransmit :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
            (∀ row : Int, geometry.isBoardRow row →
              ¬ geometry.hasVerticalObstruction
                (geometry.freeColumnCoord i) row) →
              WangTile.VMatches
                (table.combinedPayload
                  (x (geometry.freeColumnCoord i,
                    geometry.freeRowCoord j)))
                (table.combinedPayload
                  (x (geometry.freeColumnCoord i,
                    geometry.freeRowCoord ⟨j.val + 1, hj⟩))))
    (siteCompatible :
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.hCompatible
            (table.combinedSite
              (x (geometry.freeColumnCoord i,
                geometry.freeRowCoord j)))
            (table.combinedSite
              (x (geometry.freeColumnCoord ⟨i.val + 1, hi⟩,
                geometry.freeRowCoord j))) = true) ∧
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.vCompatible
            (table.combinedSite
              (x (geometry.freeColumnCoord i,
                geometry.freeRowCoord j)))
            (table.combinedSite
              (x (geometry.freeColumnCoord i,
                geometry.freeRowCoord ⟨j.val + 1, hj⟩))) = true)) :
    CorridorProductWitnessRouting table x geometry where
  siteRect := fun i j =>
    table.combinedSite
      (x (geometry.freeColumnCoord i, geometry.freeRowCoord j))
  payloadWitness := fun i j =>
    ⟨table.combinedPayload
      (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)),
      table.combinedPayload_product
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j))⟩
  active := active
  cornerSite := cornerSite
  htransmit := htransmit
  vtransmit := vtransmit
  siteCompatible := siteCompatible

@[simp]
theorem ofCombinedSites_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (active cornerSite htransmit vtransmit siteCompatible)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (ofCombinedSites (table := table) (x := x) (geometry := geometry)
      active cornerSite htransmit vtransmit siteCompatible).siteRect i j =
      table.combinedSite
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) :=
  rfl

@[simp]
theorem ofCombinedSites_payloadWitness_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (active cornerSite htransmit vtransmit siteCompatible)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    ((ofCombinedSites (table := table) (x := x) (geometry := geometry)
      active cornerSite htransmit vtransmit siteCompatible).payloadWitness i j).1 =
      table.combinedPayload
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) :=
  rfl

end CorridorProductWitnessRouting

/--
Robinson corridor routing stated only in terms of decoded combined-tiling sites.

The product decomposition is intentionally absent from this structure: it is
supplied mechanically by `CombinedSiteCorridorRouting.toCorridorProductWitnessRouting`.
-/
structure CombinedSiteCorridorRouting
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) : Type where
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive
          (table.roleAtSite
            (table.combinedSite
              (x (geometry.freeColumnCoord i,
                geometry.freeRowCoord j)))) = true
  cornerSite :
    table.combinedSite
      (x (geometry.freeColumnCoord
        ⟨0, RobinsonSquare.freeGridSide_pos level⟩,
        geometry.freeRowCoord
          ⟨0, RobinsonSquare.freeGridSide_pos level⟩)) =
      table.cornerSite
  htransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          (∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column
              (geometry.freeRowCoord j)) →
            WangTile.HMatches
              (table.combinedPayload
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord j)))
              (table.combinedPayload
                (x (geometry.freeColumnCoord ⟨i.val + 1, hi⟩,
                  geometry.freeRowCoord j)))
  vtransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          (∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction
              (geometry.freeColumnCoord i) row) →
            WangTile.VMatches
              (table.combinedPayload
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord j)))
              (table.combinedPayload
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord ⟨j.val + 1, hj⟩)))
  siteCompatible :
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.hCompatible
          (table.combinedSite
            (x (geometry.freeColumnCoord i,
              geometry.freeRowCoord j)))
          (table.combinedSite
            (x (geometry.freeColumnCoord ⟨i.val + 1, hi⟩,
              geometry.freeRowCoord j))) = true) ∧
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.vCompatible
          (table.combinedSite
            (x (geometry.freeColumnCoord i,
              geometry.freeRowCoord j)))
          (table.combinedSite
            (x (geometry.freeColumnCoord i,
              geometry.freeRowCoord ⟨j.val + 1, hj⟩))) = true)

namespace CombinedSiteCorridorRouting

/--
Build combined-site corridor routing from an explicit selected site rectangle.

This is the proof-facing constructor for the geometric extraction: first name
the Figure 18 site seen at each free crossing, prove that it agrees with the
decoded combined tile there, and then state active/corner/local-compatibility
facts against that cleaner rectangle.
-/
noncomputable def ofSiteRect
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (siteRect :
      Fin (RobinsonSquare.freeGridSide level) →
        Fin (RobinsonSquare.freeGridSide level) → Figure18Site)
    (site_eq :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          table.combinedSite
            (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) =
          siteRect i j)
    (active :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          CellRole.isActive (table.roleAtSite (siteRect i j)) = true)
    (cornerSite :
      siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
        ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite)
    (htransmit :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
            (∀ column : Int, geometry.isBoardColumn column →
              ¬ geometry.hasHorizontalObstruction column
                (geometry.freeRowCoord j)) →
              WangTile.HMatches
                (table.combinedPayload
                  (x (geometry.freeColumnCoord i,
                    geometry.freeRowCoord j)))
                (table.combinedPayload
                  (x (geometry.freeColumnCoord ⟨i.val + 1, hi⟩,
                    geometry.freeRowCoord j))))
    (vtransmit :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
            (∀ row : Int, geometry.isBoardRow row →
              ¬ geometry.hasVerticalObstruction
                (geometry.freeColumnCoord i) row) →
              WangTile.VMatches
                (table.combinedPayload
                  (x (geometry.freeColumnCoord i,
                    geometry.freeRowCoord j)))
                (table.combinedPayload
                  (x (geometry.freeColumnCoord i,
                    geometry.freeRowCoord ⟨j.val + 1, hj⟩))))
    (siteCompatible :
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.hCompatible
            (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
      (∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          Figure18Site.vCompatible
            (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)) :
    CombinedSiteCorridorRouting table x geometry where
  active := by
    intro i j
    simpa [site_eq i j] using active i j
  cornerSite := by
    simpa [site_eq ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩] using cornerSite
  htransmit := htransmit
  vtransmit := vtransmit
  siteCompatible := by
    rcases siteCompatible with ⟨hcompat, vcompat⟩
    constructor
    · intro i j hi
      simpa [site_eq i j, site_eq ⟨i.val + 1, hi⟩ j] using
        hcompat i j hi
    · intro i j hj
      simpa [site_eq i j, site_eq i ⟨j.val + 1, hj⟩] using
        vcompat i j hj

/--
Decoded combined-site corridor routing with the site rectangle named
explicitly.

This is the proof target intended for the local scaffold extraction: choose the
Figure 18 site at every free crossing, prove that it agrees with the decoded
combined tile there, and state the active/corner/compatibility facts directly
on that named rectangle.
-/
structure SiteRectRouting
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    {level : Nat}
    (geometry : RobinsonBoardSignalGeometry level) : Type where
  siteRect :
    Fin (RobinsonSquare.freeGridSide level) →
      Fin (RobinsonSquare.freeGridSide level) → Figure18Site
  site_eq :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        table.combinedSite
          (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) =
        siteRect i j
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite
  htransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          (∀ column : Int, geometry.isBoardColumn column →
            ¬ geometry.hasHorizontalObstruction column
              (geometry.freeRowCoord j)) →
            WangTile.HMatches
              (table.combinedPayload
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord j)))
              (table.combinedPayload
                (x (geometry.freeColumnCoord ⟨i.val + 1, hi⟩,
                  geometry.freeRowCoord j)))
  vtransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          (∀ row : Int, geometry.isBoardRow row →
            ¬ geometry.hasVerticalObstruction
              (geometry.freeColumnCoord i) row) →
            WangTile.VMatches
              (table.combinedPayload
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord j)))
              (table.combinedPayload
                (x (geometry.freeColumnCoord i,
                  geometry.freeRowCoord ⟨j.val + 1, hj⟩)))
  siteCompatible :
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.hCompatible
          (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.vCompatible
          (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)

namespace SiteRectRouting

/-- The selected coordinate of a site-rectangle routing is a free crossing. -/
theorem selectedCoord_isFreeCrossing
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (_routing : SiteRectRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    geometry.IsFreeCrossing
      (geometry.freeColumnCoord i) (geometry.freeRowCoord j) :=
  geometry.isFreeCrossing_freeCoord i j

/--
The site rectangle records the decoded combined-tile site at each selected
free crossing.
-/
theorem combinedSite_eq_at_selectedCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : SiteRectRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    table.combinedSite
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) =
      routing.siteRect i j :=
  routing.site_eq i j

/-- The decoded site at each selected free crossing is active. -/
theorem active_at_selectedCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : SiteRectRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    CellRole.isActive (table.roleAtSite
      (table.combinedSite
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)))) = true := by
  simpa [routing.combinedSite_eq_at_selectedCoord i j] using
    routing.active i j

/-- Selected free crossings have neither obstruction through the crossing cell. -/
theorem noObstruction_at_selectedCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (_routing : SiteRectRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (¬ geometry.hasHorizontalObstruction
        (geometry.freeColumnCoord i) (geometry.freeRowCoord j)) ∧
      ¬ geometry.hasVerticalObstruction
        (geometry.freeColumnCoord i) (geometry.freeRowCoord j) :=
  geometry.noObstruction_at_freeCrossing i j

/-- Forget the named site rectangle after using it to build combined routing. -/
noncomputable def toCombinedSiteCorridorRouting
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : SiteRectRouting table x geometry) :
    CombinedSiteCorridorRouting table x geometry :=
  ofSiteRect routing.siteRect routing.site_eq routing.active routing.cornerSite
    routing.htransmit routing.vtransmit routing.siteCompatible

end SiteRectRouting

/--
Canonical-site-rectangle routing at one Robinson board level.

This is the local proof shape for the canonical Section 7 geometry: the free
crossings are already the selected canonical rows and columns, so the payload
transmission fields do not ask the caller to restate the obstruction-signal
premises.  Those premises are reintroduced automatically when converting to the
general `SiteRectRouting` interface.
-/
structure CanonicalSiteRectRouting
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed))
    (level : Nat) : Type where
  siteRect :
    Fin (RobinsonSquare.freeGridSide level) →
      Fin (RobinsonSquare.freeGridSide level) → Figure18Site
  site_eq :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        table.combinedSite
          (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
            (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)) =
        siteRect i j
  active :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        CellRole.isActive (table.roleAtSite (siteRect i j)) = true
  cornerSite :
    siteRect ⟨0, RobinsonSquare.freeGridSide_pos level⟩
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩ = table.cornerSite
  htransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.HMatches
            (table.combinedPayload
              (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
                (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
            (table.combinedPayload
              (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
                ⟨i.val + 1, hi⟩,
                (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
  vtransmit :
    ∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
        ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
          WangTile.VMatches
            (table.combinedPayload
              (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
                (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
            (table.combinedPayload
              (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
                (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
                  ⟨j.val + 1, hj⟩)))
  siteCompatible :
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hi : i.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.hCompatible
          (siteRect i j) (siteRect ⟨i.val + 1, hi⟩ j) = true) ∧
    (∀ i : Fin (RobinsonSquare.freeGridSide level),
      ∀ j : Fin (RobinsonSquare.freeGridSide level),
      ∀ hj : j.val + 1 < RobinsonSquare.freeGridSide level,
        Figure18Site.vCompatible
          (siteRect i j) (siteRect i ⟨j.val + 1, hj⟩) = true)

namespace CanonicalSiteRectRouting

/--
Build canonical site-rectangle routing from the two genuinely geometric facts:
every canonical free crossing decodes to an active site, and the lower-left
crossing decodes to the corner site.

For the canonical obstruction geometry, adjacent free crossings are adjacent
plane cells.  Therefore local Figure 18 compatibility and payload transmission
are consequences of `ValidPlaneTiling`.
-/
noncomputable def ofActiveCorner
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (hx : ValidPlaneTiling
      (combineWithScaffold table.presentation.toScaffold T seed) x)
    (active :
      ∀ i : Fin (RobinsonSquare.freeGridSide level),
        ∀ j : Fin (RobinsonSquare.freeGridSide level),
          CellRole.isActive
            (table.roleAtSite
              (table.combinedSite
                (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
                  (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))) =
            true)
    (cornerSite :
      table.combinedSite
          (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
              ⟨0, RobinsonSquare.freeGridSide_pos level⟩,
            (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
              ⟨0, RobinsonSquare.freeGridSide_pos level⟩)) =
        table.cornerSite) :
    CanonicalSiteRectRouting table x level where
  siteRect := fun i j =>
    table.combinedSite
      (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
        (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j))
  site_eq := by
    intro i j
    rfl
  active := active
  cornerSite := cornerSite
  htransmit := by
    intro i j hi
    have hcompat :
        Figure18Site.hCompatible
          (table.combinedSite
            (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
              (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
          (table.combinedSite
            (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
              ⟨i.val + 1, hi⟩,
              (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j))) =
          true := by
      exact table.combinedSite_hCompatible_of_selectedCoords hx
        (RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
        (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
        (RobinsonBoardSignalGeometry.canonical_freeColumnCoord_succ level)
        i j hi
    exact Figure18IndexedRoutedFixedCornerSquare.payload_hMatches_of_validPlaneTiling
      hx hcompat
      (table.combinedPayload_product
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
      (table.combinedPayload_product
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
          ⟨i.val + 1, hi⟩,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
  vtransmit := by
    intro i j hj
    have vcompat :
        Figure18Site.vCompatible
          (table.combinedSite
            (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
              (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
          (table.combinedSite
            (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
              (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
                ⟨j.val + 1, hj⟩))) =
          true := by
      exact table.combinedSite_vCompatible_of_selectedCoords hx
        (RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
        (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
        (RobinsonBoardSignalGeometry.canonical_freeRowCoord_succ level)
        i j hj
    exact Figure18IndexedRoutedFixedCornerSquare.payload_vMatches_of_validPlaneTiling
      hx vcompat
      (table.combinedPayload_product
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))
      (table.combinedPayload_product
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
            ⟨j.val + 1, hj⟩)))
  siteCompatible := by
    constructor
    · intro i j hi
      exact table.combinedSite_hCompatible_of_selectedCoords hx
        (RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
        (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
        (RobinsonBoardSignalGeometry.canonical_freeColumnCoord_succ level)
        i j hi
    · intro i j hj
      exact table.combinedSite_vCompatible_of_selectedCoords hx
        (RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
        (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
        (RobinsonBoardSignalGeometry.canonical_freeRowCoord_succ level)
        i j hj

/--
Canonical site-rectangle routing supplies the general site-rectangle routing
interface over Robinson's canonical obstruction geometry.
-/
noncomputable def toSiteRectRouting
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (routing : CanonicalSiteRectRouting table x level) :
    SiteRectRouting table x (RobinsonBoardSignalGeometry.canonical level) where
  siteRect := routing.siteRect
  site_eq := routing.site_eq
  active := routing.active
  cornerSite := routing.cornerSite
  htransmit := by
    intro i j hi _hclear
    exact routing.htransmit i j hi
  vtransmit := by
    intro i j hj _hclear
    exact routing.vtransmit i j hj
  siteCompatible := routing.siteCompatible

@[simp]
theorem toSiteRectRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (routing : CanonicalSiteRectRouting table x level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toSiteRectRouting.siteRect i j = routing.siteRect i j :=
  rfl

end CanonicalSiteRectRouting

/--
Extract product witnesses from the combined tiling after the geometric proof has
selected and checked the combined sites.
-/
noncomputable def toCorridorProductWitnessRouting
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : CombinedSiteCorridorRouting table x geometry) :
    CorridorProductWitnessRouting table x geometry :=
  CorridorProductWitnessRouting.ofCombinedSites
    routing.active routing.cornerSite routing.htransmit routing.vtransmit
    routing.siteCompatible

@[simp]
theorem toCorridorProductWitnessRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : CombinedSiteCorridorRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toCorridorProductWitnessRouting.siteRect i j =
      table.combinedSite
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) :=
  rfl

@[simp]
theorem toCorridorProductWitnessRouting_payloadWitness_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : CombinedSiteCorridorRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (routing.toCorridorProductWitnessRouting.payloadWitness i j).1 =
      table.combinedPayload
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) :=
  rfl

@[simp]
theorem ofSiteRect_toCorridorProductWitnessRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (siteRect :
      Fin (RobinsonSquare.freeGridSide level) →
        Fin (RobinsonSquare.freeGridSide level) → Figure18Site)
    (site_eq active cornerSite htransmit vtransmit siteCompatible)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    ((ofSiteRect (table := table) (x := x) (geometry := geometry)
      siteRect site_eq active cornerSite htransmit vtransmit
      siteCompatible).toCorridorProductWitnessRouting).siteRect i j =
      siteRect i j := by
  simp [toCorridorProductWitnessRouting_siteRect_apply, site_eq i j]

@[simp]
theorem ofSiteRect_toCorridorProductWitnessRouting_payloadWitness_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (siteRect :
      Fin (RobinsonSquare.freeGridSide level) →
        Fin (RobinsonSquare.freeGridSide level) → Figure18Site)
    (site_eq active cornerSite htransmit vtransmit siteCompatible)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (((ofSiteRect (table := table) (x := x) (geometry := geometry)
      siteRect site_eq active cornerSite htransmit vtransmit
      siteCompatible).toCorridorProductWitnessRouting).payloadWitness i j).1 =
      table.combinedPayload
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) :=
  rfl

@[simp]
theorem SiteRectRouting.toCombinedSiteCorridorRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : SiteRectRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (routing.toCombinedSiteCorridorRouting.toCorridorProductWitnessRouting).siteRect
      i j = routing.siteRect i j :=
  routing.site_eq i j

@[simp]
theorem SiteRectRouting.toCombinedSiteCorridorRouting_payloadWitness_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : SiteRectRouting table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    ((routing.toCombinedSiteCorridorRouting.toCorridorProductWitnessRouting).payloadWitness
      i j).1 =
      table.combinedPayload
        (x (geometry.freeColumnCoord i, geometry.freeRowCoord j)) := by
  simp [SiteRectRouting.toCombinedSiteCorridorRouting]

end CombinedSiteCorridorRouting

namespace Routing

/-- Assemble the full signal certificate from geometry plus routing data. -/
def toCertificate
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry) :
    Figure18RobinsonBoardSignalCertificate table x level :=
  ofGeometry geometry routing.siteRect routing.payloadRect routing.active
    routing.cornerSite routing.product routing.hmatch routing.vmatch

@[simp]
theorem toCertificate_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toCertificate.siteRect i j = routing.siteRect i j :=
  rfl

@[simp]
theorem toCertificate_payloadRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toCertificate.payloadRect i j = routing.payloadRect i j :=
  rfl

/--
Ordinary routing already contains the payload rectangle and product equations,
so it can be re-exposed in pointwise product-witness form.
-/
def toProductWitnessRouting
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry) :
    ProductWitnessRouting table x geometry where
  siteRect := routing.siteRect
  payloadWitness := fun i j => ⟨routing.payloadRect i j, routing.product i j⟩
  active := routing.active
  cornerSite := routing.cornerSite
  hmatch := routing.hmatch
  vmatch := routing.vmatch
  siteCompatible := by
    simpa [Figure18RobinsonBoardSignalCertificate.SiteCompatible,
      Figure18RobinsonBoardSignalCertificate.ofGeometry] using
      routing.siteCompatible

@[simp]
theorem toProductWitnessRouting_siteRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toProductWitnessRouting.siteRect i j = routing.siteRect i j :=
  rfl

@[simp]
theorem toProductWitnessRouting_payloadWitness_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (routing.toProductWitnessRouting.payloadWitness i j).1 =
      routing.payloadRect i j :=
  rfl

@[simp]
theorem toProductWitnessRouting_payloadRect_apply
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    routing.toProductWitnessRouting.payloadRect i j =
      routing.payloadRect i j :=
  rfl

@[simp]
theorem toCertificate_geometry
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry) :
    routing.toCertificate.geometry = geometry := by
  rfl

theorem toCertificate_siteCompatible
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat} {geometry : RobinsonBoardSignalGeometry level}
    (routing : Routing table x geometry) :
    routing.toCertificate.SiteCompatible :=
  routing.siteCompatible

end Routing

/-- The selected free columns are exactly the columns enumerated by the certificate. -/
theorem isFreeColumn_iff_exists_freeColumnCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column : Int) :
    certificate.isFreeColumn column ↔
      ∃ i : Fin (RobinsonSquare.freeGridSide level),
        certificate.freeColumnCoord i = column := by
  constructor
  · exact certificate.freeColumnCoord_complete column
  · rintro ⟨i, rfl⟩
    exact certificate.freeColumnCoord_free i

/-- The selected free rows are exactly the rows enumerated by the certificate. -/
theorem isFreeRow_iff_exists_freeRowCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (row : Int) :
    certificate.isFreeRow row ↔
      ∃ j : Fin (RobinsonSquare.freeGridSide level),
        certificate.freeRowCoord j = row := by
  constructor
  · exact certificate.freeRowCoord_complete row
  · rintro ⟨j, rfl⟩
    exact certificate.freeRowCoord_free j

/-- A selected free row has no horizontal obstruction at any board column. -/
theorem noHorizontalObstruction_of_freeRowCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (column : Int) (hcolumn : certificate.isBoardColumn column)
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    ¬ certificate.hasHorizontalObstruction column
      (certificate.freeRowCoord j) := by
  have hrow := certificate.freeRow_iff_noHorizontalObstruction
    (certificate.freeRowCoord j) (certificate.freeRowCoord_board j)
  exact (hrow.1 (certificate.freeRowCoord_free j)) column hcolumn

/-- A selected free column has no vertical obstruction at any board row. -/
theorem noVerticalObstruction_of_freeColumnCoord
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (row : Int) (hrow : certificate.isBoardRow row) :
    ¬ certificate.hasVerticalObstruction
      (certificate.freeColumnCoord i) row := by
  have hcolumn := certificate.freeColumn_iff_noVerticalObstruction
    (certificate.freeColumnCoord i) (certificate.freeColumnCoord_board i)
  exact (hcolumn.1 (certificate.freeColumnCoord_free i)) row hrow

/-- A horizontal obstruction through a board row prevents that row from being free. -/
theorem not_freeRow_of_horizontalObstruction
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column row : Int}
    (hrow : certificate.isBoardRow row)
    (hcolumn : certificate.isBoardColumn column)
    (hobs : certificate.hasHorizontalObstruction column row) :
    ¬ certificate.isFreeRow row := by
  intro hfree
  exact (certificate.freeRow_iff_noHorizontalObstruction row hrow).1 hfree
    column hcolumn hobs

/-- A vertical obstruction through a board column prevents that column from being free. -/
theorem not_freeColumn_of_verticalObstruction
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column row : Int}
    (hcolumn : certificate.isBoardColumn column)
    (hrow : certificate.isBoardRow row)
    (hobs : certificate.hasVerticalObstruction column row) :
    ¬ certificate.isFreeColumn column := by
  intro hfree
  exact (certificate.freeColumn_iff_noVerticalObstruction column hcolumn).1
    hfree row hrow hobs

/--
Every non-free board row has a horizontal obstruction at some board column.
-/
theorem exists_horizontalObstruction_of_boardRow_not_free
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {row : Int}
    (hrow : certificate.isBoardRow row)
    (hnotFree : ¬ certificate.isFreeRow row) :
    ∃ column : Int,
      certificate.isBoardColumn column ∧
        certificate.hasHorizontalObstruction column row := by
  by_contra hnone
  apply hnotFree
  refine (certificate.freeRow_iff_noHorizontalObstruction row hrow).2 ?_
  intro column hcolumn hobs
  exact hnone ⟨column, hcolumn, hobs⟩

/--
Every non-free board column has a vertical obstruction at some board row.
-/
theorem exists_verticalObstruction_of_boardColumn_not_free
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    {column : Int}
    (hcolumn : certificate.isBoardColumn column)
    (hnotFree : ¬ certificate.isFreeColumn column) :
    ∃ row : Int,
      certificate.isBoardRow row ∧
        certificate.hasVerticalObstruction column row := by
  by_contra hnone
  apply hnotFree
  refine (certificate.freeColumn_iff_noVerticalObstruction column hcolumn).2 ?_
  intro row hrow hobs
  exact hnone ⟨row, hrow, hobs⟩

/--
At a selected free-row/free-column crossing, neither obstruction signal is
present.
-/
theorem noObstruction_at_freeCrossing
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (¬ certificate.hasHorizontalObstruction
        (certificate.freeColumnCoord i) (certificate.freeRowCoord j)) ∧
      ¬ certificate.hasVerticalObstruction
        (certificate.freeColumnCoord i) (certificate.freeRowCoord j) := by
  constructor
  · exact certificate.noHorizontalObstruction_of_freeRowCoord
      (certificate.freeColumnCoord i) (certificate.freeColumnCoord_board i) j
  · exact certificate.noVerticalObstruction_of_freeColumnCoord
      i (certificate.freeRowCoord j) (certificate.freeRowCoord_board j)

/--
Column-coordinate recurrence between consecutive Robinson signal certificates.

This is the coordinate-level form of Robinson's repeated free-column pattern;
the proof of Section 7 should supply this for the certificates it constructs.
-/
def ColumnCoordinateStep
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (parent : Figure18RobinsonBoardSignalCertificate table x level)
    (child : Figure18RobinsonBoardSignalCertificate table x (level + 1)) :
    Type :=
  RobinsonSquare.FreeLineCoordinateStep level
    parent.freeColumnCoord child.freeColumnCoord

/--
Row-coordinate recurrence between consecutive Robinson signal certificates.
-/
def RowCoordinateStep
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (parent : Figure18RobinsonBoardSignalCertificate table x level)
    (child : Figure18RobinsonBoardSignalCertificate table x (level + 1)) :
    Type :=
  RobinsonSquare.FreeLineCoordinateStep level
    parent.freeRowCoord child.freeRowCoord

/--
Both coordinate recurrences needed for the next-level Robinson board to be
assembled from two translated copies of the previous level's free grid.
-/
structure CoordinateStep
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (parent : Figure18RobinsonBoardSignalCertificate table x level)
    (child : Figure18RobinsonBoardSignalCertificate table x (level + 1)) :
    Type where
  columns : ColumnCoordinateStep parent child
  rows : RowCoordinateStep parent child

/--
A coordinate recurrence proved at the obstruction-geometry level induces the
same recurrence for full Figure 18 signal certificates.
-/
def CoordinateStep.ofGeometry
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step :
      RobinsonBoardSignalGeometry.CoordinateStep
        parent.geometry child.geometry) :
    CoordinateStep parent child where
  columns := by
    exact step.columns
  rows := by
    exact step.rows

/--
Column-coordinate overlap forced by the two translated copies in Robinson's
free-line recurrence.
-/
theorem columnCoordinateStep_overlap
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : ColumnCoordinateStep parent child) :
    parent.freeColumnCoord (RobinsonSquare.freeGridLast level) +
        step.leftOffset =
      parent.freeColumnCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.overlap step

/-- Row-coordinate overlap forced by the free-line recurrence. -/
theorem rowCoordinateStep_overlap
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : RowCoordinateStep parent child) :
    parent.freeRowCoord (RobinsonSquare.freeGridLast level) +
        step.leftOffset =
      parent.freeRowCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.overlap step

/-- Child column coordinate from its canonical previous-level preimage. -/
theorem columnCoordinateStep_child_eq_preimage
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : ColumnCoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeColumnCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.leftOffset
      | .right =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.child_eq_preimage step i

/-- Child row coordinate from its canonical previous-level preimage. -/
theorem rowCoordinateStep_child_eq_preimage
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : RowCoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeRowCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.leftOffset
      | .right =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rightOffset :=
  RobinsonSquare.FreeLineCoordinateStep.child_eq_preimage step i

namespace CoordinateStep

/-- Column-coordinate overlap from a combined coordinate step. -/
theorem column_overlap
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child) :
    parent.freeColumnCoord (RobinsonSquare.freeGridLast level) +
        step.columns.leftOffset =
      parent.freeColumnCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.columns.rightOffset :=
  columnCoordinateStep_overlap step.columns

/-- Row-coordinate overlap from a combined coordinate step. -/
theorem row_overlap
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child) :
    parent.freeRowCoord (RobinsonSquare.freeGridLast level) +
        step.rows.leftOffset =
      parent.freeRowCoord ⟨0, RobinsonSquare.freeGridSide_pos level⟩ +
        step.rows.rightOffset :=
  rowCoordinateStep_overlap step.rows

/-- Child column coordinate from a combined coordinate step. -/
theorem column_child_eq_preimage
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeColumnCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.columns.leftOffset
      | .right =>
          parent.freeColumnCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.columns.rightOffset :=
  columnCoordinateStep_child_eq_preimage step.columns i

/-- Child row coordinate from a combined coordinate step. -/
theorem row_child_eq_preimage
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    child.freeRowCoord i =
      match (RobinsonSquare.freeLinePreimage level i).side with
      | .left =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rows.leftOffset
      | .right =>
          parent.freeRowCoord
            (RobinsonSquare.freeLinePreimage level i).index +
            step.rows.rightOffset :=
  rowCoordinateStep_child_eq_preimage step.rows i

/--
The lower-left translated copy of a parent free-grid crossing inside the next
Robinson level.
-/
theorem childCoord_left_left
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (child.freeColumnCoord (RobinsonSquare.freeLineLeftEmbedding level i),
      child.freeRowCoord (RobinsonSquare.freeLineLeftEmbedding level j)) =
    (parent.freeColumnCoord i + step.columns.leftOffset,
      parent.freeRowCoord j + step.rows.leftOffset) := by
  apply Prod.ext
  · exact step.columns.left i
  · exact step.rows.left j

/--
The upper-left translated copy of a parent free-grid crossing inside the next
Robinson level.
-/
theorem childCoord_left_right
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (child.freeColumnCoord (RobinsonSquare.freeLineLeftEmbedding level i),
      child.freeRowCoord (RobinsonSquare.freeLineRightEmbedding level j)) =
    (parent.freeColumnCoord i + step.columns.leftOffset,
      parent.freeRowCoord j + step.rows.rightOffset) := by
  apply Prod.ext
  · exact step.columns.left i
  · exact step.rows.right j

/--
The lower-right translated copy of a parent free-grid crossing inside the next
Robinson level.
-/
theorem childCoord_right_left
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (child.freeColumnCoord (RobinsonSquare.freeLineRightEmbedding level i),
      child.freeRowCoord (RobinsonSquare.freeLineLeftEmbedding level j)) =
    (parent.freeColumnCoord i + step.columns.rightOffset,
      parent.freeRowCoord j + step.rows.leftOffset) := by
  apply Prod.ext
  · exact step.columns.right i
  · exact step.rows.left j

/--
The upper-right translated copy of a parent free-grid crossing inside the next
Robinson level.
-/
theorem childCoord_right_right
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide level))
    (j : Fin (RobinsonSquare.freeGridSide level)) :
    (child.freeColumnCoord (RobinsonSquare.freeLineRightEmbedding level i),
      child.freeRowCoord (RobinsonSquare.freeLineRightEmbedding level j)) =
    (parent.freeColumnCoord i + step.columns.rightOffset,
      parent.freeRowCoord j + step.rows.rightOffset) := by
  apply Prod.ext
  · exact step.columns.right i
  · exact step.rows.right j

/--
Coordinate value of any child free-grid crossing, expressed through the
canonical column and row preimages in the previous Robinson level.
-/
theorem childCoord_eq_preimage
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {parent : Figure18RobinsonBoardSignalCertificate table x level}
    {child : Figure18RobinsonBoardSignalCertificate table x (level + 1)}
    (step : CoordinateStep parent child)
    (i : Fin (RobinsonSquare.freeGridSide (level + 1)))
    (j : Fin (RobinsonSquare.freeGridSide (level + 1))) :
    (child.freeColumnCoord i, child.freeRowCoord j) =
      match (RobinsonSquare.freeLinePreimage level i).side,
          (RobinsonSquare.freeLinePreimage level j).side with
      | .left, .left =>
          (parent.freeColumnCoord
              (RobinsonSquare.freeLinePreimage level i).index +
              step.columns.leftOffset,
            parent.freeRowCoord
              (RobinsonSquare.freeLinePreimage level j).index +
              step.rows.leftOffset)
      | .left, .right =>
          (parent.freeColumnCoord
              (RobinsonSquare.freeLinePreimage level i).index +
              step.columns.leftOffset,
            parent.freeRowCoord
              (RobinsonSquare.freeLinePreimage level j).index +
              step.rows.rightOffset)
      | .right, .left =>
          (parent.freeColumnCoord
              (RobinsonSquare.freeLinePreimage level i).index +
              step.columns.rightOffset,
            parent.freeRowCoord
              (RobinsonSquare.freeLinePreimage level j).index +
              step.rows.leftOffset)
      | .right, .right =>
          (parent.freeColumnCoord
              (RobinsonSquare.freeLinePreimage level i).index +
              step.columns.rightOffset,
            parent.freeRowCoord
              (RobinsonSquare.freeLinePreimage level j).index +
              step.rows.rightOffset) := by
  cases hcol : (RobinsonSquare.freeLinePreimage level i).side <;>
    cases hrow : (RobinsonSquare.freeLinePreimage level j).side
  all_goals
    apply Prod.ext
    · have h := column_child_eq_preimage step i
      simpa [hcol] using h
    · have h := row_child_eq_preimage step j
      simpa [hrow] using h

end CoordinateStep

/--
Forget the Section 7 obstruction-signal bookkeeping after it has selected and
routed the free grid.
-/
def toRoutedFreeGrid
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    Figure18RobinsonBoardRoutedFreeGrid table x
      (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide_pos level) where
  freeColumnCoord := certificate.freeColumnCoord
  freeRowCoord := certificate.freeRowCoord
  siteRect := certificate.siteRect
  payloadRect := certificate.payloadRect
  active := certificate.active
  cornerSite := certificate.cornerSite
  product := certificate.product
  hmatch := certificate.hmatch
  vmatch := certificate.vmatch

/--
After the obstruction-signal bookkeeping has selected and routed a Robinson
free grid, the certificate yields the extracted fixed-corner payload square.
-/
theorem tileable
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    (certificate : Figure18RobinsonBoardSignalCertificate table x level) :
    TileableFixedCornerSquare T seed (RobinsonSquare.freeGridSide level) :=
  certificate.toRoutedFreeGrid.tileable

/-- Local site compatibility transfers to the routed free-grid view. -/
theorem siteCompatible_toRoutedFreeGrid
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    {level : Nat}
    {certificate : Figure18RobinsonBoardSignalCertificate table x level}
    (hsite : certificate.SiteCompatible) :
    certificate.toRoutedFreeGrid.SiteCompatible := by
  simpa [toRoutedFreeGrid,
    SiteCompatible,
    Figure18RobinsonBoardRoutedFreeGrid.SiteCompatible] using hsite

end Figure18RobinsonBoardSignalCertificate

/--
Level-indexed Robinson Section 7 signal invariant.

This is the intended geometric proof target from Robinson's original argument.
It is stronger than the public routed-grid invariant because it also records
the obstruction signals used to recognize the free rows and columns.
-/
def HasFigure18RobinsonBoardLevelSignalCertificatesForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ level : Nat,
        Nonempty (Figure18RobinsonBoardSignalCertificate table x level)

/--
Level-indexed Robinson Section 7 signal invariant with finite local site
compatibility for the selected virtual free-grid neighbors.
-/
def HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ level : Nat,
        Nonempty
          { certificate :
              Figure18RobinsonBoardSignalCertificate table x level //
            certificate.SiteCompatible }

/-- Forget the finite local site checks from a local signal certificate. -/
theorem hasFigure18RobinsonBoardLevelSignalCertificatesForTable_of_local
    {table : Figure18RoleTable}
    (hlocal :
      HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable table) :
    HasFigure18RobinsonBoardLevelSignalCertificatesForTable table := by
  intro T seed x hx level
  rcases hlocal x hx level with ⟨certificate, _hsite⟩
  exact ⟨certificate⟩

/--
Level-indexed Robinson Section 7 signal invariant with the free-line
recurrence between consecutive board levels.

This records the part of Robinson's Section 7 argument that says the
next-level free-row/free-column pattern is made from two translated copies of
the previous level's pattern, overlapping at the central free line.
-/
def HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ level : Nat,
        Nonempty
          (Σ parent : Figure18RobinsonBoardSignalCertificate table x level,
            Σ child : Figure18RobinsonBoardSignalCertificate table x (level + 1),
              Figure18RobinsonBoardSignalCertificate.CoordinateStep
                parent child)

/--
Forgetting the coordinate recurrence leaves the obstruction-signal certificate
surface used by the existing scaffold reduction.
-/
theorem hasFigure18RobinsonBoardLevelSignalCertificatesForTable_of_coordinateSteps
    {table : Figure18RoleTable}
    (hsteps :
      HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable table) :
    HasFigure18RobinsonBoardLevelSignalCertificatesForTable table := by
  intro T seed x hx level
  rcases hsteps x hx level with ⟨parent, child, step⟩
  exact ⟨parent⟩

/--
Level-indexed Robinson Section 7 signal invariant with both finite local site
compatibility and the free-line recurrence between consecutive board levels.

This is the preferred proof target for the concrete scaffold: the local site
checks feed the finite layer-stack verifier, while the coordinate step records
Robinson's recurrence for the free rows and columns.
-/
def HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ level : Nat,
        Nonempty
          (Σ parent :
              { certificate :
                  Figure18RobinsonBoardSignalCertificate table x level //
                certificate.SiteCompatible },
            Σ child :
              { certificate :
                  Figure18RobinsonBoardSignalCertificate table x (level + 1) //
                certificate.SiteCompatible },
              Figure18RobinsonBoardSignalCertificate.CoordinateStep
                parent.1 child.1)

/--
Coherent level tower for Robinson Section 7 signal certificates.

Robinson's nested-board proof constructs one board certificate at every level
and a coordinate recurrence between consecutive levels.  This tower form is
closer to that construction than `HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable`,
which only asks for an independent parent/child pair at each level.
-/
def HasFigure18RobinsonBoardLevelSignalTowerForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (Σ certificates :
            (level : Nat) →
              Figure18RobinsonBoardSignalCertificate table x level,
          ∀ level : Nat,
            Figure18RobinsonBoardSignalCertificate.CoordinateStep
              (certificates level) (certificates (level + 1)))

/--
Coherent level tower with the finite local Figure 18 compatibility checks
needed by the layer-stack verifier.
-/
def HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (Σ certificates :
            (level : Nat) →
              { certificate :
                  Figure18RobinsonBoardSignalCertificate table x level //
                certificate.SiteCompatible },
          ∀ level : Nat,
            Figure18RobinsonBoardSignalCertificate.CoordinateStep
              (certificates level).1 (certificates (level + 1)).1)

/--
Cleaner witness shape for Robinson's coherent Section 7 local tower.

The existing theorem-facing `HasFigure18RobinsonBoardLevelSignalLocalTowerForTable`
uses a dependent sigma of subtype-valued certificates.  This structure exposes
the same data as ordinary fields: one board signal certificate per level, a
local Figure 18 compatibility proof for each level, and the free-line coordinate
recurrence between consecutive levels.
-/
structure Figure18RobinsonBoardSignalLocalTower
    (table : Figure18RoleTable)
    {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)) :
    Type where
  certificates :
    (level : Nat) → Figure18RobinsonBoardSignalCertificate table x level
  siteCompatible :
    ∀ level : Nat, (certificates level).SiteCompatible
  steps :
    ∀ level : Nat,
      Figure18RobinsonBoardSignalCertificate.CoordinateStep
        (certificates level) (certificates (level + 1))

namespace Figure18RobinsonBoardSignalLocalTower

/-- Convert the field-based local tower into the subtype tower used downstream. -/
def toSubtypeTower
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    (tower : Figure18RobinsonBoardSignalLocalTower table x) :
    (Σ certificates :
        (level : Nat) →
          { certificate :
              Figure18RobinsonBoardSignalCertificate table x level //
            certificate.SiteCompatible },
      ∀ level : Nat,
        Figure18RobinsonBoardSignalCertificate.CoordinateStep
          (certificates level).1 (certificates (level + 1)).1) :=
  ⟨fun level => ⟨tower.certificates level, tower.siteCompatible level⟩,
    tower.steps⟩

/--
Build the proof-facing local tower from a pure obstruction-geometry tower and
Figure 18 routing data at each level.
-/
def ofGeometryTower
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    (geometryTower : RobinsonBoardSignalGeometryTower)
    (routing :
      ∀ level : Nat,
        Figure18RobinsonBoardSignalCertificate.Routing table x
          (geometryTower.geometries level)) :
    Figure18RobinsonBoardSignalLocalTower table x where
  certificates := fun level => (routing level).toCertificate
  siteCompatible := fun level =>
    (routing level).toCertificate_siteCompatible
  steps := fun level =>
    Figure18RobinsonBoardSignalCertificate.CoordinateStep.ofGeometry
      (geometryTower.steps level)

/-- Recover the field-based local tower from the subtype tower. -/
def ofSubtypeTower
    {table : Figure18RoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.presentation.toScaffold T seed)}
    (tower :
      (Σ certificates :
          (level : Nat) →
            { certificate :
                Figure18RobinsonBoardSignalCertificate table x level //
              certificate.SiteCompatible },
        ∀ level : Nat,
          Figure18RobinsonBoardSignalCertificate.CoordinateStep
            (certificates level).1 (certificates (level + 1)).1)) :
    Figure18RobinsonBoardSignalLocalTower table x where
  certificates := fun level => (tower.1 level).1
  siteCompatible := fun level => (tower.1 level).2
  steps := tower.2

end Figure18RobinsonBoardSignalLocalTower

/--
Field-based local towers are exactly the existing theorem-facing local tower
surface.
-/
theorem hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_iff_tower
    {table : Figure18RoleTable} :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table ↔
      ∀ {T : TileSet} {seed : WangTile}
        (x : Int × Int → TileIn (combineWithScaffold
          table.presentation.toScaffold T seed)),
        ValidPlaneTiling (combineWithScaffold
          table.presentation.toScaffold T seed) x →
          Nonempty (Figure18RobinsonBoardSignalLocalTower table x) := by
  constructor
  · intro htower T seed x hx
    rcases htower x hx with ⟨tower⟩
    exact ⟨Figure18RobinsonBoardSignalLocalTower.ofSubtypeTower tower⟩
  · intro htower T seed x hx
    rcases htower x hx with ⟨tower⟩
    exact ⟨tower.toSubtypeTower⟩

/--
Constructor for the existing local-tower obligation from the cleaner
field-based Robinson Section 7 witness.
-/
theorem hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower
    {table : Figure18RoleTable}
    (htower :
      ∀ {T : TileSet} {seed : WangTile}
        (x : Int × Int → TileIn (combineWithScaffold
          table.presentation.toScaffold T seed)),
        ValidPlaneTiling (combineWithScaffold
          table.presentation.toScaffold T seed) x →
          Nonempty (Figure18RobinsonBoardSignalLocalTower table x)) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_iff_tower.2 htower

/--
Robinson Section 7 proof target split into pure obstruction geometry plus
Figure 18 routing over that geometry.

The geometry tower records the nested-board/free-line recurrence independent of
the payload tiles.  The routing data, still depending on the combined tiling,
decodes the Figure 18 sites at the free crossings and proves their local
compatibility.
-/
def HasFigure18RobinsonBoardGeometryTowerRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (Σ geometryTower : RobinsonBoardSignalGeometryTower,
          ∀ level : Nat,
            Figure18RobinsonBoardSignalCertificate.Routing table x
              (geometryTower.geometries level))

/--
Robinson Section 7 proof target split into pure obstruction geometry plus
decoded combined-site corridor routing.

Unlike the fixed/canonical variants, the geometry tower is selected after a
combined tiling is given.  This matches Robinson's board argument more closely:
the red borders and their free rows/columns are extracted from the tiling, and
the Figure 18 data is then routed along those free corridors.
-/
def HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (Σ geometryTower : RobinsonBoardSignalGeometryTower,
          ∀ level : Nat,
            Figure18RobinsonBoardSignalCertificate.CombinedSiteCorridorRouting
              table x (geometryTower.geometries level))

/--
Figure 18 routing over a fixed Robinson obstruction-geometry tower.

This is the payload-dependent half of the Section 7 proof once the pure
board/free-line geometry has been chosen.
-/
def HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
    (table : Figure18RoleTable)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          Figure18RobinsonBoardSignalCertificate.Routing table x
            (geometryTower.geometries level))

/--
Product-witness Figure 18 routing over a fixed Robinson obstruction-geometry
tower.

This is a more constructive target for the payload-dependent half of the
Section 7 proof: at each free crossing, exhibit a payload component of the
combined tile, then convert those pointwise witnesses to the theorem-facing
`Routing` package.
-/
def HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
    (table : Figure18RoleTable)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          Figure18RobinsonBoardSignalCertificate.ProductWitnessRouting
            table x (geometryTower.geometries level))

/--
Robinson Section 7 routing over a fixed geometry tower, stated with explicit
payload transmission along unobstructed board rows and columns.

This is the next proof-facing target after the pure red-border geometry: local
tile rules should show that no obstruction signal on a selected free line
transports the relevant payload edge color across that board corridor.
-/
def HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable
    (table : Figure18RoleTable)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          Figure18RobinsonBoardSignalCertificate.CorridorProductWitnessRouting
            table x (geometryTower.geometries level))

/--
Robinson Section 7 routing over a fixed geometry tower, stated at the decoded
combined-site level.

This is the most concrete scaffold target short of proving the local tile
rules: the geometric proof selects the free crossings in the combined tiling,
proves the decoded Figure 18 sites are the expected active/corner sites, and
shows unobstructed corridors transmit the decoded payload edge colors.
-/
def HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
    (table : Figure18RoleTable)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          Figure18RobinsonBoardSignalCertificate.CombinedSiteCorridorRouting
            table x (geometryTower.geometries level))

/--
Site-rectangle form of combined-site corridor routing over a fixed geometry
tower.

This keeps the selected Figure 18 site rectangle visible in the proof
obligation, so the local scaffold argument can prove recognizability and
compatibility against named sites before forgetting that extra data.
-/
def HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTowerForTable
    (table : Figure18RoleTable)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          Figure18RobinsonBoardSignalCertificate.CombinedSiteCorridorRouting.SiteRectRouting
            table x (geometryTower.geometries level))

/--
Robinson Section 7 proof target with a single geometry tower selected
independently of the payload tiles and the combined tiling.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∃ geometryTower : RobinsonBoardSignalGeometryTower,
    HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
      table geometryTower

/--
Fixed-geometry variant whose payload-dependent routing is supplied in
pointwise product-witness form.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∃ geometryTower : RobinsonBoardSignalGeometryTower,
    HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
      table geometryTower

/--
Fixed-geometry variant whose payload routing is supplied by explicit corridor
transmission facts.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∃ geometryTower : RobinsonBoardSignalGeometryTower,
    HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable
      table geometryTower

/--
Fixed-geometry variant whose payload routing is supplied by decoded
combined-site corridor facts.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∃ geometryTower : RobinsonBoardSignalGeometryTower,
    HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
      table geometryTower

/--
Fixed-geometry variant whose payload routing is supplied by named site
rectangles at the free crossings.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerSiteRectCombinedSiteCorridorRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∃ geometryTower : RobinsonBoardSignalGeometryTower,
    HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTowerForTable
      table geometryTower

/--
Routing over the canonical Robinson obstruction-geometry tower.

This is equivalent to the canonical product-witness target, but often closer to
the theorem-facing certificate shape.
-/
def HasFigure18RobinsonBoardCanonicalRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
    table canonicalRobinsonBoardSignalGeometryTower

/--
Product-witness routing over the canonical Robinson obstruction-geometry tower.

After the pure Section 7 geometry has been fixed by
`canonicalRobinsonBoardSignalGeometryTower`, this is the remaining
payload-dependent routing target.
-/
def HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
    table canonicalRobinsonBoardSignalGeometryTower

/--
Robinson-style corridor transmission over the canonical obstruction-geometry
tower.
-/
def HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable
    table canonicalRobinsonBoardSignalGeometryTower

/--
Decoded combined-site corridor routing over the canonical Robinson
obstruction-geometry tower.
-/
def HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
    table canonicalRobinsonBoardSignalGeometryTower

/--
Named site-rectangle routing over the canonical Robinson obstruction-geometry
tower.
-/
def HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTowerForTable
    table canonicalRobinsonBoardSignalGeometryTower

section CanonicalFreeSiteRectRouting

open Figure18RobinsonBoardSignalCertificate.CombinedSiteCorridorRouting

/--
Canonical site-rectangle routing with obstruction premises already discharged.

This is the proof-facing variant for the canonical Robinson tower: at each
level the local extraction supplies a named site rectangle and direct payload
transmission across the canonical free crossings.  It converts to
`HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable`
by reintroducing the general obstruction-premise fields automatically.
-/
def HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          CanonicalSiteRectRouting table x level)

/--
The irreducible active/corner part of canonical free-site-rectangle routing.

For canonical free crossings, the payload transmission and local site
compatibility fields are forced by `ValidPlaneTiling`; the geometric scaffold
proof only has to show that those crossings decode to active Figure 18 sites
and that the lower-left crossing is the distinguished corner site.
-/
def HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      Nonempty
        (∀ level : Nat,
          (∀ i : Fin (RobinsonSquare.freeGridSide level),
            ∀ j : Fin (RobinsonSquare.freeGridSide level),
              CellRole.isActive
                (table.roleAtSite
                  (table.combinedSite
                    (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
                      (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)))) =
                true) ∧
          table.combinedSite
              (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord
                  ⟨0, RobinsonSquare.freeGridSide_pos level⟩,
                (RobinsonBoardSignalGeometry.canonical level).freeRowCoord
                  ⟨0, RobinsonSquare.freeGridSide_pos level⟩)) =
            table.cornerSite)

/--
Origin-zero indexed active/corner windows.

The usual active-corner window interface lets the selected square appear at any
origin.  Canonical free-site routing needs the same local recognition at the
canonical free coordinates `0, ..., n - 1`, so this stricter target fixes the
origin to `(0, 0)`.
-/
def HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty
          { window : Figure18IndexedActiveCornerWindow table x n hn //
              window.origin = (0, 0) }

def HasFigure18IndexedActiveCornerOriginZeroWindows
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    Prop :=
  HasFigure18IndexedActiveCornerOriginZeroWindowsForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Semantic origin-zero active/corner windows, phrased directly in terms of the
decoded scaffold site of each combined tile.

This is the leaner target for the geometric Section 7 proof: once the Figure 18
site decoded at each origin-zero coordinate is known to be active, and the
lower-left site is known to be the distinguished corner, the Figure 13 index,
quadrant, and product witnesses required by
`Figure18IndexedActiveCornerWindow` are recovered automatically from the
combined-tile decomposition.
-/
def HasFigure18OriginZeroCombinedActiveCornerWindowsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ n : Nat, 0 < n →
        (∀ i : Fin n, ∀ j : Fin n,
          CellRole.isActive
            (table.roleAtSite
              (table.combinedSite
                (x (Int.ofNat i.val, Int.ofNat j.val)))) = true) ∧
        table.roleAtSite (table.combinedSite (x (0, 0))) = CellRole.corner

/--
Decoded-site origin-zero active/corner windows supply indexed origin-zero
windows.  The proof extracts Figure 13 indices, quadrants, and payload product
witnesses from `table.combinedSite` and `table.combinedPayload`.
-/
theorem
    hasFigure18IndexedActiveCornerOriginZeroWindowsForTable_of_combinedActiveCornerWindows
    {table : Figure18RoleTable}
    (hwindows :
      HasFigure18OriginZeroCombinedActiveCornerWindowsForTable table) :
    HasFigure18IndexedActiveCornerOriginZeroWindowsForTable table := by
  intro T seed x hx n hn
  rcases hwindows x hx n hn with ⟨hactive, hcorner⟩
  let siteAt : Fin n → Fin n → Figure18Site :=
    fun i j => table.combinedSite (x (Int.ofNat i.val, Int.ofNat j.val))
  refine ⟨⟨{
    origin := (0, 0)
    indexRect := fun i j => (siteAt i j).index
    quadrantRect := fun i j => (siteAt i j).quadrant
    active := ?_
    corner := ?_
    product := ?_
  }, rfl⟩⟩
  · intro i j
    simpa [siteAt, Figure18RoleTable.roleAtSite] using hactive i j
  · simpa [siteAt, Figure18RoleTable.roleAtSite] using hcorner
  · intro i j
    refine ⟨table.combinedPayload
      (x (Int.ofNat i.val, Int.ofNat j.val)), ?_⟩
    simpa [siteAt, Figure18Site.tile] using
      table.combinedPayload_product
        (x (Int.ofNat i.val, Int.ofNat j.val))

def HasFigure18OriginZeroCombinedActiveCornerWindows
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) :
    Prop :=
  HasFigure18OriginZeroCombinedActiveCornerWindowsForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Decoded-site origin-zero active/corner windows supply indexed origin-zero
windows for a concrete active-site/corner-site list.
-/
theorem hasFigure18IndexedActiveCornerOriginZeroWindows_of_combinedActiveCornerWindows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18OriginZeroCombinedActiveCornerWindows activeSites cornerSite) :
    HasFigure18IndexedActiveCornerOriginZeroWindows activeSites cornerSite :=
  hasFigure18IndexedActiveCornerOriginZeroWindowsForTable_of_combinedActiveCornerWindows
    hwindows

/--
Origin-zero indexed active/corner windows are a stronger form of the ordinary
translation-invariant indexed active/corner window hypothesis.
-/
theorem hasFigure18IndexedActiveCornerWindows_of_originZeroWindowsForTable
    {table : Figure18RoleTable}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable table) :
    HasFigure18IndexedActiveCornerWindows table := by
  intro T seed x hx n hn
  rcases hwindows x hx n hn with ⟨window, _horigin⟩
  exact ⟨window⟩

/--
Origin-zero indexed active/corner windows are a stronger form of the ordinary
translation-invariant indexed active/corner window hypothesis.
-/
theorem hasFigure18IndexedActiveCornerWindows_of_originZeroWindows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindows activeSites cornerSite) :
    HasFigure18IndexedActiveCornerWindows
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18IndexedActiveCornerWindows_of_originZeroWindowsForTable hwindows

/--
Origin-zero indexed active/corner windows recognize the canonical free
crossings.  The window's pointwise product witnesses identify each combined
base tile with the indexed Figure 18 site at the same canonical coordinate.
-/
theorem
    hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
    {table : Figure18RoleTable}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable table) :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable
      table := by
  intro T seed x hx
  refine ⟨fun level => ?_⟩
  rcases hwindows x hx (RobinsonSquare.freeGridSide level)
      (RobinsonSquare.freeGridSide_pos level) with
    ⟨window, horigin⟩
  constructor
  · intro i j
    let site : Figure18Site := {
      index := window.indexRect i j
      quadrant := window.quadrantRect i j
    }
    have hsite :
        table.combinedSite
            (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
              (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j)) =
          site := by
      rcases window.product i j with ⟨payload, hproduct⟩
      exact table.combinedSite_eq_of_product_site
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j))
        site payload
        (by
          simpa [site, Figure18Site.tile, horigin,
            RobinsonBoardSignalGeometry.canonical] using hproduct)
    rw [hsite]
    simpa [site, Figure18RoleTable.roleAtSite] using window.active i j
  · let i0 : Fin (RobinsonSquare.freeGridSide level) :=
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩
    let j0 : Fin (RobinsonSquare.freeGridSide level) :=
      ⟨0, RobinsonSquare.freeGridSide_pos level⟩
    let site : Figure18Site := {
      index := window.indexRect i0 j0
      quadrant := window.quadrantRect i0 j0
    }
    have hsite :
        table.combinedSite
            (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i0,
              (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j0)) =
          site := by
      rcases window.product i0 j0 with ⟨payload, hproduct⟩
      exact table.combinedSite_eq_of_product_site
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i0,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j0))
        site payload
        (by
          simpa [site, Figure18Site.tile, i0, j0, horigin,
            RobinsonBoardSignalGeometry.canonical] using hproduct)
    have hcornerRole :
        table.roleAtSite
            (table.combinedSite
              (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i0,
                (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j0))) =
          CellRole.corner := by
      rw [hsite]
      simpa [site, i0, j0, Figure18RoleTable.roleAtSite] using
        window.corner
    exact (table.roleAtSite_corner_iff
      (table.combinedSite
        (x ((RobinsonBoardSignalGeometry.canonical level).freeColumnCoord i0,
          (RobinsonBoardSignalGeometry.canonical level).freeRowCoord j0)))).1
      hcornerRole

/--
Canonical active/corner recognition at free crossings supplies full canonical
free-site-rectangle routing; validity of the combined tiling supplies the
transmission and compatibility fields.
-/
theorem
    hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_activeCorner
    {table : Figure18RoleTable}
    (hactiveCorner :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable
        table) :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table := by
  intro T seed x hx
  rcases hactiveCorner x hx with ⟨activeCorner⟩
  exact ⟨fun level =>
    CanonicalSiteRectRouting.ofActiveCorner hx
      (activeCorner level).1 (activeCorner level).2⟩

/--
Origin-zero indexed active/corner windows supply full canonical free-site
rectangle routing.  This is the table-level bridge from local recognizability
at the canonical free coordinates to Robinson Section 7 transmission routing.
-/
theorem
    hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_originZeroWindows
    {table : Figure18RoleTable}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable table) :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table :=
  hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_activeCorner
    (hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
      hwindows)

end CanonicalFreeSiteRectRouting

/--
Combined-site corridor routing over one fixed geometry tower supplies
product-witness corridor routing over the same tower.
-/
theorem
    hasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable_of_combinedSites
    {table : Figure18RoleTable}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable
      table geometryTower := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨fun level => (routing level).toCorridorProductWitnessRouting⟩

/--
Named site-rectangle routing supplies the decoded combined-site corridor target
over the same geometry tower.
-/
theorem
    hasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable_of_siteRect
    {table : Figure18RoleTable}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
      table geometryTower := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨fun level =>
    (routing level).toCombinedSiteCorridorRouting⟩

/--
Fixed-geometry named site-rectangle routing supplies fixed-geometry decoded
combined-site corridor routing.
-/
theorem
    hasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable_of_siteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerSiteRectCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable
      table := by
  rcases hrouting with ⟨geometryTower, hrouting⟩
  exact ⟨geometryTower,
    hasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable_of_siteRect
      hrouting⟩

/--
Canonical named site-rectangle routing supplies canonical decoded combined-site
corridor routing.
-/
theorem
    hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_siteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
      table :=
  hasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable_of_siteRect
    hrouting

/--
Canonical free-crossing site-rectangle routing supplies the existing canonical
site-rectangle corridor-routing target.
-/
theorem
    hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
      table := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨fun level =>
    (routing level).toSiteRectRouting⟩

/--
Canonical free-site-rectangle routing supplies canonical decoded combined-site
corridor routing.
-/
theorem
    hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_freeSiteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
      table :=
  hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_siteRect
    (hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      hrouting)

/--
Canonical free-site-rectangle routing supplies canonical corridor-transmission
routing.
-/
theorem
    hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_freeSiteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
      table :=
  hasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable_of_combinedSites
    (hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_freeSiteRect
      hrouting)

/--
Canonical free-site-rectangle routing supplies canonical product-witness
routing.
-/
theorem
    hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_freeSiteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table := by
  intro T seed x hx
  rcases
    hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_freeSiteRect
      hrouting x hx with
    ⟨routing⟩
  exact ⟨fun level => (routing level).toProductWitnessRouting⟩

/--
Canonical free-site-rectangle routing supplies canonical Robinson-board routing.

This is the direct Section 7 bridge: once the proof has identified the canonical
free crossings and shown that they transmit payload colors like a contiguous
square, the older signal-tower route can be recovered automatically.
-/
theorem hasFigure18RobinsonBoardCanonicalRoutingForTable_of_freeSiteRect
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardCanonicalRoutingForTable table := by
  intro T seed x hx
  rcases
    hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_freeSiteRect
      hrouting x hx with
    ⟨routing⟩
  exact ⟨fun level => (routing level).toRouting⟩

/--
Combined-site corridor routing with a tiling-dependent geometry tower supplies
the existing geometry-plus-routing target.
-/
theorem
    hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_geometryTowerCombinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardGeometryTowerRoutingForTable table := by
  intro T seed x hx
  rcases hrouting x hx with ⟨geometryTower, routing⟩
  refine ⟨⟨geometryTower, ?_⟩⟩
  intro level
  exact (routing level).toCorridorProductWitnessRouting.toProductWitnessRouting.toRouting

/--
Combined-site corridor routing over one fixed geometry tower supplies the
tiling-dependent geometry-combined routing target by choosing that tower.
-/
theorem
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_routingForGeometryTower
    {table : Figure18RoleTable}
    (geometryTower : RobinsonBoardSignalGeometryTower)
    (hrouting :
      HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
      table := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨⟨geometryTower, routing⟩⟩

/--
Fixed-geometry combined-site corridor routing supplies the tiling-dependent
geometry-combined routing target.
-/
theorem
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_fixed
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
      table := by
  rcases hrouting with ⟨geometryTower, hrouting⟩
  exact
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_routingForGeometryTower
      geometryTower hrouting

/--
Canonical combined-site corridor routing supplies the tiling-dependent
geometry-combined routing target by choosing the canonical Robinson tower.
-/
theorem
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_canonical
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
      table :=
  hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_routingForGeometryTower
    canonicalRobinsonBoardSignalGeometryTower hrouting

/--
Canonical combined-site corridor routing supplies the existing canonical
corridor-routing target.
-/
theorem
    hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_combinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
      table :=
  hasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable_of_combinedSites
    hrouting

/--
Fixed-geometry combined-site corridor routing supplies the existing
fixed-geometry corridor-routing target.
-/
theorem
    hasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRoutingForTable_of_combinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRoutingForTable
      table := by
  rcases hrouting with ⟨geometryTower, hrouting⟩
  exact ⟨geometryTower,
    hasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable_of_combinedSites
      hrouting⟩

/--
Corridor-transmission routing over one fixed geometry tower supplies pointwise
product-witness routing over the same tower.
-/
theorem
    hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable_of_corridor
    {table : Figure18RoleTable}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
      table geometryTower := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨fun level => (routing level).toProductWitnessRouting⟩

/--
Canonical corridor-transmission routing supplies the existing canonical
product-witness routing target.
-/
theorem
    hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_corridor
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        table) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table :=
  hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable_of_corridor
    hrouting

/--
Fixed-geometry corridor-transmission routing supplies the existing
fixed-geometry product-witness routing target.
-/
theorem
    hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_corridor
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRoutingForTable
        table) :
    HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
      table := by
  rcases hrouting with ⟨geometryTower, hrouting⟩
  exact ⟨geometryTower,
    hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable_of_corridor
      hrouting⟩

/--
Routing over one fixed geometry tower supplies pointwise product witnesses over
that same tower.
-/
theorem
    hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable_of_routing
    {table : Figure18RoleTable}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
      table geometryTower := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨fun level => (routing level).toProductWitnessRouting⟩

/-- Canonical routing supplies canonical product-witness routing. -/
theorem
    hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_routing
    {table : Figure18RoleTable}
    (hrouting : HasFigure18RobinsonBoardCanonicalRoutingForTable table) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table :=
  hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable_of_routing
    hrouting

/--
Routing over the canonical Robinson tower supplies the older existential
fixed-geometry product-witness target.
-/
theorem
    hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table) :
    HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
      table :=
  ⟨canonicalRobinsonBoardSignalGeometryTower, hrouting⟩

/--
Pointwise product-witness routing over one fixed geometry tower supplies the
existing theorem-facing routing-over-geometry predicate.
-/
theorem
    hasFigure18RobinsonBoardRoutingForGeometryTowerForTable_of_productWitnessRouting
    {table : Figure18RoleTable}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
      table geometryTower := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨fun level => (routing level).toRouting⟩

/--
Fixed geometry plus pointwise product-witness routing supplies the existing
fixed-geometry routing predicate.
-/
theorem
    hasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable_of_productWitnessRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
        table) :
    HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable table := by
  rcases hrouting with ⟨geometryTower, hrouting⟩
  exact ⟨geometryTower,
    hasFigure18RobinsonBoardRoutingForGeometryTowerForTable_of_productWitnessRouting
      hrouting⟩

/--
Routing over one fixed geometry tower supplies the earlier geometry-plus-routing
target.
-/
theorem hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_routingForGeometryTower
    {table : Figure18RoleTable}
    (geometryTower : RobinsonBoardSignalGeometryTower)
    (hrouting :
      HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
        table geometryTower) :
    HasFigure18RobinsonBoardGeometryTowerRoutingForTable table := by
  intro T seed x hx
  rcases hrouting x hx with ⟨routing⟩
  exact ⟨⟨geometryTower, routing⟩⟩

/--
A fixed geometry tower with routing data is a direct refinement of the
geometry-plus-routing target.
-/
theorem hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_fixedGeometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardGeometryTowerRoutingForTable table := by
  rcases hrouting with ⟨geometryTower, hrouting⟩
  exact hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_routingForGeometryTower
    geometryTower hrouting

/--
The geometry-plus-routing target supplies the existing coherent local tower
surface used downstream.
-/
theorem hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table := by
  refine hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_tower ?_
  intro T seed x hx
  rcases hrouting x hx with ⟨geometryTower, routing⟩
  exact ⟨Figure18RobinsonBoardSignalLocalTower.ofGeometryTower
    geometryTower routing⟩

/--
Decoded combined-site corridor routing supplies the coherent local tower
surface directly.

This is the paper-shaped Section 7 route: the tiling supplies the board/free-line
geometry, and the local corridor facts show that the selected free crossings
carry a contiguous payload square.
-/
theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerCombinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_geometryTowerCombinedSites
      hrouting)

/--
The fixed-geometry routing target supplies the existing coherent local tower
surface used downstream.
-/
theorem hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_fixedGeometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_fixedGeometryTowerRouting
      hrouting)

/--
Canonical Robinson-board routing supplies the local Section 7 tower used by the
finite stack checker.
-/
theorem hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
    {table : Figure18RoleTable}
    (hrouting : HasFigure18RobinsonBoardCanonicalRoutingForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_routingForGeometryTower
      canonicalRobinsonBoardSignalGeometryTower hrouting)

/--
Canonical product-witness routing supplies the local Section 7 tower used by
the finite stack checker.
-/
theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalProductWitnessRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
    (hasFigure18RobinsonBoardRoutingForGeometryTowerForTable_of_productWitnessRouting
      hrouting)

/--
Canonical free-site-rectangle routing supplies the local Section 7 tower used by
the finite stack checker.
-/
theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRectRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
    (hasFigure18RobinsonBoardCanonicalRoutingForTable_of_freeSiteRect
      hrouting)

/--
Origin-zero indexed active/corner windows supply the local Section 7 tower used
by the finite stack checker.
-/
theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_originZeroWindows
    {table : Figure18RoleTable}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindowsForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRectRouting
    (hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_originZeroWindows
      hwindows)

/-- Forget the coordinate recurrence from the combined Section 7 signal target. -/
theorem hasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable_of_localCoordinateSteps
    {table : Figure18RoleTable}
    (hsteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable table := by
  intro T seed x hx level
  rcases hsteps x hx level with ⟨parent, child, step⟩
  exact ⟨parent⟩

/-- Forget the local site checks from the combined Section 7 signal target. -/
theorem hasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable_of_localCoordinateSteps
    {table : Figure18RoleTable}
    (hsteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable table) :
    HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable table := by
  intro T seed x hx level
  rcases hsteps x hx level with ⟨parent, child, step⟩
  exact ⟨parent.1, child.1, step⟩

/--
A coherent Section 7 tower supplies the older independent coordinate-step
surface by taking the consecutive levels from the same tower.
-/
theorem hasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable_of_tower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalTowerForTable table) :
    HasFigure18RobinsonBoardLevelSignalCoordinateStepsForTable table := by
  intro T seed x hx level
  rcases htower x hx with ⟨certificates, steps⟩
  exact ⟨certificates level, certificates (level + 1), steps level⟩

/--
A coherent local Section 7 tower supplies the existing local coordinate-step
surface by taking consecutive levels from the same tower.
-/
theorem hasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable_of_localTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable table := by
  intro T seed x hx level
  rcases htower x hx with ⟨certificates, steps⟩
  exact ⟨certificates level, certificates (level + 1), steps level⟩

/-- Forget local site compatibility from a coherent local Section 7 tower. -/
theorem hasFigure18RobinsonBoardLevelSignalTowerForTable_of_localTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    HasFigure18RobinsonBoardLevelSignalTowerForTable table := by
  intro T seed x hx
  rcases htower x hx with ⟨certificates, steps⟩
  refine ⟨⟨fun level => (certificates level).1, ?_⟩⟩
  intro level
  exact steps level

/--
Level-indexed Robinson-board/free-grid invariant.

This matches the recursive board proof more directly than the public
`HasFigure18RobinsonBoardRoutedFreeGridsForTable` surface: for every Robinson
board level, produce the whole free grid of side `2^level + 1`.
-/
def HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ level : Nat,
        Nonempty (Figure18RobinsonBoardRoutedFreeGrid table x
          (RobinsonSquare.freeGridSide level)
          (RobinsonSquare.freeGridSide_pos level))

/--
Level-indexed Robinson-board/free-grid invariant retaining the finite local
site compatibility needed by the generated Figure 18 stack checker.
-/
def HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ level : Nat,
        Nonempty
          { grid : Figure18RobinsonBoardRoutedFreeGrid table x
              (RobinsonSquare.freeGridSide level)
              (RobinsonSquare.freeGridSide_pos level) //
            grid.SiteCompatible }

/--
Robinson's obstruction-signal board certificate is a direct refinement of the
level-indexed routed free-grid certificate used downstream.
-/
theorem hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_signalCertificates
    {table : Figure18RoleTable}
    (hsignal : HasFigure18RobinsonBoardLevelSignalCertificatesForTable table) :
    HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable table := by
  intro T seed x hx level
  rcases hsignal x hx level with ⟨certificate⟩
  exact ⟨certificate.toRoutedFreeGrid⟩

/--
Robinson's local obstruction-signal board certificate refines the compatible
routed free-grid certificate used by the finite stack checker.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localSignalCertificates
    {table : Figure18RoleTable}
    (hsignal : HasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table := by
  intro T seed x hx level
  rcases hsignal x hx level with ⟨certificate, hsite⟩
  exact ⟨⟨certificate.toRoutedFreeGrid,
    certificate.siteCompatible_toRoutedFreeGrid hsite⟩⟩

/-- Forget local site compatibility from compatible level routed grids. -/
theorem hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_compatible
    {table : Figure18RoleTable}
    (hgrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table) :
    HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable table := by
  intro T seed x hx level
  rcases hgrids x hx level with ⟨grid, _hsite⟩
  exact ⟨grid⟩

/--
Local coordinate-step certificates refine compatible level routed grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localCoordinateSteps
    {table : Figure18RoleTable}
    (hsteps :
      HasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localSignalCertificates
    (hasFigure18RobinsonBoardLevelSignalLocalCertificatesForTable_of_localCoordinateSteps
      hsteps)

/--
A coherent local Section 7 tower directly supplies compatible level routed
free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localCoordinateSteps
    (hasFigure18RobinsonBoardLevelSignalLocalCoordinateStepsForTable_of_localTower
      htower)

/--
Geometry plus per-level Figure 18 routing directly supplies compatible level
routed free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerRouting
      hrouting)

/--
Fixed-geometry routing directly supplies compatible level routed free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_fixedGeometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_fixedGeometryTowerRouting
      hrouting)

/--
Canonical Robinson-board routing directly supplies compatible level routed
free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalRouting
    {table : Figure18RoleTable}
    (hrouting : HasFigure18RobinsonBoardCanonicalRoutingForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
      hrouting)

/--
Canonical product-witness routing directly supplies compatible level routed
free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalProductWitnessRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalProductWitnessRouting
      hrouting)

/--
Canonical corridor-transmission routing directly supplies compatible level
routed free grids.  This is the closest theorem-facing form to Robinson's
Section 7 statement that the board transmits payload signals along the selected
unobstructed free rows and columns as a contiguous square.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCorridorRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
        table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalProductWitnessRouting
    (hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_corridor
      hrouting)

/--
Canonical free-site-rectangle routing directly supplies compatible level routed
free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalFreeSiteRectRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRectRouting
      hrouting)

/--
Decoded combined-site corridor routing directly supplies compatible level
routed free grids.  This is the finite-checker-facing form of Robinson's
Section 7 route: the board/free-line argument supplies decoded crossings and
corridor payload transmission, then each board level becomes a compatible
virtual free grid.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerCombinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerCombinedSites
      hrouting)

/--
Fixed-geometry decoded corridor routing directly supplies compatible level
routed free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_fixedGeometryCombinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerCombinedSites
    (hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_fixed
      hrouting)

/--
Canonical decoded corridor routing directly supplies compatible level routed
free grids.
-/
theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCombinedSites
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
        table) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerCombinedSites
    (hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_canonical
      hrouting)

/--
A coherent local Section 7 tower directly supplies level routed free grids.
-/
theorem hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_localTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_compatible
    (hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_localTower
      htower)

/-- Robinson-board/free-grid invariant for a specified Figure 18 role table. -/
def HasFigure18RobinsonBoardRoutedFreeGridsForTable
    (table : Figure18RoleTable) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18RobinsonBoardRoutedFreeGrid table x n hn)

theorem hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_level
    {table : Figure18RoleTable}
    (hlevel : HasFigure18RobinsonBoardLevelRoutedFreeGridsForTable table) :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable table := by
  intro T seed x hx n hn
  rcases RobinsonSquare.exists_level_with_payload_capacity n with
    ⟨level, hcap⟩
  rcases hlevel x hx level with ⟨grid⟩
  exact ⟨grid.restrict hn hcap⟩

/--
A coherent local Section 7 tower supplies routed free grids of every requested
finite size.
-/
theorem hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_localTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_level
    (hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_localTower
      htower)

/--
Geometry plus per-level Figure 18 routing supplies routed free grids of every
requested finite size.
-/
theorem hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_geometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_localTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerRouting
      hrouting)

/--
Fixed-geometry routing supplies routed free grids of every requested finite
size.
-/
theorem hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_fixedGeometryTowerRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable table) :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_fixedGeometryTowerRouting
      hrouting)

/--
Canonical Robinson-board routing supplies routed free grids of every requested
finite size.
-/
theorem hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalRouting
    {table : Figure18RoleTable}
    (hrouting : HasFigure18RobinsonBoardCanonicalRoutingForTable table) :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_routingForGeometryTower
      canonicalRobinsonBoardSignalGeometryTower hrouting)

/--
Canonical product-witness routing supplies routed free grids of every requested
finite size.
-/
theorem
    hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalProductWitnessRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table) :
    HasFigure18RobinsonBoardRoutedFreeGridsForTable table :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalRouting
    (hasFigure18RobinsonBoardRoutingForGeometryTowerForTable_of_productWitnessRouting
      hrouting)

theorem hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    {table : Figure18RoleTable}
    (hgrids : HasFigure18RobinsonBoardRoutedFreeGridsForTable table) :
    HasFigure18IndexedRoutedFixedCornerSquares table := by
  intro T seed x hx n hn
  rcases hgrids x hx n hn with ⟨grid⟩
  exact ⟨grid.toIndexedRoutedFixedCornerSquare⟩

/--
Canonical product-witness routing directly supplies the indexed-routed
fixed-corner-square forcing interface.
-/
theorem
    hasFigure18IndexedRoutedFixedCornerSquaresForTable_of_canonicalProductWitnessRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable table) :
    HasFigure18IndexedRoutedFixedCornerSquares table :=
  hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    (hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalProductWitnessRouting
      hrouting)

/--
Robinson-board/free-grid invariant for a generated listed-active Figure 18 role
table.
-/
def HasFigure18RobinsonBoardRoutedFreeGrids
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardRoutedFreeGridsForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Robinson-board geometry-plus-routing invariant for a generated listed-active
Figure 18 role table.
-/
def HasFigure18RobinsonBoardGeometryTowerRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardGeometryTowerRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Robinson-board geometry-plus-decoded-combined-site corridor invariant for a
generated listed-active Figure 18 role table.  The geometry tower may depend on
the tiling, matching Robinson's Section 7 board extraction.
-/
def HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Figure 18 routing over a fixed Robinson obstruction-geometry tower for a
generated listed-active role table.
-/
def HasFigure18RobinsonBoardRoutingForGeometryTower
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  HasFigure18RobinsonBoardRoutingForGeometryTowerForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable
    geometryTower

/--
Product-witness routing over a fixed Robinson obstruction-geometry tower for a
generated listed-active role table.
-/
def HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTower
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable
    geometryTower

/--
Corridor-transmission product-witness routing over a fixed Robinson
obstruction-geometry tower for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTower
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable
    geometryTower

/--
Combined-site corridor routing over a fixed Robinson obstruction-geometry tower
for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTower
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable
    geometryTower

/--
Named site-rectangle routing over a fixed Robinson obstruction-geometry tower
for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTower
    (activeSites : List Figure18Site) (cornerSite : Figure18Site)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTowerForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable
    geometryTower

/--
Generated listed-active Figure 18 invariant with one geometry tower selected
independently of the payload tiles and tiling.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Generated listed-active Figure 18 invariant with one geometry tower selected
independently of the payload tiles and product-witness routing supplied over
that tower.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Generated listed-active Figure 18 invariant with one geometry tower selected
independently of the payload tiles and corridor-transmission routing supplied
over that tower.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Generated listed-active Figure 18 invariant with one geometry tower selected
independently of the payload tiles and combined-site corridor facts supplied
over that tower.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Generated listed-active Figure 18 invariant with one geometry tower selected
independently of the payload tiles and site-rectangle routing supplied over
that tower.
-/
def HasFigure18RobinsonBoardFixedGeometryTowerSiteRectCombinedSiteCorridorRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerSiteRectCombinedSiteCorridorRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Routing over the canonical Robinson obstruction-geometry tower for a generated
listed-active role table.
-/
def HasFigure18RobinsonBoardCanonicalRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Product-witness routing over the canonical Robinson obstruction-geometry tower
for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardCanonicalProductWitnessRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Corridor-transmission routing over the canonical Robinson obstruction-geometry
tower for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Combined-site corridor routing over the canonical Robinson obstruction-geometry
tower for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Named site-rectangle routing over the canonical Robinson obstruction-geometry
tower for a generated listed-active role table.
-/
def HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Canonical free-site-rectangle routing over Robinson's obstruction-geometry
tower for a generated listed-active role table.

This is the direct Section 7 target: obstruction arguments have already
identified the selected free crossings, so horizontal and vertical transmission
facts are stated without repeating clear-row and clear-column premises.
-/
def HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

/--
Active/corner recognition at canonical free crossings for a generated
listed-active role table.
-/
def HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCorner
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable
    (Figure18RoleTable.FlatRoleTable.ofActiveSites
      activeSites cornerSite).toRoleTable

theorem hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCorner_of_originZeroWindows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindows
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCorner
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
    hwindows

theorem hasFigure18RobinsonBoardCanonicalFreeSiteRectRouting_of_activeCorner
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hactiveCorner :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCorner
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_activeCorner
    hactiveCorner

theorem hasFigure18RobinsonBoardCanonicalFreeSiteRectRouting_of_originZeroWindows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindows
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable_of_originZeroWindows
    hwindows

theorem
    hasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTower_of_combinedSites
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTower
        activeSites cornerSite geometryTower) :
    HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTower
      activeSites cornerSite geometryTower :=
  hasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTowerForTable_of_combinedSites
    hrouting

theorem
    hasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTower_of_siteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTower
        activeSites cornerSite geometryTower) :
    HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTower
      activeSites cornerSite geometryTower :=
  hasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTowerForTable_of_siteRect
    hrouting

theorem hasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteRouting_of_siteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerSiteRectCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRoutingForTable_of_siteRect
    hrouting

theorem hasFigure18RobinsonBoardCanonicalCombinedSiteRouting_of_siteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_siteRect
    hrouting

theorem hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteRouting_of_freeSiteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRoutingForTable_of_freeSiteRect
    hrouting

theorem hasFigure18RobinsonBoardCanonicalCombinedSiteRouting_of_freeSiteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRoutingForTable_of_freeSiteRect
    hrouting

theorem hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting_of_freeSiteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_freeSiteRect
    hrouting

theorem hasFigure18RobinsonBoardCanonicalProductWitnessRouting_of_freeSiteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_freeSiteRect
    hrouting

theorem hasFigure18RobinsonBoardCanonicalRouting_of_freeSiteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalRouting activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalRoutingForTable_of_freeSiteRect
    hrouting

theorem
    hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting_of_combinedSites
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRoutingForTable_of_combinedSites
    hrouting

theorem
    hasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRouting_of_combinedSites
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRoutingForTable_of_combinedSites
    hrouting

theorem
    hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTower_of_corridor
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardCorridorProductWitnessRoutingForGeometryTower
        activeSites cornerSite geometryTower) :
    HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTower
      activeSites cornerSite geometryTower :=
  hasFigure18RobinsonBoardProductWitnessRoutingForGeometryTowerForTable_of_corridor
    hrouting

theorem
    hasFigure18RobinsonBoardCanonicalProductWitnessRouting_of_corridor
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_corridor
    hrouting

theorem
    hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRouting_of_corridor
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCorridorProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_corridor
    hrouting

theorem hasFigure18RobinsonBoardRoutingForGeometryTower_of_productWitnessRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      HasFigure18RobinsonBoardProductWitnessRoutingForGeometryTower
        activeSites cornerSite geometryTower) :
    HasFigure18RobinsonBoardRoutingForGeometryTower activeSites cornerSite
      geometryTower :=
  hasFigure18RobinsonBoardRoutingForGeometryTowerForTable_of_productWitnessRouting
    hrouting

theorem hasFigure18RobinsonBoardFixedGeometryTowerRouting_of_productWitnessRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardFixedGeometryTowerRouting activeSites
      cornerSite :=
  hasFigure18RobinsonBoardFixedGeometryTowerRoutingForTable_of_productWitnessRouting
    hrouting

theorem hasFigure18RobinsonBoardCanonicalProductWitnessRouting_of_routing
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalRouting activeSites cornerSite) :
    HasFigure18RobinsonBoardCanonicalProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardCanonicalProductWitnessRoutingForTable_of_routing
    hrouting

theorem hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRouting_of_canonical
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardFixedGeometryTowerProductWitnessRoutingForTable_of_canonical
    hrouting

theorem hasFigure18RobinsonBoardGeometryTowerRouting_of_fixedGeometryTowerRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRouting activeSites
        cornerSite) :
    HasFigure18RobinsonBoardGeometryTowerRouting activeSites cornerSite :=
  hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_fixedGeometryTowerRouting
    hrouting

theorem
    hasFigure18RobinsonBoardGeometryTowerCombinedSiteRouting_of_routingForGeometryTower
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (geometryTower : RobinsonBoardSignalGeometryTower)
    (hrouting :
      HasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTower
        activeSites cornerSite geometryTower) :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_routingForGeometryTower
    geometryTower hrouting

theorem hasFigure18RobinsonBoardGeometryTowerCombinedSiteRouting_of_fixed
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_fixed
    hrouting

theorem hasFigure18RobinsonBoardGeometryTowerCombinedSiteRouting_of_canonical
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
      activeSites cornerSite :=
  hasFigure18RobinsonBoardGeometryTowerCombinedSiteRoutingForTable_of_canonical
    hrouting

theorem hasFigure18RobinsonBoardGeometryTowerRouting_of_geometryTowerCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardGeometryTowerRouting activeSites cornerSite :=
  hasFigure18RobinsonBoardGeometryTowerRoutingForTable_of_geometryTowerCombinedSites
    hrouting

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_geometryTowerRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerRouting activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_geometryTowerRouting
    hrouting

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_geometryTowerCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRouting_of_geometryTowerCombinedSiteRouting
      hrouting)

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_fixedGeometryTowerRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardFixedGeometryTowerRouting activeSites
        cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_geometryTowerRouting
    (hasFigure18RobinsonBoardGeometryTowerRouting_of_fixedGeometryTowerRouting
      hrouting)

theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_geometryTowerCombinedSites
    hrouting

theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_geometryTowerCombinedSites
    hrouting

theorem hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonical
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalRouting activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalRouting
    hrouting

theorem
    hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable_of_canonicalCombinedSites
    hrouting

theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalProductWitness
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalProductWitnessRouting
    hrouting

theorem
    hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRect
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRectRouting
    hrouting

theorem
    hasFigure18RobinsonBoardLevelSignalLocalTower_of_originZeroWindows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18IndexedActiveCornerOriginZeroWindows
        activeSites cornerSite) :
    HasFigure18RobinsonBoardLevelSignalLocalTowerForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_originZeroWindows
    hwindows

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalRouting activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalRouting
    hrouting

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalProductWitnessRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_canonicalProductWitnessRouting
    hrouting

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalCorridorRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalProductWitnessRouting
    (hasFigure18RobinsonBoardCanonicalProductWitnessRouting_of_corridor
      hrouting)

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalCorridorRouting
    (hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting_of_combinedSites
      hrouting)

theorem hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalFreeSiteRectRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalCombinedSiteRouting
    (hasFigure18RobinsonBoardCanonicalCombinedSiteRouting_of_freeSiteRect
      hrouting)

theorem hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGrids
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hgrids :
      HasFigure18RobinsonBoardRoutedFreeGrids activeSites cornerSite) :
    HasFigure18IndexedRoutedFixedCornerSquares
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    hgrids

theorem
    hasFigure18IndexedRoutedFixedCornerSquares_of_canonicalProductWitnessRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18IndexedRoutedFixedCornerSquares
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18IndexedRoutedFixedCornerSquaresForTable_of_canonicalProductWitnessRouting
    hrouting

theorem
    hasFigure18IndexedRoutedFixedCornerSquares_of_canonicalCorridorRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
        activeSites cornerSite) :
    HasFigure18IndexedRoutedFixedCornerSquares
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18IndexedRoutedFixedCornerSquares_of_canonicalProductWitnessRouting
    (hasFigure18RobinsonBoardCanonicalProductWitnessRouting_of_corridor
      hrouting)

theorem
    hasFigure18IndexedRoutedFixedCornerSquares_of_canonicalCombinedSiteRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
        activeSites cornerSite) :
    HasFigure18IndexedRoutedFixedCornerSquares
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable :=
  hasFigure18IndexedRoutedFixedCornerSquares_of_canonicalCorridorRouting
    (hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting_of_combinedSites
      hrouting)

/--
Structured listed-active window invariant for a specified Figure 18 role table.

This version avoids rebuilding the role table from the active-site list.  It is
useful while transporting concrete Figure 18 witnesses across generated active
site lists.
-/
def HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
    (table : Figure18RoleTable)
    (activeSites : List Figure18Site) (cornerSite : Figure18Site) : Prop :=
  ∀ {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold
      table.presentation.toScaffold T seed)),
    ValidPlaneTiling (combineWithScaffold
      table.presentation.toScaffold T seed) x →
      ∀ n : Nat, ∀ hn : 0 < n,
        Nonempty (Figure18ListedActiveSiteFixedCornerSquare
          table activeSites cornerSite x n hn)

theorem hasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable_of_windows
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSites cornerSite) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable
      activeSites cornerSite :=
  hwindows

theorem hasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable_mono_activeSites
    {table : Figure18RoleTable}
    {activeSites activeSites' : List Figure18Site}
    {cornerSite : Figure18Site}
    (hsubset :
      ∀ site : Figure18Site, site ∈ activeSites → site ∈ activeSites')
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
        table activeSites cornerSite) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
      table activeSites' cornerSite := by
  intro T seed x hx n hn
  rcases hwindows x hx n hn with ⟨window⟩
  exact ⟨window.mono_activeSites hsubset⟩

theorem hasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable_toGeneratedActiveSites
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hwindows :
      HasFigure18ListedActiveSiteFixedCornerSquareWindows
        activeSites cornerSite) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindowsForTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).activeSites
      cornerSite := by
  intro T seed x hx n hn
  rcases hwindows x hx n hn with ⟨window⟩
  exact ⟨window.toGeneratedActiveSites⟩

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

theorem hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_indexedActive
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hindexed :
      HasFigure18IndexedActiveCornerWindows
        (Figure18RoleTable.FlatRoleTable.ofActiveSites
          activeSites cornerSite).toRoleTable) :
    HasFigure18ListedActiveSiteFixedCornerSquareWindows
      activeSites cornerSite := by
  intro T seed x hx n hn
  let flatTable :=
    Figure18RoleTable.FlatRoleTable.ofActiveSites activeSites cornerSite
  let table := flatTable.toRoleTable
  rcases hindexed x hx n hn with ⟨window⟩
  refine ⟨{
    horizontalCoord := fun i => window.origin.1 + Int.ofNat i.val
    verticalCoord := fun j => window.origin.2 + Int.ofNat j.val
    horizontalCoord_succ := ?_
    verticalCoord_succ := ?_
    listedActive := ?_
    corner := ?_
  }⟩
  · intro i hi
    change window.origin.1 + Int.ofNat (i.val + 1) =
      window.origin.1 + Int.ofNat i.val + 1
    norm_num
    exact (add_assoc window.origin.1 (Int.ofNat i.val) (1 : Int)).symm
  · intro j hj
    change window.origin.2 + Int.ofNat (j.val + 1) =
      window.origin.2 + Int.ofNat j.val + 1
    norm_num
    exact (add_assoc window.origin.2 (Int.ofNat j.val) (1 : Int)).symm
  · intro i j
    let site : Figure18Site := {
      index := window.indexRect i j
      quadrant := window.quadrantRect i j
    }
    have hsite :
        table.combinedSite
          (x (window.origin.1 + Int.ofNat i.val,
            window.origin.2 + Int.ofNat j.val)) = site := by
      rcases window.product i j with ⟨payload, hproduct⟩
      exact table.combinedSite_eq_of_product_site
        (x (window.origin.1 + Int.ofNat i.val,
          window.origin.2 + Int.ofNat j.val))
        site payload hproduct
    rw [hsite]
    have hactiveRole :
        CellRole.isActive (table.roleAtSite site) = true := by
      simpa [table, site, Figure18RoleTable.roleAtSite] using
        window.active i j
    have hrole :
        Figure18RoleTable.roleOfActiveSites activeSites cornerSite site =
          table.roleAtSite site := by
      exact (Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite
        activeSites cornerSite site).symm
    exact (Figure18RoleTable.isActive_roleOfActiveSites_iff
      activeSites cornerSite site).1 (by simpa [hrole] using hactiveRole)
  · let site : Figure18Site := {
      index := window.indexRect ⟨0, hn⟩ ⟨0, hn⟩
      quadrant := window.quadrantRect ⟨0, hn⟩ ⟨0, hn⟩
    }
    have hsite :
        table.combinedSite
          (x (window.origin.1 + Int.ofNat (⟨0, hn⟩ : Fin n).val,
            window.origin.2 + Int.ofNat (⟨0, hn⟩ : Fin n).val)) =
            site := by
      rcases window.product ⟨0, hn⟩ ⟨0, hn⟩ with
        ⟨payload, hproduct⟩
      exact table.combinedSite_eq_of_product_site
        (x (window.origin.1 + Int.ofNat (⟨0, hn⟩ : Fin n).val,
          window.origin.2 + Int.ofNat (⟨0, hn⟩ : Fin n).val))
        site payload hproduct
    have hcornerRole : table.roleAtSite site = CellRole.corner := by
      simpa [table, site, Figure18RoleTable.roleAtSite] using
        window.corner
    have hrole :
        Figure18RoleTable.roleOfActiveSites activeSites cornerSite site =
          table.roleAtSite site := by
      exact (Figure18RoleTable.FlatRoleTable.ofActiveSites_roleAtSite
        activeSites cornerSite site).symm
    have hcorner : site = cornerSite :=
      (Figure18RoleTable.roleOfActiveSites_eq_corner_iff
        activeSites cornerSite site).1
        (by simpa [hrole] using hcornerRole)
    exact hsite.trans hcorner

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

noncomputable def toIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18AdjacentProductWitnessFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn :=
  window.toAdjacentCompatibleFixedCornerSquare.toIndexedRoutedFixedCornerSquare hx

theorem tileable
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18AdjacentProductWitnessFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x) :
    TileableFixedCornerSquare T seed n :=
  window.toAdjacentCompatibleFixedCornerSquare.tileable hx

end Figure18AdjacentProductWitnessFixedCornerSquare

/--
Structured decoded-site selected-coordinate square.

This packages one witness for `HasFigure18DecodedSiteFixedCornerSquares`: the
selected coordinates are adjacent in the ambient tiling, the decoded scaffold
sites are locally compatible and active, and the lower-left selected site is
the distinguished corner.
-/
structure Figure18DecodedSiteFixedCornerSquare
    (table : Figure18RoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1
  verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1
  hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    Figure18Site.hCompatible
      (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
      (table.combinedSite
        (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) =
      true
  vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    Figure18Site.vCompatible
      (table.combinedSite (x (horizontalCoord i, verticalCoord j)))
      (table.combinedSite
        (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) =
      true
  active : ∀ i : Fin n, ∀ j : Fin n,
    CellRole.isActive
      (table.roleAtSite
        (table.combinedSite (x (horizontalCoord i, verticalCoord j)))) =
      true
  cornerSite :
    table.combinedSite
        (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
      table.cornerSite

namespace Figure18DecodedSiteFixedCornerSquare

noncomputable def toAdjacentProductWitnessFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18DecodedSiteFixedCornerSquare table x n hn) :
    Figure18AdjacentProductWitnessFixedCornerSquare table x n hn :=
  Figure18AdjacentProductWitnessFixedCornerSquare.ofCombinedSites hn
    window.horizontalCoord window.verticalCoord
    window.horizontalCoord_succ window.verticalCoord_succ
    window.hcompatible window.vcompatible window.active window.cornerSite

noncomputable def toIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold table.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18DecodedSiteFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling (combineWithScaffold table.presentation.toScaffold T seed) x) :
    Figure18IndexedRoutedFixedCornerSquare table x n hn :=
  window.toAdjacentProductWitnessFixedCornerSquare.toIndexedRoutedFixedCornerSquare hx

end Figure18DecodedSiteFixedCornerSquare

section FlatDecodedSite

set_option maxRecDepth 10000

/--
Structured flat-table decoded-site selected-coordinate square.

This packages one witness for `HasFigure18FlatDecodedSiteFixedCornerSquares`.
The active-cell condition is stated as membership in the flat table's active
site list; conversion to the role-table decoded-site form discharges the role
lookup.
-/
structure Figure18FlatDecodedSiteFixedCornerSquare
    (table : Figure18RoleTable.FlatRoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1
  verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1
  hcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hi : i.val + 1 < n,
    Figure18Site.hCompatible
      (table.toRoleTable.combinedSite
        (x (horizontalCoord i, verticalCoord j)))
      (table.toRoleTable.combinedSite
        (x (horizontalCoord ⟨i.val + 1, hi⟩, verticalCoord j))) =
      true
  vcompatible : ∀ i : Fin n, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    Figure18Site.vCompatible
      (table.toRoleTable.combinedSite
        (x (horizontalCoord i, verticalCoord j)))
      (table.toRoleTable.combinedSite
        (x (horizontalCoord i, verticalCoord ⟨j.val + 1, hj⟩))) =
      true
  activeSites : ∀ i : Fin n, ∀ j : Fin n,
    table.toRoleTable.combinedSite
      (x (horizontalCoord i, verticalCoord j)) ∈ table.activeSites
  cornerSite :
    table.toRoleTable.combinedSite
        (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
      table.cornerSite

namespace Figure18FlatDecodedSiteFixedCornerSquare

def toDecodedSiteFixedCornerSquare
    {table : Figure18RoleTable.FlatRoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18FlatDecodedSiteFixedCornerSquare table x n hn) :
    Figure18DecodedSiteFixedCornerSquare table.toRoleTable x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  horizontalCoord_succ := window.horizontalCoord_succ
  verticalCoord_succ := window.verticalCoord_succ
  hcompatible := window.hcompatible
  vcompatible := window.vcompatible
  active := by
    intro i j
    exact table.isActive_toRoleTable_of_mem_activeSites (window.activeSites i j)
  cornerSite := by
    simpa using window.cornerSite

noncomputable def toIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable.FlatRoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18FlatDecodedSiteFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed) x) :
    Figure18IndexedRoutedFixedCornerSquare table.toRoleTable x n hn :=
  window.toDecodedSiteFixedCornerSquare.toIndexedRoutedFixedCornerSquare hx

end Figure18FlatDecodedSiteFixedCornerSquare

end FlatDecodedSite

section FlatActiveSite

set_option maxRecDepth 10000

/--
Structured flat active-site selected-coordinate square.

This packages one witness for `HasFigure18FlatActiveSiteFixedCornerSquares`.
Horizontal and vertical compatibility are derived from adjacent selected
coordinates and validity of the combined tiling when converting to the flat
decoded-site form.
-/
structure Figure18FlatActiveSiteFixedCornerSquare
    (table : Figure18RoleTable.FlatRoleTable) {T : TileSet} {seed : WangTile}
    (x : Int × Int → TileIn
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed))
    (n : Nat) (hn : 0 < n) where
  horizontalCoord : Fin n → Int
  verticalCoord : Fin n → Int
  horizontalCoord_succ : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    horizontalCoord ⟨i.val + 1, hi⟩ = horizontalCoord i + 1
  verticalCoord_succ : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
    verticalCoord ⟨j.val + 1, hj⟩ = verticalCoord j + 1
  activeSites : ∀ i : Fin n, ∀ j : Fin n,
    table.toRoleTable.combinedSite
      (x (horizontalCoord i, verticalCoord j)) ∈ table.activeSites
  cornerSite :
    table.toRoleTable.combinedSite
        (x (horizontalCoord ⟨0, hn⟩, verticalCoord ⟨0, hn⟩)) =
      table.cornerSite

namespace Figure18FlatActiveSiteFixedCornerSquare

def toFlatDecodedSiteFixedCornerSquare
    {table : Figure18RoleTable.FlatRoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18FlatActiveSiteFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed) x) :
    Figure18FlatDecodedSiteFixedCornerSquare table x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  horizontalCoord_succ := window.horizontalCoord_succ
  verticalCoord_succ := window.verticalCoord_succ
  hcompatible := by
    intro i j hi
    exact table.toRoleTable.combinedSite_hCompatible_of_selectedCoords
      hx window.horizontalCoord window.verticalCoord
      window.horizontalCoord_succ i j hi
  vcompatible := by
    intro i j hj
    exact table.toRoleTable.combinedSite_vCompatible_of_selectedCoords
      hx window.horizontalCoord window.verticalCoord
      window.verticalCoord_succ i j hj
  activeSites := window.activeSites
  cornerSite := window.cornerSite

noncomputable def toIndexedRoutedFixedCornerSquare
    {table : Figure18RoleTable.FlatRoleTable} {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18FlatActiveSiteFixedCornerSquare table x n hn)
    (hx : ValidPlaneTiling
      (combineWithScaffold table.toRoleTable.presentation.toScaffold T seed) x) :
    Figure18IndexedRoutedFixedCornerSquare table.toRoleTable x n hn :=
  (window.toFlatDecodedSiteFixedCornerSquare hx).toIndexedRoutedFixedCornerSquare hx

end Figure18FlatActiveSiteFixedCornerSquare

end FlatActiveSite

namespace Figure18ListedActiveSiteFixedCornerSquare

def toFlatActiveSiteFixedCornerSquare
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18ListedActiveSiteFixedCornerSquare
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable
      activeSites cornerSite x n hn) :
    Figure18FlatActiveSiteFixedCornerSquare
      (Figure18RoleTable.FlatRoleTable.ofActiveSites activeSites cornerSite)
      x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  horizontalCoord_succ := window.horizontalCoord_succ
  verticalCoord_succ := window.verticalCoord_succ
  activeSites := by
    intro i j
    let site :=
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.combinedSite
        (x (window.horizontalCoord i, window.verticalCoord j))
    exact (Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_iff
      activeSites cornerSite site).2 (window.listedActive i j)
  cornerSite := window.corner

/--
Convert an explicit flat-table listed-active witness, using the table's own
computed active-site list, into a flat-active witness for that same table.
-/
def toFlatActiveSiteFixedCornerSquareForTable
    {table : Figure18RoleTable.FlatRoleTable}
    {T : TileSet} {seed : WangTile}
    {x : Int × Int → TileIn (combineWithScaffold
      table.toRoleTable.presentation.toScaffold T seed)}
    {n : Nat} {hn : 0 < n}
    (window : Figure18ListedActiveSiteFixedCornerSquare
      table.toRoleTable table.activeSites table.cornerSite x n hn) :
    Figure18FlatActiveSiteFixedCornerSquare table x n hn where
  horizontalCoord := window.horizontalCoord
  verticalCoord := window.verticalCoord
  horizontalCoord_succ := window.horizontalCoord_succ
  verticalCoord_succ := window.verticalCoord_succ
  activeSites := by
    intro i j
    rcases window.listedActive i j with hcorner | hactive
    · rw [hcorner]
      exact table.corner_mem_activeSites
    · exact hactive
  cornerSite := window.corner

end Figure18ListedActiveSiteFixedCornerSquare

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

theorem hasFigure18RoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    {table : Figure18RoleTable}
    (hgrids : HasFigure18RobinsonBoardRoutedFreeGridsForTable table) :
    HasFigure18RoutedFixedCornerSquares table :=
  hasFigure18RoutedFixedCornerSquares_of_indexed
    (hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
      hgrids)

theorem hasFigure18RoutedFixedCornerSquares_of_robinsonBoardSignalLocalTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    HasFigure18RoutedFixedCornerSquares table :=
  hasFigure18RoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    (hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_localTower htower)

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

theorem forcesFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    {table : Figure18RoleTable}
    (hgrids : HasFigure18RobinsonBoardRoutedFreeGridsForTable table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18Routed
    (hasFigure18RoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
      hgrids)

/--
Compatible level-indexed Robinson board/free-grid witnesses directly force
fixed-corner payload squares.

This is the Section 7 board route in its proof-facing form: the geometric
argument supplies a compatible routed free grid at each Robinson board level,
and the existing cofinality of board levels gives routed payload squares of
every requested finite size.
-/
theorem forcesFixedCornerSquares_of_robinsonBoardLevelCompatibleRoutedFreeGridsForTable
    {table : Figure18RoleTable}
    (hgrids :
      HasFigure18RobinsonBoardLevelCompatibleRoutedFreeGridsForTable table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_robinsonBoardRoutedFreeGridsForTable
    (hasFigure18RobinsonBoardRoutedFreeGridsForTable_of_level
      (hasFigure18RobinsonBoardLevelRoutedFreeGridsForTable_of_compatible
        hgrids))

theorem forcesFixedCornerSquares_of_robinsonBoardSignalLocalTower
    {table : Figure18RoleTable}
    (htower :
      HasFigure18RobinsonBoardLevelSignalLocalTowerForTable table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_figure18Routed
    (hasFigure18RoutedFixedCornerSquares_of_robinsonBoardSignalLocalTower
      htower)

/--
Robinson Section 7 canonical free-site-rectangle routing directly supplies the
abstract scaffold forcing invariant.

This is the proof-facing bridge from the paper's obstruction/free-line
argument to the general scaffold reduction: once free/free site rectangles are
routed through the board corridors, the combined tiling forces arbitrarily
large fixed-corner payload squares.
-/
theorem forcesFixedCornerSquares_of_robinsonBoardCanonicalFreeSiteRectRoutingForTable
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table) :
    ForcesFixedCornerSquares table.presentation.toScaffold :=
  forcesFixedCornerSquares_of_robinsonBoardSignalLocalTower
    (hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRectRouting
      hrouting)

/--
Listed-site version of
`forcesFixedCornerSquares_of_robinsonBoardCanonicalFreeSiteRectRoutingForTable`.
-/
theorem forcesFixedCornerSquares_of_robinsonBoardCanonicalFreeSiteRectRouting
    {activeSites : List Figure18Site} {cornerSite : Figure18Site}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
        activeSites cornerSite) :
    ForcesFixedCornerSquares
      (Figure18RoleTable.FlatRoleTable.ofActiveSites
        activeSites cornerSite).toRoleTable.presentation.toScaffold :=
  forcesFixedCornerSquares_of_robinsonBoardCanonicalFreeSiteRectRoutingForTable
    hrouting

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

namespace Figure18FlexibleCertificate

/--
Build the abstract flexible scaffold certificate directly from Robinson
Section 7 canonical free-site-rectangle routing.

This keeps the proof-facing route aligned with the general scaffold theorem:
the routing argument supplies `ForcesFixedCornerSquares`, while realization is
kept as the separate positive-box/layer-patch obligation.
-/
def ofRobinsonBoardCanonicalFreeSiteRectRouting
    {table : Figure18RoleTable}
    (hrouting :
      HasFigure18RobinsonBoardCanonicalFreeSiteRectRoutingForTable table)
    (realizes :
      RealizesActiveCornerSquares table.presentation.toScaffold) :
    Figure18FlexibleCertificate table where
  forces :=
    forcesFixedCornerSquares_of_robinsonBoardCanonicalFreeSiteRectRoutingForTable
      hrouting
  realizes := realizes

theorem isScaffold
    {table : Figure18RoleTable}
    (certificate : Figure18FlexibleCertificate table) :
    IsScaffold table.presentation.toScaffold :=
  isScaffold_of_flexibleCertificate {
    forces := certificate.forces
    realizes := certificate.realizes
  }

end Figure18FlexibleCertificate

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

theorem scaffold_corner_mem (D : Figure18ScaffoldData) :
    D.scaffold.corner ∈ D.scaffold.tiles := by
  simpa [scaffold, presentation, table] using
    D.table.toRoleTable.scaffold_corner_mem

def HasLocalFreeSquareInvariant (D : Figure18ScaffoldData) : Prop :=
  HasFigure18ListedActiveSiteFixedCornerSquares D.activeSites D.cornerSite

def HasLocalFreeSquareWindowInvariant (D : Figure18ScaffoldData) : Prop :=
  HasFigure18ListedActiveSiteFixedCornerSquareWindows
    D.activeSites D.cornerSite

def HasRobinsonBoardAdjacentFreeGridInvariant (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardAdjacentFreeGrids D.activeSites D.cornerSite

def HasRobinsonBoardRoutedFreeGridInvariant (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardRoutedFreeGrids D.activeSites D.cornerSite

def HasRobinsonBoardGeometryTowerRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardGeometryTowerRouting D.activeSites D.cornerSite

def HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardGeometryTowerCombinedSiteCorridorRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardSiteRectCombinedSiteRoutingForGeometryTowerInvariant
    (D : Figure18ScaffoldData)
    (geometryTower : RobinsonBoardSignalGeometryTower) : Prop :=
  HasFigure18RobinsonBoardSiteRectCombinedSiteCorridorRoutingForGeometryTower
    D.activeSites D.cornerSite geometryTower

def HasRobinsonBoardFixedGeometryTowerRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardCanonicalRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalRouting D.activeSites D.cornerSite

def HasRobinsonBoardCanonicalProductWitnessRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalProductWitnessRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardCanonicalCorridorRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalCombinedSiteCorridorRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardFixedGeometryTowerSiteRectCombinedSiteCorridorRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteCorridorRouting
    D.activeSites D.cornerSite

def HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalFreeSiteRectRouting
    D.activeSites D.cornerSite

/--
Robinson Section 7 obstruction-routing target for the concrete Figure 18
scaffold data.

This is the proof surface suggested by Robinson's board argument: red borders
produce boards, obstruction signals identify exactly the free rows and columns,
and those free-line crossings carry the payload square.  In the current
formalization this is represented by canonical free-site-rectangle routing.
-/
def HasRobinsonSection7ObstructionRoutingInvariant
    (D : Figure18ScaffoldData) : Prop :=
  D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant

def HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCorner
    D.activeSites D.cornerSite

/--
Robinson Section 7 board/free-line target before the final routing fields are
packaged.

The first component is the pure obstruction geometry: red borders produce
boards whose unobstructed rows and columns form the virtual square.  The second
component is the finite local recognition that the canonical free crossings are
active Figure 18 sites and that the lower-left crossing is the distinguished
corner.  The remaining payload transmission and site-compatibility fields are
then supplied by valid tiling edges in
`HasRobinsonSection7ObstructionRoutingInvariant.ofBoardFreeLineActiveCorner`.
-/
def HasRobinsonSection7BoardFreeLineActiveCornerInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasRobinsonBoardSignalGeometryTower ∧
    D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant

def HasIndexedActiveCornerOriginZeroWindowInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18IndexedActiveCornerOriginZeroWindowsForTable D.table.toRoleTable

def HasRobinsonBoardLevelSignalLocalTowerInvariant
    (D : Figure18ScaffoldData) : Prop :=
  HasFigure18RobinsonBoardLevelSignalLocalTowerForTable D.table.toRoleTable

def HasIndexedRoutedForces (D : Figure18ScaffoldData) : Prop :=
  HasFigure18IndexedRoutedFixedCornerSquares D.table.toRoleTable

def HasLocalFreeSquareWindowInvariant.ofIndexedActive
    {D : Figure18ScaffoldData}
    (hindexed : HasFigure18IndexedActiveCornerWindows D.table.toRoleTable) :
    D.HasLocalFreeSquareWindowInvariant :=
  hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_indexedActive
    hindexed

def HasLocalFreeSquareWindowInvariant.ofOriginZeroWindows
    {D : Figure18ScaffoldData}
    (hwindows : D.HasIndexedActiveCornerOriginZeroWindowInvariant) :
    D.HasLocalFreeSquareWindowInvariant :=
  HasLocalFreeSquareWindowInvariant.ofIndexedActive
    (hasFigure18IndexedActiveCornerWindows_of_originZeroWindowsForTable
      hwindows)

def HasLocalFreeSquareWindowInvariant.ofRobinsonBoardAdjacentFreeGrid
    {D : Figure18ScaffoldData}
    (hgrids : D.HasRobinsonBoardAdjacentFreeGridInvariant) :
    D.HasLocalFreeSquareWindowInvariant :=
  hasFigure18ListedActiveSiteFixedCornerSquareWindows_of_robinsonBoardAdjacentFreeGrids
    hgrids

def HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    {D : Figure18ScaffoldData}
    (hgrids : D.HasRobinsonBoardRoutedFreeGridInvariant) :
    D.HasIndexedRoutedForces :=
  hasFigure18IndexedRoutedFixedCornerSquares_of_robinsonBoardRoutedFreeGrids
    hgrids

def HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardGeometryTowerRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_geometryTowerRouting hrouting

def HasRobinsonBoardGeometryTowerRoutingInvariant.ofGeometryTowerCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant) :
    D.HasRobinsonBoardGeometryTowerRoutingInvariant :=
  hasFigure18RobinsonBoardGeometryTowerRouting_of_geometryTowerCombinedSiteRouting
    hrouting

def HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofSiteRect
    {D : Figure18ScaffoldData}
    {geometryTower : RobinsonBoardSignalGeometryTower}
    (hrouting :
      D.HasRobinsonBoardSiteRectCombinedSiteRoutingForGeometryTowerInvariant
        geometryTower) :
    D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant :=
  hasFigure18RobinsonBoardGeometryTowerCombinedSiteRouting_of_routingForGeometryTower
    geometryTower
    (hasFigure18RobinsonBoardCombinedSiteCorridorRoutingForGeometryTower_of_siteRect
      hrouting)

def HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofCanonicalCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant) :
    D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant :=
  hasFigure18RobinsonBoardGeometryTowerCombinedSiteRouting_of_canonical
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_geometryTowerCombinedSiteRouting
    hrouting

def HasRobinsonBoardGeometryTowerRoutingInvariant.ofFixedGeometryTowerRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardFixedGeometryTowerRoutingInvariant) :
    D.HasRobinsonBoardGeometryTowerRoutingInvariant :=
  hasFigure18RobinsonBoardGeometryTowerRouting_of_fixedGeometryTowerRouting
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofFixedGeometryTowerRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardFixedGeometryTowerRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_fixedGeometryTowerRouting
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalRouting hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalProductWitnessRouting
    {D : Figure18ScaffoldData}
    (hrouting :
      D.HasRobinsonBoardCanonicalProductWitnessRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalProductWitnessRouting
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCorridorRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalCorridorRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalCorridorRouting
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalCombinedSiteRouting
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofFixedGeometryTowerSiteRectCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting :
      D.HasRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerCombinedSiteRouting
    (hasFigure18RobinsonBoardGeometryTowerCombinedSiteRouting_of_fixed
      (hasFigure18RobinsonBoardFixedGeometryTowerCombinedSiteRouting_of_siteRect
        hrouting))

def HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalSiteRectCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting :
      D.HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCombinedSiteRouting
    (hasFigure18RobinsonBoardCanonicalCombinedSiteRouting_of_siteRect hrouting)

def HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant.ofFreeSiteRect
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant :=
  hasFigure18RobinsonBoardCanonicalSiteRectCombinedSiteRouting_of_freeSiteRect
    hrouting

def HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant.ofActiveCorner
    {D : Figure18ScaffoldData}
    (hactiveCorner :
      D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant) :
    D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant :=
  hasFigure18RobinsonBoardCanonicalFreeSiteRectRouting_of_activeCorner
    hactiveCorner

def HasRobinsonSection7ObstructionRoutingInvariant.ofActiveCorner
    {D : Figure18ScaffoldData}
    (hactiveCorner :
      D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant) :
    D.HasRobinsonSection7ObstructionRoutingInvariant :=
  HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant.ofActiveCorner
    hactiveCorner

/--
The board/free-line Section 7 target supplies the existing obstruction-routing
invariant.  The pure geometry component is kept in the source invariant so the
proof obligation matches Robinson's board argument, while the canonical routing
bridge uses the already fixed canonical tower.
-/
def HasRobinsonSection7ObstructionRoutingInvariant.ofBoardFreeLineActiveCorner
    {D : Figure18ScaffoldData}
    (hboard :
      D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant) :
    D.HasRobinsonSection7ObstructionRoutingInvariant :=
  HasRobinsonSection7ObstructionRoutingInvariant.ofActiveCorner hboard.2

/--
Canonical Robinson board/free-line geometry plus active/corner recognition at
canonical free crossings gives the proof-facing Section 7 target.
-/
def HasRobinsonSection7BoardFreeLineActiveCornerInvariant.ofActiveCorner
    {D : Figure18ScaffoldData}
    (hactiveCorner :
      D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant) :
    D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant :=
  ⟨hasRobinsonBoardSignalGeometryTower, hactiveCorner⟩

def HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant.ofBoardFreeLineActiveCorner
    {D : Figure18ScaffoldData}
    (hboard : D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant) :
    D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant :=
  hboard.2

/--
The pure obstruction-geometry half of the proof-facing Section 7 board/free-line
target is already supplied by the canonical Robinson tower.  Thus the remaining
concrete scaffold obligation is exactly active/corner recognition at the
canonical free crossings.
-/
theorem hasRobinsonSection7BoardFreeLineActiveCornerInvariant_iff_activeCorner
    (D : Figure18ScaffoldData) :
    D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant ↔
      D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant :=
  ⟨HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant.ofBoardFreeLineActiveCorner,
    HasRobinsonSection7BoardFreeLineActiveCornerInvariant.ofActiveCorner⟩

def HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant.ofOriginZeroWindows
    {D : Figure18ScaffoldData}
    (hwindows : D.HasIndexedActiveCornerOriginZeroWindowInvariant) :
    D.HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant :=
  hasFigure18RobinsonBoardCanonicalFreeSiteRectActiveCornerForTable_of_originZeroWindows
    hwindows

/--
Origin-zero active/corner windows supply the bare Figure 18 board/free-line
Section 7 target.
-/
def HasRobinsonSection7BoardFreeLineActiveCornerInvariant.ofOriginZeroWindows
    {D : Figure18ScaffoldData}
    (hwindows : D.HasIndexedActiveCornerOriginZeroWindowInvariant) :
    D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant :=
  HasRobinsonSection7BoardFreeLineActiveCornerInvariant.ofActiveCorner
    (HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant.ofOriginZeroWindows
      hwindows)

/-- Short alias for the origin-zero-to-board/free-line Section 7 bridge. -/
def boardFreeLineActiveCornerOfOriginZeroWindows
    {D : Figure18ScaffoldData}
    (hwindows : D.HasIndexedActiveCornerOriginZeroWindowInvariant) :
    D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant :=
  HasRobinsonSection7BoardFreeLineActiveCornerInvariant.ofOriginZeroWindows
    hwindows

def HasRobinsonSection7ObstructionRoutingInvariant.ofOriginZeroWindows
    {D : Figure18ScaffoldData}
    (hwindows : D.HasIndexedActiveCornerOriginZeroWindowInvariant) :
    D.HasRobinsonSection7ObstructionRoutingInvariant :=
  HasRobinsonSection7ObstructionRoutingInvariant.ofActiveCorner
    (HasRobinsonBoardCanonicalFreeSiteRectActiveCornerInvariant.ofOriginZeroWindows
      hwindows)

def HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant.ofFreeSiteRect
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant :=
  hasFigure18RobinsonBoardCanonicalCombinedSiteRouting_of_freeSiteRect
    hrouting

def HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofFreeSiteRect
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant :=
  HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofCanonicalCombinedSiteRouting
    (HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant.ofFreeSiteRect
      hrouting)

def HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofSection7ObstructionRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonSection7ObstructionRoutingInvariant) :
    D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant :=
  HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofFreeSiteRect
    hrouting

def HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofBoardFreeLineActiveCorner
    {D : Figure18ScaffoldData}
    (hboard : D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant) :
    D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant :=
  HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant.ofSection7ObstructionRouting
    (HasRobinsonSection7ObstructionRoutingInvariant.ofBoardFreeLineActiveCorner
      hboard)

def HasRobinsonBoardCanonicalCorridorRoutingInvariant.ofFreeSiteRect
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardCanonicalCorridorRoutingInvariant :=
  hasFigure18RobinsonBoardCanonicalCorridorProductWitnessRouting_of_freeSiteRect
    hrouting

def HasRobinsonBoardCanonicalProductWitnessRoutingInvariant.ofFreeSiteRect
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardCanonicalProductWitnessRoutingInvariant :=
  hasFigure18RobinsonBoardCanonicalProductWitnessRouting_of_freeSiteRect
    hrouting

def HasRobinsonBoardCanonicalRoutingInvariant.ofFreeSiteRect
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardCanonicalRoutingInvariant :=
  hasFigure18RobinsonBoardCanonicalRouting_of_freeSiteRect hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalFreeSiteRectRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  hasFigure18RobinsonBoardRoutedFreeGrids_of_canonicalFreeSiteRectRouting
    hrouting

def HasRobinsonBoardLevelSignalLocalTowerInvariant.ofCanonicalFreeSiteRectRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasRobinsonBoardLevelSignalLocalTowerInvariant :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_canonicalFreeSiteRect
    hrouting

def HasRobinsonBoardLevelSignalLocalTowerInvariant.ofOriginZeroWindows
    {D : Figure18ScaffoldData}
    (hwindows : D.HasIndexedActiveCornerOriginZeroWindowInvariant) :
    D.HasRobinsonBoardLevelSignalLocalTowerInvariant :=
  hasFigure18RobinsonBoardLevelSignalLocalTowerForTable_of_originZeroWindows
    hwindows

def HasRobinsonBoardRoutedFreeGridInvariant.ofSection7ObstructionRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonSection7ObstructionRoutingInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalFreeSiteRectRouting
    hrouting

def HasRobinsonBoardRoutedFreeGridInvariant.ofBoardFreeLineActiveCorner
    {D : Figure18ScaffoldData}
    (hboard : D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant) :
    D.HasRobinsonBoardRoutedFreeGridInvariant :=
  HasRobinsonBoardRoutedFreeGridInvariant.ofSection7ObstructionRouting
    (HasRobinsonSection7ObstructionRoutingInvariant.ofBoardFreeLineActiveCorner
      hboard)

def HasRobinsonBoardLevelSignalLocalTowerInvariant.ofSection7ObstructionRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonSection7ObstructionRoutingInvariant) :
    D.HasRobinsonBoardLevelSignalLocalTowerInvariant :=
  HasRobinsonBoardLevelSignalLocalTowerInvariant.ofCanonicalFreeSiteRectRouting
    hrouting

def HasRobinsonBoardLevelSignalLocalTowerInvariant.ofBoardFreeLineActiveCorner
    {D : Figure18ScaffoldData}
    (hboard : D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant) :
    D.HasRobinsonBoardLevelSignalLocalTowerInvariant :=
  HasRobinsonBoardLevelSignalLocalTowerInvariant.ofSection7ObstructionRouting
    (HasRobinsonSection7ObstructionRoutingInvariant.ofBoardFreeLineActiveCorner
      hboard)

def HasIndexedRoutedForces.ofRobinsonBoardGeometryTowerRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardGeometryTowerRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerRouting hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardGeometryTowerCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerCombinedSiteRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardFixedGeometryTowerRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardFixedGeometryTowerRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofFixedGeometryTowerRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardCanonicalRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalRouting hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardCanonicalProductWitnessRouting
    {D : Figure18ScaffoldData}
    (hrouting :
      D.HasRobinsonBoardCanonicalProductWitnessRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalProductWitnessRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardCanonicalCorridorRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalCorridorRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCorridorRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardCanonicalCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCombinedSiteRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting :
      D.HasRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofFixedGeometryTowerSiteRectCombinedSiteRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardCanonicalSiteRectCombinedSiteRouting
    {D : Figure18ScaffoldData}
    (hrouting :
      D.HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalSiteRectCombinedSiteRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonBoardCanonicalFreeSiteRectRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalFreeSiteRectRouting
      hrouting)

def HasIndexedRoutedForces.ofRobinsonSection7ObstructionRouting
    {D : Figure18ScaffoldData}
    (hrouting : D.HasRobinsonSection7ObstructionRoutingInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonBoardCanonicalFreeSiteRectRouting
    hrouting

def HasIndexedRoutedForces.ofBoardFreeLineActiveCorner
    {D : Figure18ScaffoldData}
    (hboard : D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant) :
    D.HasIndexedRoutedForces :=
  HasIndexedRoutedForces.ofRobinsonSection7ObstructionRouting
    (HasRobinsonSection7ObstructionRoutingInvariant.ofBoardFreeLineActiveCorner
      hboard)

def HasRealizationInvariant (D : Figure18ScaffoldData) : Prop :=
  RealizesActiveCornerSquares D.scaffold

def HasLayerPatchRealizationInvariant (D : Figure18ScaffoldData) : Prop :=
  HasActiveCornerLayerBoxPatches D.scaffold

def HasActiveCornerIndexedBoxInvariant (D : Figure18ScaffoldData) : Prop :=
  ∀ r : Nat, Nonempty (ActiveCornerIndexedBox D.scaffold r)

def HasPositiveActiveCornerIndexedBoxInvariant
    (D : Figure18ScaffoldData) : Prop :=
  ∀ r : Nat, 0 < r → Nonempty (ActiveCornerIndexedBox D.scaffold r)

def HasPositiveTranslatedActiveCornerIndexedBoxInvariant
    (D : Figure18ScaffoldData) : Prop :=
  ∀ r : Nat, 0 < r →
    ∃ origin : Int × Int,
      Nonempty (TranslatedActiveCornerIndexedBox D.scaffold r origin)

/--
Positive translated scaffold boxes whose active cells are isolated.

This is a convenient Robinson-board realization target: build the finite
scaffold patch at its natural translated coordinates, then prove there are no
adjacent active-active cells in that patch.  The payload index can then be the
constant `1 × 1` index.
-/
def HasPositiveTranslatedIsolatedActiveBoxInvariant
    (D : Figure18ScaffoldData) : Prop :=
  ∀ r : Nat, 0 < r →
    ∃ origin : Int × Int,
      ∃ base : TranslatedBoxPattern D.scaffold.tiles r origin,
        ValidTranslatedBoxTiling D.scaffold.tiles r origin base ∧
          (∀ p : TranslatedBox r origin,
            ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
              D.scaffold.active (base p).1 = true →
                D.scaffold.active
                  (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
                  False) ∧
          (∀ p : TranslatedBox r origin,
            ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
              D.scaffold.active (base p).1 = true →
                D.scaffold.active
                  (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
                  False)

theorem HasRealizationInvariant.ofLayerPatches
    {D : Figure18ScaffoldData}
    (hpatches : D.HasLayerPatchRealizationInvariant) :
    D.HasRealizationInvariant :=
  realizesActiveCornerSquares_of_realizesActiveCornerBoxes
    (realizesActiveCornerBoxes_of_activeCornerLayerBoxPatches hpatches)

theorem HasLayerPatchRealizationInvariant.ofActiveCornerIndexedBoxes
    {D : Figure18ScaffoldData}
    (hboxes : D.HasActiveCornerIndexedBoxInvariant) :
    D.HasLayerPatchRealizationInvariant :=
  activeCornerLayerBoxPatches_of_activeCornerIndexedBoxes hboxes

theorem HasActiveCornerIndexedBoxInvariant.ofPositive
    {D : Figure18ScaffoldData}
    (hboxes : D.HasPositiveActiveCornerIndexedBoxInvariant) :
    D.HasActiveCornerIndexedBoxInvariant :=
  ActiveCornerIndexedBox.nonempty_all_of_pos_and_corner_mem
    D.scaffold_corner_mem hboxes

theorem HasPositiveActiveCornerIndexedBoxInvariant.ofTranslated
    {D : Figure18ScaffoldData}
    (hboxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.HasPositiveActiveCornerIndexedBoxInvariant :=
  TranslatedActiveCornerIndexedBox.nonempty_centered_pos_of_translated_pos
    hboxes

theorem HasPositiveTranslatedActiveCornerIndexedBoxInvariant.ofIsolatedActiveBoxes
    {D : Figure18ScaffoldData}
    (hboxes : D.HasPositiveTranslatedIsolatedActiveBoxInvariant) :
    D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant :=
  TranslatedActiveCornerIndexedBox.positive_nonempty_of_noAdjacentActive
    hboxes

/--
An active scaffold tile in a Figure 18 scaffold decodes to one of the generated
active sites, with the distinguished corner included as an allowed active site.
-/
theorem exists_allowedSite_of_active_tile
    (D : Figure18ScaffoldData)
    (tile : TileIn D.scaffold.tiles)
    (hactive : D.scaffold.active tile.1 = true) :
    ∃ site : Figure18Site,
      tile.1 = site.tile ∧
        (site = D.cornerSite ∨ site ∈ D.activeSiteData.sites) := by
  let table := D.table.toRoleTable
  have htile : tile.1 ∈ table.presentation.tiles := by
    simpa [table, scaffold, presentation] using tile.2
  let site := table.siteOfPresentationTile tile.1 htile
  refine ⟨site, (table.siteOfPresentationTile_tile htile).symm, ?_⟩
  have hactiveRole :
      CellRole.isActive (table.roleAtSite site) = true := by
    have hactivePresentation :
        CellRole.isActive (table.presentation.role tile.1) = true := by
      simpa [table, scaffold, presentation] using hactive
    rw [table.presentation_active_siteOfPresentationTile htile]
      at hactivePresentation
    exact hactivePresentation
  have hmem : site ∈ D.table.activeSites := by
    exact (D.table.mem_activeSites_iff site).2
      ⟨table.siteOfPresentationTile_mem_all htile, hactiveRole⟩
  simpa [table, Figure18ScaffoldData.table,
    Figure18ScaffoldData.activeSites] using
    (Figure18RoleTable.FlatRoleTable.mem_ofActiveSites_activeSites_iff
      D.activeSites D.cornerSite site).1 hmem

/--
If the generated active/corner site set has no horizontally compatible pairs,
then no valid translated box over the corresponding scaffold has adjacent
active cells in the east direction.
-/
theorem no_active_hsucc_of_noAllowedSiteHPairs
    (D : Figure18ScaffoldData)
    (hno : ∀ left : Figure18Site,
      left = D.cornerSite ∨ left ∈ D.activeSiteData.sites →
        ∀ right : Figure18Site,
          right = D.cornerSite ∨ right ∈ D.activeSiteData.sites →
            Figure18Site.hCompatible left right = false)
    {r : Nat} {origin : Int × Int}
    {base : TranslatedBoxPattern D.scaffold.tiles r origin}
    (base_valid : ValidTranslatedBoxTiling D.scaffold.tiles r origin base) :
    ∀ p : TranslatedBox r origin,
      ∀ hp : InTranslatedBox r origin (p.1.1 + 1, p.1.2),
        D.scaffold.active (base p).1 = true →
          D.scaffold.active
            (base ⟨(p.1.1 + 1, p.1.2), hp⟩).1 = true →
            False := by
  intro p hp hpActive hqActive
  let q : TranslatedBox r origin := ⟨(p.1.1 + 1, p.1.2), hp⟩
  rcases D.exists_allowedSite_of_active_tile (base p) hpActive with
    ⟨left, hleftTile, hleftAllowed⟩
  rcases D.exists_allowedSite_of_active_tile (base q) hqActive with
    ⟨right, hrightTile, hrightAllowed⟩
  have hcompatTrue : Figure18Site.hCompatible left right = true := by
    apply Figure18Site.hCompatible_of_hMatches
    simpa [q, hleftTile, hrightTile] using base_valid.1 p hp
  have hcompatFalse : Figure18Site.hCompatible left right = false :=
    hno left hleftAllowed right hrightAllowed
  rw [hcompatFalse] at hcompatTrue
  simp at hcompatTrue

/--
If the generated active/corner site set has no vertically compatible pairs,
then no valid translated box over the corresponding scaffold has adjacent
active cells in the north direction.
-/
theorem no_active_vsucc_of_noAllowedSiteVPairs
    (D : Figure18ScaffoldData)
    (hno : ∀ lower : Figure18Site,
      lower = D.cornerSite ∨ lower ∈ D.activeSiteData.sites →
        ∀ upper : Figure18Site,
          upper = D.cornerSite ∨ upper ∈ D.activeSiteData.sites →
            Figure18Site.vCompatible lower upper = false)
    {r : Nat} {origin : Int × Int}
    {base : TranslatedBoxPattern D.scaffold.tiles r origin}
    (base_valid : ValidTranslatedBoxTiling D.scaffold.tiles r origin base) :
    ∀ p : TranslatedBox r origin,
      ∀ hp : InTranslatedBox r origin (p.1.1, p.1.2 + 1),
        D.scaffold.active (base p).1 = true →
          D.scaffold.active
            (base ⟨(p.1.1, p.1.2 + 1), hp⟩).1 = true →
            False := by
  intro p hp hpActive hqActive
  let q : TranslatedBox r origin := ⟨(p.1.1, p.1.2 + 1), hp⟩
  rcases D.exists_allowedSite_of_active_tile (base p) hpActive with
    ⟨lower, hlowerTile, hlowerAllowed⟩
  rcases D.exists_allowedSite_of_active_tile (base q) hqActive with
    ⟨upper, hupperTile, hupperAllowed⟩
  have hcompatTrue : Figure18Site.vCompatible lower upper = true := by
    apply Figure18Site.vCompatible_of_vMatches
    simpa [q, hlowerTile, hupperTile] using base_valid.2 p hp
  have hcompatFalse : Figure18Site.vCompatible lower upper = false :=
    hno lower hlowerAllowed upper hupperAllowed
  rw [hcompatFalse] at hcompatTrue
  simp at hcompatTrue

/--
Positive translated valid boxes become isolated-active boxes when the generated
active/corner site set has no locally compatible active/corner neighbors.
-/
theorem HasPositiveTranslatedIsolatedActiveBoxInvariant.ofValidTranslatedBoxes
    {D : Figure18ScaffoldData}
    (hnoH : ∀ left : Figure18Site,
      left = D.cornerSite ∨ left ∈ D.activeSiteData.sites →
        ∀ right : Figure18Site,
          right = D.cornerSite ∨ right ∈ D.activeSiteData.sites →
            Figure18Site.hCompatible left right = false)
    (hnoV : ∀ lower : Figure18Site,
      lower = D.cornerSite ∨ lower ∈ D.activeSiteData.sites →
        ∀ upper : Figure18Site,
          upper = D.cornerSite ∨ upper ∈ D.activeSiteData.sites →
            Figure18Site.vCompatible lower upper = false)
    (hboxes :
      ∀ r : Nat, 0 < r →
        ∃ origin : Int × Int,
          ∃ base : TranslatedBoxPattern D.scaffold.tiles r origin,
            ValidTranslatedBoxTiling D.scaffold.tiles r origin base) :
    D.HasPositiveTranslatedIsolatedActiveBoxInvariant := by
  intro r hr
  rcases hboxes r hr with ⟨origin, base, base_valid⟩
  exact ⟨origin, base, base_valid,
    D.no_active_hsucc_of_noAllowedSiteHPairs hnoH base_valid,
    D.no_active_vsucc_of_noAllowedSiteVPairs hnoV base_valid⟩

theorem HasActiveCornerIndexedBoxInvariant.ofPositiveTranslated
    {D : Figure18ScaffoldData}
    (hboxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.HasActiveCornerIndexedBoxInvariant :=
  HasActiveCornerIndexedBoxInvariant.ofPositive
    (HasPositiveActiveCornerIndexedBoxInvariant.ofTranslated hboxes)

theorem HasLayerPatchRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
    {D : Figure18ScaffoldData}
    (hboxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.HasLayerPatchRealizationInvariant :=
  HasLayerPatchRealizationInvariant.ofActiveCornerIndexedBoxes
    (HasActiveCornerIndexedBoxInvariant.ofPositiveTranslated hboxes)

theorem HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes
    {D : Figure18ScaffoldData}
    (hboxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.HasRealizationInvariant :=
  HasRealizationInvariant.ofLayerPatches
    (HasLayerPatchRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes hboxes)

/--
The two geometric facts still needed after the finite Figure 18 active-site
data has been transcribed.
-/
structure Certificate (D : Figure18ScaffoldData) : Prop where
  localFreeSquares : D.HasLocalFreeSquareInvariant
  realizes : D.HasRealizationInvariant

/--
Routed certificate for the Robinson board argument.  This is the preferred
certificate shape for Section 7 of Robinson's paper: the board/free-row proof
directly supplies routed payload squares rather than adjacent active windows.
-/
structure RoutedCertificate (D : Figure18ScaffoldData) : Prop where
  indexedRoutedForces : D.HasIndexedRoutedForces
  realizes : D.HasRealizationInvariant

def RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant
    (D : Figure18ScaffoldData)
    (boardFreeGrids : D.HasRobinsonBoardRoutedFreeGridInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate where
  indexedRoutedForces :=
    HasIndexedRoutedForces.ofRobinsonBoardRoutedFreeGrid boardFreeGrids
  realizes := realizes

def RoutedCertificate.ofRobinsonBoardGeometryTowerRoutingInvariant
    (D : Figure18ScaffoldData)
    (geometryRouting : D.HasRobinsonBoardGeometryTowerRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerRouting
      geometryRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData)
    (geometryRouting :
      D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofGeometryTowerCombinedSiteRouting
      geometryRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardFixedGeometryTowerRoutingInvariant
    (D : Figure18ScaffoldData)
    (fixedGeometryRouting :
      D.HasRobinsonBoardFixedGeometryTowerRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofFixedGeometryTowerRouting
      fixedGeometryRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardCanonicalRoutingInvariant
    (D : Figure18ScaffoldData)
    (canonicalRouting : D.HasRobinsonBoardCanonicalRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalRouting
      canonicalRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardCanonicalProductWitnessRoutingInvariant
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalProductWitnessRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalProductWitnessRouting
      canonicalRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardCanonicalCorridorRoutingInvariant
    (D : Figure18ScaffoldData)
    (canonicalRouting : D.HasRobinsonBoardCanonicalCorridorRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCorridorRouting
      canonicalRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardCanonicalCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalCombinedSiteRouting
      canonicalRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData)
    (fixedRouting :
      D.HasRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofFixedGeometryTowerSiteRectCombinedSiteRouting
      fixedRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalSiteRectCombinedSiteRouting
      canonicalRouting)
    realizes

def RoutedCertificate.ofRobinsonBoardCanonicalFreeSiteRectRoutingInvariant
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D
    (HasRobinsonBoardRoutedFreeGridInvariant.ofCanonicalFreeSiteRectRouting
      canonicalRouting)
    realizes

def RoutedCertificate.ofRobinsonSection7ObstructionRoutingInvariant
    (D : Figure18ScaffoldData)
    (section7Routing : D.HasRobinsonSection7ObstructionRoutingInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalFreeSiteRectRoutingInvariant D
    section7Routing realizes

/--
Robinson Section 7 board/free-line geometry plus realization gives the routed
scaffold certificate directly.
-/
def RoutedCertificate.ofRobinsonSection7BoardFreeLineActiveCornerInvariant
    (D : Figure18ScaffoldData)
    (boardFreeLineActiveCorner :
      D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.RoutedCertificate where
  indexedRoutedForces :=
    HasIndexedRoutedForces.ofBoardFreeLineActiveCorner
      boardFreeLineActiveCorner
  realizes := realizes

/--
Robinson Section 7 board/free-line geometry plus finite layer patches gives the
routed scaffold certificate directly.
-/
def RoutedCertificate.ofRobinsonSection7BoardFreeLineLayerPatches
    (D : Figure18ScaffoldData)
    (boardFreeLineActiveCorner :
      D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonSection7BoardFreeLineActiveCornerInvariant D
    boardFreeLineActiveCorner
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardRoutedFreeGridLayerPatches
    (D : Figure18ScaffoldData)
    (boardFreeGrids : D.HasRobinsonBoardRoutedFreeGridInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D boardFreeGrids
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardGeometryTowerRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (geometryRouting : D.HasRobinsonBoardGeometryTowerRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardGeometryTowerRoutingInvariant D
    geometryRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardFixedGeometryTowerRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (fixedGeometryRouting :
      D.HasRobinsonBoardFixedGeometryTowerRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardFixedGeometryTowerRoutingInvariant D
    fixedGeometryRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardCanonicalRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (canonicalRouting : D.HasRobinsonBoardCanonicalRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardCanonicalProductWitnessRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalProductWitnessRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalProductWitnessRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardCanonicalCorridorRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (canonicalRouting : D.HasRobinsonBoardCanonicalCorridorRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalCorridorRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardCanonicalCombinedSiteRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalCombinedSiteRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardCanonicalSiteRectCombinedSiteRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardCanonicalFreeSiteRectRoutingLayerPatches
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalFreeSiteRectRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofLayerPatches patches)

/--
Robinson Section 7 obstruction routing plus finite layer patches gives the
routed scaffold certificate.

This is the structured backward target suggested by the board/free-line proof:
the Section 7 obstruction argument supplies the routed free-grid forcing side,
while finite layer patches supply the realization side.
-/
def RoutedCertificate.ofRobinsonSection7LayerPatches
    (D : Figure18ScaffoldData)
    (section7Routing : D.HasRobinsonSection7ObstructionRoutingInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonSection7ObstructionRoutingInvariant D
    section7Routing
    (HasRealizationInvariant.ofLayerPatches patches)

def RoutedCertificate.ofRobinsonBoardRoutedFreeGridPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (boardFreeGrids : D.HasRobinsonBoardRoutedFreeGridInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardRoutedFreeGridInvariant D boardFreeGrids
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofRobinsonBoardGeometryTowerRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (geometryRouting : D.HasRobinsonBoardGeometryTowerRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardGeometryTowerRoutingInvariant D
    geometryRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofRobinsonBoardGeometryTowerCombinedSiteRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (geometryRouting :
      D.HasRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardGeometryTowerCombinedSiteRoutingInvariant D
    geometryRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofFixedGeometryTowerSiteRectCombinedPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (fixedRouting :
      D.HasRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardFixedGeometryTowerSiteRectCombinedSiteRoutingInvariant D
    fixedRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofRobinsonBoardFixedGeometryTowerRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (fixedGeometryRouting :
      D.HasRobinsonBoardFixedGeometryTowerRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardFixedGeometryTowerRoutingInvariant D
    fixedGeometryRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofRobinsonBoardCanonicalRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (canonicalRouting : D.HasRobinsonBoardCanonicalRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def
    RoutedCertificate.ofRobinsonBoardCanonicalProductWitnessRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalProductWitnessRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalProductWitnessRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofRobinsonBoardCanonicalCorridorRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (canonicalRouting : D.HasRobinsonBoardCanonicalCorridorRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalCorridorRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def
    RoutedCertificate.ofRobinsonBoardCanonicalCombinedSiteRoutingPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalCombinedSiteRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalCombinedSiteRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofCanonicalSiteRectCombinedPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalSiteRectCombinedSiteRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofCanonicalFreeSiteRectPositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (canonicalRouting :
      D.HasRobinsonBoardCanonicalFreeSiteRectRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonBoardCanonicalFreeSiteRectRoutingInvariant D
    canonicalRouting
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.ofRobinsonSection7PositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (section7Routing : D.HasRobinsonSection7ObstructionRoutingInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonSection7ObstructionRoutingInvariant D
    section7Routing
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

/--
Robinson Section 7 board/free-line geometry plus positive translated active
corner boxes gives the routed scaffold certificate directly.
-/
def RoutedCertificate.ofRobinsonSection7BoardFreeLinePositiveTranslatedBoxes
    (D : Figure18ScaffoldData)
    (boardFreeLineActiveCorner :
      D.HasRobinsonSection7BoardFreeLineActiveCornerInvariant)
    (boxes : D.HasPositiveTranslatedActiveCornerIndexedBoxInvariant) :
    D.RoutedCertificate :=
  RoutedCertificate.ofRobinsonSection7BoardFreeLineActiveCornerInvariant D
    boardFreeLineActiveCorner
    (HasRealizationInvariant.ofPositiveTranslatedActiveCornerIndexedBoxes boxes)

def RoutedCertificate.toIndexedRoutedCertificate
    {D : Figure18ScaffoldData} (certificate : D.RoutedCertificate) :
    Figure18IndexedRoutedCertificate D.table.toRoleTable where
  indexedRoutedForces := certificate.indexedRoutedForces
  realizes := by
    simpa [HasRealizationInvariant, scaffold, presentation, table]
      using certificate.realizes

def RoutedCertificate.toRoutedCertificate
    {D : Figure18ScaffoldData} (certificate : D.RoutedCertificate) :
    Figure18RoutedCertificate D.table.toRoleTable :=
  certificate.toIndexedRoutedCertificate.toRoutedCertificate

def RoutedCertificate.toFlexibleCertificate
    {D : Figure18ScaffoldData} (certificate : D.RoutedCertificate) :
    Figure18FlexibleCertificate D.table.toRoleTable :=
  certificate.toIndexedRoutedCertificate.toFlexibleCertificate

theorem RoutedCertificate.isScaffold
    {D : Figure18ScaffoldData} (certificate : D.RoutedCertificate) :
    IsScaffold D.scaffold := by
  simpa [scaffold, presentation, table] using
    certificate.toIndexedRoutedCertificate.isScaffold

def Certificate.ofWindowInvariant
    {D : Figure18ScaffoldData}
    (localFreeSquareWindows : D.HasLocalFreeSquareWindowInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.Certificate where
  localFreeSquares :=
    hasFigure18ListedActiveSiteFixedCornerSquares_of_windows
      localFreeSquareWindows
  realizes := realizes

def Certificate.ofWindowInvariantLayerPatches
    {D : Figure18ScaffoldData}
    (localFreeSquareWindows : D.HasLocalFreeSquareWindowInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.Certificate :=
  Certificate.ofWindowInvariant localFreeSquareWindows
    (HasRealizationInvariant.ofLayerPatches patches)

def Certificate.ofWindows
    (D : Figure18ScaffoldData)
    (localFreeSquareWindows : D.HasLocalFreeSquareWindowInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.Certificate :=
  Certificate.ofWindowInvariant localFreeSquareWindows realizes

def Certificate.ofWindowsLayerPatches
    (D : Figure18ScaffoldData)
    (localFreeSquareWindows : D.HasLocalFreeSquareWindowInvariant)
    (patches : D.HasLayerPatchRealizationInvariant) :
    D.Certificate :=
  Certificate.ofWindowInvariantLayerPatches localFreeSquareWindows patches

def Certificate.ofRobinsonBoardAdjacentFreeGridInvariant
    (D : Figure18ScaffoldData)
    (boardFreeGrids : D.HasRobinsonBoardAdjacentFreeGridInvariant)
    (realizes : D.HasRealizationInvariant) :
    D.Certificate :=
  Certificate.ofWindowInvariant
    (HasLocalFreeSquareWindowInvariant.ofRobinsonBoardAdjacentFreeGrid
      (D := D)
      boardFreeGrids)
    realizes

def Certificate.ofIndexedActiveWindows
    (D : Figure18ScaffoldData)
    (indexedActiveWindows :
      HasFigure18IndexedActiveCornerWindows D.table.toRoleTable)
    (realizes : D.HasRealizationInvariant) :
    D.Certificate :=
  Certificate.ofWindows D
    (HasLocalFreeSquareWindowInvariant.ofIndexedActive indexedActiveWindows)
    realizes

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

/--
The remaining Robinson-board tileability target is independent of the chosen
active/corner sites: every `Figure18ScaffoldData` presentation uses the same
subdivided Figure 13 scaffold tiles.
-/
theorem positiveTranslatedValidBoxes_ofFigure18ScaffoldTileableBoxes
    (D : Figure18ScaffoldData)
    (hboxes : ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    ∀ r : Nat, 0 < r →
      ∃ origin : Int × Int,
        ∃ base : TranslatedBoxPattern D.scaffold.tiles r origin,
          ValidTranslatedBoxTiling D.scaffold.tiles r origin base :=
  positiveTranslatedValidBoxes_of_tileableBoxes
    (fun r hr => by
      simpa [D.scaffold_tiles] using hboxes r hr)

/--
Shared route from Robinson-board tileability of the concrete Figure 18
scaffold tiles to the isolated-active-box invariant for a particular active
site choice.
-/
theorem HasPositiveTranslatedIsolatedActiveBoxInvariant.ofFigure18ScaffoldTileableBoxes
    {D : Figure18ScaffoldData}
    (hnoH : ∀ left : Figure18Site,
      left = D.cornerSite ∨ left ∈ D.activeSiteData.sites →
        ∀ right : Figure18Site,
          right = D.cornerSite ∨ right ∈ D.activeSiteData.sites →
            Figure18Site.hCompatible left right = false)
    (hnoV : ∀ lower : Figure18Site,
      lower = D.cornerSite ∨ lower ∈ D.activeSiteData.sites →
        ∀ upper : Figure18Site,
          upper = D.cornerSite ∨ upper ∈ D.activeSiteData.sites →
            Figure18Site.vCompatible lower upper = false)
    (hboxes : ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    D.HasPositiveTranslatedIsolatedActiveBoxInvariant :=
  HasPositiveTranslatedIsolatedActiveBoxInvariant.ofValidTranslatedBoxes hnoH hnoV
    (positiveTranslatedValidBoxes_ofFigure18ScaffoldTileableBoxes D hboxes)

theorem isolatedActiveBoxes_ofFigure18ScaffoldTileableBoxes
    {D : Figure18ScaffoldData}
    (hnoH : ∀ left : Figure18Site,
      left = D.cornerSite ∨ left ∈ D.activeSiteData.sites →
        ∀ right : Figure18Site,
          right = D.cornerSite ∨ right ∈ D.activeSiteData.sites →
            Figure18Site.hCompatible left right = false)
    (hnoV : ∀ lower : Figure18Site,
      lower = D.cornerSite ∨ lower ∈ D.activeSiteData.sites →
        ∀ upper : Figure18Site,
          upper = D.cornerSite ∨ upper ∈ D.activeSiteData.sites →
            Figure18Site.vCompatible lower upper = false)
    (hboxes : ∀ r : Nat, 0 < r → TileableBox figure18ScaffoldTiles r) :
    D.HasPositiveTranslatedIsolatedActiveBoxInvariant :=
  HasPositiveTranslatedIsolatedActiveBoxInvariant.ofFigure18ScaffoldTileableBoxes
    hnoH hnoV hboxes

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
