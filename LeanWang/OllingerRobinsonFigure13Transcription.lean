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

def tile (site : Figure18Site) : WangTile :=
  fig13QuarterTile site.index site.quadrant

/-- All Figure 18 quadrant sites, ordered by Figure 13 tile index then quadrant. -/
def all : List Figure18Site :=
  (List.finRange 92).flatMap fun i =>
    Quadrant.all.map fun q => ({ index := i, quadrant := q } : Figure18Site)

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

def smokeFlatRoles : List CellRole :=
  CellRole.corner :: List.replicate 367 CellRole.inactive

@[simp]
theorem smokeRoleRows_length : smokeRoleRows.length = 92 := by
  decide

@[simp]
theorem smokeFlatRoles_length : smokeFlatRoles.length = 368 := by
  change (CellRole.corner :: List.replicate 367 CellRole.inactive).length = 368
  rw [List.length_cons, List.length_replicate]

def smokeCornerIndex : Fin 92 :=
  ⟨0, by decide⟩

def smokeCornerQuadrant : Quadrant :=
  Quadrant.southwest

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

@[simp]
theorem smoke_roleAt_corner :
    smoke.roleAt smokeCornerIndex smokeCornerQuadrant = CellRole.corner :=
  smoke.roleAt_corner

theorem smoke_presentation_tiles :
    smoke.presentation.tiles = TileSubdivision.subdivideTileSet fig13Tiles :=
  smoke.presentation_tiles

end Figure18RoleTable

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

end Figure18IndexedRoutedFixedCornerSquare

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
