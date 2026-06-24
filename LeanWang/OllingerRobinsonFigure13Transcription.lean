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
