/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinsonScaffold

/-!
Finite transcription helpers for the Ollinger/Robinson scaffold.

Figure 13 of Jeandel and Vanier's notes gives the scaffold as finite tile data.
This module provides the Lean-side data format for that transcription: each tile
is recorded once with its payload role, and a primitive-recursive finite lookup
turns the transcription into the `ScaffoldPresentation` interface.
-/

namespace LeanWang
namespace OllingerRobinson

/-- One transcribed scaffold tile together with its payload role. -/
structure RoleTileSpec where
  tile : WangTile
  role : CellRole
deriving DecidableEq, Repr

namespace RoleTileSpec

/-- Readable constructor for transcribing a tile by edge colors and role. -/
def ofEdges (role : CellRole) (n s e w : Nat) : RoleTileSpec where
  tile := { n := n, s := s, e := e, w := w }
  role := role

def toPair (spec : RoleTileSpec) : WangTile × CellRole :=
  (spec.tile, spec.role)

@[simp]
theorem ofEdges_tile (role : CellRole) (n s e w : Nat) :
    (ofEdges role n s e w).tile = { n := n, s := s, e := e, w := w } :=
  rfl

@[simp]
theorem ofEdges_role (role : CellRole) (n s e w : Nat) :
    (ofEdges role n s e w).role = role :=
  rfl

@[simp]
theorem toPair_fst (spec : RoleTileSpec) :
    spec.toPair.1 = spec.tile :=
  rfl

@[simp]
theorem toPair_snd (spec : RoleTileSpec) :
    spec.toPair.2 = spec.role :=
  rfl

end RoleTileSpec

/-- Shorthand for one row of concrete scaffold data: role followed by edge colors. -/
def spec (role : CellRole) (n s e w : Nat) : RoleTileSpec :=
  RoleTileSpec.ofEdges role n s e w

/--
Finite role lookup used by a concrete scaffold transcription.

Tiles not listed in the transcription default to `inactive`; this default is
irrelevant for the scaffold tileset itself, whose membership is the transcribed
tile list, but it makes the role decoder total on `WangTile`.
-/
def lookupRole : List (WangTile × CellRole) → WangTile → CellRole
  | [], _ => CellRole.inactive
  | (tile, role) :: entries, query =>
      if query = tile then role else lookupRole entries query

@[simp]
theorem lookupRole_nil (query : WangTile) :
    lookupRole [] query = CellRole.inactive :=
  rfl

@[simp]
theorem lookupRole_cons (tile query : WangTile) (role : CellRole)
    (entries : List (WangTile × CellRole)) :
    lookupRole ((tile, role) :: entries) query =
      if query = tile then role else lookupRole entries query :=
  rfl

theorem lookupRole_primrec (entries : List (WangTile × CellRole)) :
    Primrec (lookupRole entries) := by
  induction entries with
  | nil =>
      exact Primrec.const CellRole.inactive
  | cons entry entries ih =>
      rcases entry with ⟨tile, role⟩
      exact (Primrec.ite
        (Primrec.eq.comp Primrec.id (Primrec.const tile))
        (Primrec.const role) ih).of_eq fun query => by
          simp [lookupRole]

/-- The concrete tiles in a transcribed scaffold list. -/
def tilesOfSpecs (specs : List RoleTileSpec) : TileSet :=
  specs.map RoleTileSpec.tile

/-- Role lookup entries extracted from a transcribed scaffold list. -/
def roleEntriesOfSpecs (specs : List RoleTileSpec) : List (WangTile × CellRole) :=
  specs.map RoleTileSpec.toPair

/-!
The tile list in Figure 13 is meant to be a set.  Keeping this as a separate
finite check catches accidental duplicate transcriptions before the more
semantic scaffold obligations are attempted.
-/
def nodupTilesBool (specs : List RoleTileSpec) : Bool :=
  decide (List.Nodup (tilesOfSpecs specs))

theorem nodupTiles_of_nodupTilesBool {specs : List RoleTileSpec}
    (hcheck : nodupTilesBool specs = true) :
    List.Nodup (tilesOfSpecs specs) := by
  exact of_decide_eq_true hcheck

@[simp]
theorem mem_tilesOfSpecs {specs : List RoleTileSpec} {tile : WangTile} :
    tile ∈ tilesOfSpecs specs ↔ ∃ spec ∈ specs, spec.tile = tile := by
  simp [tilesOfSpecs]

@[simp]
theorem roleEntriesOfSpecs_nil :
    roleEntriesOfSpecs [] = [] :=
  rfl

@[simp]
theorem roleEntriesOfSpecs_cons (spec : RoleTileSpec) (specs : List RoleTileSpec) :
    roleEntriesOfSpecs (spec :: specs) = spec.toPair :: roleEntriesOfSpecs specs :=
  rfl

theorem lookupRole_eq_role_of_mem_of_nodup
    {specs : List RoleTileSpec} (hnodup : List.Nodup (tilesOfSpecs specs))
    {spec : RoleTileSpec} (hspec : spec ∈ specs) :
    lookupRole (roleEntriesOfSpecs specs) spec.tile = spec.role := by
  induction specs with
  | nil =>
      cases hspec
  | cons head tail ih =>
      simp only [tilesOfSpecs, List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hspec
      rcases hspec with hhead | htail
      · subst head
        simp [lookupRole]
      · have hne : spec.tile ≠ head.tile := by
          intro heq
          have hmemTail : spec.tile ∈ tilesOfSpecs tail := by
            exact (mem_tilesOfSpecs.2 ⟨spec, htail, rfl⟩)
          exact hnodup.1 (by simpa [heq] using hmemTail)
        simpa [lookupRole, hne] using ih hnodup.2 htail

theorem lookupRole_eq_role_of_mem_of_nodupTilesBool
    {specs : List RoleTileSpec} (hcheck : nodupTilesBool specs = true)
    {spec : RoleTileSpec} (hspec : spec ∈ specs) :
    lookupRole (roleEntriesOfSpecs specs) spec.tile = spec.role :=
  lookupRole_eq_role_of_mem_of_nodup (nodupTiles_of_nodupTilesBool hcheck) hspec

theorem mem_tilesOfSpecs_of_lookupRole_eq_corner
    {specs : List RoleTileSpec} {tile : WangTile}
    (hlookup : lookupRole (roleEntriesOfSpecs specs) tile = CellRole.corner) :
    tile ∈ tilesOfSpecs specs := by
  induction specs with
  | nil =>
      simp at hlookup
  | cons head tail ih =>
      by_cases htile : tile = head.tile
      · simp [tilesOfSpecs, htile]
      · have htail : lookupRole (roleEntriesOfSpecs tail) tile = CellRole.corner := by
          simpa [roleEntriesOfSpecs, RoleTileSpec.toPair, lookupRole, htile] using hlookup
        have hmemTail : tile ∈ tilesOfSpecs tail := ih htail
        rcases mem_tilesOfSpecs.1 hmemTail with ⟨spec, hspec, hspecTile⟩
        exact mem_tilesOfSpecs.2 ⟨spec, List.mem_cons_of_mem head hspec, hspecTile⟩

/-!
The following checker is intentionally role-level, not presentation-level.  For
the concrete Figure 13 list, it lets the data say directly that the only tile
declared with role `corner` is the distinguished corner tile.  Together with
the no-duplicate-tile check, this implies the presentation's finite sanity
condition.
-/

def cornerRoleUniqueBool (specs : List RoleTileSpec) (cornerTile : WangTile) :
    Bool :=
  specs.all fun spec =>
    decide (spec.role = CellRole.corner) == decide (spec.tile = cornerTile)

theorem cornerRoleUniqueBool_of_forall_mem
    {specs : List RoleTileSpec} {cornerTile : WangTile}
    (hunique : ∀ spec : RoleTileSpec, spec ∈ specs →
      (spec.role = CellRole.corner ↔ spec.tile = cornerTile)) :
    cornerRoleUniqueBool specs cornerTile = true := by
  unfold cornerRoleUniqueBool
  rw [List.all_eq_true]
  intro spec hspec
  rw [beq_iff_eq]
  exact Bool.decide_congr (hunique spec hspec)

private theorem cornerRoleUniqueBool_mem_eq
    {specs : List RoleTileSpec} {cornerTile : WangTile}
    (hcheck : cornerRoleUniqueBool specs cornerTile = true)
    {spec : RoleTileSpec} (hspec : spec ∈ specs) :
    decide (spec.role = CellRole.corner) = decide (spec.tile = cornerTile) := by
  unfold cornerRoleUniqueBool at hcheck
  have hall := List.all_eq_true.1 hcheck spec hspec
  cases hleft : decide (spec.role = CellRole.corner) <;>
    cases hright : decide (spec.tile = cornerTile) <;>
      simp [hleft, hright] at hall ⊢

theorem spec_tile_eq_corner_of_cornerRoleUniqueBool
    {specs : List RoleTileSpec} {cornerTile : WangTile}
    (hcheck : cornerRoleUniqueBool specs cornerTile = true)
    {spec : RoleTileSpec} (hspec : spec ∈ specs)
    (hrole : spec.role = CellRole.corner) :
    spec.tile = cornerTile := by
  have heq := cornerRoleUniqueBool_mem_eq hcheck hspec
  have hleft : decide (spec.role = CellRole.corner) = true :=
    decide_eq_true hrole
  have hright : decide (spec.tile = cornerTile) = true := by
    simpa [hleft] using heq.symm
  exact of_decide_eq_true hright

theorem cornerRoleUnique_of_nodupTilesBool
    {specs : List RoleTileSpec} {cornerTile : WangTile}
    (hnodup : nodupTilesBool specs = true)
    (hunique : cornerRoleUniqueBool specs cornerTile = true) :
    ∀ tile : WangTile, tile ∈ tilesOfSpecs specs →
      lookupRole (roleEntriesOfSpecs specs) tile = CellRole.corner →
        tile = cornerTile := by
  intro tile htile hrole
  rcases mem_tilesOfSpecs.1 htile with ⟨spec, hspec, hspecTile⟩
  have hlookup := lookupRole_eq_role_of_mem_of_nodupTilesBool hnodup hspec
  have hspecRole : spec.role = CellRole.corner := by
    have hlookupTile : lookupRole (roleEntriesOfSpecs specs) tile = spec.role := by
      simpa [hspecTile] using hlookup
    exact hlookupTile.symm.trans hrole
  exact hspecTile.symm.trans
    (spec_tile_eq_corner_of_cornerRoleUniqueBool hunique hspec hspecRole)

/--
Turn a finite role transcription into a scaffold presentation.

The `corner_role` proof is intentionally explicit. For the final Figure 13 data
it should be discharged by normalization, making transcription mistakes visible
at the boundary where the distinguished corner tile is declared.
-/
def presentationOfSpecs
    (specs : List RoleTileSpec) (cornerTile : WangTile)
    (hcorner : lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner) :
    ScaffoldPresentation where
  tiles := tilesOfSpecs specs
  role := lookupRole (roleEntriesOfSpecs specs)
  cornerTile := cornerTile
  role_primrec := lookupRole_primrec (roleEntriesOfSpecs specs)
  corner_role := hcorner

@[simp]
theorem presentationOfSpecs_tiles
    (specs : List RoleTileSpec) (cornerTile : WangTile)
    (hcorner : lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner) :
    (presentationOfSpecs specs cornerTile hcorner).tiles = tilesOfSpecs specs :=
  rfl

@[simp]
theorem presentationOfSpecs_role
    (specs : List RoleTileSpec) (cornerTile tile : WangTile)
    (hcorner : lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner) :
    (presentationOfSpecs specs cornerTile hcorner).role tile =
      lookupRole (roleEntriesOfSpecs specs) tile :=
  rfl

@[simp]
theorem presentationOfSpecs_cornerTile
    (specs : List RoleTileSpec) (cornerTile : WangTile)
    (hcorner : lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner) :
    (presentationOfSpecs specs cornerTile hcorner).cornerTile = cornerTile :=
  rfl

theorem sanityBool_of_specChecks
    {specs : List RoleTileSpec} {cornerTile : WangTile}
    (hcorner : lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner)
    (hnodup : nodupTilesBool specs = true)
    (hunique : cornerRoleUniqueBool specs cornerTile = true) :
    (presentationOfSpecs specs cornerTile hcorner).sanityBool = true := by
  unfold ScaffoldPresentation.sanityBool
  rw [Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    exact mem_tilesOfSpecs_of_lookupRole_eq_corner hcorner
  · unfold ScaffoldPresentation.cornerUniqueBool
    rw [List.all_eq_true]
    intro tile htile
    have hunique' := cornerRoleUnique_of_nodupTilesBool hnodup hunique
    rw [beq_iff_eq]
    apply Bool.decide_congr
    constructor
    · intro hrole
      have htileCorner : tile = cornerTile :=
        hunique' tile (by simpa [presentationOfSpecs] using htile)
          (by simpa [presentationOfSpecs] using hrole)
      simpa [presentationOfSpecs] using htileCorner
    · intro htileCorner
      simpa [presentationOfSpecs, htileCorner] using hcorner

/--
Finite checks for a transcribed scaffold tile list, before the geometric
recognizability and realization facts are supplied.

This is the target for the Figure 13 transcription: the list has no duplicate
tiles, the declared corner decodes as `CellRole.corner`, and the presentation's
finite sanity checker accepts it.
-/
structure FiniteCheckedTranscription where
  specs : List RoleTileSpec
  cornerTile : WangTile
  corner_role :
    lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner
  nodup : nodupTilesBool specs = true
  sanity :
    (presentationOfSpecs specs cornerTile corner_role).sanityBool = true

/--
Package a concrete role transcription from the finite checks that are easiest
to audit on the raw list: the declared corner decodes as a corner, tiles are
not duplicated, and no other listed tile is declared as the corner.
-/
def finiteCheckedTranscriptionOfSpecChecks
    (specs : List RoleTileSpec) (cornerTile : WangTile)
    (hcorner : lookupRole (roleEntriesOfSpecs specs) cornerTile = CellRole.corner)
    (hnodup : nodupTilesBool specs = true)
    (hunique : cornerRoleUniqueBool specs cornerTile = true) :
    FiniteCheckedTranscription where
  specs := specs
  cornerTile := cornerTile
  corner_role := hcorner
  nodup := hnodup
  sanity := sanityBool_of_specChecks hcorner hnodup hunique

namespace FiniteCheckedTranscription

def presentation (D : FiniteCheckedTranscription) : ScaffoldPresentation :=
  presentationOfSpecs D.specs D.cornerTile D.corner_role

theorem nodup_tiles (D : FiniteCheckedTranscription) :
    List.Nodup (tilesOfSpecs D.specs) :=
  nodupTiles_of_nodupTilesBool D.nodup

theorem sanityProp (D : FiniteCheckedTranscription) :
    D.presentation.Sanity :=
  ScaffoldPresentation.sanity_of_sanityBool D.sanity

theorem corner_mem (D : FiniteCheckedTranscription) :
    D.cornerTile ∈ tilesOfSpecs D.specs := by
  simpa [presentation] using D.sanityProp.corner_mem

theorem corner_unique (D : FiniteCheckedTranscription) :
    ∀ tile : WangTile, tile ∈ tilesOfSpecs D.specs →
      lookupRole (roleEntriesOfSpecs D.specs) tile = CellRole.corner →
        tile = D.cornerTile := by
  simpa [presentation] using D.sanityProp.corner_unique

theorem lookupRole_eq_role_of_mem (D : FiniteCheckedTranscription)
    {spec : RoleTileSpec} (hspec : spec ∈ D.specs) :
    lookupRole (roleEntriesOfSpecs D.specs) spec.tile = spec.role :=
  lookupRole_eq_role_of_mem_of_nodup D.nodup_tiles hspec

theorem corner_unique_of_spec_role (D : FiniteCheckedTranscription)
    {spec : RoleTileSpec} (hspec : spec ∈ D.specs)
    (hrole : spec.role = CellRole.corner) :
    spec.tile = D.cornerTile := by
  exact D.corner_unique spec.tile
    (mem_tilesOfSpecs.2 ⟨spec, hspec, rfl⟩)
    (by simpa [D.lookupRole_eq_role_of_mem hspec] using hrole)

end FiniteCheckedTranscription

/--
Concrete scaffold transcription package.

The remaining hard geometric facts, `recognizable` and `realizes`, stay stated
against the derived presentation. This keeps the finite data, finite sanity
check, and geometric proof obligations in one inspectable object.
-/
structure CheckedTranscription where
  finite : FiniteCheckedTranscription
  recognizable :
    HasPresentedRecognizableFreeSquares
      finite.presentation
  realizes :
    RealizesActiveCornerSquares finite.presentation.toScaffold

/--
Checked finite transcription plus the flexible geometric certificate shape.

This is likely the better target for the Robinson/Ollinger Figure 18 argument:
the finite Figure 13 data is checked once, and the geometric proof may directly
extract payload fixed-corner squares through the scaffold channels.
-/
structure CheckedFlexibleTranscription where
  finite : FiniteCheckedTranscription
  forces : ForcesFixedCornerSquares finite.presentation.toScaffold
  realizes : RealizesActiveCornerSquares finite.presentation.toScaffold

namespace CheckedTranscription

def presentation (D : CheckedTranscription) : ScaffoldPresentation :=
  D.finite.presentation

def toCheckedPresentedInstance (D : CheckedTranscription) :
    CheckedPresentedInstance where
  presentation := D.presentation
  sanity := D.finite.sanity
  recognizable := D.recognizable
  realizes := D.realizes

theorem isScaffold (D : CheckedTranscription) :
    IsScaffold D.presentation.toScaffold :=
  D.toCheckedPresentedInstance.isScaffold

end CheckedTranscription

namespace CheckedFlexibleTranscription

def presentation (D : CheckedFlexibleTranscription) : ScaffoldPresentation :=
  D.finite.presentation

def toPresentedFlexibleInstance (D : CheckedFlexibleTranscription) :
    PresentedFlexibleInstance where
  presentation := D.presentation
  certificate := {
    forces := D.forces
    realizes := D.realizes
  }

theorem isScaffold (D : CheckedFlexibleTranscription) :
    IsScaffold D.presentation.toScaffold :=
  D.toPresentedFlexibleInstance.isScaffold

end CheckedFlexibleTranscription

end OllingerRobinson
end LeanWang
