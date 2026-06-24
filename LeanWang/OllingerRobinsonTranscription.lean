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

def toPair (spec : RoleTileSpec) : WangTile × CellRole :=
  (spec.tile, spec.role)

@[simp]
theorem toPair_fst (spec : RoleTileSpec) :
    spec.toPair.1 = spec.tile :=
  rfl

@[simp]
theorem toPair_snd (spec : RoleTileSpec) :
    spec.toPair.2 = spec.role :=
  rfl

end RoleTileSpec

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
