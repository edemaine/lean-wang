/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PointedExtension
import LeanWang.RoutedScaffold
import LeanWang.Compactness

/-!
# Routed scaffolds for pointed full-plane payloads

The Robinson signal components need not place a distinguished crossing at the
southwest corner of the component.  Their natural backward input is therefore
a full-plane payload tiling with the distinguished payload at the origin.

`PointedExtension` supplies exactly that input from a seeded source quadrant.
The already-proved forward scaffold theorem is unchanged: it extracts finite
southwest-rooted squares of the extended tileset, which decode back to source
squares.
-/

namespace LeanWang

/-- A valid full-plane tiling with a prescribed tile at coordinate zero. -/
def TilesPointedPlane (T : TileSet) (seed : WangTile) : Prop :=
  ∃ plane : Int × Int → TileIn T,
    ValidPlaneTiling T plane ∧ (plane (0, 0)).1 = seed

namespace PointedExtension

theorem tilesPointedPlane_of_tilesQuarterWithSeed
    {T : TileSet} {seed : WangTile} :
    TilesQuarterWithSeed T seed →
      TilesPointedPlane (tiles T seed) (pointedSeed seed) :=
  exists_pointed_plane_of_tilesQuarterWithSeed

end PointedExtension

/-- Backward scaffold property needed for pointed full-plane payloads. -/
def RealizesRoutedPointedPlanes (S : RoutedScaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile),
    TilesPointedPlane T seed →
      TilesPlane (combineWithRoutedScaffold S T seed)

/-- Finite-patch form of pointed full-plane realization. -/
def HasRoutedCombinedBoxLayerPatchesOfPointedPlanes
    (S : RoutedScaffold) : Prop :=
  ∀ (T : TileSet) (seed : WangTile)
    (plane : Int × Int → TileIn T),
    ValidPlaneTiling T plane → (plane (0, 0)).1 = seed →
      ∀ r : Nat, Nonempty (RoutedCombinedBoxLayerPatch S T seed r)

/-- Pointed finite patches produce a combined plane by ordinary Wang
compactness. -/
theorem realizesRoutedPointedPlanes_of_combinedBoxLayerPatches
    {S : RoutedScaffold}
    (patches : HasRoutedCombinedBoxLayerPatchesOfPointedPlanes S) :
    RealizesRoutedPointedPlanes S := by
  intro T seed pointed
  rcases pointed with ⟨plane, valid, seeded⟩
  apply tilesPlane_of_all_tileableBoxes
  intro radius
  rcases patches T seed plane valid seeded radius with ⟨patch⟩
  exact patch.tileableBox

/-- The pointed extension turns the asymmetric forward/backward scaffold
properties into an exact seeded-quarter-plane reduction. -/
theorem routedPointedExtension_reduction_correct
    {S : RoutedScaffold}
    (realizes : RealizesRoutedPointedPlanes S)
    (forces : ForcesRoutedFixedCornerSquares S)
    (T : TileSet) (seed : WangTile) :
    TilesPlane (combineWithRoutedScaffold S
        (PointedExtension.tiles T seed) (PointedExtension.pointedSeed seed)) ↔
      TilesQuarterWithSeed T seed := by
  constructor
  · intro combined
    apply tilesQuarterWithSeed_of_all_fixedCornerSquares
    intro size positive
    exact PointedExtension.source_fixedCornerSquare_of_extension
      (forces combined size positive)
  · intro source
    exact realizes _ _
      (PointedExtension.tilesPointedPlane_of_tilesQuarterWithSeed source)

end LeanWang
