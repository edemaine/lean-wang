/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104HierarchyRecurrence

/-!
Decode ordinary corrected-Ollinger Wang tilings to typed `Fin 104` planes.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PlaneDecode

open Desubstitution FiniteRecognizability

theorem exists_index_of_mem_tileSet {wang : WangTile}
    (hwang : wang ∈ tileSet) :
    ∃ index : Index, tile (components index) = wang := by
  have hmap : wang ∈ alphabet.map tile := by
    simpa only [tileSet, List.mem_eraseDups] using hwang
  rcases List.mem_map.1 hmap with ⟨component, hcomponent, rfl⟩
  obtain ⟨position, hposition⟩ := List.mem_iff_get.1 hcomponent
  let index : Index := ⟨position.val, by
    simpa only [alphabet_length] using position.isLt⟩
  refine ⟨index, ?_⟩
  have hcomponents : components index = component := by
    change alphabet.get position = component
    exact hposition
  rw [hcomponents]

theorem indexOfTile_correct {wang : WangTile} (hwang : wang ∈ tileSet) :
    tile (components (indexOfTile wang)) = wang := by
  obtain ⟨index, hindex⟩ := exists_index_of_mem_tileSet hwang
  have hmem : index ∈ indexCandidates wang := by
    simp [indexCandidates, hindex]
  cases hcandidates : indexCandidates wang with
  | nil => simp [hcandidates] at hmem
  | cons head tail =>
      have hhead : head ∈ indexCandidates wang := by
        rw [hcandidates]
        exact List.mem_cons_self
      have hheadTile : tile (components head) = wang := by
        simpa [indexCandidates] using hhead
      simpa [indexOfTile, hcandidates] using hheadTile

/-- Decode each Wang tile in a plane to its unique corrected index. -/
def indexPlane (x : Int × Int → TileIn tileSet) : IndexPlane :=
  fun p => indexOfTile (x p).1

@[simp]
theorem tile_indexPlane (x : Int × Int → TileIn tileSet) (p : Int × Int) :
    tile (components (indexPlane x p)) = (x p).1 :=
  indexOfTile_correct (x p).2

/-- Matching of an ordinary Wang tiling transfers to its typed index plane. -/
theorem indexPlane_valid {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    ValidIndexPlane (indexPlane x) := by
  constructor
  · intro p
    simpa only [tile_indexPlane] using hx.1 p
  · intro p
    simpa only [tile_indexPlane] using hx.2 p

/-- Every corrected-Ollinger Wang tiling has a typed desubstitution tower. -/
noncomputable def towerOfTiling {x : Int × Int → TileIn tileSet}
    (hx : ValidPlaneTiling tileSet x) :
    Hierarchy.Tower ⟨indexPlane x, indexPlane_valid hx⟩ :=
  Hierarchy.tower ⟨indexPlane x, indexPlane_valid hx⟩

theorem tilesPlane_iff_indexPlane :
    TilesPlane tileSet ↔ ∃ z : IndexPlane, ValidIndexPlane z := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨indexPlane x, indexPlane_valid hx⟩
  · rintro ⟨z, hz⟩
    let x : Int × Int → TileIn tileSet := fun p =>
      ⟨tile (components (z p)), tile_components_mem (z p)⟩
    exact ⟨x, hz⟩

end PlaneDecode
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
