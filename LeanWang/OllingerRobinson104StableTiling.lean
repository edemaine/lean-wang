/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104StableTilesCorrect
import LeanWang.OllingerRobinson104Tiling

/-!
Plane tileability for the substitution-stable corrected Ollinger edge colors.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace DerivedOne

def Compatible {w h : Nat} (R : IndexRectangle w h) : Prop :=
  (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
    WangTile.HMatches
      (derivedTile 1 (R i j))
      (derivedTile 1 (R ⟨i.val + 1, hi⟩ j))) ∧
  (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
    WangTile.VMatches
      (derivedTile 1 (R i j))
      (derivedTile 1 (R i ⟨j.val + 1, hj⟩)))

def tileRectangle {w h : Nat} (R : IndexRectangle w h) : Rectangle w h :=
  fun i j => derivedTile 1 (R i j)

theorem tileRectangle_valid {w h : Nat} {R : IndexRectangle w h}
    (hR : Compatible R) :
    ValidRectangle (derivedTileSet 1) (tileRectangle R) := by
  exact ⟨fun i j => derivedTile_mem_derivedTileSet 1 (R i j), hR.1, hR.2⟩

private theorem expand_hMatches_within {w h : Nat}
    (R : IndexRectangle w h) (i : Fin w) (j : Fin h) (dj : Fin 2) :
    WangTile.HMatches
      (derivedTile 1 (childBlock (R i j) ⟨0, by decide⟩ dj))
      (derivedTile 1 (childBlock (R i j) ⟨1, by decide⟩ dj)) := by
  exact (derivedChildRectangle_valid_one (R i j)).2.1
    ⟨0, by decide⟩ dj (by decide)

private theorem expand_vMatches_within {w h : Nat}
    (R : IndexRectangle w h) (i : Fin w) (j : Fin h) (di : Fin 2) :
    WangTile.VMatches
      (derivedTile 1 (childBlock (R i j) di ⟨0, by decide⟩))
      (derivedTile 1 (childBlock (R i j) di ⟨1, by decide⟩)) := by
  exact (derivedChildRectangle_valid_one (R i j)).2.2
    di ⟨0, by decide⟩ (by decide)

private theorem expand_hMatches_boundary {w h : Nat}
    {R : IndexRectangle w h} (hR : Compatible R)
    (i : Fin w) (j : Fin h) (hi : i.val + 1 < w) (dj : Fin 2) :
    WangTile.HMatches
      (derivedTile 1 (childBlock (R i j) ⟨1, by decide⟩ dj))
      (derivedTile 1
        (childBlock (R ⟨i.val + 1, hi⟩ j) ⟨0, by decide⟩ dj)) := by
  have hboundary := (hMatches_derived_one_iff_child
    (R i j) (R ⟨i.val + 1, hi⟩ j)).1 (hR.1 i j hi)
  have hcases : dj.val = 0 ∨ dj.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hdj : dj = ⟨0, by decide⟩ := Fin.ext hzero
    simpa [hdj, DerivedChildHMatches, derivedChildRectangle, offset0, offset1]
      using hboundary.1
  · have hdj : dj = ⟨1, by decide⟩ := Fin.ext hone
    simpa [hdj, DerivedChildHMatches, derivedChildRectangle, offset0, offset1]
      using hboundary.2

private theorem expand_vMatches_boundary {w h : Nat}
    {R : IndexRectangle w h} (hR : Compatible R)
    (i : Fin w) (j : Fin h) (hj : j.val + 1 < h) (di : Fin 2) :
    WangTile.VMatches
      (derivedTile 1 (childBlock (R i j) di ⟨1, by decide⟩))
      (derivedTile 1
        (childBlock (R i ⟨j.val + 1, hj⟩) di ⟨0, by decide⟩)) := by
  have hboundary := (vMatches_derived_one_iff_child
    (R i j) (R i ⟨j.val + 1, hj⟩)).1 (hR.2 i j hj)
  have hcases : di.val = 0 ∨ di.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hdi : di = ⟨0, by decide⟩ := Fin.ext hzero
    simpa [hdi, DerivedChildVMatches, derivedChildRectangle, offset0, offset1]
      using hboundary.1
  · have hdi : di = ⟨1, by decide⟩ := Fin.ext hone
    simpa [hdi, DerivedChildVMatches, derivedChildRectangle, offset0, offset1]
      using hboundary.2

theorem expand_compatible {w h : Nat} {R : IndexRectangle w h}
    (hR : Compatible R) : Compatible R.expand := by
  constructor
  · intro i j hi
    rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one i with hzero | hone
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_zero i hi hzero with
        ⟨hblock, hoff⟩
      have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨0, by decide⟩ :=
        Fin.ext hzero
      simpa [IndexRectangle.expand, hblock, hoff, hoff_i] using
        expand_hMatches_within R
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset j)
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_one i hi hone with
        ⟨hb, hblock, hoff⟩
      have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨1, by decide⟩ :=
        Fin.ext hone
      simpa [IndexRectangle.expand, hblock, hoff, hoff_i] using
        expand_hMatches_boundary hR
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j) hb
          (Figure16.BlockGrid.doubledOffset j)
  · intro i j hj
    rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one j with hzero | hone
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_zero j hj hzero with
        ⟨hblock, hoff⟩
      have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨0, by decide⟩ :=
        Fin.ext hzero
      simpa [IndexRectangle.expand, hblock, hoff, hoff_j] using
        expand_vMatches_within R
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_one j hj hone with
        ⟨hb, hblock, hoff⟩
      have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨1, by decide⟩ :=
        Fin.ext hone
      simpa [IndexRectangle.expand, hblock, hoff, hoff_j] using
        expand_vMatches_boundary hR
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j) hb
          (Figure16.BlockGrid.doubledOffset i)

theorem substitutionSquare_compatible (level : Nat) :
    Compatible (substitutionSquare level) := by
  induction level with
  | zero =>
      simp [Compatible, substitutionSquare, substitutionSide]
  | succ level ih =>
      exact expand_compatible ih

theorem tileableSquare_substitutionSide (level : Nat) :
    TileableSquare (derivedTileSet 1) (substitutionSide level) :=
  ⟨tileRectangle (substitutionSquare level),
    tileRectangle_valid (substitutionSquare_compatible level)⟩

theorem all_tileableSquares :
    ∀ n : Nat, TileableSquare (derivedTileSet 1) n := by
  intro n
  exact tileableSquare_crop (level_le_substitutionSide n)
    (tileableSquare_substitutionSide n)

/-- The substitution-stable corrected Ollinger tileset tiles the plane. -/
theorem tilesPlane_derivedTileSet_one : TilesPlane (derivedTileSet 1) :=
  (tilesPlane_iff_all_tileableSquares (derivedTileSet 1)).2 all_tileableSquares

end DerivedOne
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
