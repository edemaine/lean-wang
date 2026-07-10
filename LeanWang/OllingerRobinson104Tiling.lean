/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Compactness
import LeanWang.OllingerRobinson104Tiles

/-!
Plane tileability of the corrected Ollinger substitution alphabet.

The finite certificates in `OllingerRobinson104Tiles` prove that every tile
has a valid `2 x 2` substitution image and that substitution preserves matching
boundaries. Here those local checks are iterated and compactness turns the
resulting cofinal family of finite squares into a plane tiling.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

/-- A finite rectangle labelled by corrected Ollinger tile indices. -/
abbrev IndexRectangle (w h : Nat) := Fin w → Fin h → Index

namespace IndexRectangle

/-- Matching condition on an index rectangle, interpreted through `tile`. -/
def Compatible {w h : Nat} (R : IndexRectangle w h) : Prop :=
  (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
    WangTile.HMatches
      (tile (components (R i j)))
      (tile (components (R ⟨i.val + 1, hi⟩ j)))) ∧
  (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
    WangTile.VMatches
      (tile (components (R i j)))
      (tile (components (R i ⟨j.val + 1, hj⟩))))

/-- Forget corrected tile indices to their Wang tiles. -/
def tileRectangle {w h : Nat} (R : IndexRectangle w h) : Rectangle w h :=
  fun i j => tile (components (R i j))

theorem tileRectangle_valid {w h : Nat} {R : IndexRectangle w h}
    (hR : R.Compatible) :
    ValidRectangle tileSet R.tileRectangle := by
  exact ⟨fun i j => tile_components_mem (R i j), hR.1, hR.2⟩

/-- Replace each index by its corrected Figure 16 child block. -/
def expand {w h : Nat} (R : IndexRectangle w h) :
    IndexRectangle (2 * w) (2 * h) :=
  fun i j => childBlock
    (R (Figure16.BlockGrid.doubledBlockCoord i)
      (Figure16.BlockGrid.doubledBlockCoord j))
    (Figure16.BlockGrid.doubledOffset i)
    (Figure16.BlockGrid.doubledOffset j)

private theorem expand_hMatches_within {w h : Nat}
    (R : IndexRectangle w h) (i : Fin w) (j : Fin h) (dj : Fin 2) :
    WangTile.HMatches
      (tile (components (childBlock (R i j) ⟨0, by decide⟩ dj)))
      (tile (components (childBlock (R i j) ⟨1, by decide⟩ dj))) := by
  have hvalid := childRectangle_valid (R i j)
  exact hvalid.2.1 ⟨0, by decide⟩ dj (by decide)

private theorem expand_vMatches_within {w h : Nat}
    (R : IndexRectangle w h) (i : Fin w) (j : Fin h) (di : Fin 2) :
    WangTile.VMatches
      (tile (components (childBlock (R i j) di ⟨0, by decide⟩)))
      (tile (components (childBlock (R i j) di ⟨1, by decide⟩))) := by
  have hvalid := childRectangle_valid (R i j)
  exact hvalid.2.2 di ⟨0, by decide⟩ (by decide)

private theorem expand_hMatches_boundary {w h : Nat}
    {R : IndexRectangle w h} (hR : R.Compatible)
    (i : Fin w) (j : Fin h) (hi : i.val + 1 < w) (dj : Fin 2) :
    WangTile.HMatches
      (tile (components (childBlock (R i j) ⟨1, by decide⟩ dj)))
      (tile (components
        (childBlock (R ⟨i.val + 1, hi⟩ j) ⟨0, by decide⟩ dj))) := by
  have hboundary := childHMatches_of_hMatches
    (R i j) (R ⟨i.val + 1, hi⟩ j) (hR.1 i j hi)
  have hcases : dj.val = 0 ∨ dj.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hdj : dj = ⟨0, by decide⟩ := Fin.ext hzero
    simpa [hdj, ChildHMatches, childRectangle] using hboundary.1
  · have hdj : dj = ⟨1, by decide⟩ := Fin.ext hone
    simpa [hdj, ChildHMatches, childRectangle] using hboundary.2

private theorem expand_vMatches_boundary {w h : Nat}
    {R : IndexRectangle w h} (hR : R.Compatible)
    (i : Fin w) (j : Fin h) (hj : j.val + 1 < h) (di : Fin 2) :
    WangTile.VMatches
      (tile (components (childBlock (R i j) di ⟨1, by decide⟩)))
      (tile (components
        (childBlock (R i ⟨j.val + 1, hj⟩) di ⟨0, by decide⟩))) := by
  have hboundary := childVMatches_of_vMatches
    (R i j) (R i ⟨j.val + 1, hj⟩) (hR.2 i j hj)
  have hcases : di.val = 0 ∨ di.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hdi : di = ⟨0, by decide⟩ := Fin.ext hzero
    simpa [hdi, ChildVMatches, childRectangle] using hboundary.1
  · have hdi : di = ⟨1, by decide⟩ := Fin.ext hone
    simpa [hdi, ChildVMatches, childRectangle] using hboundary.2

theorem expand_compatible {w h : Nat} {R : IndexRectangle w h}
    (hR : R.Compatible) : R.expand.Compatible := by
  constructor
  · intro i j hi
    rcases Figure16.BlockGrid.doubledOffset_eq_zero_or_one i with hzero | hone
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_zero i hi hzero with
        ⟨hblock, hoff⟩
      have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨0, by decide⟩ :=
        Fin.ext hzero
      simpa [expand, hblock, hoff, hoff_i] using
        expand_hMatches_within R
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset j)
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_one i hi hone with
        ⟨hb, hblock, hoff⟩
      have hoff_i : Figure16.BlockGrid.doubledOffset i = ⟨1, by decide⟩ :=
        Fin.ext hone
      simpa [expand, hblock, hoff, hoff_i] using
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
      simpa [expand, hblock, hoff, hoff_j] using
        expand_vMatches_within R
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j)
          (Figure16.BlockGrid.doubledOffset i)
    · rcases Figure16.BlockGrid.doubled_succ_of_offset_one j hj hone with
        ⟨hb, hblock, hoff⟩
      have hoff_j : Figure16.BlockGrid.doubledOffset j = ⟨1, by decide⟩ :=
        Fin.ext hone
      simpa [expand, hblock, hoff, hoff_j] using
        expand_vMatches_boundary hR
          (Figure16.BlockGrid.doubledBlockCoord i)
          (Figure16.BlockGrid.doubledBlockCoord j) hb
          (Figure16.BlockGrid.doubledOffset i)

end IndexRectangle

/-- Side length after `level` substitution steps. -/
def substitutionSide : Nat → Nat
  | 0 => 1
  | level + 1 => 2 * substitutionSide level

@[simp]
theorem substitutionSide_zero : substitutionSide 0 = 1 := rfl

@[simp]
theorem substitutionSide_succ (level : Nat) :
    substitutionSide (level + 1) = 2 * substitutionSide level := rfl

theorem substitutionSide_pos (level : Nat) : 0 < substitutionSide level := by
  induction level with
  | zero => simp
  | succ level ih => simp [substitutionSide, ih]

theorem level_le_substitutionSide (level : Nat) :
    level ≤ substitutionSide level := by
  induction level with
  | zero => simp
  | succ level ih =>
      rw [substitutionSide_succ]
      have hpos := substitutionSide_pos level
      omega

/-- Iterated corrected substitution square, starting from tile zero. -/
def substitutionSquare :
    (level : Nat) → IndexRectangle (substitutionSide level) (substitutionSide level)
  | 0 => fun _ _ => ⟨0, by decide⟩
  | level + 1 => (substitutionSquare level).expand

theorem substitutionSquare_compatible (level : Nat) :
    (substitutionSquare level).Compatible := by
  induction level with
  | zero =>
      simp [IndexRectangle.Compatible, substitutionSquare, substitutionSide]
  | succ level ih =>
      exact IndexRectangle.expand_compatible ih

theorem tileableSquare_substitutionSide (level : Nat) :
    TileableSquare tileSet (substitutionSide level) :=
  ⟨(substitutionSquare level).tileRectangle,
    IndexRectangle.tileRectangle_valid (substitutionSquare_compatible level)⟩

theorem all_tileableSquares : ∀ n : Nat, TileableSquare tileSet n := by
  intro n
  exact tileableSquare_crop (level_le_substitutionSide n)
    (tileableSquare_substitutionSide n)

/-- The corrected Ollinger Wang tileset tiles the plane. -/
theorem tilesPlane_tileSet : TilesPlane tileSet :=
  (tilesPlane_iff_all_tileableSquares tileSet).2 all_tileableSquares

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
