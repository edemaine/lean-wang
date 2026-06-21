/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
This file contains the concrete Wang-tile objects used by the project.

The representation is deliberately computability-friendly: colors are natural
numbers and a finite tileset is a list of tiles.
-/

namespace LeanWang

/-- A Wang tile, represented by the colors on its north, south, east, and west edges. -/
structure WangTile where
  n : Nat
  s : Nat
  e : Nat
  w : Nat
deriving DecidableEq, Repr

/-- A finite Wang tileset. Duplicates are harmless and ignored by membership predicates. -/
abbrev TileSet := List WangTile

/-- View a Wang tile as the quadruple of its edge colors. -/
def WangTile.toTuple (t : WangTile) : Nat × Nat × Nat × Nat :=
  (t.n, t.s, t.e, t.w)

/-- Build a Wang tile from the quadruple of its edge colors. -/
def WangTile.ofTuple (p : Nat × Nat × Nat × Nat) : WangTile where
  n := p.1
  s := p.2.1
  e := p.2.2.1
  w := p.2.2.2

/-- Wang tiles are encoded by their four natural-number edge colors. -/
def WangTile.equivTuple : WangTile ≃ Nat × Nat × Nat × Nat where
  toFun := WangTile.toTuple
  invFun := WangTile.ofTuple
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro p
    rcases p with ⟨n, s, e, w⟩
    rfl

instance instPrimcodableWangTile : Primcodable WangTile :=
  Primcodable.ofEquiv (Nat × Nat × Nat × Nat) WangTile.equivTuple

/-- Encode a finite Wang tileset as a natural number. -/
def encodeTileSet (T : TileSet) : Nat :=
  Encodable.encode T

/--
Decode a natural number as a finite Wang tileset. Invalid codes decode to the
empty tileset; every actual tileset has a canonical code via `encodeTileSet`.
-/
def decodeTileSet (n : Nat) : TileSet :=
  (Encodable.decode (α := TileSet) n).getD []

@[simp]
theorem decodeTileSet_encodeTileSet (T : TileSet) :
    decodeTileSet (encodeTileSet T) = T := by
  simp [decodeTileSet, encodeTileSet]

theorem decodeTileSet_surjective : Function.Surjective decodeTileSet := by
  intro T
  exact ⟨encodeTileSet T, decodeTileSet_encodeTileSet T⟩

theorem encodeTileSet_computable : Computable encodeTileSet := by
  change Computable fun T : TileSet => Encodable.encode T
  exact Computable.encode

theorem decodeTileSet_computable : Computable decodeTileSet := by
  change Computable fun n : Nat => (Encodable.decode (α := TileSet) n).getD []
  exact Computable.option_getD Computable.decode (Computable.const ([] : TileSet))

/-- The type of tiles belonging to a fixed tileset. -/
abbrev TileIn (T : TileSet) :=
  { t : WangTile // t ∈ T }

namespace WangTile

/-- Horizontal compatibility: `left` may be placed immediately west of `right`. -/
def HMatches (left right : WangTile) : Prop :=
  left.e = right.w

/-- Vertical compatibility: `lower` may be placed immediately south of `upper`. -/
def VMatches (lower upper : WangTile) : Prop :=
  lower.n = upper.s

instance (left right : WangTile) : Decidable (HMatches left right) := by
  unfold HMatches
  infer_instance

instance (lower upper : WangTile) : Decidable (VMatches lower upper) := by
  unfold VMatches
  infer_instance

end WangTile

/-- A complete tiling of the integer plane by a finite tileset. -/
def ValidPlaneTiling (T : TileSet) (x : Int × Int → TileIn T) : Prop :=
  (∀ p : Int × Int, WangTile.HMatches (x p).1 (x (p.1 + 1, p.2)).1) ∧
    (∀ p : Int × Int, WangTile.VMatches (x p).1 (x (p.1, p.2 + 1)).1)

/-- A tileset tiles the whole plane. -/
def TilesPlane (T : TileSet) : Prop :=
  ∃ x : Int × Int → TileIn T, ValidPlaneTiling T x

/-- The centered integer box `[-r, r] × [-r, r]`. -/
def InBox (r : Nat) (p : Int × Int) : Prop :=
  -(r : Int) ≤ p.1 ∧ p.1 ≤ (r : Int) ∧
    -(r : Int) ≤ p.2 ∧ p.2 ≤ (r : Int)

/-- Coordinates in the centered integer box `[-r, r] × [-r, r]`. -/
abbrev Box (r : Nat) :=
  { p : Int × Int // InBox r p }

/-- A finite centered box assignment. -/
abbrev BoxPattern (T : TileSet) (r : Nat) :=
  Box r → TileIn T

/-- Validity of a centered finite box tiling. -/
def ValidBoxTiling (T : TileSet) (r : Nat) (x : BoxPattern T r) : Prop :=
  (∀ p : Box r, ∀ hp : InBox r (p.1.1 + 1, p.1.2),
    WangTile.HMatches (x p).1 (x ⟨(p.1.1 + 1, p.1.2), hp⟩).1) ∧
    (∀ p : Box r, ∀ hp : InBox r (p.1.1, p.1.2 + 1),
      WangTile.VMatches (x p).1 (x ⟨(p.1.1, p.1.2 + 1), hp⟩).1)

/-- A tileset tiles the centered integer box `[-r, r] × [-r, r]`. -/
def TileableBox (T : TileSet) (r : Nat) : Prop :=
  ∃ x : BoxPattern T r, ValidBoxTiling T r x

/-- A complete tiling of the first quadrant `Nat × Nat`. -/
def ValidQuarterTiling (T : TileSet) (x : Nat × Nat → TileIn T) : Prop :=
  (∀ p : Nat × Nat, WangTile.HMatches (x p).1 (x (p.1 + 1, p.2)).1) ∧
    (∀ p : Nat × Nat, WangTile.VMatches (x p).1 (x (p.1, p.2 + 1)).1)

/-- A tileset tiles the first quadrant with a prescribed tile at the origin. -/
def TilesQuarterWithSeed (T : TileSet) (seed : WangTile) : Prop :=
  ∃ x : Nat × Nat → TileIn T, ValidQuarterTiling T x ∧ (x (0, 0)).1 = seed

/-- A finite rectangle assignment with width `w` and height `h`. -/
abbrev Rectangle (w h : Nat) :=
  Fin w → Fin h → WangTile

/-- Row-major indexing of a finite rectangle stored as a flat list. -/
def rectIndex (w : Nat) (i j : Nat) : Nat :=
  j * w + i

/-- Read cell `(i, j)` from a row-major rectangle pattern. -/
def getRectCell? (xs : List WangTile) (w i j : Nat) : Option WangTile :=
  xs[rectIndex w i j]?

/-- All words of length `n` over a finite alphabet. -/
def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => List.flatMap (fun tail =>
      alphabet.map fun head => head :: tail
    ) (words alphabet n)

/--
Executable checker for a row-major `w × h` rectangle pattern.

The pattern must have exactly `w * h` cells, every cell must belong to `T`, and
all east/north adjacencies inside the rectangle must match.
-/
def validRectListBool (T : TileSet) (w h : Nat) (xs : List WangTile) : Bool :=
  xs.length == w * h &&
    (List.range w).all fun i =>
      (List.range h).all fun j =>
        match getRectCell? xs w i j with
        | none => false
        | some tile =>
            decide (tile ∈ T) &&
              (if _hi : i + 1 < w then
                match getRectCell? xs w (i + 1) j with
                | none => false
                | some east => decide (WangTile.HMatches tile east)
              else true) &&
                (if _hj : j + 1 < h then
                  match getRectCell? xs w i (j + 1) with
                  | none => false
                  | some north => decide (WangTile.VMatches tile north)
                else true)

/-- Exhaustive finite search for a valid `w × h` rectangle over `T`. -/
def tileableRectangleBool (T : TileSet) (w h : Nat) : Bool :=
  (words T (w * h)).any fun xs => validRectListBool T w h xs

/-- Exhaustive finite search for a valid `n × n` square over `T`. -/
def tileableSquareBool (T : TileSet) (n : Nat) : Bool :=
  tileableRectangleBool T n n

/-- The one-color tile used for executable sanity checks. -/
def monochromeTile : WangTile where
  n := 0
  s := 0
  e := 0
  w := 0

example : tileableSquareBool [monochromeTile] 2 = true := by
  decide

/-- Validity of a finite rectangular Wang tiling. -/
def ValidRectangle (T : TileSet) {w h : Nat} (x : Rectangle w h) : Prop :=
  (∀ i : Fin w, ∀ j : Fin h, x i j ∈ T) ∧
    (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
      WangTile.HMatches (x i j) (x ⟨i.val + 1, hi⟩ j)) ∧
      (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
        WangTile.VMatches (x i j) (x i ⟨j.val + 1, hj⟩))

instance decidableValidRectangle (T : TileSet) {w h : Nat} (x : Rectangle w h) :
    Decidable (ValidRectangle T x) := by
  unfold ValidRectangle
  infer_instance

/-- Boolean checker for finite rectangular Wang tilings. -/
def validRectangleBool (T : TileSet) {w h : Nat} (x : Rectangle w h) : Bool :=
  decide (ValidRectangle T x)

@[simp]
theorem validRectangleBool_eq_true (T : TileSet) {w h : Nat} (x : Rectangle w h) :
    validRectangleBool T x = true ↔ ValidRectangle T x := by
  simp [validRectangleBool]

/-- A tileset tiles a finite `w × h` rectangle. -/
def TileableRectangle (T : TileSet) (w h : Nat) : Prop :=
  ∃ x : Rectangle w h, ValidRectangle T x

/-- A tileset tiles a finite `n × n` square. -/
def TileableSquare (T : TileSet) (n : Nat) : Prop :=
  TileableRectangle T n n

/--
A tileset tiles a nonempty `n × n` square with a prescribed tile in the lower-left
corner. The `0 < n` witness avoids manufacturing a corner in the empty square.
-/
def TileableFixedCornerSquare (T : TileSet) (seed : WangTile) (n : Nat) : Prop :=
  ∃ hn : 0 < n, ∃ x : Rectangle n n,
    ValidRectangle T x ∧ x ⟨0, hn⟩ ⟨0, hn⟩ = seed

/-- If a plane tiling exists, every finite square is tileable by restriction. -/
theorem tileableSquare_of_tilesPlane {T : TileSet} :
    TilesPlane T → ∀ n : Nat, TileableSquare T n := by
  intro hT n
  rcases hT with ⟨x, hxH, hxV⟩
  refine ⟨fun i j => (x (Int.ofNat i.val, Int.ofNat j.val)).1, ?_⟩
  constructor
  · intro i j
    exact (x (Int.ofNat i.val, Int.ofNat j.val)).2
  constructor
  · intro i j hi
    exact hxH (Int.ofNat i.val, Int.ofNat j.val)
  · intro i j hj
    exact hxV (Int.ofNat i.val, Int.ofNat j.val)

/-- If a plane tiling exists, every centered finite box is tileable by restriction. -/
theorem tileableBox_of_tilesPlane {T : TileSet} :
    TilesPlane T → ∀ r : Nat, TileableBox T r := by
  intro hT r
  rcases hT with ⟨x, hxH, hxV⟩
  refine ⟨fun p => x p.1, ?_⟩
  constructor
  · intro p hp
    exact hxH p.1
  · intro p hp
    exact hxV p.1

/-- A seeded quarter-plane tiling restricts to every nonempty seeded square. -/
theorem fixedCornerSquare_of_tilesQuarterWithSeed {T : TileSet} {seed : WangTile} :
    TilesQuarterWithSeed T seed →
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n := by
  intro hT n hn
  rcases hT with ⟨x, hx, hseed⟩
  rcases hx with ⟨hxH, hxV⟩
  refine ⟨hn, fun i j => (x (i.val, j.val)).1, ?_, ?_⟩
  · constructor
    · intro i j
      exact (x (i.val, j.val)).2
    constructor
    · intro i j hi
      exact hxH (i.val, j.val)
    · intro i j hj
      exact hxV (i.val, j.val)
  · exact hseed

/--
Seeded quarter-plane compactness. The forward direction is
`fixedCornerSquare_of_tilesQuarterWithSeed`; the reverse direction is another
diagonal compactness argument.
-/
theorem tilesQuarterWithSeed_iff_all_fixedCornerSquares (T : TileSet) (seed : WangTile) :
    TilesQuarterWithSeed T seed ↔
      ∀ n : Nat, 0 < n → TileableFixedCornerSquare T seed n := by
  constructor
  · exact fixedCornerSquare_of_tilesQuarterWithSeed
  · intro _h
    sorry

end LeanWang
