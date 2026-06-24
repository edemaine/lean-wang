/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
Two-by-two Wang-tile subdivision.

Figure 18 of the Ollinger/Robinson scaffold uses quarters of scaffold tiles as
the payload-carrying sites.  This module records a generic subdivision of a
Wang tile into four quadrant tiles, so quarter-level scaffold data can later be
turned back into an ordinary Wang tileset.
-/

namespace LeanWang

/-- The four quadrants of a subdivided Wang tile. -/
inductive Quadrant where
  | southwest
  | southeast
  | northwest
  | northeast
deriving DecidableEq, Repr

namespace Quadrant

/-- Horizontal coordinate of a quadrant: `false` for west, `true` for east. -/
def xBit : Quadrant → Bool
  | southwest => false
  | southeast => true
  | northwest => false
  | northeast => true

/-- Vertical coordinate of a quadrant: `false` for south, `true` for north. -/
def yBit : Quadrant → Bool
  | southwest => false
  | southeast => false
  | northwest => true
  | northeast => true

def toBits (q : Quadrant) : Bool × Bool :=
  (q.xBit, q.yBit)

def ofBits : Bool × Bool → Quadrant
  | (false, false) => southwest
  | (true, false) => southeast
  | (false, true) => northwest
  | (true, true) => northeast

def equivBits : Quadrant ≃ Bool × Bool where
  toFun := toBits
  invFun := ofBits
  left_inv := by
    intro q
    cases q <;> rfl
  right_inv := by
    intro bits
    rcases bits with ⟨x, y⟩
    cases x <;> cases y <;> rfl

instance instPrimcodable : Primcodable Quadrant :=
  Primcodable.ofEquiv (Bool × Bool) equivBits

def all : List Quadrant :=
  [southwest, southeast, northwest, northeast]

@[simp]
theorem all_length : all.length = 4 := by
  decide

theorem mem_all (q : Quadrant) : q ∈ all := by
  cases q <;> decide

end Quadrant

namespace TileSubdivision

private def bitCode (b : Bool) : Nat :=
  if b then 1 else 0

private def tileCode (t : WangTile) : Nat :=
  Nat.pair t.n (Nat.pair t.s (Nat.pair t.e t.w))

/-- Horizontal macro-edge colors are split by west/east half. -/
def horizontalEdgeColor (x : Bool) (color : Nat) : Nat :=
  Nat.pair 0 (Nat.pair (bitCode x) color)

/-- Vertical macro-edge colors are split by south/north half. -/
def verticalEdgeColor (y : Bool) (color : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (bitCode y) color)

/-- Internal vertical seam color between west and east quadrants. -/
def internalVerticalColor (t : WangTile) (y : Bool) : Nat :=
  Nat.pair 2 (Nat.pair (bitCode y) (tileCode t))

/-- Internal horizontal seam color between south and north quadrants. -/
def internalHorizontalColor (t : WangTile) (x : Bool) : Nat :=
  Nat.pair 3 (Nat.pair (bitCode x) (tileCode t))

/-- The quadrant tile of `t` in the 2x2 subdivision. -/
def subdivideTileAt (t : WangTile) : Quadrant → WangTile
  | .southwest =>
      { n := internalHorizontalColor t false
        s := horizontalEdgeColor false t.s
        e := internalVerticalColor t false
        w := verticalEdgeColor false t.w }
  | .southeast =>
      { n := internalHorizontalColor t true
        s := horizontalEdgeColor true t.s
        e := verticalEdgeColor false t.e
        w := internalVerticalColor t false }
  | .northwest =>
      { n := horizontalEdgeColor false t.n
        s := internalHorizontalColor t false
        e := internalVerticalColor t true
        w := verticalEdgeColor true t.w }
  | .northeast =>
      { n := horizontalEdgeColor true t.n
        s := internalHorizontalColor t true
        e := verticalEdgeColor true t.e
        w := internalVerticalColor t true }

/-- The four quadrant tiles of one Wang tile. -/
def subdivideTile (t : WangTile) : TileSet :=
  Quadrant.all.map (subdivideTileAt t)

/-- Subdivide every tile of a finite tileset into four quadrant tiles. -/
def subdivideTileSet (T : TileSet) : TileSet :=
  T.flatMap subdivideTile

@[simp]
theorem subdivideTile_length (t : WangTile) :
    (subdivideTile t).length = 4 := by
  simp [subdivideTile]

@[simp]
theorem subdivideTileSet_nil :
    subdivideTileSet [] = [] :=
  rfl

@[simp]
theorem subdivideTileSet_cons (t : WangTile) (T : TileSet) :
    subdivideTileSet (t :: T) = subdivideTile t ++ subdivideTileSet T :=
  rfl

theorem hMatches_southwest_southeast (t : WangTile) :
    WangTile.HMatches
      (subdivideTileAt t .southwest) (subdivideTileAt t .southeast) :=
  rfl

theorem hMatches_northwest_northeast (t : WangTile) :
    WangTile.HMatches
      (subdivideTileAt t .northwest) (subdivideTileAt t .northeast) :=
  rfl

theorem vMatches_southwest_northwest (t : WangTile) :
    WangTile.VMatches
      (subdivideTileAt t .southwest) (subdivideTileAt t .northwest) :=
  rfl

theorem vMatches_southeast_northeast (t : WangTile) :
    WangTile.VMatches
      (subdivideTileAt t .southeast) (subdivideTileAt t .northeast) :=
  rfl

theorem hMatches_northeast_northwest_of_hMatches {left right : WangTile}
    (h : WangTile.HMatches left right) :
    WangTile.HMatches
      (subdivideTileAt left .northeast) (subdivideTileAt right .northwest) := by
  simpa [WangTile.HMatches, subdivideTileAt, verticalEdgeColor] using h

theorem hMatches_southeast_southwest_of_hMatches {left right : WangTile}
    (h : WangTile.HMatches left right) :
    WangTile.HMatches
      (subdivideTileAt left .southeast) (subdivideTileAt right .southwest) := by
  simpa [WangTile.HMatches, subdivideTileAt, verticalEdgeColor] using h

theorem vMatches_northwest_southwest_of_vMatches {lower upper : WangTile}
    (h : WangTile.VMatches lower upper) :
    WangTile.VMatches
      (subdivideTileAt lower .northwest) (subdivideTileAt upper .southwest) := by
  simpa [WangTile.VMatches, subdivideTileAt, horizontalEdgeColor] using h

theorem vMatches_northeast_southeast_of_vMatches {lower upper : WangTile}
    (h : WangTile.VMatches lower upper) :
    WangTile.VMatches
      (subdivideTileAt lower .northeast) (subdivideTileAt upper .southeast) := by
  simpa [WangTile.VMatches, subdivideTileAt, horizontalEdgeColor] using h

end TileSubdivision

end LeanWang
