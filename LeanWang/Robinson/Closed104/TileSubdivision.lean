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

theorem toBits_primrec : Primrec toBits := by
  simpa [equivBits] using
    (Primrec.of_equiv (e := equivBits) : Primrec equivBits)

theorem xBit_primrec : Primrec xBit :=
  Primrec.fst.comp toBits_primrec

theorem yBit_primrec : Primrec yBit :=
  Primrec.snd.comp toBits_primrec

def all : List Quadrant :=
  [southwest, southeast, northwest, northeast]

@[simp]
theorem all_length : all.length = 4 := by
  decide

theorem mem_all (q : Quadrant) : q ∈ all := by
  cases q <;> decide

instance : Fintype Quadrant := Fintype.ofList all mem_all

end Quadrant

namespace TileSubdivision

private def bitCode (b : Bool) : Nat :=
  if b then 1 else 0

private def tileCode (t : WangTile) : Nat :=
  Nat.pair t.n (Nat.pair t.s (Nat.pair t.e t.w))

private theorem bitCode_primrec : Primrec (fun b : Bool => bitCode b) := by
  exact (Primrec.cond (α := Bool) (σ := Nat) Primrec.id
    (Primrec.const (α := Bool) (1 : Nat))
    (Primrec.const (α := Bool) (0 : Nat))).of_eq fun b => by
      cases b <;> rfl

private theorem tileCode_primrec : Primrec (fun t : WangTile => tileCode t) := by
  unfold tileCode
  exact Primrec₂.natPair.comp WangTile.n_primrec
    (Primrec₂.natPair.comp WangTile.s_primrec
      (Primrec₂.natPair.comp WangTile.e_primrec WangTile.w_primrec))

set_option linter.flexible false in
private theorem tileCode_injective : Function.Injective tileCode := by
  intro t u h
  cases t
  cases u
  simp [tileCode, Nat.pair_eq_pair] at h ⊢
  exact h

/-- Horizontal macro-edge colors are split by west/east half. -/
def horizontalEdgeColor (x : Bool) (color : Nat) : Nat :=
  Nat.pair 0 (Nat.pair (bitCode x) color)

theorem horizontalEdgeColor_primrec :
    Primrec (fun p : Bool × Nat => horizontalEdgeColor p.1 p.2) := by
  unfold horizontalEdgeColor
  exact Primrec₂.natPair.comp (Primrec.const (α := Bool × Nat) (0 : Nat))
    (Primrec₂.natPair.comp (bitCode_primrec.comp Primrec.fst) Primrec.snd)

theorem horizontalEdgeColor_primrec₂ : Primrec₂ horizontalEdgeColor :=
  Primrec₂.mk horizontalEdgeColor_primrec

/-- Vertical macro-edge colors are split by south/north half. -/
def verticalEdgeColor (y : Bool) (color : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (bitCode y) color)

theorem verticalEdgeColor_primrec :
    Primrec (fun p : Bool × Nat => verticalEdgeColor p.1 p.2) := by
  unfold verticalEdgeColor
  exact Primrec₂.natPair.comp (Primrec.const (α := Bool × Nat) (1 : Nat))
    (Primrec₂.natPair.comp (bitCode_primrec.comp Primrec.fst) Primrec.snd)

theorem verticalEdgeColor_primrec₂ : Primrec₂ verticalEdgeColor :=
  Primrec₂.mk verticalEdgeColor_primrec

/-- Internal vertical seam color between west and east quadrants. -/
def internalVerticalColor (t : WangTile) (y : Bool) : Nat :=
  Nat.pair 2 (Nat.pair (bitCode y) (tileCode t))

theorem internalVerticalColor_primrec :
    Primrec (fun p : WangTile × Bool => internalVerticalColor p.1 p.2) := by
  unfold internalVerticalColor
  exact Primrec₂.natPair.comp (Primrec.const (α := WangTile × Bool) (2 : Nat))
    (Primrec₂.natPair.comp (bitCode_primrec.comp Primrec.snd)
      (tileCode_primrec.comp Primrec.fst))

theorem internalVerticalColor_primrec₂ : Primrec₂ internalVerticalColor :=
  Primrec₂.mk internalVerticalColor_primrec

/-- Internal horizontal seam color between south and north quadrants. -/
def internalHorizontalColor (t : WangTile) (x : Bool) : Nat :=
  Nat.pair 3 (Nat.pair (bitCode x) (tileCode t))

theorem internalHorizontalColor_primrec :
    Primrec (fun p : WangTile × Bool => internalHorizontalColor p.1 p.2) := by
  unfold internalHorizontalColor
  exact Primrec₂.natPair.comp (Primrec.const (α := WangTile × Bool) (3 : Nat))
    (Primrec₂.natPair.comp (bitCode_primrec.comp Primrec.snd)
      (tileCode_primrec.comp Primrec.fst))

theorem internalHorizontalColor_primrec₂ : Primrec₂ internalHorizontalColor :=
  Primrec₂.mk internalHorizontalColor_primrec

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

theorem subdivideTileAt_primrec :
    Primrec (fun p : WangTile × Quadrant => subdivideTileAt p.1 p.2) := by
  let t : WangTile × Quadrant → WangTile := fun p => p.1
  let x : WangTile × Quadrant → Bool := fun p => p.2.xBit
  let y : WangTile × Quadrant → Bool := fun p => p.2.yBit
  let nFn : WangTile × Quadrant → Nat := fun p =>
    bif y p then horizontalEdgeColor (x p) (t p).n
    else internalHorizontalColor (t p) (x p)
  let sFn : WangTile × Quadrant → Nat := fun p =>
    bif y p then internalHorizontalColor (t p) (x p)
    else horizontalEdgeColor (x p) (t p).s
  let eFn : WangTile × Quadrant → Nat := fun p =>
    bif x p then verticalEdgeColor (y p) (t p).e
    else internalVerticalColor (t p) (y p)
  let wFn : WangTile × Quadrant → Nat := fun p =>
    bif x p then internalVerticalColor (t p) (y p)
    else verticalEdgeColor (y p) (t p).w
  have ht : Primrec t := Primrec.fst
  have hx : Primrec x := Quadrant.xBit_primrec.comp Primrec.snd
  have hy : Primrec y := Quadrant.yBit_primrec.comp Primrec.snd
  have hnH : Primrec
      (fun p : WangTile × Quadrant => horizontalEdgeColor (x p) (t p).n) :=
    horizontalEdgeColor_primrec₂.comp hx (WangTile.n_primrec.comp ht)
  have hHorizontalInternal : Primrec
      (fun p : WangTile × Quadrant => internalHorizontalColor (t p) (x p)) :=
    internalHorizontalColor_primrec₂.comp ht hx
  have hn : Primrec nFn := Primrec.cond hy hnH hHorizontalInternal
  have hsH : Primrec
      (fun p : WangTile × Quadrant => horizontalEdgeColor (x p) (t p).s) :=
    horizontalEdgeColor_primrec₂.comp hx (WangTile.s_primrec.comp ht)
  have hs : Primrec sFn := Primrec.cond hy hHorizontalInternal hsH
  have heV : Primrec
      (fun p : WangTile × Quadrant => verticalEdgeColor (y p) (t p).e) :=
    verticalEdgeColor_primrec₂.comp hy (WangTile.e_primrec.comp ht)
  have hVerticalInternal : Primrec
      (fun p : WangTile × Quadrant => internalVerticalColor (t p) (y p)) :=
    internalVerticalColor_primrec₂.comp ht hy
  have he : Primrec eFn := Primrec.cond hx heV hVerticalInternal
  have hwV : Primrec
      (fun p : WangTile × Quadrant => verticalEdgeColor (y p) (t p).w) :=
    verticalEdgeColor_primrec₂.comp hy (WangTile.w_primrec.comp ht)
  have hw : Primrec wFn := Primrec.cond hx hVerticalInternal hwV
  have htuple : Primrec
      (fun p : WangTile × Quadrant => (nFn p, sFn p, eFn p, wFn p)) :=
    Primrec.pair hn (Primrec.pair hs (Primrec.pair he hw))
  have htile : Primrec
      (fun p : WangTile × Quadrant =>
        WangTile.ofTuple (nFn p, sFn p, eFn p, wFn p)) :=
    WangTile.ofTuple_primrec.comp htuple
  exact htile.of_eq fun p => by
    rcases p with ⟨tile, q⟩
    cases q <;> rfl

theorem subdivideTileAt_primrec₂ : Primrec₂ subdivideTileAt :=
  Primrec₂.mk subdivideTileAt_primrec

theorem hMatches_west_east (t : WangTile) (y : Bool) :
    WangTile.HMatches
      (subdivideTileAt t (Quadrant.ofBits (false, y)))
      (subdivideTileAt t (Quadrant.ofBits (true, y))) := by
  cases y <;> rfl

theorem vMatches_south_north (t : WangTile) (x : Bool) :
    WangTile.VMatches
      (subdivideTileAt t (Quadrant.ofBits (x, false)))
      (subdivideTileAt t (Quadrant.ofBits (x, true))) := by
  cases x <;> rfl

theorem hMatches_east_west_of_hMatches {left right : WangTile} (y : Bool)
    (h : WangTile.HMatches left right) :
    WangTile.HMatches
      (subdivideTileAt left (Quadrant.ofBits (true, y)))
      (subdivideTileAt right (Quadrant.ofBits (false, y))) := by
  cases y <;>
    simpa [WangTile.HMatches, subdivideTileAt, verticalEdgeColor,
      Quadrant.ofBits] using h

theorem vMatches_north_south_of_vMatches {lower upper : WangTile} (x : Bool)
    (h : WangTile.VMatches lower upper) :
    WangTile.VMatches
      (subdivideTileAt lower (Quadrant.ofBits (x, true)))
      (subdivideTileAt upper (Quadrant.ofBits (x, false))) := by
  cases x <;>
    simpa [WangTile.VMatches, subdivideTileAt, horizontalEdgeColor,
      Quadrant.ofBits] using h

set_option linter.flexible false in
theorem hMatches_subdivideTileAt_iff
    (left right : WangTile) (q r : Quadrant) :
    WangTile.HMatches (subdivideTileAt left q) (subdivideTileAt right r) ↔
      match q, r with
      | .southwest, .southeast => left = right
      | .northwest, .northeast => left = right
      | .southeast, .southwest => WangTile.HMatches left right
      | .northeast, .northwest => WangTile.HMatches left right
      | _, _ => False := by
  cases q <;> cases r <;> cases left <;> cases right <;>
    simp [WangTile.HMatches, subdivideTileAt, horizontalEdgeColor,
      verticalEdgeColor, internalVerticalColor, internalHorizontalColor,
      bitCode, tileCode, Nat.pair_eq_pair]

set_option linter.flexible false in
theorem vMatches_subdivideTileAt_iff
    (lower upper : WangTile) (q r : Quadrant) :
    WangTile.VMatches (subdivideTileAt lower q) (subdivideTileAt upper r) ↔
      match q, r with
      | .southwest, .northwest => lower = upper
      | .southeast, .northeast => lower = upper
      | .northwest, .southwest => WangTile.VMatches lower upper
      | .northeast, .southeast => WangTile.VMatches lower upper
      | _, _ => False := by
  cases q <;> cases r <;> cases lower <;> cases upper <;>
    simp [WangTile.VMatches, subdivideTileAt, horizontalEdgeColor,
      verticalEdgeColor, internalVerticalColor, internalHorizontalColor,
      bitCode, tileCode, Nat.pair_eq_pair]

end TileSubdivision

end LeanWang
