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
  have hnI : Primrec
      (fun p : WangTile × Quadrant => internalHorizontalColor (t p) (x p)) :=
    internalHorizontalColor_primrec₂.comp ht hx
  have hn : Primrec nFn := Primrec.cond hy hnH hnI
  have hsI : Primrec
      (fun p : WangTile × Quadrant => internalHorizontalColor (t p) (x p)) :=
    internalHorizontalColor_primrec₂.comp ht hx
  have hsH : Primrec
      (fun p : WangTile × Quadrant => horizontalEdgeColor (x p) (t p).s) :=
    horizontalEdgeColor_primrec₂.comp hx (WangTile.s_primrec.comp ht)
  have hs : Primrec sFn := Primrec.cond hy hsI hsH
  have heV : Primrec
      (fun p : WangTile × Quadrant => verticalEdgeColor (y p) (t p).e) :=
    verticalEdgeColor_primrec₂.comp hy (WangTile.e_primrec.comp ht)
  have heI : Primrec
      (fun p : WangTile × Quadrant => internalVerticalColor (t p) (y p)) :=
    internalVerticalColor_primrec₂.comp ht hy
  have he : Primrec eFn := Primrec.cond hx heV heI
  have hwI : Primrec
      (fun p : WangTile × Quadrant => internalVerticalColor (t p) (y p)) :=
    internalVerticalColor_primrec₂.comp ht hy
  have hwV : Primrec
      (fun p : WangTile × Quadrant => verticalEdgeColor (y p) (t p).w) :=
    verticalEdgeColor_primrec₂.comp hy (WangTile.w_primrec.comp ht)
  have hw : Primrec wFn := Primrec.cond hx hwI hwV
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

theorem subdivideTileAt_mem_subdivideTileSet {T : TileSet} {t : WangTile}
    (ht : t ∈ T) (q : Quadrant) :
    subdivideTileAt t q ∈ subdivideTileSet T := by
  rw [subdivideTileSet, List.mem_flatMap]
  refine ⟨t, ht, ?_⟩
  rw [subdivideTile]
  exact List.mem_map.2 ⟨q, Quadrant.mem_all q, rfl⟩

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

set_option linter.flexible false in
theorem subdivideTileAt_pair_injective :
    Function.Injective (fun p : WangTile × Quadrant => subdivideTileAt p.1 p.2) := by
  intro p q h
  rcases p with ⟨t, qt⟩
  rcases q with ⟨u, qu⟩
  cases qt <;> cases qu <;> cases t <;> cases u <;>
    simp [subdivideTileAt, horizontalEdgeColor, verticalEdgeColor,
      internalVerticalColor, internalHorizontalColor, bitCode, tileCode,
      Nat.pair_eq_pair] at h ⊢
  all_goals
    try exact h
    try exact h.1
    try exact h.2.1

theorem subdivideTileAt_eq_iff (t u : WangTile) (q r : Quadrant) :
    subdivideTileAt t q = subdivideTileAt u r ↔ t = u ∧ q = r := by
  constructor
  · intro h
    have hp : (t, q) = (u, r) :=
      subdivideTileAt_pair_injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mem_of_subdivideTileAt_mem_subdivideTileSet {T : TileSet}
    {t : WangTile} {q : Quadrant}
    (h : subdivideTileAt t q ∈ subdivideTileSet T) :
    t ∈ T := by
  rw [subdivideTileSet, List.mem_flatMap] at h
  rcases h with ⟨u, hu, hsub⟩
  rw [subdivideTile] at hsub
  rcases List.mem_map.1 hsub with ⟨r, _hr, hrt⟩
  have hpair : (u, r) = (t, q) :=
    subdivideTileAt_pair_injective hrt
  have hut : u = t := congrArg Prod.fst hpair
  exact hut ▸ hu

theorem subdivideTile_nodup (t : WangTile) :
    (subdivideTile t).Nodup := by
  unfold subdivideTile
  apply List.Nodup.map
  · intro q r h
    exact (subdivideTileAt_eq_iff t t q r).1 h |>.2
  · decide

theorem subdivideTile_disjoint_subdivideTileSet_of_not_mem
    {t : WangTile} {T : TileSet} (hnot : t ∉ T) :
    (subdivideTile t).Disjoint (subdivideTileSet T) := by
  intro x hx hy
  rw [subdivideTile] at hx
  rcases List.mem_map.1 hx with ⟨q, _hq, hxq⟩
  rw [subdivideTileSet, List.mem_flatMap] at hy
  rcases hy with ⟨u, hu, hyu⟩
  rw [subdivideTile] at hyu
  rcases List.mem_map.1 hyu with ⟨r, _hr, hyr⟩
  have hpair : (t, q) = (u, r) :=
    subdivideTileAt_pair_injective (hxq.trans hyr.symm)
  have htu : t = u := congrArg Prod.fst hpair
  exact hnot (htu.symm ▸ hu)

theorem subdivideTileSet_nodup_of_nodup {T : TileSet}
    (hT : T.Nodup) :
    (subdivideTileSet T).Nodup := by
  induction T with
  | nil =>
      simp [subdivideTileSet]
  | cons t T ih =>
      simp only [subdivideTileSet_cons]
      rw [List.nodup_cons] at hT
      exact List.Nodup.append (subdivideTile_nodup t) (ih hT.2)
        (subdivideTile_disjoint_subdivideTileSet_of_not_mem hT.1)

/--
Compress an aligned 2-by-2 subdivision boundary certificate back to the
underlying raw Wang rectangle.

This is the local form needed when a construction works with quarter-sites:
membership of one quarter recovers membership of the raw tile, and the
east/north macro-edge matches are read from the corresponding subdivided
boundary edges.
-/
theorem validRectangle_of_subdivideTileAt_boundaries {T : TileSet}
    {w h : Nat} (x : Rectangle w h)
    (hmem : ∀ i : Fin w, ∀ j : Fin h,
      subdivideTileAt (x i j) .southwest ∈ subdivideTileSet T)
    (hh : ∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
      WangTile.HMatches
        (subdivideTileAt (x i j) .southeast)
        (subdivideTileAt (x ⟨i.val + 1, hi⟩ j) .southwest))
    (hv : ∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
      WangTile.VMatches
        (subdivideTileAt (x i j) .northwest)
        (subdivideTileAt (x i ⟨j.val + 1, hj⟩) .southwest)) :
    ValidRectangle T x := by
  constructor
  · intro i j
    exact mem_of_subdivideTileAt_mem_subdivideTileSet (hmem i j)
  constructor
  · intro i j hi
    exact
      (hMatches_subdivideTileAt_iff
        (x i j) (x ⟨i.val + 1, hi⟩ j)
        Quadrant.southeast Quadrant.southwest).1 (hh i j hi)
  · intro i j hj
    exact
      (vMatches_subdivideTileAt_iff
        (x i j) (x i ⟨j.val + 1, hj⟩)
        Quadrant.northwest Quadrant.southwest).1 (hv i j hj)

private def intParityBit (z : Int) : Bool :=
  z % 2 = 1

private def pointQuadrant (p : Int × Int) : Quadrant :=
  Quadrant.ofBits (intParityBit p.1, intParityBit p.2)

private def macroPoint (p : Int × Int) : Int × Int :=
  (p.1 / 2, p.2 / 2)

private theorem intParityBit_eq_false_of_emod_eq_zero {z : Int}
    (h : z % 2 = 0) :
    intParityBit z = false := by
  simp [intParityBit, h]

private theorem intParityBit_eq_true_of_emod_eq_one {z : Int}
    (h : z % 2 = 1) :
    intParityBit z = true := by
  simp [intParityBit, h]

private theorem intParityBit_succ_eq_true_of_emod_eq_zero {z : Int}
    (h : z % 2 = 0) :
    intParityBit (z + 1) = true := by
  have hsucc : (z + 1) % 2 = 1 := by
    omega
  exact intParityBit_eq_true_of_emod_eq_one hsucc

private theorem intParityBit_succ_eq_false_of_emod_eq_one {z : Int}
    (h : z % 2 = 1) :
    intParityBit (z + 1) = false := by
  have hsucc : (z + 1) % 2 = 0 := by
    omega
  exact intParityBit_eq_false_of_emod_eq_zero hsucc

private theorem succ_div_two_of_emod_eq_zero {z : Int}
    (h : z % 2 = 0) :
    (z + 1) / 2 = z / 2 := by
  omega

private theorem succ_div_two_of_emod_eq_one {z : Int}
    (h : z % 2 = 1) :
    (z + 1) / 2 = z / 2 + 1 := by
  omega

private def subdividedPlaneTiling {T : TileSet}
    (x : Int × Int → TileIn T) :
    Int × Int → TileIn (subdivideTileSet T) := fun p =>
  let tile := x (macroPoint p)
  ⟨subdivideTileAt tile.1 (pointQuadrant p),
    subdivideTileAt_mem_subdivideTileSet tile.2 (pointQuadrant p)⟩

theorem validPlaneTiling_subdivideTileSet_of_validPlaneTiling {T : TileSet}
    {x : Int × Int → TileIn T}
    (hx : ValidPlaneTiling T x) :
    ValidPlaneTiling (subdivideTileSet T) (subdividedPlaneTiling x) := by
  constructor
  · intro p
    rcases Int.emod_two_eq_zero_or_one p.1 with hx0 | hx1
    · have hdiv : (p.1 + 1) / 2 = p.1 / 2 :=
        succ_div_two_of_emod_eq_zero hx0
      have hbit : intParityBit p.1 = false :=
        intParityBit_eq_false_of_emod_eq_zero hx0
      have hbit' : intParityBit (p.1 + 1) = true :=
        intParityBit_succ_eq_true_of_emod_eq_zero hx0
      rcases Int.emod_two_eq_zero_or_one p.2 with hy0 | hy1
      · have hybit : intParityBit p.2 = false :=
          intParityBit_eq_false_of_emod_eq_zero hy0
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hybit, Quadrant.ofBits] using
          hMatches_southwest_southeast ((x (p.1 / 2, p.2 / 2)).1)
      · have hybit : intParityBit p.2 = true :=
          intParityBit_eq_true_of_emod_eq_one hy1
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hybit, Quadrant.ofBits] using
          hMatches_northwest_northeast ((x (p.1 / 2, p.2 / 2)).1)
    · have hdiv : (p.1 + 1) / 2 = p.1 / 2 + 1 :=
        succ_div_two_of_emod_eq_one hx1
      have hbit : intParityBit p.1 = true :=
        intParityBit_eq_true_of_emod_eq_one hx1
      have hbit' : intParityBit (p.1 + 1) = false :=
        intParityBit_succ_eq_false_of_emod_eq_one hx1
      rcases Int.emod_two_eq_zero_or_one p.2 with hy0 | hy1
      · have hybit : intParityBit p.2 = false :=
          intParityBit_eq_false_of_emod_eq_zero hy0
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hybit, Quadrant.ofBits] using
          hMatches_southeast_southwest_of_hMatches
            (left := (x (p.1 / 2, p.2 / 2)).1)
            (right := (x (p.1 / 2 + 1, p.2 / 2)).1)
            (hx.1 (p.1 / 2, p.2 / 2))
      · have hybit : intParityBit p.2 = true :=
          intParityBit_eq_true_of_emod_eq_one hy1
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hybit, Quadrant.ofBits] using
          hMatches_northeast_northwest_of_hMatches
            (left := (x (p.1 / 2, p.2 / 2)).1)
            (right := (x (p.1 / 2 + 1, p.2 / 2)).1)
            (hx.1 (p.1 / 2, p.2 / 2))
  · intro p
    rcases Int.emod_two_eq_zero_or_one p.2 with hy0 | hy1
    · have hdiv : (p.2 + 1) / 2 = p.2 / 2 :=
        succ_div_two_of_emod_eq_zero hy0
      have hbit : intParityBit p.2 = false :=
        intParityBit_eq_false_of_emod_eq_zero hy0
      have hbit' : intParityBit (p.2 + 1) = true :=
        intParityBit_succ_eq_true_of_emod_eq_zero hy0
      rcases Int.emod_two_eq_zero_or_one p.1 with hx0 | hx1
      · have hxbit : intParityBit p.1 = false :=
          intParityBit_eq_false_of_emod_eq_zero hx0
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hxbit, Quadrant.ofBits] using
          vMatches_southwest_northwest ((x (p.1 / 2, p.2 / 2)).1)
      · have hxbit : intParityBit p.1 = true :=
          intParityBit_eq_true_of_emod_eq_one hx1
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hxbit, Quadrant.ofBits] using
          vMatches_southeast_northeast ((x (p.1 / 2, p.2 / 2)).1)
    · have hdiv : (p.2 + 1) / 2 = p.2 / 2 + 1 :=
        succ_div_two_of_emod_eq_one hy1
      have hbit : intParityBit p.2 = true :=
        intParityBit_eq_true_of_emod_eq_one hy1
      have hbit' : intParityBit (p.2 + 1) = false :=
        intParityBit_succ_eq_false_of_emod_eq_one hy1
      rcases Int.emod_two_eq_zero_or_one p.1 with hx0 | hx1
      · have hxbit : intParityBit p.1 = false :=
          intParityBit_eq_false_of_emod_eq_zero hx0
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hxbit, Quadrant.ofBits] using
          vMatches_northwest_southwest_of_vMatches
            (lower := (x (p.1 / 2, p.2 / 2)).1)
            (upper := (x (p.1 / 2, p.2 / 2 + 1)).1)
            (hx.2 (p.1 / 2, p.2 / 2))
      · have hxbit : intParityBit p.1 = true :=
          intParityBit_eq_true_of_emod_eq_one hx1
        simpa [subdividedPlaneTiling, macroPoint, pointQuadrant, hdiv, hbit,
          hbit', hxbit, Quadrant.ofBits] using
          vMatches_northeast_southeast_of_vMatches
            (lower := (x (p.1 / 2, p.2 / 2)).1)
            (upper := (x (p.1 / 2, p.2 / 2 + 1)).1)
            (hx.2 (p.1 / 2, p.2 / 2))

theorem tilesPlane_subdivideTileSet_of_tilesPlane {T : TileSet} :
    TilesPlane T → TilesPlane (subdivideTileSet T) := by
  rintro ⟨x, hx⟩
  exact ⟨subdividedPlaneTiling x,
    validPlaneTiling_subdivideTileSet_of_validPlaneTiling hx⟩

end TileSubdivision

end LeanWang
