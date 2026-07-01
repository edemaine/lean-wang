/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
Figure 16 substitution data for the Ollinger/Robinson scaffold.

The labels here match the reference image
[figures/figure16-layer-components.png](../figures/figure16-layer-components.png).
This file records the human transcription of the three layer substitutions and
the finite local compatibility check that every displayed `2 × 2` block has
matching internal Wang edges.

The edge colors assigned to the component symbols are symbolic equivalence-class
identifiers for the local seams forced by the Figure 16 substitution blocks.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure16

/-- Thin red+green layer components. -/
inductive Thin where
  | a
  | b
  | c
  | d
deriving DecidableEq, Repr

namespace Thin

def all : List Thin := [.a, .b, .c, .d]

end Thin

/-- Thick red+green layer components. -/
inductive Thick where
  | a | b | c | d
  | e | f | g | h
  | i | j | k | l
  | m | n | o | p
  | q | r | s | t
deriving DecidableEq, Repr

namespace Thick

def all : List Thick := [
  .a, .b, .c, .d,
  .e, .f, .g, .h,
  .i, .j, .k, .l,
  .m, .n, .o, .p,
  .q, .r, .s, .t
]

end Thick

/-- Thick line atoms used in the `L2e`-`L2p` decompositions. -/
inductive ThickLine where
  | r0 | r1 | r2 | r3
  | g0 | g1 | g2 | g3
deriving DecidableEq, Repr

namespace ThickLine

def all : List ThickLine := [.r0, .r1, .r2, .r3, .g0, .g1, .g2, .g3]

end ThickLine

/--
A formal sum of two distinct thick-line atoms in Figure 16.

The order records the atom placements used by `phiL2Component2`: `first` is the
northwest atom and `second` is the southeast atom.  As a geometric sum this
order is not intended to carry extra meaning.
-/
structure ThickLineSum where
  first : ThickLine
  second : ThickLine
  distinct : first ≠ second

namespace ThickLineSum

def mkDistinct (first second : ThickLine) (distinct : first ≠ second) :
    ThickLineSum where
  first := first
  second := second
  distinct := distinct

end ThickLineSum

/-- Black layer components. -/
inductive Black where
  | a
  | b
  | c
  | d
  | e
deriving DecidableEq, Repr

namespace Black

def all : List Black := [.a, .b, .c, .d, .e]

end Black

/-- Any component that appears as one cell of a Figure 16 substitution block. -/
inductive Symbol where
  | blank
  | thin (component : Thin)
  | thick (component : Thick)
  | line (component : ThickLine)
  | black (component : Black)
deriving DecidableEq, Repr

namespace Symbol

def L1a : Symbol := .thin .a
def L1b : Symbol := .thin .b
def L1c : Symbol := .thin .c
def L1d : Symbol := .thin .d

def L2a : Symbol := .thick .a
def L2b : Symbol := .thick .b
def L2c : Symbol := .thick .c
def L2d : Symbol := .thick .d
def L2e : Symbol := .thick .e
def L2f : Symbol := .thick .f
def L2g : Symbol := .thick .g
def L2h : Symbol := .thick .h
def L2i : Symbol := .thick .i
def L2j : Symbol := .thick .j
def L2k : Symbol := .thick .k
def L2l : Symbol := .thick .l
def L2m : Symbol := .thick .m
def L2n : Symbol := .thick .n
def L2o : Symbol := .thick .o
def L2p : Symbol := .thick .p
def L2q : Symbol := .thick .q
def L2r : Symbol := .thick .r
def L2s : Symbol := .thick .s
def L2t : Symbol := .thick .t

def R0 : Symbol := .line .r0
def R1 : Symbol := .line .r1
def R2 : Symbol := .line .r2
def R3 : Symbol := .line .r3
def G0 : Symbol := .line .g0
def G1 : Symbol := .line .g1
def G2 : Symbol := .line .g2
def G3 : Symbol := .line .g3

def L3a : Symbol := .black .a
def L3b : Symbol := .black .b
def L3c : Symbol := .black .c
def L3d : Symbol := .black .d
def L3e : Symbol := .black .e

def all : List Symbol := [
  .blank,
  L1a, L1b, L1c, L1d,
  L2a, L2b, L2c, L2d,
  L2e, L2f, L2g, L2h,
  L2i, L2j, L2k, L2l,
  L2m, L2n, L2o, L2p,
  L2q, L2r, L2s, L2t,
  R0, R1, R2, R3,
  G0, G1, G2, G3,
  L3a, L3b, L3c, L3d, L3e
]

end Symbol

namespace Thick

/--
The `L2e`-`L2t` components are sums of two distinct thick-line atoms.

The first four `L2` components are corner components rather than two-line sums,
so they return `none`.
-/
def lineSum? : Thick → Option ThickLineSum
  | .a => none
  | .b => none
  | .c => none
  | .d => none
  | .e => some <| ThickLineSum.mkDistinct .r0 .r1 (by decide)
  | .f => some <| ThickLineSum.mkDistinct .r2 .r1 (by decide)
  | .g => some <| ThickLineSum.mkDistinct .r2 .r3 (by decide)
  | .h => some <| ThickLineSum.mkDistinct .r0 .r3 (by decide)
  | .i => some <| ThickLineSum.mkDistinct .g0 .r3 (by decide)
  | .j => some <| ThickLineSum.mkDistinct .r0 .g1 (by decide)
  | .k => some <| ThickLineSum.mkDistinct .g2 .r1 (by decide)
  | .l => some <| ThickLineSum.mkDistinct .r2 .g3 (by decide)
  | .m => some <| ThickLineSum.mkDistinct .g0 .g1 (by decide)
  | .n => some <| ThickLineSum.mkDistinct .g2 .g1 (by decide)
  | .o => some <| ThickLineSum.mkDistinct .g2 .g3 (by decide)
  | .p => some <| ThickLineSum.mkDistinct .g0 .g3 (by decide)
  | .q => some <| ThickLineSum.mkDistinct .g2 .r3 (by decide)
  | .r => some <| ThickLineSum.mkDistinct .r2 .g1 (by decide)
  | .s => some <| ThickLineSum.mkDistinct .g0 .r1 (by decide)
  | .t => some <| ThickLineSum.mkDistinct .r0 .g3 (by decide)

def hasLineSum (component : Thick) : Prop :=
  component.lineSum?.isSome

instance (component : Thick) : Decidable component.hasLineSum := by
  unfold hasLineSum
  infer_instance

end Thick

namespace Symbol

private def t (n s e w : Nat) : WangTile where
  n := n
  s := s
  e := e
  w := w

/--
Symbolic Wang-tile edges for the Figure 16 components.

These natural colors are not Figure 13 edge-color ids.  They are the local seam
equivalence classes induced by the substitution blocks below.
-/
def tile : Symbol → WangTile
  | .blank => t 0 1 2 3
  | .thin .a => t 4 5 6 7
  | .thin .b => t 8 9 10 11
  | .thin .c => t 9 12 13 6
  | .thin .d => t 14 4 11 15
  | .thick .a => t 16 17 18 19
  | .thick .b => t 20 21 18 22
  | .thick .c => t 23 24 25 26
  | .thick .d => t 27 28 29 30
  | .thick .e => t 20 31 32 33
  | .thick .f => t 23 34 32 35
  | .thick .g => t 23 36 18 37
  | .thick .h => t 20 38 18 39
  | .thick .i => t 27 40 18 41
  | .thick .j => t 20 42 29 43
  | .thick .k => t 16 44 32 45
  | .thick .l => t 23 46 25 47
  | .thick .m => t 27 48 29 49
  | .thick .n => t 16 50 29 51
  | .thick .o => t 16 52 25 53
  | .thick .p => t 27 54 25 55
  | .thick .q => t 16 68 18 69
  | .thick .r => t 23 66 29 67
  | .thick .s => t 27 64 32 65
  | .thick .t => t 20 70 25 71
  | .line .r0 => t 17 20 3 2
  | .line .r1 => t 1 0 26 32
  | .line .r2 => t 28 23 3 2
  | .line .r3 => t 1 0 30 18
  | .line .g0 => t 24 27 3 2
  | .line .g1 => t 1 0 19 29
  | .line .g2 => t 21 16 3 2
  | .line .g3 => t 1 0 22 25
  | .black .a => t 56 57 58 59
  | .black .b => t 57 60 58 58
  | .black .c => t 57 61 59 59
  | .black .d => t 57 57 59 62
  | .black .e => t 56 56 59 63

def tileSet : TileSet :=
  all.map tile

theorem mem_all (symbol : Symbol) : symbol ∈ all := by
  cases symbol with
  | blank =>
      decide
  | thin component =>
      cases component <;> decide
  | thick component =>
      cases component <;> decide
  | line component =>
      cases component <;> decide
  | black component =>
      cases component <;> decide

theorem tile_mem_tileSet (symbol : Symbol) :
    tile symbol ∈ tileSet :=
  List.mem_map.2 ⟨symbol, mem_all symbol, rfl⟩

end Symbol

namespace ThickLineSum

def symbols (sum : ThickLineSum) : Symbol × Symbol :=
  (.line sum.first, .line sum.second)

end ThickLineSum

/-- A displayed `2 × 2` Figure 16 block, listed north row then south row. -/
structure Block where
  northwest : Symbol
  northeast : Symbol
  southwest : Symbol
  southeast : Symbol
deriving DecidableEq, Repr

namespace Block

def mkRows (northwest northeast southwest southeast : Symbol) : Block where
  northwest := northwest
  northeast := northeast
  southwest := southwest
  southeast := southeast

/-- Internal Wang-edge compatibility inside a `2 × 2` block. -/
def Compatible (B : Block) : Prop :=
  WangTile.HMatches (Symbol.tile B.northwest) (Symbol.tile B.northeast) ∧
  WangTile.HMatches (Symbol.tile B.southwest) (Symbol.tile B.southeast) ∧
  WangTile.VMatches (Symbol.tile B.southwest) (Symbol.tile B.northwest) ∧
  WangTile.VMatches (Symbol.tile B.southeast) (Symbol.tile B.northeast)

instance (B : Block) : Decidable B.Compatible := by
  unfold Compatible
  infer_instance

def compatibleBool (B : Block) : Bool :=
  decide B.Compatible

theorem compatible_of_compatibleBool {B : Block} (h : B.compatibleBool = true) :
    B.Compatible := by
  unfold compatibleBool at h
  exact of_decide_eq_true h

theorem north_hMatches {B : Block} (h : B.Compatible) :
    WangTile.HMatches (Symbol.tile B.northwest) (Symbol.tile B.northeast) :=
  h.1

theorem south_hMatches {B : Block} (h : B.Compatible) :
    WangTile.HMatches (Symbol.tile B.southwest) (Symbol.tile B.southeast) :=
  h.2.1

theorem west_vMatches {B : Block} (h : B.Compatible) :
    WangTile.VMatches (Symbol.tile B.southwest) (Symbol.tile B.northwest) :=
  h.2.2.1

theorem east_vMatches {B : Block} (h : B.Compatible) :
    WangTile.VMatches (Symbol.tile B.southeast) (Symbol.tile B.northeast) :=
  h.2.2.2

/-- Read a block entry by rectangle coordinates: `i = 0` is west, `j = 0` is south. -/
def entry (B : Block) (i j : Fin 2) : Symbol :=
  if j.val = 0 then
    if i.val = 0 then B.southwest else B.southeast
  else
    if i.val = 0 then B.northwest else B.northeast

@[simp]
theorem entry_southwest (B : Block) :
    B.entry ⟨0, by decide⟩ ⟨0, by decide⟩ = B.southwest := by
  simp [entry]

@[simp]
theorem entry_southeast (B : Block) :
    B.entry ⟨1, by decide⟩ ⟨0, by decide⟩ = B.southeast := by
  simp [entry]

@[simp]
theorem entry_northwest (B : Block) :
    B.entry ⟨0, by decide⟩ ⟨1, by decide⟩ = B.northwest := by
  simp [entry]

@[simp]
theorem entry_northeast (B : Block) :
    B.entry ⟨1, by decide⟩ ⟨1, by decide⟩ = B.northeast := by
  simp [entry]

/-- The four Wang tiles appearing in a block. -/
def tileSet (B : Block) : TileSet := [
  Symbol.tile B.southwest,
  Symbol.tile B.southeast,
  Symbol.tile B.northwest,
  Symbol.tile B.northeast
]

/-- The block as a `2 × 2` Wang-tile rectangle. -/
def rectangle (B : Block) : Rectangle 2 2 :=
  fun i j => Symbol.tile (B.entry i j)

theorem rectangle_mem_tileSet (B : Block) (i j : Fin 2) :
    B.rectangle i j ∈ B.tileSet := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  have hi_cases : i = 0 ∨ i = 1 := by omega
  have hj_cases : j = 0 ∨ j = 1 := by omega
  rcases hi_cases with rfl | rfl <;>
    rcases hj_cases with rfl | rfl <;>
      simp [rectangle, entry, tileSet]

theorem rectangle_hMatches_of_compatible {B : Block} (h : B.Compatible)
    (i j : Fin 2) (hi : i.val + 1 < 2) :
    WangTile.HMatches (B.rectangle i j) (B.rectangle ⟨i.val + 1, hi⟩ j) := by
  rcases i with ⟨i, hi_lt⟩
  rcases j with ⟨j, hj_lt⟩
  simp at hi
  have hi_zero : i = 0 := by omega
  have hj_cases : j = 0 ∨ j = 1 := by omega
  subst i
  rcases hj_cases with rfl | rfl
  · simpa [rectangle, entry] using Block.south_hMatches h
  · simpa [rectangle, entry] using Block.north_hMatches h

theorem rectangle_vMatches_of_compatible {B : Block} (h : B.Compatible)
    (i j : Fin 2) (hj : j.val + 1 < 2) :
    WangTile.VMatches (B.rectangle i j) (B.rectangle i ⟨j.val + 1, hj⟩) := by
  rcases i with ⟨i, hi_lt⟩
  rcases j with ⟨j, hj_lt⟩
  simp at hj
  have hi_cases : i = 0 ∨ i = 1 := by omega
  have hj_zero : j = 0 := by omega
  subst j
  rcases hi_cases with rfl | rfl
  · simpa [rectangle, entry] using Block.west_vMatches h
  · simpa [rectangle, entry] using Block.east_vMatches h

theorem validRectangle_of_compatible {B : Block} (h : B.Compatible) :
    ValidRectangle B.tileSet B.rectangle := by
  refine ⟨rectangle_mem_tileSet B, ?_, ?_⟩
  · exact rectangle_hMatches_of_compatible h
  · exact rectangle_vMatches_of_compatible h

theorem rectangle_mem_symbolTileSet (B : Block) (i j : Fin 2) :
    B.rectangle i j ∈ Symbol.tileSet :=
  Symbol.tile_mem_tileSet (B.entry i j)

theorem validRectangle_symbolTileSet_of_compatible {B : Block} (h : B.Compatible) :
    ValidRectangle Symbol.tileSet B.rectangle := by
  refine ⟨rectangle_mem_symbolTileSet B, ?_, ?_⟩
  · exact rectangle_hMatches_of_compatible h
  · exact rectangle_vMatches_of_compatible h

/--
A locally compatible Figure 16 substitution block is a tileable `2 × 2`
symbol square.
-/
theorem tileableSquare_symbolTileSet_of_compatible {B : Block}
    (h : B.Compatible) :
    TileableSquare Symbol.tileSet 2 :=
  ⟨B.rectangle, validRectangle_symbolTileSet_of_compatible h⟩

/-- East-west compatibility between adjacent `2 × 2` blocks. -/
def hBoundaryMatches (left right : Block) : Prop :=
  WangTile.HMatches (Symbol.tile left.southeast) (Symbol.tile right.southwest) ∧
  WangTile.HMatches (Symbol.tile left.northeast) (Symbol.tile right.northwest)

/-- North-south compatibility between adjacent `2 × 2` blocks. -/
def vBoundaryMatches (lower upper : Block) : Prop :=
  WangTile.VMatches (Symbol.tile lower.northwest) (Symbol.tile upper.southwest) ∧
  WangTile.VMatches (Symbol.tile lower.northeast) (Symbol.tile upper.southeast)

instance (left right : Block) : Decidable (left.hBoundaryMatches right) := by
  unfold hBoundaryMatches
  infer_instance

instance (lower upper : Block) : Decidable (lower.vBoundaryMatches upper) := by
  unfold vBoundaryMatches
  infer_instance

theorem hBoundaryMatches_of_boundary
    {left right : Block}
    (hsouth : WangTile.HMatches (Symbol.tile left.southeast) (Symbol.tile right.southwest))
    (hnorth : WangTile.HMatches (Symbol.tile left.northeast) (Symbol.tile right.northwest)) :
    left.hBoundaryMatches right := by
  exact ⟨hsouth, hnorth⟩

theorem vBoundaryMatches_of_boundary
    {lower upper : Block}
    (hwest : WangTile.VMatches (Symbol.tile lower.northwest) (Symbol.tile upper.southwest))
    (heast : WangTile.VMatches (Symbol.tile lower.northeast) (Symbol.tile upper.southeast)) :
    lower.vBoundaryMatches upper := by
  exact ⟨hwest, heast⟩

end Block

/--
A grid of Figure 16 substitution blocks, before expanding each block into its
four component symbols.
-/
abbrev BlockGrid (w h : Nat) := Fin w → Fin h → Block

namespace BlockGrid

/--
Compatibility condition for a grid of Figure 16 blocks.  Each block has valid
internal seams, and neighboring blocks agree across their shared boundaries.
-/
def Compatible {w h : Nat} (G : BlockGrid w h) : Prop :=
  (∀ i : Fin w, ∀ j : Fin h, (G i j).Compatible) ∧
  (∀ i : Fin w, ∀ j : Fin h, ∀ hi : i.val + 1 < w,
    (G i j).hBoundaryMatches (G ⟨i.val + 1, hi⟩ j)) ∧
  (∀ i : Fin w, ∀ j : Fin h, ∀ hj : j.val + 1 < h,
    (G i j).vBoundaryMatches (G i ⟨j.val + 1, hj⟩))

def expandedSymbol {w h : Nat} (G : BlockGrid w h)
    (i : Fin w) (j : Fin h) (di dj : Fin 2) : Symbol :=
  (G i j).entry di dj

def expandedTile {w h : Nat} (G : BlockGrid w h)
    (i : Fin w) (j : Fin h) (di dj : Fin 2) : WangTile :=
  Symbol.tile (expandedSymbol G i j di dj)

theorem expandedTile_mem_symbolTileSet {w h : Nat} (G : BlockGrid w h)
    (i : Fin w) (j : Fin h) (di dj : Fin 2) :
    expandedTile G i j di dj ∈ Symbol.tileSet :=
  Symbol.tile_mem_tileSet (expandedSymbol G i j di dj)

theorem expanded_hMatches_within {w h : Nat} {G : BlockGrid w h}
    (hG : Compatible G) (i : Fin w) (j : Fin h) (dj : Fin 2) :
    WangTile.HMatches
      (expandedTile G i j ⟨0, by decide⟩ dj)
      (expandedTile G i j ⟨1, by decide⟩ dj) := by
  rcases dj with ⟨dj, hdj⟩
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  rcases hdj_cases with rfl | rfl
  · simpa [expandedTile, expandedSymbol, Block.entry] using
      Block.south_hMatches (hG.1 i j)
  · simpa [expandedTile, expandedSymbol, Block.entry] using
      Block.north_hMatches (hG.1 i j)

theorem expanded_hMatches_boundary {w h : Nat} {G : BlockGrid w h}
    (hG : Compatible G) (i : Fin w) (j : Fin h)
    (hi : i.val + 1 < w) (dj : Fin 2) :
    WangTile.HMatches
      (expandedTile G i j ⟨1, by decide⟩ dj)
      (expandedTile G ⟨i.val + 1, hi⟩ j ⟨0, by decide⟩ dj) := by
  rcases dj with ⟨dj, hdj⟩
  have hdj_cases : dj = 0 ∨ dj = 1 := by omega
  have hboundary := hG.2.1 i j hi
  rcases hdj_cases with rfl | rfl
  · simpa [expandedTile, expandedSymbol, Block.entry, Block.hBoundaryMatches] using
      hboundary.1
  · simpa [expandedTile, expandedSymbol, Block.entry, Block.hBoundaryMatches] using
      hboundary.2

theorem expanded_vMatches_within {w h : Nat} {G : BlockGrid w h}
    (hG : Compatible G) (i : Fin w) (j : Fin h) (di : Fin 2) :
    WangTile.VMatches
      (expandedTile G i j di ⟨0, by decide⟩)
      (expandedTile G i j di ⟨1, by decide⟩) := by
  rcases di with ⟨di, hdi⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  rcases hdi_cases with rfl | rfl
  · simpa [expandedTile, expandedSymbol, Block.entry] using
      Block.west_vMatches (hG.1 i j)
  · simpa [expandedTile, expandedSymbol, Block.entry] using
      Block.east_vMatches (hG.1 i j)

theorem expanded_vMatches_boundary {w h : Nat} {G : BlockGrid w h}
    (hG : Compatible G) (i : Fin w) (j : Fin h)
    (hj : j.val + 1 < h) (di : Fin 2) :
    WangTile.VMatches
      (expandedTile G i j di ⟨1, by decide⟩)
      (expandedTile G i ⟨j.val + 1, hj⟩ di ⟨0, by decide⟩) := by
  rcases di with ⟨di, hdi⟩
  have hdi_cases : di = 0 ∨ di = 1 := by omega
  have hboundary := hG.2.2 i j hj
  rcases hdi_cases with rfl | rfl
  · simpa [expandedTile, expandedSymbol, Block.entry, Block.vBoundaryMatches] using
      hboundary.1
  · simpa [expandedTile, expandedSymbol, Block.entry, Block.vBoundaryMatches] using
      hboundary.2

/-- Block coordinate of a cell in the doubled expansion. -/
def doubledBlockCoord {w : Nat} (i : Fin (2 * w)) : Fin w :=
  ⟨i.val / 2, by
    have hi : i.val < 2 * w := i.isLt
    omega⟩

/-- In-block offset of a cell in the doubled expansion. -/
def doubledOffset {w : Nat} (i : Fin (2 * w)) : Fin 2 :=
  ⟨i.val % 2, by omega⟩

theorem doubledOffset_eq_zero_or_one {w : Nat} (i : Fin (2 * w)) :
    (doubledOffset i).val = 0 ∨ (doubledOffset i).val = 1 := by
  have hlt : (doubledOffset i).val < 2 := (doubledOffset i).isLt
  omega

theorem doubled_succ_of_offset_zero {w : Nat}
    (i : Fin (2 * w)) (hi : i.val + 1 < 2 * w)
    (hzero : (doubledOffset i).val = 0) :
    doubledBlockCoord ⟨i.val + 1, hi⟩ = doubledBlockCoord i ∧
      doubledOffset ⟨i.val + 1, hi⟩ = ⟨1, by decide⟩ := by
  have hmod : i.val % 2 = 0 := by
    simpa [doubledOffset] using hzero
  have hdecomp : 2 * (i.val / 2) + i.val % 2 = i.val :=
    Nat.div_add_mod i.val 2
  have hi_eq : i.val = 2 * (i.val / 2) := by omega
  constructor
  · apply Fin.ext
    simp [doubledBlockCoord]
    omega
  · apply Fin.ext
    simp [doubledOffset]
    omega

theorem doubled_succ_of_offset_one {w : Nat}
    (i : Fin (2 * w)) (hi : i.val + 1 < 2 * w)
    (hone : (doubledOffset i).val = 1) :
    ∃ hb : (doubledBlockCoord i).val + 1 < w,
      doubledBlockCoord ⟨i.val + 1, hi⟩ =
          ⟨(doubledBlockCoord i).val + 1, hb⟩ ∧
        doubledOffset ⟨i.val + 1, hi⟩ = ⟨0, by decide⟩ := by
  have hmod : i.val % 2 = 1 := by
    simpa [doubledOffset] using hone
  have hdecomp : 2 * (i.val / 2) + i.val % 2 = i.val :=
    Nat.div_add_mod i.val 2
  have hi_eq : i.val = 2 * (i.val / 2) + 1 := by omega
  have hb : (doubledBlockCoord i).val + 1 < w := by
    simp [doubledBlockCoord]
    omega
  refine ⟨hb, ?_, ?_⟩
  · apply Fin.ext
    simp [doubledBlockCoord]
    omega
  · apply Fin.ext
    simp [doubledOffset]
    omega

/-- The `2w × 2h` rectangle obtained by expanding every Figure 16 block. -/
def expandedRectangle {w h : Nat} (G : BlockGrid w h) :
    Rectangle (2 * w) (2 * h) :=
  fun i j =>
    expandedTile G (doubledBlockCoord i) (doubledBlockCoord j)
      (doubledOffset i) (doubledOffset j)

/--
A compatible grid of Figure 16 substitution blocks expands to a valid Wang
rectangle over the finite component-symbol tileset.
-/
theorem expandedRectangle_valid {w h : Nat} {G : BlockGrid w h}
    (hG : Compatible G) :
    ValidRectangle Symbol.tileSet (expandedRectangle G) := by
  constructor
  · intro i j
    exact expandedTile_mem_symbolTileSet G
      (doubledBlockCoord i) (doubledBlockCoord j)
      (doubledOffset i) (doubledOffset j)
  constructor
  · intro i j hi
    rcases doubledOffset_eq_zero_or_one i with hzero | hone
    · rcases doubled_succ_of_offset_zero i hi hzero with
        ⟨hblock, hoff⟩
      have hoff_i : doubledOffset i = ⟨0, by decide⟩ := Fin.ext hzero
      simpa [expandedRectangle, hblock, hoff, hoff_i] using
        expanded_hMatches_within hG (doubledBlockCoord i)
          (doubledBlockCoord j) (doubledOffset j)
    · rcases doubled_succ_of_offset_one i hi hone with
        ⟨hb, hblock, hoff⟩
      have hoff_i : doubledOffset i = ⟨1, by decide⟩ := Fin.ext hone
      simpa [expandedRectangle, hblock, hoff, hoff_i] using
        expanded_hMatches_boundary hG (doubledBlockCoord i)
          (doubledBlockCoord j) hb (doubledOffset j)
  · intro i j hj
    rcases doubledOffset_eq_zero_or_one j with hzero | hone
    · rcases doubled_succ_of_offset_zero j hj hzero with
        ⟨hblock, hoff⟩
      have hoff_j : doubledOffset j = ⟨0, by decide⟩ := Fin.ext hzero
      simpa [expandedRectangle, hblock, hoff, hoff_j] using
        expanded_vMatches_within hG (doubledBlockCoord i)
          (doubledBlockCoord j) (doubledOffset i)
    · rcases doubled_succ_of_offset_one j hj hone with
        ⟨hb, hblock, hoff⟩
      have hoff_j : doubledOffset j = ⟨1, by decide⟩ := Fin.ext hone
      simpa [expandedRectangle, hblock, hoff, hoff_j] using
        expanded_vMatches_boundary hG (doubledBlockCoord i)
          (doubledBlockCoord j) hb (doubledOffset i)

/--
A compatible grid of Figure 16 substitution blocks gives a tileable doubled
rectangle over the component-symbol tileset.
-/
theorem tileableExpandedRectangle {w h : Nat} {G : BlockGrid w h}
    (hG : Compatible G) :
    TileableRectangle Symbol.tileSet (2 * w) (2 * h) :=
  ⟨expandedRectangle G, expandedRectangle_valid hG⟩

/-- Square specialization of `tileableExpandedRectangle`. -/
theorem tileableExpandedSquare {n : Nat} {G : BlockGrid n n}
    (hG : Compatible G) :
    TileableSquare Symbol.tileSet (2 * n) :=
  tileableExpandedRectangle hG

end BlockGrid

/-- `phi_L1(*)`. -/
def phiL1Star : Block :=
  .mkRows .L1d .L1b .L1a .L1c

/-- First summand of `phi_L2`, applied to an `L1` component. -/
def phiL2Component1 : Thin → Block
  | .a => .mkRows .G3 .L2b .blank .G2
  | .b => .mkRows .R3 .L2d .blank .R2
  | .c => .mkRows .R1 .L2c .blank .G0
  | .d => .mkRows .G1 .L2a .blank .R0

/-- Second summand of `phi_L2`, applied to an `L2` component. -/
def phiL2Component2 : Thick → Block
  | .a => .mkRows .G2 .blank .L2a .R3
  | .b => .mkRows .R0 .blank .L2b .R3
  | .c => .mkRows .R2 .blank .L2c .G3
  | .d => .mkRows .G0 .blank .L2d .G1
  | .e => .mkRows .R0 .blank .L2e .R1
  | .f => .mkRows .R2 .blank .L2f .R1
  | .g => .mkRows .R2 .blank .L2g .R3
  | .h => .mkRows .R0 .blank .L2h .R3
  | .i => .mkRows .G0 .blank .L2i .R3
  | .j => .mkRows .R0 .blank .L2j .G1
  | .k => .mkRows .G2 .blank .L2k .R1
  | .l => .mkRows .R2 .blank .L2l .G3
  | .m => .mkRows .G0 .blank .L2m .G1
  | .n => .mkRows .G2 .blank .L2n .G1
  | .o => .mkRows .G2 .blank .L2o .G3
  | .p => .mkRows .G0 .blank .L2p .G3
  | .q => .mkRows .G2 .blank .L2q .R3
  | .r => .mkRows .R2 .blank .L2r .G1
  | .s => .mkRows .G0 .blank .L2s .R1
  | .t => .mkRows .R0 .blank .L2t .G3

namespace Thick

def lineSumBlock? (component : Thick) : Option Block :=
  component.lineSum?.map fun sum =>
    .mkRows (Symbol.line sum.first) .blank (.thick component)
      (Symbol.line sum.second)

theorem phiL2Component2_eq_lineSumBlock_of_lineSum
    {component : Thick} {sum : ThickLineSum}
    (h : component.lineSum? = some sum) :
    phiL2Component2 component =
      .mkRows (Symbol.line sum.first) .blank (.thick component)
        (Symbol.line sum.second) := by
  cases component <;>
    simp [lineSum?, ThickLineSum.mkDistinct] at h
  all_goals
    subst sum
    rfl

theorem lineSumBlock?_eq_some_phiL2Component2
    {component : Thick} (h : component.hasLineSum) :
    component.lineSumBlock? = some (phiL2Component2 component) := by
  cases component <;>
    simp [hasLineSum, lineSumBlock?, lineSum?, ThickLineSum.mkDistinct,
      phiL2Component2, Symbol.R0, Symbol.R1, Symbol.R2, Symbol.R3,
      Symbol.G0, Symbol.G1, Symbol.G2, Symbol.G3, Symbol.L2e, Symbol.L2f,
      Symbol.L2g, Symbol.L2h, Symbol.L2i, Symbol.L2j, Symbol.L2k,
      Symbol.L2l, Symbol.L2m, Symbol.L2n, Symbol.L2o, Symbol.L2p,
      Symbol.L2q, Symbol.L2r, Symbol.L2s, Symbol.L2t] at h ⊢

end Thick

/-- `phi_L3`, applied to a black-layer component. -/
def phiL3 : Black → Block
  | .a => .mkRows .L3e .L3a .L3a .L3b
  | .b => .mkRows .L3d .L3a .L3b .L3b
  | .c => .mkRows .L3d .L3a .L3c .L3c
  | .d => .mkRows .L3d .L3a .L3d .L3c
  | .e => .mkRows .L3e .L3a .L3e .L3c

/-!
Named theorem form of the human Figure 16 transcription.  These facts are
definitionally true, but keeping the displayed rows as theorem names makes the
transcription easy to audit and reference from the Figure 13 layer decoder.
-/
namespace HumanTranscription

theorem phiL1Star_row :
    phiL1Star = .mkRows .L1d .L1b .L1a .L1c :=
  rfl

theorem phiL2Component1_a :
    phiL2Component1 .a = .mkRows .G3 .L2b .blank .G2 :=
  rfl

theorem phiL2Component1_b :
    phiL2Component1 .b = .mkRows .R3 .L2d .blank .R2 :=
  rfl

theorem phiL2Component1_c :
    phiL2Component1 .c = .mkRows .R1 .L2c .blank .G0 :=
  rfl

theorem phiL2Component1_d :
    phiL2Component1 .d = .mkRows .G1 .L2a .blank .R0 :=
  rfl

theorem phiL2Component2_a :
    phiL2Component2 .a = .mkRows .G2 .blank .L2a .R3 :=
  rfl

theorem phiL2Component2_b :
    phiL2Component2 .b = .mkRows .R0 .blank .L2b .R3 :=
  rfl

theorem phiL2Component2_c :
    phiL2Component2 .c = .mkRows .R2 .blank .L2c .G3 :=
  rfl

theorem phiL2Component2_d :
    phiL2Component2 .d = .mkRows .G0 .blank .L2d .G1 :=
  rfl

theorem phiL2Component2_e :
    phiL2Component2 .e = .mkRows .R0 .blank .L2e .R1 :=
  rfl

theorem phiL2Component2_f :
    phiL2Component2 .f = .mkRows .R2 .blank .L2f .R1 :=
  rfl

theorem phiL2Component2_g :
    phiL2Component2 .g = .mkRows .R2 .blank .L2g .R3 :=
  rfl

theorem phiL2Component2_h :
    phiL2Component2 .h = .mkRows .R0 .blank .L2h .R3 :=
  rfl

theorem phiL2Component2_i :
    phiL2Component2 .i = .mkRows .G0 .blank .L2i .R3 :=
  rfl

theorem phiL2Component2_j :
    phiL2Component2 .j = .mkRows .R0 .blank .L2j .G1 :=
  rfl

theorem phiL2Component2_k :
    phiL2Component2 .k = .mkRows .G2 .blank .L2k .R1 :=
  rfl

theorem phiL2Component2_l :
    phiL2Component2 .l = .mkRows .R2 .blank .L2l .G3 :=
  rfl

theorem phiL2Component2_m :
    phiL2Component2 .m = .mkRows .G0 .blank .L2m .G1 :=
  rfl

theorem phiL2Component2_n :
    phiL2Component2 .n = .mkRows .G2 .blank .L2n .G1 :=
  rfl

theorem phiL2Component2_o :
    phiL2Component2 .o = .mkRows .G2 .blank .L2o .G3 :=
  rfl

theorem phiL2Component2_p :
    phiL2Component2 .p = .mkRows .G0 .blank .L2p .G3 :=
  rfl

theorem phiL2Component2_q :
    phiL2Component2 .q = .mkRows .G2 .blank .L2q .R3 :=
  rfl

theorem phiL2Component2_r :
    phiL2Component2 .r = .mkRows .R2 .blank .L2r .G1 :=
  rfl

theorem phiL2Component2_s :
    phiL2Component2 .s = .mkRows .G0 .blank .L2s .R1 :=
  rfl

theorem phiL2Component2_t :
    phiL2Component2 .t = .mkRows .R0 .blank .L2t .G3 :=
  rfl

theorem phiL3_a :
    phiL3 .a = .mkRows .L3e .L3a .L3a .L3b :=
  rfl

theorem phiL3_b :
    phiL3 .b = .mkRows .L3d .L3a .L3b .L3b :=
  rfl

theorem phiL3_c :
    phiL3 .c = .mkRows .L3d .L3a .L3c .L3c :=
  rfl

theorem phiL3_d :
    phiL3 .d = .mkRows .L3d .L3a .L3d .L3c :=
  rfl

theorem phiL3_e :
    phiL3 .e = .mkRows .L3e .L3a .L3e .L3c :=
  rfl

end HumanTranscription

/-- Domain of the finite Figure 16 substitution rule table. -/
inductive RuleSource where
  | l1Star
  | l2Component1 (component : Thin)
  | l2Component2 (component : Thick)
  | l3 (component : Black)
deriving DecidableEq, Repr

namespace RuleSource

def all : List RuleSource :=
  .l1Star ::
    (Thin.all.map .l2Component1) ++
      (Thick.all.map .l2Component2) ++
        (Black.all.map .l3)

def block : RuleSource → Block
  | .l1Star => phiL1Star
  | .l2Component1 component => phiL2Component1 component
  | .l2Component2 component => phiL2Component2 component
  | .l3 component => phiL3 component

theorem mem_all (source : RuleSource) : source ∈ all := by
  cases source with
  | l1Star =>
      decide
  | l2Component1 component =>
      cases component <;> decide
  | l2Component2 component =>
      cases component <;> decide
  | l3 component =>
      cases component <;> decide

theorem all_nodup : all.Nodup := by
  decide

end RuleSource

/-- One row of the finite Figure 16 substitution table. -/
structure SubstitutionRule where
  source : RuleSource
  block : Block
deriving DecidableEq, Repr

namespace SubstitutionRule

def ofSource (source : RuleSource) : SubstitutionRule where
  source := source
  block := source.block

@[simp]
theorem ofSource_source (source : RuleSource) :
    (ofSource source).source = source :=
  rfl

@[simp]
theorem ofSource_block (source : RuleSource) :
    (ofSource source).block = source.block :=
  rfl

end SubstitutionRule

/-- The complete finite Figure 16 substitution table. -/
def substitutionRules : List SubstitutionRule :=
  RuleSource.all.map SubstitutionRule.ofSource

def substitutionRuleSources : List RuleSource :=
  substitutionRules.map SubstitutionRule.source

theorem substitutionRuleSources_eq_all :
    substitutionRuleSources = RuleSource.all := by
  decide

theorem substitutionRuleSources_nodup :
    substitutionRuleSources.Nodup := by
  simpa [substitutionRuleSources_eq_all] using RuleSource.all_nodup

theorem mem_substitutionRules_iff {rule : SubstitutionRule} :
    rule ∈ substitutionRules ↔ ∃ source : RuleSource,
      source ∈ RuleSource.all ∧ SubstitutionRule.ofSource source = rule := by
  simp [substitutionRules]

/-- Named block used only for finite checks and readable diagnostics. -/
structure NamedBlock where
  name : String
  block : Block
deriving DecidableEq, Repr

namespace NamedBlock

def compatibleBool (entry : NamedBlock) : Bool :=
  entry.block.compatibleBool

end NamedBlock

def l1Component1Blocks : List NamedBlock := [
  ⟨"phi_L2_component1(L1a)", phiL2Component1 .a⟩,
  ⟨"phi_L2_component1(L1b)", phiL2Component1 .b⟩,
  ⟨"phi_L2_component1(L1c)", phiL2Component1 .c⟩,
  ⟨"phi_L2_component1(L1d)", phiL2Component1 .d⟩
]

def l2Component2Blocks : List NamedBlock := [
  ⟨"phi_L2_component2(L2a)", phiL2Component2 .a⟩,
  ⟨"phi_L2_component2(L2b)", phiL2Component2 .b⟩,
  ⟨"phi_L2_component2(L2c)", phiL2Component2 .c⟩,
  ⟨"phi_L2_component2(L2d)", phiL2Component2 .d⟩,
  ⟨"phi_L2_component2(L2e)", phiL2Component2 .e⟩,
  ⟨"phi_L2_component2(L2f)", phiL2Component2 .f⟩,
  ⟨"phi_L2_component2(L2g)", phiL2Component2 .g⟩,
  ⟨"phi_L2_component2(L2h)", phiL2Component2 .h⟩,
  ⟨"phi_L2_component2(L2i)", phiL2Component2 .i⟩,
  ⟨"phi_L2_component2(L2j)", phiL2Component2 .j⟩,
  ⟨"phi_L2_component2(L2k)", phiL2Component2 .k⟩,
  ⟨"phi_L2_component2(L2l)", phiL2Component2 .l⟩,
  ⟨"phi_L2_component2(L2m)", phiL2Component2 .m⟩,
  ⟨"phi_L2_component2(L2n)", phiL2Component2 .n⟩,
  ⟨"phi_L2_component2(L2o)", phiL2Component2 .o⟩,
  ⟨"phi_L2_component2(L2p)", phiL2Component2 .p⟩,
  ⟨"phi_L2_component2(L2q)", phiL2Component2 .q⟩,
  ⟨"phi_L2_component2(L2r)", phiL2Component2 .r⟩,
  ⟨"phi_L2_component2(L2s)", phiL2Component2 .s⟩,
  ⟨"phi_L2_component2(L2t)", phiL2Component2 .t⟩
]

def l3Blocks : List NamedBlock := [
  ⟨"phi_L3(L3a)", phiL3 .a⟩,
  ⟨"phi_L3(L3b)", phiL3 .b⟩,
  ⟨"phi_L3(L3c)", phiL3 .c⟩,
  ⟨"phi_L3(L3d)", phiL3 .d⟩,
  ⟨"phi_L3(L3e)", phiL3 .e⟩
]

/-- All Figure 16 substitution blocks whose internal edges should match. -/
def allSubstitutionBlocks : List NamedBlock :=
  ⟨"phi_L1(*)", phiL1Star⟩ ::
    l1Component1Blocks ++ l2Component2Blocks ++ l3Blocks

def allSubstitutionBlocksCompatibleBool : Bool :=
  allSubstitutionBlocks.all NamedBlock.compatibleBool

/-- Finite check that every encoded Figure 16 substitution block is locally valid. -/
theorem allSubstitutionBlocksCompatibleBool_eq_true :
    allSubstitutionBlocksCompatibleBool = true := by
  decide

/-- Proposition-level form of the local Figure 16 compatibility check. -/
theorem compatible_of_mem_allSubstitutionBlocks
    {entry : NamedBlock} (hentry : entry ∈ allSubstitutionBlocks) :
    entry.block.Compatible := by
  have hall := allSubstitutionBlocksCompatibleBool_eq_true
  unfold allSubstitutionBlocksCompatibleBool at hall
  have hentryBool := List.all_eq_true.1 hall entry hentry
  exact Block.compatible_of_compatibleBool hentryBool

theorem phiL1Star_compatible : phiL1Star.Compatible := by
  decide

theorem phiL1Star_validRectangle :
    ValidRectangle phiL1Star.tileSet phiL1Star.rectangle :=
  Block.validRectangle_of_compatible phiL1Star_compatible

theorem phiL1Star_validRectangle_symbolTileSet :
    ValidRectangle Symbol.tileSet phiL1Star.rectangle :=
  Block.validRectangle_symbolTileSet_of_compatible phiL1Star_compatible

theorem phiL1Star_tileableSquare_symbolTileSet :
    TileableSquare Symbol.tileSet 2 :=
  Block.tileableSquare_symbolTileSet_of_compatible phiL1Star_compatible

theorem phiL2Component1_compatible (component : Thin) :
    (phiL2Component1 component).Compatible := by
  cases component <;> decide

theorem phiL2Component1_validRectangle (component : Thin) :
    ValidRectangle (phiL2Component1 component).tileSet
      (phiL2Component1 component).rectangle :=
  Block.validRectangle_of_compatible (phiL2Component1_compatible component)

theorem phiL2Component1_validRectangle_symbolTileSet (component : Thin) :
    ValidRectangle Symbol.tileSet (phiL2Component1 component).rectangle :=
  Block.validRectangle_symbolTileSet_of_compatible
    (phiL2Component1_compatible component)

theorem phiL2Component1_tileableSquare_symbolTileSet (component : Thin) :
    TileableSquare Symbol.tileSet 2 :=
  Block.tileableSquare_symbolTileSet_of_compatible
    (phiL2Component1_compatible component)

theorem phiL2Component2_compatible (component : Thick) :
    (phiL2Component2 component).Compatible := by
  cases component <;> decide

theorem phiL2Component2_validRectangle (component : Thick) :
    ValidRectangle (phiL2Component2 component).tileSet
      (phiL2Component2 component).rectangle :=
  Block.validRectangle_of_compatible (phiL2Component2_compatible component)

theorem phiL2Component2_validRectangle_symbolTileSet (component : Thick) :
    ValidRectangle Symbol.tileSet (phiL2Component2 component).rectangle :=
  Block.validRectangle_symbolTileSet_of_compatible
    (phiL2Component2_compatible component)

theorem phiL2Component2_tileableSquare_symbolTileSet (component : Thick) :
    TileableSquare Symbol.tileSet 2 :=
  Block.tileableSquare_symbolTileSet_of_compatible
    (phiL2Component2_compatible component)

theorem phiL3_compatible (component : Black) :
    (phiL3 component).Compatible := by
  cases component <;> decide

theorem phiL3_validRectangle (component : Black) :
    ValidRectangle (phiL3 component).tileSet (phiL3 component).rectangle :=
  Block.validRectangle_of_compatible (phiL3_compatible component)

theorem phiL3_validRectangle_symbolTileSet (component : Black) :
    ValidRectangle Symbol.tileSet (phiL3 component).rectangle :=
  Block.validRectangle_symbolTileSet_of_compatible (phiL3_compatible component)

theorem phiL3_tileableSquare_symbolTileSet (component : Black) :
    TileableSquare Symbol.tileSet 2 :=
  Block.tileableSquare_symbolTileSet_of_compatible (phiL3_compatible component)

namespace RuleSource

theorem block_compatible (source : RuleSource) : source.block.Compatible := by
  cases source with
  | l1Star =>
      exact phiL1Star_compatible
  | l2Component1 component =>
      exact phiL2Component1_compatible component
  | l2Component2 component =>
      exact phiL2Component2_compatible component
  | l3 component =>
      exact phiL3_compatible component

theorem block_validRectangle_symbolTileSet (source : RuleSource) :
    ValidRectangle Symbol.tileSet source.block.rectangle :=
  Block.validRectangle_symbolTileSet_of_compatible source.block_compatible

theorem block_tileableSquare_symbolTileSet (source : RuleSource) :
    TileableSquare Symbol.tileSet 2 :=
  Block.tileableSquare_symbolTileSet_of_compatible source.block_compatible

end RuleSource

namespace SubstitutionRule

theorem block_eq_source_block {rule : SubstitutionRule}
    (h : rule ∈ substitutionRules) :
    rule.block = rule.source.block := by
  rcases mem_substitutionRules_iff.1 h with ⟨source, _hsource, rfl⟩
  rfl

theorem source_mem_all {rule : SubstitutionRule}
    (h : rule ∈ substitutionRules) :
    rule.source ∈ RuleSource.all := by
  rcases mem_substitutionRules_iff.1 h with ⟨source, hsource, rfl⟩
  simpa using hsource

theorem block_compatible {rule : SubstitutionRule}
    (h : rule ∈ substitutionRules) :
    rule.block.Compatible := by
  rw [block_eq_source_block h]
  exact rule.source.block_compatible

theorem block_validRectangle_symbolTileSet {rule : SubstitutionRule}
    (h : rule ∈ substitutionRules) :
    ValidRectangle Symbol.tileSet rule.block.rectangle := by
  rw [block_eq_source_block h]
  exact rule.source.block_validRectangle_symbolTileSet

theorem block_tileableSquare_symbolTileSet {rule : SubstitutionRule}
    (h : rule ∈ substitutionRules) :
    TileableSquare Symbol.tileSet 2 :=
  ⟨rule.block.rectangle, block_validRectangle_symbolTileSet h⟩

theorem ofSource_mem (source : RuleSource) :
    ofSource source ∈ substitutionRules := by
  simp [substitutionRules, RuleSource.mem_all]

theorem mem_substitutionRules_iff_source_and_block {rule : SubstitutionRule} :
    rule ∈ substitutionRules ↔
      rule.source ∈ RuleSource.all ∧ rule.block = rule.source.block := by
  constructor
  · intro h
    exact ⟨source_mem_all h, block_eq_source_block h⟩
  · rintro ⟨hsource, hblock⟩
    rcases rule with ⟨source, block⟩
    simp only at hsource hblock
    subst block
    exact List.mem_map.2 ⟨source, hsource, rfl⟩

theorem eq_of_mem_same_source {rule other : SubstitutionRule}
    (hrule : rule ∈ substitutionRules) (hother : other ∈ substitutionRules)
    (hsource : rule.source = other.source) :
    rule = other := by
  rcases rule with ⟨ruleSource, ruleBlock⟩
  rcases other with ⟨otherSource, otherBlock⟩
  simp only at hsource
  subst otherSource
  have hruleBlock : ruleBlock = ruleSource.block :=
    block_eq_source_block (rule := ⟨ruleSource, ruleBlock⟩) hrule
  have hotherBlock : otherBlock = ruleSource.block :=
    block_eq_source_block (rule := ⟨ruleSource, otherBlock⟩) hother
  subst ruleBlock
  subst otherBlock
  rfl

theorem eq_of_mem_source {rule : SubstitutionRule}
    (hmem : rule ∈ substitutionRules) {source : RuleSource}
    (hsource : rule.source = source) :
    rule = ofSource source := by
  exact eq_of_mem_same_source hmem (ofSource_mem source) hsource

theorem exists_unique_for_source (source : RuleSource) :
    ∃! rule : SubstitutionRule, rule ∈ substitutionRules ∧ rule.source = source := by
  refine ⟨ofSource source, ⟨ofSource_mem source, rfl⟩, ?_⟩
  intro rule hrule
  exact eq_of_mem_source hrule.1 hrule.2

end SubstitutionRule

/--
The certified finite Figure 16 substitution table.

This packages the human Figure 16 transcription as the Lean object later
scaffold arguments should consume: the listed source rules are complete and
nonduplicated, and every expansion is a valid `2 × 2` Wang rectangle over the
shared component-symbol tileset.
-/
structure CertifiedSubstitutionTable where
  rules : List SubstitutionRule
  complete : rules.map SubstitutionRule.source = RuleSource.all
  nodupSources : (rules.map SubstitutionRule.source).Nodup
  correct : ∀ {rule : SubstitutionRule}, rule ∈ rules →
    rule.block = rule.source.block
  valid : ∀ {rule : SubstitutionRule}, rule ∈ rules →
    ValidRectangle Symbol.tileSet rule.block.rectangle

namespace CertifiedSubstitutionTable

theorem source_mem_all
    (table : CertifiedSubstitutionTable) {rule : SubstitutionRule}
    (hmem : rule ∈ table.rules) :
    rule.source ∈ RuleSource.all := by
  rw [← table.complete]
  exact List.mem_map.2 ⟨rule, hmem, rfl⟩

theorem source_nodup_on_rules
    (table : CertifiedSubstitutionTable) :
    (table.rules.map SubstitutionRule.source).Nodup :=
  table.nodupSources

theorem block_eq_source_block
    (table : CertifiedSubstitutionTable) {rule : SubstitutionRule}
    (hmem : rule ∈ table.rules) :
    rule.block = rule.source.block :=
  table.correct hmem

theorem exists_rule_for_source
    (table : CertifiedSubstitutionTable) (source : RuleSource) :
    ∃ rule : SubstitutionRule, rule ∈ table.rules ∧ rule.source = source := by
  have hsource : source ∈ table.rules.map SubstitutionRule.source := by
    rw [table.complete]
    exact RuleSource.mem_all source
  rcases List.mem_map.1 hsource with ⟨rule, hmem, hsource⟩
  exact ⟨rule, hmem, hsource⟩

theorem eq_of_mem_same_source
    (table : CertifiedSubstitutionTable) {rule other : SubstitutionRule}
    (hrule : rule ∈ table.rules) (hother : other ∈ table.rules)
    (hsource : rule.source = other.source) :
    rule = other :=
  List.inj_on_of_nodup_map table.nodupSources hrule hother hsource

theorem eq_of_mem_source
    (table : CertifiedSubstitutionTable) {rule : SubstitutionRule}
    (hmem : rule ∈ table.rules) {source : RuleSource}
    (hsource : rule.source = source) :
    rule = (table.exists_rule_for_source source).choose := by
  have hchosen := (table.exists_rule_for_source source).choose_spec
  exact table.eq_of_mem_same_source hmem hchosen.1
    (hsource.trans hchosen.2.symm)

theorem exists_unique_rule_for_source
    (table : CertifiedSubstitutionTable) (source : RuleSource) :
    ∃! rule : SubstitutionRule, rule ∈ table.rules ∧ rule.source = source := by
  rcases table.exists_rule_for_source source with ⟨rule, hmem, hsource⟩
  refine ⟨rule, ⟨hmem, hsource⟩, ?_⟩
  intro other hother
  exact table.eq_of_mem_same_source hother.1 hmem (hother.2.trans hsource.symm)

theorem block_eq_source_block_of_source
    (table : CertifiedSubstitutionTable) {rule : SubstitutionRule}
    (hmem : rule ∈ table.rules) {source : RuleSource}
    (hsource : rule.source = source) :
    rule.block = source.block := by
  rw [table.block_eq_source_block hmem, hsource]

theorem source_block_validRectangle
    (table : CertifiedSubstitutionTable) (source : RuleSource) :
    ValidRectangle Symbol.tileSet source.block.rectangle := by
  rcases table.exists_rule_for_source source with ⟨rule, hmem, hsource⟩
  simpa [table.block_eq_source_block_of_source hmem hsource] using
    table.valid hmem

theorem source_block_tileableSquare
    (table : CertifiedSubstitutionTable) (source : RuleSource) :
    TileableSquare Symbol.tileSet 2 :=
  ⟨source.block.rectangle, table.source_block_validRectangle source⟩

end CertifiedSubstitutionTable

/-- Figure 16 substitution rules with their finite certification. -/
def certifiedSubstitutionTable : CertifiedSubstitutionTable where
  rules := substitutionRules
  complete := substitutionRuleSources_eq_all
  nodupSources := substitutionRuleSources_nodup
  correct := by
    intro rule hmem
    exact SubstitutionRule.block_eq_source_block hmem
  valid := by
    intro rule hmem
    exact SubstitutionRule.block_validRectangle_symbolTileSet hmem

@[simp]
theorem certifiedSubstitutionTable_rules :
    certifiedSubstitutionTable.rules = substitutionRules :=
  rfl

@[simp]
theorem certifiedSubstitutionTable_complete :
    certifiedSubstitutionTable.rules.map SubstitutionRule.source = RuleSource.all :=
  substitutionRuleSources_eq_all

/--
Bundled audit certificate for the human Figure 16 transcription.

The row fields are the literal `2 × 2` blocks from the human transcription.
The final fields expose the finite checks consumed downstream: the substitution
rule table is complete and source-unique, and every listed block has matching
internal Wang edges.
-/
structure HumanTranscriptionCertificate : Prop where
  phiL1Star_row :
    phiL1Star = .mkRows .L1d .L1b .L1a .L1c
  phiL2Component1_a :
    phiL2Component1 .a = .mkRows .G3 .L2b .blank .G2
  phiL2Component1_b :
    phiL2Component1 .b = .mkRows .R3 .L2d .blank .R2
  phiL2Component1_c :
    phiL2Component1 .c = .mkRows .R1 .L2c .blank .G0
  phiL2Component1_d :
    phiL2Component1 .d = .mkRows .G1 .L2a .blank .R0
  phiL2Component2_a :
    phiL2Component2 .a = .mkRows .G2 .blank .L2a .R3
  phiL2Component2_b :
    phiL2Component2 .b = .mkRows .R0 .blank .L2b .R3
  phiL2Component2_c :
    phiL2Component2 .c = .mkRows .R2 .blank .L2c .G3
  phiL2Component2_d :
    phiL2Component2 .d = .mkRows .G0 .blank .L2d .G1
  phiL2Component2_e :
    phiL2Component2 .e = .mkRows .R0 .blank .L2e .R1
  phiL2Component2_f :
    phiL2Component2 .f = .mkRows .R2 .blank .L2f .R1
  phiL2Component2_g :
    phiL2Component2 .g = .mkRows .R2 .blank .L2g .R3
  phiL2Component2_h :
    phiL2Component2 .h = .mkRows .R0 .blank .L2h .R3
  phiL2Component2_i :
    phiL2Component2 .i = .mkRows .G0 .blank .L2i .R3
  phiL2Component2_j :
    phiL2Component2 .j = .mkRows .R0 .blank .L2j .G1
  phiL2Component2_k :
    phiL2Component2 .k = .mkRows .G2 .blank .L2k .R1
  phiL2Component2_l :
    phiL2Component2 .l = .mkRows .R2 .blank .L2l .G3
  phiL2Component2_m :
    phiL2Component2 .m = .mkRows .G0 .blank .L2m .G1
  phiL2Component2_n :
    phiL2Component2 .n = .mkRows .G2 .blank .L2n .G1
  phiL2Component2_o :
    phiL2Component2 .o = .mkRows .G2 .blank .L2o .G3
  phiL2Component2_p :
    phiL2Component2 .p = .mkRows .G0 .blank .L2p .G3
  phiL2Component2_q :
    phiL2Component2 .q = .mkRows .G2 .blank .L2q .R3
  phiL2Component2_r :
    phiL2Component2 .r = .mkRows .R2 .blank .L2r .G1
  phiL2Component2_s :
    phiL2Component2 .s = .mkRows .G0 .blank .L2s .R1
  phiL2Component2_t :
    phiL2Component2 .t = .mkRows .R0 .blank .L2t .G3
  phiL3_a :
    phiL3 .a = .mkRows .L3e .L3a .L3a .L3b
  phiL3_b :
    phiL3 .b = .mkRows .L3d .L3a .L3b .L3b
  phiL3_c :
    phiL3 .c = .mkRows .L3d .L3a .L3c .L3c
  phiL3_d :
    phiL3 .d = .mkRows .L3d .L3a .L3d .L3c
  phiL3_e :
    phiL3 .e = .mkRows .L3e .L3a .L3e .L3c
  sourceTableComplete :
    substitutionRuleSources = RuleSource.all
  sourceTableNodup :
    substitutionRuleSources.Nodup
  allBlocksCompatible :
    allSubstitutionBlocksCompatibleBool = true
  certifiedTableRules :
    certifiedSubstitutionTable.rules = substitutionRules
  certifiedTableComplete :
    certifiedSubstitutionTable.rules.map SubstitutionRule.source =
      RuleSource.all

/-- The checked Figure 16 transcription, including the corrected `L2d` row. -/
theorem humanTranscriptionCertificate :
    HumanTranscriptionCertificate where
  phiL1Star_row := HumanTranscription.phiL1Star_row
  phiL2Component1_a := HumanTranscription.phiL2Component1_a
  phiL2Component1_b := HumanTranscription.phiL2Component1_b
  phiL2Component1_c := HumanTranscription.phiL2Component1_c
  phiL2Component1_d := HumanTranscription.phiL2Component1_d
  phiL2Component2_a := HumanTranscription.phiL2Component2_a
  phiL2Component2_b := HumanTranscription.phiL2Component2_b
  phiL2Component2_c := HumanTranscription.phiL2Component2_c
  phiL2Component2_d := HumanTranscription.phiL2Component2_d
  phiL2Component2_e := HumanTranscription.phiL2Component2_e
  phiL2Component2_f := HumanTranscription.phiL2Component2_f
  phiL2Component2_g := HumanTranscription.phiL2Component2_g
  phiL2Component2_h := HumanTranscription.phiL2Component2_h
  phiL2Component2_i := HumanTranscription.phiL2Component2_i
  phiL2Component2_j := HumanTranscription.phiL2Component2_j
  phiL2Component2_k := HumanTranscription.phiL2Component2_k
  phiL2Component2_l := HumanTranscription.phiL2Component2_l
  phiL2Component2_m := HumanTranscription.phiL2Component2_m
  phiL2Component2_n := HumanTranscription.phiL2Component2_n
  phiL2Component2_o := HumanTranscription.phiL2Component2_o
  phiL2Component2_p := HumanTranscription.phiL2Component2_p
  phiL2Component2_q := HumanTranscription.phiL2Component2_q
  phiL2Component2_r := HumanTranscription.phiL2Component2_r
  phiL2Component2_s := HumanTranscription.phiL2Component2_s
  phiL2Component2_t := HumanTranscription.phiL2Component2_t
  phiL3_a := HumanTranscription.phiL3_a
  phiL3_b := HumanTranscription.phiL3_b
  phiL3_c := HumanTranscription.phiL3_c
  phiL3_d := HumanTranscription.phiL3_d
  phiL3_e := HumanTranscription.phiL3_e
  sourceTableComplete := substitutionRuleSources_eq_all
  sourceTableNodup := substitutionRuleSources_nodup
  allBlocksCompatible := allSubstitutionBlocksCompatibleBool_eq_true
  certifiedTableRules := certifiedSubstitutionTable_rules
  certifiedTableComplete := certifiedSubstitutionTable_complete

end Figure16
end OllingerRobinson
end LeanWang
