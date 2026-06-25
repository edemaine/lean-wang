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
deriving DecidableEq, Repr

namespace Thick

def all : List Thick := [
  .a, .b, .c, .d,
  .e, .f, .g, .h,
  .i, .j, .k, .l,
  .m, .n, .o, .p
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

end Symbol

namespace Thick

/--
The `L2e`-`L2p` components are sums of two distinct thick-line atoms.

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

end Block

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
      Symbol.L2l, Symbol.L2m, Symbol.L2n, Symbol.L2o, Symbol.L2p] at h ⊢

end Thick

/-- `phi_L3`, applied to a black-layer component. -/
def phiL3 : Black → Block
  | .a => .mkRows .L3e .L3a .L3a .L3b
  | .b => .mkRows .L3d .L3a .L3b .L3b
  | .c => .mkRows .L3d .L3a .L3c .L3c
  | .d => .mkRows .L3d .L3a .L3d .L3c
  | .e => .mkRows .L3e .L3a .L3e .L3c

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
  ⟨"phi_L2_component2(L2p)", phiL2Component2 .p⟩
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

theorem phiL2Component1_compatible (component : Thin) :
    (phiL2Component1 component).Compatible := by
  cases component <;> decide

theorem phiL2Component2_compatible (component : Thick) :
    (phiL2Component2 component).Compatible := by
  cases component <;> decide

theorem phiL3_compatible (component : Black) :
    (phiL3 component).Compatible := by
  cases component <;> decide

end Figure16
end OllingerRobinson
end LeanWang
