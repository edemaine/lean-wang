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

end Figure16
end OllingerRobinson
end LeanWang
