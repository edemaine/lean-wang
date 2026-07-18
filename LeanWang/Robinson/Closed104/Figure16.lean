/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
Figure 16 substitution data for the Ollinger/Robinson scaffold.

The labels here match the reference image
[figures/figure16-layer-components.png](../../../figures/figure16-layer-components.png).
This file records the component symbols and the human transcription of the
three layer substitutions.  Standalone compatibility and transcription checks
are retained in `Figure16Audit.lean` outside the active proof graph.

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


end Thick

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


/-- Read a block entry by rectangle coordinates: `i = 0` is west, `j = 0` is south. -/
def entry (B : Block) (i j : Fin 2) : Symbol :=
  if j.val = 0 then
    if i.val = 0 then B.southwest else B.southeast
  else
    if i.val = 0 then B.northwest else B.northeast


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
  | .b => .mkRows .R0 .blank .L2b .R1
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


/-- `phi_L3`, applied to a black-layer component. -/
def phiL3 : Black → Block
  | .a => .mkRows .L3e .L3a .L3a .L3b
  | .b => .mkRows .L3d .L3a .L3b .L3b
  | .c => .mkRows .L3d .L3a .L3c .L3c
  | .d => .mkRows .L3d .L3a .L3d .L3c
  | .e => .mkRows .L3e .L3a .L3e .L3c

end Figure16
end OllingerRobinson
end LeanWang
