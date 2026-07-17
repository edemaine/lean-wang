/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Figure16
import LeanWang.Robinson.Closed104.TileSubdivision

/-!
Direct component data for the corrected 104-tile Ollinger/Robinson alphabet.

The list is the Lean representation of
[figures/fig13-human.tsv](../../../figures/fig13-human.tsv), whose component labels are
shown in
[figures/figure16-layer-components.png](../../../figures/figure16-layer-components.png).
The Figure 16 substitutions come from the human transcription retained in
[figures/fig16-human.txt](../../../figures/fig16-human.txt).
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104

/-- A complete thin/thick/black component triple for one tile. -/
abbrev Components := Figure16.Thin × Figure16.Thick × Figure16.Black

/-- West/east coordinate of a quadrant inside a Figure 16 block. -/
def quadrantColumn : Quadrant → Fin 2
  | .southwest => ⟨0, by decide⟩
  | .southeast => ⟨1, by decide⟩
  | .northwest => ⟨0, by decide⟩
  | .northeast => ⟨1, by decide⟩

/-- South/north coordinate of a quadrant inside a Figure 16 block. -/
def quadrantRow : Quadrant → Fin 2
  | .southwest => ⟨0, by decide⟩
  | .southeast => ⟨0, by decide⟩
  | .northwest => ⟨1, by decide⟩
  | .northeast => ⟨1, by decide⟩

/-- Quadrant selected by a west/east and south/north offset. -/
def quadrantOfOffset (di dj : Fin 2) : Quadrant :=
  if dj.val = 0 then
    if di.val = 0 then .southwest else .southeast
  else
    if di.val = 0 then .northwest else .northeast

/-- Does a pair of L2 summand symbols overlay to the requested thick component? -/
def thickOverlayBool
    (first second : Figure16.Symbol) (target : Figure16.Thick) : Bool :=
  match first, second with
  | .blank, .thick component => decide (component = target)
  | .thick component, .blank => decide (component = target)
  | .line firstLine, .line secondLine =>
      match target.lineSum? with
      | none => false
      | some sum =>
          decide ((sum.first = firstLine ∧ sum.second = secondLine) ∨
            (sum.first = secondLine ∧ sum.second = firstLine))
  | _, _ => false

/-- Does `child` equal the component triple produced at one parent quadrant? -/
def componentTripleChildMatchesBool
    (parent : Components) (quadrant : Quadrant) (child : Components) : Bool :=
  decide (Figure16.Symbol.thin child.1 =
    Figure16.phiL1Star.entry (quadrantColumn quadrant) (quadrantRow quadrant)) &&
  thickOverlayBool
    ((Figure16.phiL2Component1 parent.1).entry
      (quadrantColumn quadrant) (quadrantRow quadrant))
    ((Figure16.phiL2Component2 parent.2.1).entry
      (quadrantColumn quadrant) (quadrantRow quadrant))
    child.2.1 &&
  decide (Figure16.Symbol.black child.2.2 =
    (Figure16.phiL3 parent.2.2).entry
      (quadrantColumn quadrant) (quadrantRow quadrant))

/-- The corrected Figure 13 component alphabet, in tile-index order. -/
def alphabet : List Components := [
  (.a, .b, .a), -- 0
  (.a, .c, .a), -- 1
  (.a, .a, .a), -- 2
  (.a, .d, .a), -- 3
  (.b, .b, .a), -- 4
  (.b, .c, .a), -- 5
  (.b, .a, .a), -- 6
  (.b, .d, .a), -- 7
  (.c, .m, .b), -- 8
  (.c, .m, .c), -- 9
  (.c, .i, .b), -- 10
  (.c, .i, .c), -- 11
  (.c, .t, .c), -- 12
  (.c, .e, .c), -- 13
  (.c, .j, .c), -- 14
  (.c, .h, .c), -- 15
  (.c, .l, .b), -- 16
  (.c, .f, .b), -- 17
  (.c, .r, .b), -- 18
  (.c, .g, .b), -- 19
  (.c, .o, .b), -- 20
  (.c, .o, .c), -- 21
  (.c, .k, .b), -- 22
  (.c, .k, .c), -- 23
  (.c, .n, .b), -- 24
  (.c, .n, .c), -- 25
  (.c, .q, .b), -- 26
  (.c, .q, .c), -- 27
  (.c, .p, .b), -- 28
  (.c, .p, .c), -- 29
  (.c, .s, .b), -- 30
  (.c, .s, .c), -- 31
  (.a, .m, .b), -- 32
  (.a, .m, .c), -- 33
  (.a, .i, .b), -- 34
  (.a, .i, .c), -- 35
  (.a, .t, .c), -- 36
  (.a, .e, .c), -- 37
  (.a, .j, .c), -- 38
  (.a, .h, .c), -- 39
  (.a, .l, .b), -- 40
  (.a, .f, .b), -- 41
  (.a, .r, .b), -- 42
  (.a, .g, .b), -- 43
  (.a, .o, .b), -- 44
  (.a, .o, .c), -- 45
  (.a, .k, .b), -- 46
  (.a, .k, .c), -- 47
  (.a, .n, .b), -- 48
  (.a, .n, .c), -- 49
  (.a, .q, .b), -- 50
  (.a, .q, .c), -- 51
  (.a, .p, .b), -- 52
  (.a, .p, .c), -- 53
  (.a, .s, .b), -- 54
  (.a, .s, .c), -- 55
  (.d, .t, .d), -- 56
  (.d, .t, .e), -- 57
  (.d, .e, .d), -- 58
  (.d, .j, .d), -- 59
  (.d, .j, .e), -- 60
  (.d, .h, .e), -- 61
  (.d, .l, .d), -- 62
  (.d, .l, .e), -- 63
  (.d, .f, .d), -- 64
  (.d, .r, .d), -- 65
  (.d, .r, .e), -- 66
  (.d, .g, .e), -- 67
  (.d, .o, .d), -- 68
  (.d, .o, .e), -- 69
  (.d, .k, .d), -- 70
  (.d, .n, .d), -- 71
  (.d, .n, .e), -- 72
  (.d, .q, .e), -- 73
  (.d, .p, .d), -- 74
  (.d, .p, .e), -- 75
  (.d, .s, .d), -- 76
  (.d, .m, .d), -- 77
  (.d, .m, .e), -- 78
  (.d, .i, .e), -- 79
  (.a, .t, .d), -- 80
  (.a, .t, .e), -- 81
  (.a, .e, .d), -- 82
  (.a, .j, .d), -- 83
  (.a, .j, .e), -- 84
  (.a, .h, .e), -- 85
  (.a, .l, .d), -- 86
  (.a, .l, .e), -- 87
  (.a, .f, .d), -- 88
  (.a, .r, .d), -- 89
  (.a, .r, .e), -- 90
  (.a, .g, .e), -- 91
  (.a, .o, .d), -- 92
  (.a, .o, .e), -- 93
  (.a, .k, .d), -- 94
  (.a, .n, .d), -- 95
  (.a, .n, .e), -- 96
  (.a, .q, .e), -- 97
  (.a, .p, .d), -- 98
  (.a, .p, .e), -- 99
  (.a, .s, .d), -- 100
  (.a, .m, .d), -- 101
  (.a, .m, .e), -- 102
  (.a, .i, .e) -- 103
]

end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
