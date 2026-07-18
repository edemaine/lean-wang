/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Figure16

/-!
# Figure 16 transcription audit

This standalone module checks the human transcription recorded in
`figures/fig16-human.txt`. The active Robinson proof imports only
`Figure16.lean`; this file gives each component symbol a symbolic Wang-tile
interpretation and checks every displayed `2 x 2` substitution block locally.

The colors below are seam equivalence classes induced by Figure 16, not the
edge-color identifiers of the final 104-tile alphabet.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure16

namespace Thick

def hasLineSum (component : Thick) : Prop :=
  component.lineSum?.isSome

instance (component : Thick) : Decidable component.hasLineSum := by
  unfold hasLineSum
  infer_instance

/-- Exactly the sixteen non-corner thick components are two-line sums. -/
def lineSumComponents : List Thick :=
  [.e, .f, .g, .h, .i, .j, .k, .l, .m, .n, .o, .p, .q, .r, .s, .t]

theorem all_filter_hasLineSum :
    Thick.all.filter Thick.hasLineSum = lineSumComponents := by
  decide

@[simp]
theorem lineSumComponents_length : lineSumComponents.length = 16 := by
  decide

/-- The line atoms recorded by `lineSum?` are exactly those displayed around
the corresponding component in the second `phi_L2` summand. -/
theorem phiL2Component2_eq_lineSum
    {component : Thick} {sum : ThickLineSum}
    (h : component.lineSum? = some sum) :
    phiL2Component2 component =
      .mkRows (.line sum.first) .blank (.thick component) (.line sum.second) := by
  cases component <;>
    simp [lineSum?, ThickLineSum.mkDistinct] at h
  all_goals
    subst sum
    rfl

end Thick

namespace Symbol

private def t (n s e w : Nat) : WangTile := ⟨n, s, e, w⟩

/-- Symbolic Wang-tile edges for the Figure 16 component seams. -/
def tile : Symbol → WangTile
  | .blank => t 0 1 2 3
  | .thin .a => t 4 5 6 7
  | .thin .b => t 8 9 10 11
  | .thin .c => t 9 12 13 6
  | .thin .d => t 14 4 11 15
  | .thick .a => t 16 17 18 19
  | .thick .b => t 20 21 32 22
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

end Symbol

namespace Block

/-- Internal Wang-edge compatibility of a displayed `2 x 2` block. -/
def Compatible (block : Block) : Prop :=
  WangTile.HMatches (Symbol.tile block.northwest) (Symbol.tile block.northeast) ∧
  WangTile.HMatches (Symbol.tile block.southwest) (Symbol.tile block.southeast) ∧
  WangTile.VMatches (Symbol.tile block.southwest) (Symbol.tile block.northwest) ∧
  WangTile.VMatches (Symbol.tile block.southeast) (Symbol.tile block.northeast)

instance (block : Block) : Decidable block.Compatible := by
  unfold Compatible
  infer_instance

end Block

set_option linter.style.nativeDecide false in
theorem phiL1Star_compatible : phiL1Star.Compatible := by
  native_decide

set_option linter.style.nativeDecide false in
theorem phiL2Component1_compatible (component : Thin) :
    (phiL2Component1 component).Compatible := by
  cases component <;> native_decide

set_option linter.style.nativeDecide false in
theorem phiL2Component2_compatible (component : Thick) :
    (phiL2Component2 component).Compatible := by
  cases component <;> native_decide

set_option linter.style.nativeDecide false in
theorem phiL3_compatible (component : Black) :
    (phiL3 component).Compatible := by
  cases component <;> native_decide

/-- One proposition-level certificate covering every block in the human
Figure 16 transcription. -/
theorem allTranscribedBlocksCompatible :
    phiL1Star.Compatible ∧
    (∀ component : Thin, (phiL2Component1 component).Compatible) ∧
    (∀ component : Thick, (phiL2Component2 component).Compatible) ∧
    (∀ component : Black, (phiL3 component).Compatible) :=
  ⟨phiL1Star_compatible, phiL2Component1_compatible,
    phiL2Component2_compatible, phiL3_compatible⟩

end Figure16
end OllingerRobinson
end LeanWang
