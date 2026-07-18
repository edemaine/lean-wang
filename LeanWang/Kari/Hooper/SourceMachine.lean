/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.DominoProblem
import LeanWang.Kari.Hooper.FiniteControl
import LeanWang.UniversalTM0.Semantic

/-!
# The fixed source machine for Hooper's construction

The universal evaluator in `LeanWang.UniversalTM0.Semantic` is one fixed
Mathlib `TM0` machine whose varying finite tape input encodes a
`Nat.Partrec.Code`.  Its ambient label type is infinite, although the fixed
machine has a finite transition-closed support.

This file restricts that machine to its support, embeds its ordinary input tape
into the unrestricted full-tape semantics, and proves the exact designated-run
endpoint needed by Hooper: `DominoProblem.FixedNonhalting c` is equivalent to
immortality from the canonical configuration for `c`.
-/

noncomputable section

namespace LeanWang
namespace Kari
namespace Hooper
namespace SourceMachine

open Turing

/-- Tape alphabet of the fixed universal evaluator after Mathlib's TM2-to-TM1
translation. -/
abbrev Alphabet :=
  Turing.TM2to1.Γ' UniversalTM0Semantic.Stack
    UniversalTM0Semantic.StackSymbol

instance : Fintype Alphabet :=
  inferInstance

instance : DecidableEq Alphabet :=
  Classical.decEq Alphabet

/-- Ambient label type produced by Mathlib's TM1-to-TM0 translation. -/
abbrev AmbientState :=
  Turing.TM1to0.Λ' UniversalTM0Semantic.tm1

instance : DecidableEq AmbientState :=
  Classical.decEq AmbientState

/-- The universal evaluator packaged with its fixed finite support. -/
def supported : SupportedMachine Alphabet AmbientState where
  machine := UniversalTM0Semantic.tm0
  states := UniversalTM0Semantic.tm0Support
  supports := UniversalTM0Semantic.tm0_supports

/-- The actual finite state type used for the source machine. -/
abbrev State := supported.State

/-- One fixed universal source machine with genuinely finite control. -/
def machine : Turing.TM0.Machine Alphabet State :=
  supported.restrict

/-- The ordinary Mathlib initial configuration for source program `c`. -/
def ambientInitial (c : Nat.Partrec.Code) : Turing.TM0.Cfg Alphabet AmbientState :=
  Turing.TM0.init (UniversalTM0Semantic.input c)

/-- The same initial configuration in unrestricted full-tape semantics. -/
def ambientCanonical (c : Nat.Partrec.Code) : FullTM0.Cfg Alphabet AmbientState :=
  FullTM0.Cfg.ofMathlib (ambientInitial c)

theorem ambientCanonical_supported (c : Nat.Partrec.Code) :
    (ambientCanonical c).q ∈ supported.states := by
  exact supported.supports.1

/-- Canonical full-tape configuration of the finite-control source machine. -/
def canonical (c : Nat.Partrec.Code) : FullTM0.Cfg Alphabet State :=
  supported.liftCfg (ambientCanonical c) (ambientCanonical_supported c)

/-- The canonical source control state is fixed; only its tape depends on the
program code. -/
@[simp]
theorem canonical_q (c : Nat.Partrec.Code) :
    (canonical c).q = (default : State) := by
  apply Subtype.ext
  rfl

@[simp]
theorem forget_canonical (c : Nat.Partrec.Code) :
    supported.forgetCfg (canonical c) = ambientCanonical c :=
  supported.forgetCfg_liftCfg _ _

private theorem tm0_eval_dom_iff_step_eval_dom (c : Nat.Partrec.Code) :
    (Turing.TM0.eval UniversalTM0Semantic.tm0
      (UniversalTM0Semantic.input c)).Dom ↔
      (StateTransition.eval (Turing.TM0.step UniversalTM0Semantic.tm0)
        (ambientInitial c)).Dom := by
  rfl

/-- Fixed-input nonhalting is exactly immortality of the designated source
configuration.  This theorem concerns one canonical start; Hooper's later
compiler turns it into existence of an arbitrary immortal configuration. -/
theorem fixedNonhalting_iff_immortalFrom (c : Nat.Partrec.Code) :
    DominoProblem.FixedNonhalting c ↔
      FullTM0.ImmortalFrom machine (canonical c) := by
  have huniversal := UniversalTM0Semantic.tm0_eval_dom_iff c
  have hfinite :
      ¬ (Turing.TM0.eval UniversalTM0Semantic.tm0
        (UniversalTM0Semantic.input c)).Dom ↔
        Dynamics.ImmortalFrom (Turing.TM0.step UniversalTM0Semantic.tm0)
          (ambientInitial c) := by
    rw [tm0_eval_dom_iff_step_eval_dom]
    exact Dynamics.not_eval_dom_iff_immortalFrom _ _
  have hfull :
      Dynamics.ImmortalFrom (Turing.TM0.step UniversalTM0Semantic.tm0)
          (ambientInitial c) ↔
        FullTM0.ImmortalFrom UniversalTM0Semantic.tm0
          (ambientCanonical c) := by
    exact FullTM0.immortalFrom_step_ofMathlib_iff _ _
  have hrestricted :
      FullTM0.ImmortalFrom machine (canonical c) ↔
        FullTM0.ImmortalFrom UniversalTM0Semantic.tm0
          (ambientCanonical c) := by
    have h := supported.immortalFrom_forgetCfg_iff (canonical c)
    rw [forget_canonical] at h
    change FullTM0.ImmortalFrom supported.restrict (canonical c) ↔
      FullTM0.ImmortalFrom UniversalTM0Semantic.tm0 (ambientCanonical c)
    exact h
  rw [DominoProblem.FixedNonhalting]
  exact (not_congr huniversal.symm).trans
    (hfinite.trans (hfull.trans hrestricted.symm))

end SourceMachine
end Hooper
end Kari
end LeanWang
