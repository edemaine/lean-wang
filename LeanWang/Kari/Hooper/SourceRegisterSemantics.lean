/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SourceControl

/-!
# Designated source computation in register semantics

`SourceControl.registerStep` is the high-level specification implemented by
the four-register counter program.  This file identifies its canonical start
and proves that its infinite run is exactly the fixed-input nonhalting problem.
The proof first commutes every finite iterate with decoding to Mathlib's source
machine, then uses the already verified finite-support/full-tape bridge.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace SourceRegisterSemantics

open Turing

noncomputable section

/-- Canonical high-level register configuration for source code `c`. -/
def canonical (c : Nat.Partrec.Code) : SourceControl.RegisterCfg :=
  ⟨(SourceMachine.canonical c).q, StackEncoding.sourceInitialRegisters c⟩

/-- Decoding the canonical register tuple gives the ordinary finite-support
configuration whose full-tape image is `SourceMachine.canonical c`. -/
theorem ofMathlib_decode_canonical (c : Nat.Partrec.Code) :
    FullTM0.Cfg.ofMathlib (canonical c).decode =
      SourceMachine.canonical c := by
  apply congrArg₂ FullTM0.Cfg.mk
  · rfl
  · exact StackEncoding.fullTape_sourceInitialRegisters c

/-- Decoding commutes with every finite high-level register iterate. -/
theorem iterate_decode (n : Nat) (cfg : SourceControl.RegisterCfg) :
    (Dynamics.iterate SourceControl.registerStep n cfg).map
        SourceControl.RegisterCfg.decode =
      Dynamics.iterate (Turing.TM0.step SourceMachine.machine) n cfg.decode := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Dynamics.iterate_succ, Dynamics.iterate_succ]
      rw [← ih]
      cases hiterate : Dynamics.iterate SourceControl.registerStep n cfg with
      | none => simp
      | some current =>
          simpa [hiterate] using SourceControl.decode_registerStep current

/-- A high-level register computation survives `n` steps exactly when its
decoded source computation survives `n` steps. -/
theorem survives_iff (cfg : SourceControl.RegisterCfg) (n : Nat) :
    Dynamics.Survives SourceControl.registerStep cfg n ↔
      Dynamics.Survives (Turing.TM0.step SourceMachine.machine)
        cfg.decode n := by
  constructor
  · rintro ⟨next, hnext⟩
    refine ⟨next.decode, ?_⟩
    have h := iterate_decode n cfg
    simpa [hnext] using h.symm
  · rintro ⟨next, hnext⟩
    cases hregister : Dynamics.iterate SourceControl.registerStep n cfg with
    | none =>
        have h := iterate_decode n cfg
        rw [hregister] at h
        simp only [Option.map_none] at h
        rw [← h] at hnext
        simp at hnext
    | some registerNext => exact ⟨registerNext, hregister⟩

/-- Immortality of the register specification is exactly immortality of its
decoded finite-support source configuration. -/
theorem immortalFrom_iff (cfg : SourceControl.RegisterCfg) :
    Dynamics.ImmortalFrom SourceControl.registerStep cfg ↔
      Dynamics.ImmortalFrom (Turing.TM0.step SourceMachine.machine)
        cfg.decode := by
  simp only [Dynamics.ImmortalFrom]
  exact forall_congr' (survives_iff cfg)

/-- The designated register computation is immortal exactly for a code in
the fixed nonhalting language. -/
theorem fixedNonhalting_iff_immortalFrom (c : Nat.Partrec.Code) :
    DominoProblem.FixedNonhalting c ↔
      Dynamics.ImmortalFrom SourceControl.registerStep (canonical c) := by
  rw [SourceMachine.fixedNonhalting_iff_immortalFrom]
  rw [immortalFrom_iff]
  rw [FullTM0.immortalFrom_step_ofMathlib_iff]
  rw [ofMathlib_decode_canonical]

end

end SourceRegisterSemantics
end Hooper
end Kari
end LeanWang
