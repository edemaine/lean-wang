/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenInstructionResolution

/-!
# The unconditional target-free counter-step law

The instruction-resolution layer proves the increment, zero-decrement, and
positive-decrement branches separately.  This file performs the exhaustive
abstract-step case split and packages those branches as the unconditional
`OpenStepContinuesOrHalts` law required by canonical open mortality.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenStepLaw

open Turing CounterMachine
open CounterControlOpenInstructionResolution

noncomputable section

/-- Every defined counter-program step on a tag-free open core either reaches
its exact next open logical configuration or exposes a concrete halt. -/
theorem openStepContinuesOrHalts (base : Nat) (c : Nat.Partrec.Code) :
    CounterControlCanonicalOpenMortality.OpenStepContinuesOrHalts base c := by
  intro growth current next concrete hstep hlogical
  have hcase := CounterControlStepGeometry.stepCase_of_step_eq_some hstep
  cases hcase with
  | increment register target hlookup hnext =>
      exact openStepContinuesOrHalts_of_increment base c hstep register target
        hlookup hnext hlogical
  | decrementZero register ifZero ifPositive hlookup hzero hnext =>
      exact openStepContinuesOrHalts_of_decrementZero base c hstep register
        ifZero ifPositive hlookup hzero hnext hlogical
  | decrementPositive register ifZero ifPositive hlookup hpositive hnext =>
      exact openStepContinuesOrHalts_of_decrementPositive base c hstep register
        ifZero ifPositive hlookup hpositive hnext hlogical

/-- A source code outside `FixedNonhalting` makes the genuine canonical open
configuration of the complete controller halt. -/
theorem not_fixedNonhalting_canonicalOpen_halts
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      (CounterControlOpenSimulation.canonicalOpenCfg base c) := by
  exact
    CounterControlCanonicalOpenMortality.not_fixedNonhalting_canonicalOpen_halts_of_openStep
      base c hmortal (openStepContinuesOrHalts base c)

end

end CounterControlOpenStepLaw
end Hooper
end Kari
end LeanWang
