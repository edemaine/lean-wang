/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidation
import LeanWang.Kari.Hooper.CounterControlGuardedParentSearch

/-!
# Validation-family continuation interface

The instruction-wide outward handoff is the only validation-specific
operational law.  It supplies the arbitrary monotone continuation directly.
Viewing a guarded caller from its parent cell then supplies the strict guarded
continuation from the very same theorem.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlValidationContinuation

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An instruction-wide outward handoff law discharges the arbitrary
validation-family continuation. -/
theorem foundMonotoneGuardedEntryOutcome_of_validation
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (houtward : CounterControlGenuineValidation.OutwardInstructionHandoffLaw
      base c hmortal)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  apply CounterControlGenuineValidation.validationContinuation_of_outwardLaw
    base c hmortal
    (CounterControlGenuineValidation.outwardContinuationLaw_of_instructionHandoffLaw
      base c hmortal houtward)
    current growth source instruction hrule hcommand himmortal

/-- The same arbitrary validation theorem, applied one cell farther back,
gives the strict guarded validation-family continuation. -/
theorem foundGuardedEscapeOutcome_of_validation
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (houtward : CounterControlGenuineValidation.OutwardInstructionHandoffLaw
      base c hmortal)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  let parent := CounterControlGuardedParentSearch.parentSearch current
  have hcommand' : parent.selectedRaw ∈
      validationCommands growth source instruction := by
    simpa [parent] using hcommand
  have himmortal' : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg parent) := by
    simpa [parent] using himmortal
  apply
    CounterControlGuardedParentSearch.foundGuardedEscapeOutcome_of_parentMonotone
      current
  exact foundMonotoneGuardedEntryOutcome_of_validation base c hmortal
    houtward parent growth source instruction hrule hcommand' himmortal'

end

end CounterControlValidationContinuation
end Hooper
end Kari
end LeanWang
