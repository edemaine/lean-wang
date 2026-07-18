/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFamilyAssembly
import LeanWang.Kari.Hooper.CounterControlValidationContinuation
import LeanWang.Kari.Hooper.CounterControlIncrementShiftContinuation
import LeanWang.Kari.Hooper.CounterControlDecrementEntryContinuation
import LeanWang.Kari.Hooper.CounterControlDecrementShiftContinuation

/-!
# Concrete command-family assembly

All command families except outward validation are discharged by their
specialized continuation modules.  Supplying the single instruction-wide
outward handoff law therefore constructs both the arbitrary monotone and the
strict guarded family records, and hence the two local converse laws.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlConcreteFamilies

noncomputable section

/-- Assemble all eight concrete family fields from the one remaining
validation-specific outward law. -/
theorem families_of_outwardLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (houtward : CounterControlGenuineValidation.OutwardInstructionHandoffLaw
      base c hmortal) :
    CounterControlFamilyAssembly.Families base c hmortal := by
  refine ⟨?_, ?_⟩
  · refine
      { validation := ?_
        incrementShift := ?_
        decrementEntry := ?_
        decrementShift := ?_ }
    · exact
        CounterControlValidationContinuation.foundMonotoneGuardedEntryOutcome_of_validation
          base c hmortal houtward
    · exact
        CounterControlIncrementShiftContinuation.foundMonotoneGuardedEntryOutcome_of_incrementShift
          base c hmortal
    · exact
        CounterControlDecrementEntryContinuation.foundMonotoneGuardedEntryOutcome_of_decrementEntry
          base c hmortal
    · exact
        CounterControlDecrementShiftContinuation.foundMonotoneGuardedEntryOutcome_of_decrementShift
          base c hmortal
  · refine
      { validation := ?_
        incrementShift := ?_
        decrementEntry := ?_
        decrementShift := ?_ }
    · exact
        CounterControlValidationContinuation.foundGuardedEscapeOutcome_of_validation
          base c hmortal houtward
    · intro current growth source register next hrule hcommand himmortal
      exact
        CounterControlGuardedIncrementEmbedding.incrementShift_foundGuardedEscapeOutcome
          base c hmortal current himmortal growth source register next hrule
          hcommand
    · exact
        CounterControlDecrementEntryContinuation.foundGuardedEscapeOutcome_of_decrementEntry
          base c hmortal
    · exact
        CounterControlDecrementShiftContinuation.foundGuardedEscapeOutcome_of_decrementShift
          base c hmortal

/-- A mortality-indexed outward handoff law supplies the complete local
guarded converse laws. -/
theorem laws_of_outwardLaws
    (base : Nat) (c : Nat.Partrec.Code)
    (houtward : ∀ hmortal : ¬ DominoProblem.FixedNonhalting c,
      CounterControlGenuineValidation.OutwardInstructionHandoffLaw
        base c hmortal) :
    CounterControlGuardedConverse.Laws base c := by
  apply CounterControlFamilyAssembly.laws_of_families base c
  intro hmortal
  exact families_of_outwardLaw base c hmortal (houtward hmortal)

end

end CounterControlConcreteFamilies
end Hooper
end Kari
end LeanWang
