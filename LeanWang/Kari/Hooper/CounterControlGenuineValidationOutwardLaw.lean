/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardSuffix
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardIncrement
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardIncrementCollision
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardDecrementSuffix

/-!
# Complete outward-validation handoff law

This module combines the instruction-specific continuation theorems for an
arbitrary outward validation suffix.  It is the final operational law needed
by the concrete Kari--Hooper reduction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardLaw

open CounterControlGenuineValidationOutwardIncrementCollision

noncomputable section

/-- Every live outward validation suffix either reconstructs a logical core
or hands control to a later guarded search. -/
theorem outwardInstructionHandoffLaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    CounterControlGenuineValidation.OutwardInstructionHandoffLaw
      base c hmortal := by
  intro current growth source instruction hrule obligation himmortal
  cases instruction with
  | increment register next =>
      rcases CounterControlGenuineValidationOutwardSuffix.suffix obligation with
        ⟨suffix⟩
      by_cases hoccupied :
          CounterControlExactCommandContinuation.ShiftDestinationOccupied
            (CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw
              growth source register)
            suffix.progress.suffix.finish
      · exact
          handoff_of_firstIncrementCollision base c hmortal suffix hrule
            hoccupied himmortal
      · have hblank :
            (suffix.progress.suffix.finish.move
              (CounterControlPlan.orient growth .right)).read =
                BoundedMarkerProgram.blankSymbol := by
          cases growth <;>
            simp [CounterControlExactCommandContinuation.ShiftDestinationOccupied,
              CounterControlGenuineValidationOutwardIncrement.firstIncrementRaw,
              CounterControlPlan.orient, FullTM0.Tape.read,
              FullTM0.Tape.move, FullTM0.Tape.write] at hoccupied ⊢
          all_goals exact hoccupied
        rcases
            CounterControlGenuineValidationOutwardIncrement.outwardSuffix_incrementSuccess_logical
              (base := base) (c := c) (hmortal := hmortal)
              (suffix := suffix) (hrule := hrule) (hblank := hblank)
              (himmortal := himmortal) with
          ⟨core, hreaches, hinside⟩
        exact ⟨.logical core hreaches (Nat.le_of_lt hinside)⟩
  | decrement register ifZero ifPositive =>
      exact
        CounterControlGenuineValidationOutwardDecrementSuffix.outwardDecrement_handoff
          base c hmortal current growth source register ifZero ifPositive
          hrule obligation himmortal

end

end CounterControlGenuineValidationOutwardLaw
end Hooper
end Kari
end LeanWang
