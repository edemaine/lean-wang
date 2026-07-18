/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedShiftEmbedding
import LeanWang.Kari.Hooper.CounterControlPositiveGuarding
import LeanWang.Kari.Hooper.CounterControlZeroGuarding

/-!
# Completed decrement-shift continuations

The guarded coordinate and shift modules already expose every stage of a
positive decrement schedule.  This module assembles those stages into the
command-family continuation required by strict guarded escape, and records
the automatic weak monotone consequence for positive arbitrary gaps.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlDecrementShiftContinuation

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGuardedShiftCompletion
open CounterControlResumedShiftCoordinates

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Any selected guarded positive-decrement shift completes at a containing
logical core. -/
theorem foundGuardedParentOutcome_of_decrementShift
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      decrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases
      CounterControlGuardedSearch.GuardedSearch.decrementShift_suffix_of_immortal
        base c hmortal current growth source register ifZero ifPositive hrule
        hcommand himmortal with
    ⟨suffix⟩
  rcases decrementPositiveDirectHandoff base c current growth source register
      ifZero ifPositive hrule suffix with ⟨direct⟩
  rcases
      CounterControlGuardedShiftEmbedding.decrementPositive_foundGuardedParentOutcome
        base c hmortal current himmortal growth source register ifZero
        ifPositive direct with
    ⟨outcome⟩
  exact ⟨outcome⟩

/-- Consumer-facing strict escape form of the guarded decrement-shift
continuation. -/
theorem foundGuardedEscapeOutcome_of_decrementShift
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      decrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases foundGuardedParentOutcome_of_decrementShift base c hmortal current
      growth source register ifZero ifPositive hrule hcommand himmortal with
    ⟨outcome⟩
  exact ⟨.parent outcome⟩

/-- For a positive arbitrary gap, consume one blank cell and reuse the
strict guarded decrement-shift theorem. -/
theorem foundMonotoneGuardedEntryOutcome_of_decrementShift_positive
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (hpositive : 0 < current.distance)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      decrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  let guarded := CounterControlPositiveGuarding.guardedTail current hpositive
  have hselected : guarded.selectedRaw = current.selectedRaw := rfl
  have hcommand' : guarded.selectedRaw ∈
      decrementShiftCommands growth source register := by
    simpa [hselected] using hcommand
  have hfound :=
    CounterControlPositiveGuarding.foundCfg_guardedTail current hpositive
  have himmortalGuarded : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg guarded.current) := by
    simpa [guarded, hfound] using himmortal
  rcases foundGuardedParentOutcome_of_decrementShift base c hmortal guarded
      growth source register ifZero ifPositive hrule hcommand'
      himmortalGuarded with ⟨parent⟩
  exact ⟨CounterControlPositiveGuarding.monotone_of_guardedTail_parent
    current hpositive (by simpa [guarded] using parent)⟩

/-- Every arbitrary decrement shift on an immortal orbit has a weak
monotone guarded-entry continuation.  Positive gaps consume one blank cell;
at distance zero, absence of a collision exit forces the missing guard. -/
theorem foundMonotoneGuardedEntryOutcome_of_decrementShift
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      decrementShiftCommands growth source register)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  by_cases hzero : current.distance = 0
  · rcases decrementShiftPosition_of_mem growth source register
        current.selectedRaw hcommand with ⟨position⟩
    rcases
        CounterControlZeroGuarding.guarded_of_zero_markerShift_noCollision
          base c current hzero
          ⟨growth, source, secondarySearchBase + position.before.length⟩
          position.current .right .left
          (match position.remaining with
            | [] => directRef growth source finishDirectSlot
            | _ :: _ => searchRef growth source
                (secondarySearchBase + position.before.length + 1))
          (some .right) position.raw_eq himmortal with
      ⟨guarded, hcurrent⟩
    have hcommand' : guarded.selectedRaw ∈
        decrementShiftCommands growth source register := by
      simpa only [GuardedSearch.selectedRaw, GenuineSearch.selectedRaw,
        hcurrent] using hcommand
    rcases foundGuardedParentOutcome_of_decrementShift base c hmortal guarded
        growth source register ifZero ifPositive hrule hcommand' (by
          simpa [hcurrent] using himmortal) with
      ⟨parent⟩
    exact ⟨CounterControlZeroGuarding.monotone_of_zero_guardedParent
      current hzero guarded hcurrent parent⟩
  · exact foundMonotoneGuardedEntryOutcome_of_decrementShift_positive
      base c hmortal current (Nat.pos_of_ne_zero hzero) growth source register
      ifZero ifPositive hrule hcommand himmortal

end

end CounterControlDecrementShiftContinuation
end Hooper
end Kari
end LeanWang
