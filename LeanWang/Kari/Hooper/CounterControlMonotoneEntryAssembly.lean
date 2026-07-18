/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineFoundClassification
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedCleanupProgress

/-!
# Assembly of monotone guarded entry

For an arbitrary genuine generated search, both recovery-route families
reach a containing logical core and collision cleanup reaches a larger
guarded search.  This file isolates the four remaining specialized families
and assembles all seven cases into the `MonotoneGuardedEntryLaw` used by the
alternating global unnesting argument.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlMonotoneEntryAssembly

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGenuineFoundClassification

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Specialized monotone continuations for validation and the three
non-recovery instruction-body families. -/
structure FamilyContinuations
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) : Prop where
  validation : ∀
      (current : GenuineSearch base c)
      (growth : Turing.Dir) (source : Nat)
      (instruction : CounterMachine.Instruction)
      (rule_mem : (source, instruction) ∈ GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        validationCommands growth source instruction),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current) →
        Nonempty (FoundMonotoneGuardedEntryOutcome current)
  incrementShift : ∀
      (current : GenuineSearch base c)
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        incrementShiftCommands growth source register),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current) →
        Nonempty (FoundMonotoneGuardedEntryOutcome current)
  decrementEntry : ∀
      (current : GenuineSearch base c)
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
          (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register)),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current) →
        Nonempty (FoundMonotoneGuardedEntryOutcome current)
  decrementShift : ∀
      (current : GenuineSearch base c)
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        decrementShiftCommands growth source register),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current) →
        Nonempty (FoundMonotoneGuardedEntryOutcome current)

/-- Common recovery and cleanup geometry plus the four specialized family
continuations discharge every arbitrary genuine found state. -/
theorem foundContinuation_of_families
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (families : FamilyContinuations base c hmortal)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  rcases classify_found current with ⟨outcome⟩
  cases outcome with
  | validation growth source instruction hrule hcommand =>
      exact families.validation current growth source instruction hrule
        hcommand himmortal
  | incrementShift growth source register next hrule hcommand =>
      exact families.incrementShift current growth source register next hrule
        hcommand himmortal
  | incrementRecovery growth source register next hrule hcommand =>
      exact
        CounterControlGenuineRouteEmbedding.incrementRecovery_logical_of_rule
          base c hmortal current himmortal growth source register next hrule
          hcommand
  | cleanup growth source register next hrule hcommand =>
      exact
        CounterControlGuardedCleanupProgress.foundMonotoneGuardedEntryOutcome_of_cleanup
          base c hmortal current growth source register next hrule
          (by simpa [GenuineSearch.selectedRaw] using hcommand) himmortal
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      exact families.decrementEntry current growth source register ifZero
        ifPositive hrule hcommand himmortal
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      exact families.decrementShift current growth source register ifZero
        ifPositive hrule hcommand himmortal
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      exact
        CounterControlGenuineRouteEmbedding.zeroRecovery_logical_of_rule
          base c hmortal current himmortal growth source register ifZero
          ifPositive hrule hcommand

/-- Consumer-facing monotone guarded-entry law assembled from the four
specialized family continuations. -/
theorem monotoneGuardedEntryLaw_of_families
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (families : FamilyContinuations base c hmortal) :
    CounterControlGuardedUnnesting.MonotoneGuardedEntryLaw base c := by
  apply monotoneGuardedEntryLaw_of_foundContinuationLaw base c hmortal
  intro current himmortal
  exact foundContinuation_of_families base c hmortal families current
    himmortal

end

end CounterControlMonotoneEntryAssembly
end Hooper
end Kari
end LeanWang
