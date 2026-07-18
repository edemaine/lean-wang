/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedFoundClassification

/-!
# Assembly of guarded command-family escapes

Recovery routes and collision cleanup are already discharged by the common
guarded classifier.  This file isolates the four specialized command-family
continuations still needed by that classifier and assembles them into the
single strict `GuardedEscapeLaw` consumed by global unnesting.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedEscapeAssembly

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGuardedFoundClassification

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Specialized continuations for the four command families not discharged
by generic recovery-route and cleanup geometry. -/
structure FamilyContinuations
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) : Prop where
  validation : ∀
      (current : GuardedSearch base c)
      (growth : Turing.Dir) (source : Nat)
      (instruction : CounterMachine.Instruction)
      (rule_mem : (source, instruction) ∈ GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        validationCommands growth source instruction),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current.current) →
        Nonempty (FoundGuardedEscapeOutcome current)
  incrementShift : ∀
      (current : GuardedSearch base c)
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        incrementShiftCommands growth source register),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current.current) →
        Nonempty (FoundGuardedEscapeOutcome current)
  decrementEntry : ∀
      (current : GuardedSearch base c)
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
          (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register)),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current.current) →
        Nonempty (FoundGuardedEscapeOutcome current)
  decrementShift : ∀
      (current : GuardedSearch base c)
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        decrementShiftCommands growth source register),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg current.current) →
        Nonempty (FoundGuardedEscapeOutcome current)

/-- The four specialized family continuations, together with the common
classifier, discharge every exact guarded found state. -/
theorem foundContinuation_of_families
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (families : FamilyContinuations base c hmortal)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases classify_found base c hmortal current himmortal with ⟨outcome⟩
  cases outcome with
  | solved outcome => exact ⟨outcome⟩
  | validation growth source instruction hrule hcommand =>
      exact families.validation current growth source instruction hrule
        hcommand himmortal
  | incrementShift growth source register next hrule hcommand =>
      exact families.incrementShift current growth source register next hrule
        hcommand himmortal
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      exact families.decrementEntry current growth source register ifZero
        ifPositive hrule hcommand himmortal
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      exact families.decrementShift current growth source register ifZero
        ifPositive hrule hcommand himmortal

/-- Consumer-facing strict guarded escape law assembled from the four
specialized family continuations. -/
theorem guardedEscapeLaw_of_families
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (families : FamilyContinuations base c hmortal) :
    CounterControlGuardedUnnesting.GuardedEscapeLaw base c := by
  apply guardedEscapeLaw_of_foundContinuationLaw base c hmortal
  intro current himmortal
  exact foundContinuation_of_families base c hmortal families current
    himmortal

end

end CounterControlGuardedEscapeAssembly
end Hooper
end Kari
end LeanWang
