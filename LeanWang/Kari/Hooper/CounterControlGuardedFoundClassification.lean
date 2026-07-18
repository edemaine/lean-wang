/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedCleanupProgress

/-!
# Classifying guarded found-state continuations

The seven generated command families collapse immediately to four remaining
operational branches.  Recovery routes already reach a containing logical
core, while cleanup commands already reach a strictly larger guarded search.
This file performs that common dispatch and retains exact rule provenance for
validation, the two marker-shift schedules, and decrement entry.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedFoundClassification

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlRawCallerClassification
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedSearch
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Result of dispatching the selected raw command of a guarded search.
Three families are completely discharged; the other four retain precisely
the family membership and source rule needed by their specialized suffix
proofs. -/
inductive Outcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) : Type where
  | solved (outcome : FoundGuardedEscapeOutcome current)
  | validation
      (growth : Turing.Dir) (source : Nat)
      (instruction : CounterMachine.Instruction)
      (rule_mem : (source, instruction) ∈ GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        validationCommands growth source instruction)
  | incrementShift
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        incrementShiftCommands growth source register)
  | decrementEntry
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
          (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register))
  | decrementShift
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        decrementShiftCommands growth source register)

/-- Recovery and cleanup families are discharged during generated-caller
classification. -/
theorem classify_found
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (Outcome current) := by
  cases classify current.selectedRaw current.selectedRaw_mem with
  | validation growth source instruction hrule hcommand =>
      exact ⟨.validation growth source instruction hrule hcommand⟩
  | incrementShift growth source register next hrule hcommand =>
      exact ⟨.incrementShift growth source register next hrule hcommand⟩
  | incrementRecovery growth source register next hrule hcommand =>
      rcases CounterControlGuardedRouteEmbedding.incrementRecovery_logical_of_rule
          base c hmortal current himmortal growth source register next hrule
          hcommand with ⟨outcome⟩
      exact ⟨.solved (.parent outcome)⟩
  | cleanup growth source register next hrule hcommand =>
      rcases
          CounterControlGuardedCleanupProgress.found_reaches_larger_guardedSearch_of_cleanup
            base c hmortal current growth source register next hrule
            (by simpa [GuardedSearch.selectedRaw] using hcommand)
            himmortal with
        ⟨finish, hreach, hdistance⟩
      exact ⟨.solved (.parent (.nextSearch finish hreach hdistance))⟩
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      exact ⟨.decrementEntry growth source register ifZero ifPositive
        hrule hcommand⟩
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      exact ⟨.decrementShift growth source register ifZero ifPositive
        hrule hcommand⟩
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      rcases CounterControlGuardedRouteEmbedding.zeroRecovery_logical_of_rule
          base c hmortal current himmortal growth source register ifZero
          ifPositive hrule hcommand with ⟨outcome⟩
      exact ⟨.solved (.parent outcome)⟩

end

end CounterControlGuardedFoundClassification
end Hooper
end Kari
end LeanWang
