/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineCoordinates

/-!
# Classifying arbitrary genuine found commands

The first generated search reached on an arbitrary immortal orbit need not
carry the one-cell return guard.  Its selected command nevertheless comes
from exactly the same seven source-program families as a guarded search.
This module packages that family inversion at the `GenuineSearch` level so
the monotone-entry proof can dispatch without reopening the global command
enumeration or losing the exact found coordinates.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineFoundClassification

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlRawCallerClassification
open CounterControlGlobalUnnesting

noncomputable section

/-- Exact source-list family of the raw command selected by an arbitrary
genuine generated search. -/
inductive Outcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
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
  | incrementRecovery
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        routeCommandsAux growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register))
  | cleanup
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈ cleanupCommands growth source)
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
  | zeroRecovery
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : current.selectedRaw ∈
        routeCommandsAux growth source zeroSearchBase zeroDirectBase
          (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register))

/-- Invert the selected command of an arbitrary genuine search into its
exact source-program family. -/
theorem classify_found
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) :
    Nonempty (Outcome current) := by
  cases classify current.selectedRaw current.selectedRaw_mem with
  | validation growth source instruction hrule hcommand =>
      exact ⟨.validation growth source instruction hrule hcommand⟩
  | incrementShift growth source register next hrule hcommand =>
      exact ⟨.incrementShift growth source register next hrule hcommand⟩
  | incrementRecovery growth source register next hrule hcommand =>
      exact ⟨.incrementRecovery growth source register next hrule hcommand⟩
  | cleanup growth source register next hrule hcommand =>
      exact ⟨.cleanup growth source register next hrule hcommand⟩
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      exact ⟨.decrementEntry growth source register ifZero ifPositive
        hrule hcommand⟩
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      exact ⟨.decrementShift growth source register ifZero ifPositive
        hrule hcommand⟩
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      exact ⟨.zeroRecovery growth source register ifZero ifPositive
        hrule hcommand⟩

end

end CounterControlGenuineFoundClassification
end Hooper
end Kari
end LeanWang
