/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInwardValidationReplay

/-!
# Classifying guarded validation callers

The inward half of validation already gives strict progress by replaying the
matching outward search.  This module performs the finite eight-command
split and discharges those four inward positions, leaving only the four
outward positions for the final guarded validation continuation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedValidationClassification

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Inward validation has already escaped strictly.  The four remaining
constructors retain the exact outward raw command selected at slots `4`--`7`.
-/
inductive Outcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : Type where
  | escaped (outcome : FoundGuardedEscapeOutcome current)
  | outwardOne
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 4⟩ 1 .right (directRef growth source 4) .preserve)
  | outwardTwo
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 5⟩ 2 .right (directRef growth source 5) .preserve)
  | outwardThree
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 6⟩ 3 .right (directRef growth source 6) .preserve)
  | outwardFour
      (raw_eq : current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 7⟩ 4 .right
          (bodyEntry growth source instruction) .preserve)

private theorem direction_eq_left_of_raw
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source slot : Nat) (expected : Fin 5)
    (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected .left success .preserve) :
    current.direction = orient growth .left := by
  have hdirection := current.selectedRaw_direction_eq
  rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
  rw [hraw] at hdirection
  exact hdirection.symm

/-- Split a guarded validation caller into an already-solved strict inward
replay or one of the four exact outward positions. -/
theorem classify_validation
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (Outcome current growth source instruction) := by
  have hcases := hcommand
  simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
    validationSearchBase, validationDirectBase] at hcases
  rcases hcases with hraw | hraw | hraw | hraw | hraw | hraw | hraw | hraw
  · have hdirection := direction_eq_left_of_raw current growth source 0 3
      (directRef growth source 0) hraw
    rcases
        CounterControlInwardValidationReplay.foundGuardedEscapeOutcome_of_inward_validation
          base c hmortal current growth source instruction hrule hcommand
          hdirection himmortal with
      ⟨outcome⟩
    exact ⟨.escaped outcome⟩
  · have hdirection := direction_eq_left_of_raw current growth source 1 2
      (directRef growth source 1) hraw
    rcases
        CounterControlInwardValidationReplay.foundGuardedEscapeOutcome_of_inward_validation
          base c hmortal current growth source instruction hrule hcommand
          hdirection himmortal with
      ⟨outcome⟩
    exact ⟨.escaped outcome⟩
  · have hdirection := direction_eq_left_of_raw current growth source 2 1
      (directRef growth source 2) hraw
    rcases
        CounterControlInwardValidationReplay.foundGuardedEscapeOutcome_of_inward_validation
          base c hmortal current growth source instruction hrule hcommand
          hdirection himmortal with
      ⟨outcome⟩
    exact ⟨.escaped outcome⟩
  · have hdirection := direction_eq_left_of_raw current growth source 3 0
      (directRef growth source 3) hraw
    rcases
        CounterControlInwardValidationReplay.foundGuardedEscapeOutcome_of_inward_validation
          base c hmortal current growth source instruction hrule hcommand
          hdirection himmortal with
      ⟨outcome⟩
    exact ⟨.escaped outcome⟩
  · exact ⟨.outwardOne hraw⟩
  · exact ⟨.outwardTwo hraw⟩
  · exact ⟨.outwardThree hraw⟩
  · exact ⟨.outwardFour hraw⟩

end

end CounterControlGuardedValidationClassification
end Hooper
end Kari
end LeanWang
