/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandContinuationMortality

/-!
# Classifying generated counter callers

The command-continuation API deliberately treats a generated raw command as
an opaque member of `rawCommands`.  Parent-frame unnesting needs the more
precise finite-control origin of that command.  This file inverts membership
without expanding the fixed global source program: every generated caller
belongs to one of the seven list segments used to compile its source rule.

Two consequences isolate the exceptional unnesting paths.

* No generated command is a tag navigation, and every erasing boundary
  navigation belongs to the four-command collision-cleanup suffix.
* The only generated command with a populated collision continuation is the
  first increment shift: it searches for boundary `4`, attempts to move it
  outward, and hands a collision to `testDirectSlot`.

Thus all other found-command continuations are preserving navigation or
collision-free marker shifts.  Turning those cases into a containing logical
core still requires suffix semantics which retain absolute head coordinates.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlRawCallerClassification

open Turing CounterMachine
open CounterControlPlan
open CounterControlCommandContinuationMortality

noncomputable section

/-- Exact source-list segment of a generated raw command.  The source rule is
retained so downstream continuation proofs can recover its instruction and
logical targets without reinverting `rawCommands`. -/
inductive GeneratedCallerClass (raw : RawCommand) : Prop where
  | validation
      (growth : Turing.Dir) (source : Nat)
      (instruction : CounterMachine.Instruction)
      (rule_mem : (source, instruction) ∈ GlobalSourceProgram.program)
      (command_mem : raw ∈ validationCommands growth source instruction)
  | incrementShift
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : raw ∈ incrementShiftCommands growth source register)
  | incrementRecovery
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : raw ∈
        routeCommandsAux growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register))
  | cleanup
      (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : raw ∈ cleanupCommands growth source)
  | decrementEntry
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : raw ∈
        routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
          (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register))
  | decrementShift
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : raw ∈ decrementShiftCommands growth source register)
  | zeroRecovery
      (growth : Turing.Dir) (source : Nat) (register : Register)
      (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : raw ∈
        routeCommandsAux growth source zeroSearchBase zeroDirectBase
          (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register))

/-- Invert global enumeration into the exact list segment which generated a
caller. -/
theorem classify (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    GeneratedCallerClass raw := by
  simp only [rawCommands, rawCommandsFor, List.mem_append,
    List.mem_flatMap] at hraw
  rcases hraw with ⟨rule, hrule, hcommand⟩ | ⟨rule, hrule, hcommand⟩
  · rcases rule with ⟨source, instruction⟩
    have horiented := hcommand
    cases instruction with
    | increment register next =>
        simp only [commandsForRule, List.mem_append] at horiented
        rcases horiented with hvalidation | hbody
        · exact .validation .right source (.increment register next)
            hrule hvalidation
        simp only [incrementCommands, List.mem_append] at hbody
        rcases hbody with (hshift | hrecovery) | hcleanup
        · exact .incrementShift .right source register next hrule hshift
        · exact .incrementRecovery .right source register next hrule hrecovery
        · exact .cleanup .right source register next hrule hcleanup
    | decrement register ifZero ifPositive =>
        simp only [commandsForRule, List.mem_append] at horiented
        rcases horiented with hvalidation | hbody
        · exact .validation .right source
            (.decrement register ifZero ifPositive) hrule hvalidation
        simp only [decrementCommands, List.mem_append] at hbody
        rcases hbody with (hentry | hshift) | hzero
        · exact .decrementEntry .right source register ifZero ifPositive
            hrule hentry
        · exact .decrementShift .right source register ifZero ifPositive
            hrule hshift
        · exact .zeroRecovery .right source register ifZero ifPositive
            hrule hzero
  · rcases rule with ⟨source, instruction⟩
    have horiented := hcommand
    cases instruction with
    | increment register next =>
        simp only [commandsForRule, List.mem_append] at horiented
        rcases horiented with hvalidation | hbody
        · exact .validation .left source (.increment register next)
            hrule hvalidation
        simp only [incrementCommands, List.mem_append] at hbody
        rcases hbody with (hshift | hrecovery) | hcleanup
        · exact .incrementShift .left source register next hrule hshift
        · exact .incrementRecovery .left source register next hrule hrecovery
        · exact .cleanup .left source register next hrule hcleanup
    | decrement register ifZero ifPositive =>
        simp only [commandsForRule, List.mem_append] at horiented
        rcases horiented with hvalidation | hbody
        · exact .validation .left source
            (.decrement register ifZero ifPositive) hrule hvalidation
        simp only [decrementCommands, List.mem_append] at hbody
        rcases hbody with (hentry | hshift) | hzero
        · exact .decrementEntry .left source register ifZero ifPositive
            hrule hentry
        · exact .decrementShift .left source register ifZero ifPositive
            hrule hshift
        · exact .zeroRecovery .left source register ifZero ifPositive
            hrule hzero

private theorem routeCommandsAux_preserving
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    (raw : RawCommand)
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route) :
    ∃ address expected direction success,
      raw = .boundaryNavigation address expected direction success .preserve := by
  induction route generalizing searchSlot directSlot with
  | nil => simp [routeCommandsAux] at hraw
  | cons leg route ih =>
      simp only [routeCommandsAux, List.mem_cons] at hraw
      rcases hraw with hraw | hraw
      · subst raw
        exact ⟨_, _, _, _, rfl⟩
      · exact ih _ _ hraw

private theorem incrementShiftCommands_marker
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (raw : RawCommand) (hraw : raw ∈
      incrementShiftCommands growth source register) :
    ∃ address expected success collision,
      raw = .markerShift address expected .left .right success
        (some .left) collision := by
  cases register <;>
    simp_all [incrementShiftCommands, incrementShiftCommandsAux,
      MarkerShift.incrementOrder] <;> aesop

private theorem decrementShiftCommands_marker
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (raw : RawCommand) (hraw : raw ∈
      decrementShiftCommands growth source register) :
    ∃ address expected success,
      raw = .markerShift address expected .right .left success
        (some .right) none := by
  cases register <;>
    simp_all [decrementShiftCommands, decrementShiftCommandsAux,
      MarkerShift.decrementOrder] <;> aesop

/-- `rawCommands` contains no tag-navigation command. -/
theorem tagNavigation_not_mem
    (address : SearchAddress) (direction : Turing.Dir)
    (success : ControlRef) :
    RawCommand.tagNavigation address direction success ∉ rawCommands := by
  intro hraw
  cases classify _ hraw with
  | validation growth source instruction hrule hcommand =>
      rcases routeCommandsAux_preserving growth source validationSearchBase
          validationDirectBase (bodyEntry growth source instruction)
          MarkerValidation.sweep _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | incrementShift growth source register next hrule hcommand =>
      rcases incrementShiftCommands_marker growth source register _ hcommand with
        ⟨_, _, _, _, heq⟩
      contradiction
  | incrementRecovery growth source register next hrule hcommand =>
      rcases routeCommandsAux_preserving growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | cleanup growth source register next hrule hcommand =>
      simp [cleanupCommands] at hcommand
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      rcases decrementShiftCommands_marker growth source register _ hcommand with
        ⟨_, _, _, heq⟩
      contradiction
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source zeroSearchBase
          zeroDirectBase (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq

/-- Every generated erasing boundary command belongs to the collision-cleanup
suffix of an increment rule. -/
theorem erase_boundary_is_cleanup
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      (.erase departure) ∈ rawCommands) :
    ∃ growth source register next,
      (source, .increment register next) ∈ GlobalSourceProgram.program ∧
      RawCommand.boundaryNavigation address expected direction success
        (.erase departure) ∈ cleanupCommands growth source := by
  cases classify _ hraw with
  | validation growth source instruction hrule hcommand =>
      rcases routeCommandsAux_preserving growth source validationSearchBase
          validationDirectBase (bodyEntry growth source instruction)
          MarkerValidation.sweep _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | incrementShift growth source register next hrule hcommand =>
      rcases incrementShiftCommands_marker growth source register _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | incrementRecovery growth source register next hrule hcommand =>
      rcases routeCommandsAux_preserving growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | cleanup growth source register next hrule hcommand =>
      exact ⟨growth, source, register, next, hrule, hcommand⟩
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      rcases decrementShiftCommands_marker growth source register _ hcommand with
        ⟨_, _, _, heq⟩
      contradiction
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source zeroSearchBase
          zeroDirectBase (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp at heq

/-- The four exact shapes of a cleanup command. -/
theorem mem_cleanupCommands_iff
    (raw : RawCommand) (growth : Turing.Dir) (source : Nat) :
    raw ∈ cleanupCommands growth source ↔
      raw = .boundaryNavigation
          ⟨growth, source, cleanupSearchBase⟩ 3 .left
          (searchRef growth source (cleanupSearchBase + 1))
          (.erase (some .left)) ∨
      raw = .boundaryNavigation
          ⟨growth, source, cleanupSearchBase + 1⟩ 2 .left
          (searchRef growth source (cleanupSearchBase + 2))
          (.erase (some .left)) ∨
      raw = .boundaryNavigation
          ⟨growth, source, cleanupSearchBase + 2⟩ 1 .left
          (searchRef growth source (cleanupSearchBase + 3))
          (.erase (some .left)) ∨
      raw = .boundaryNavigation
          ⟨growth, source, cleanupSearchBase + 3⟩ 0 .left
          (.sharedReturn growth) (.erase (some .left)) := by
  simp [cleanupCommands]

/-- Every generated marker shift moves opposite to its logical search
direction.  Increment commands search left and shift right; decrement
commands search right and shift left. -/
theorem markerShift_shift_eq_opposite_search
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift address expected search shift success
      departure collision ∈ rawCommands) :
    shift = NestingMachine.opposite search := by
  cases classify _ hraw with
  | validation growth source instruction hrule hcommand =>
      rcases routeCommandsAux_preserving growth source validationSearchBase
          validationDirectBase (bodyEntry growth source instruction)
          MarkerValidation.sweep _ hcommand with
        ⟨_, _, _, _, heq⟩
      contradiction
  | incrementShift growth source register next hrule hcommand =>
      rcases incrementShiftCommands_marker growth source register _ hcommand with
        ⟨_, _, _, _, heq⟩
      simp_all [NestingMachine.opposite]
  | incrementRecovery growth source register next hrule hcommand =>
      rcases routeCommandsAux_preserving growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      contradiction
  | cleanup growth source register next hrule hcommand =>
      simp [cleanupCommands] at hcommand
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      contradiction
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      rcases decrementShiftCommands_marker growth source register _ hcommand with
        ⟨_, _, _, heq⟩
      simp_all [NestingMachine.opposite]
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source zeroSearchBase
          zeroDirectBase (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) _ hcommand with
        ⟨_, _, _, _, heq⟩
      contradiction

/-- Physical orientation preserves the opposition of a generated marker
shift's search and shift directions. -/
theorem markerShift_oriented_shift_eq_opposite_search
    (address : SearchAddress) (expected : Fin 5)
    (search shift : Turing.Dir) (success : ControlRef)
    (departure : Option Turing.Dir) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift address expected search shift success
      departure collision ∈ rawCommands) :
    orient address.growth shift =
      NestingMachine.opposite (orient address.growth search) := by
  rw [markerShift_shift_eq_opposite_search address expected search shift
    success departure collision hraw]
  cases address.growth <;> cases search <;> rfl

set_option maxHeartbeats 500000 in
-- The proof expands the four finite increment-shift schedules.
/-- A populated collision continuation identifies the unique outward
boundary-`4` increment command and its cleanup handoff. -/
theorem collision_ref_shape
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (reference : ControlRef)
    (hcollision : rawCollisionRef raw = some reference) :
    ∃ growth source register next success,
      (source, .increment register next) ∈ GlobalSourceProgram.program ∧
      raw = .markerShift
        ⟨growth, source, bodySearchBase⟩ 4 .left .right success
        (some .left) (some (directRef growth source testDirectSlot)) ∧
      reference = directRef growth source testDirectSlot := by
  cases classify raw hraw with
  | validation growth source instruction hrule hcommand =>
      rcases routeCommandsAux_preserving growth source validationSearchBase
          validationDirectBase (bodyEntry growth source instruction)
          MarkerValidation.sweep raw hcommand with
        ⟨_, _, _, _, heq⟩
      subst raw
      simp [rawCollisionRef] at hcollision
  | incrementShift growth source register next hrule hcommand =>
      cases register <;>
        simp_all [incrementShiftCommands, incrementShiftCommandsAux,
          MarkerShift.incrementOrder, rawCollisionRef] <;> aesop
  | incrementRecovery growth source register next hrule hcommand =>
      rcases routeCommandsAux_preserving growth source secondarySearchBase
          (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) raw hcommand with
        ⟨_, _, _, _, heq⟩
      subst raw
      simp [rawCollisionRef] at hcollision
  | cleanup growth source register next hrule hcommand =>
      rcases (mem_cleanupCommands_iff raw growth source).mp hcommand with
        rfl | rfl | rfl | rfl <;>
        simp [rawCollisionRef] at hcollision
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) raw hcommand with
        ⟨_, _, _, _, heq⟩
      subst raw
      simp [rawCollisionRef] at hcollision
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      rcases decrementShiftCommands_marker growth source register raw hcommand with
        ⟨_, _, _, heq⟩
      subst raw
      simp [rawCollisionRef] at hcollision
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      rcases routeCommandsAux_preserving growth source zeroSearchBase
          zeroDirectBase (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) raw hcommand with
        ⟨_, _, _, _, heq⟩
      subst raw
      simp [rawCollisionRef] at hcollision

end

end CounterControlRawCallerClassification
end Hooper
end Kari
end LeanWang
