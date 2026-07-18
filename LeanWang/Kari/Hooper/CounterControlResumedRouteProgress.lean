/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedExactContinuation
import LeanWang.Kari.Hooper.CounterControlRouteSuffixMortality

/-!
# Advancing ordinary resumed callers through their route suffix

Generated parent callers have seven symbolic origins.  Four are preserving
navigation routes: validation, increment recovery, decrement entry, and zero
recovery.  From the exact successful command handoff, their remaining route
can be traversed without assuming that the selected caller was its first
command.

This file performs that composition.  Route cases reach their advertised
symbolic endpoint with a full `RouteTailGaps` coordinate trace; only the two
marker-shift schedules and the increment cleanup family remain unadvanced.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlResumedRouteProgress

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlCommandContinuationMortality
open CounterControlExactCommandContinuation
open CounterControlRawCallerClassification
open CounterControlRouteSuffixMortality
open CounterControlPrefixInstructionResolution
open CounterControlPrefixResume

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

private theorem boundaryPreserve_of_mem_routeCommandsAux
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    {raw : RawCommand}
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route) :
    ∃ address expected direction success,
      raw = .boundaryNavigation address expected direction success
        .preserve := by
  induction route generalizing searchSlot directSlot with
  | nil => simp [routeCommandsAux] at hraw
  | cons leg route ih =>
      simp only [routeCommandsAux, List.mem_cons] at hraw
      rcases hraw with hhead | htail
      · subst raw
        exact ⟨_, _, _, _, rfl⟩
      · exact ih (searchSlot := searchSlot + 1)
          (directSlot := directSlot + 1) htail

private theorem exactSuccessTape_eq_of_mem_routeCommandsAux
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    {raw : RawCommand}
    (hraw : raw ∈ routeCommandsAux growth source searchSlot directSlot
      after route)
    (T : FullTM0.Tape (Symbol numTags)) :
    exactSuccessTape raw T = T := by
  rcases boundaryPreserve_of_mem_routeCommandsAux growth source searchSlot
      directSlot after route hraw with
    ⟨address, expected, direction, success, rfl⟩
  rfl

private theorem rawTargetMatches_of_compiled
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) :
    RawTargetMatches raw T := by
  rw [CounterControlCommandAt.compileRawCommand_spec] at hmatch
  cases raw <;>
    simpa [CounterControlCommandAt.compileRawAtTag,
      compileNavigationAction, Command.target,
      RawTargetMatches, Target.Matches] using hmatch

/-- A selected resumed route caller, advanced from its exact found state to
the route's advertised endpoint. -/
structure ResumedRouteEnd
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg) : Type where
  suffix : RouteSuffixReached base c growth source searchSlot directSlot
    after route resumed.selectedRaw resumed.parentFoundTape
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (CounterControlParentContinuation.foundCfg resumed.next)
    ⟨resolve base c after, suffix.finish⟩

/-- Exact post-success classification.  Route families have already been
advanced to their route endpoint; marker schedules and cleanup retain their
precise generated-family evidence for the next specialized layer. -/
inductive Outcome
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start) : Type where
  | validation (growth : Turing.Dir) (source : Nat)
      (instruction : CounterMachine.Instruction)
      (progress : ResumedRouteEnd resumed growth source
        validationSearchBase validationDirectBase
        (bodyEntry growth source instruction) MarkerValidation.sweep)
  | incrementShift (growth : Turing.Dir) (source : Nat)
      (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : resumed.selectedRaw ∈
        incrementShiftCommands growth source register)
  | incrementRecovery (growth : Turing.Dir) (source : Nat)
      (register : Register) (next : Nat)
      (progress : ResumedRouteEnd resumed growth source secondarySearchBase
        (bodyDirectBase + 2) (.logical growth next)
        (AnchoredCounterGeometry.routeFromIncrement register))
  | cleanup (growth : Turing.Dir) (source : Nat)
      (register : Register) (next : Nat)
      (rule_mem : (source, .increment register next) ∈
        GlobalSourceProgram.program)
      (command_mem : resumed.selectedRaw ∈ cleanupCommands growth source)
  | decrementEntry (growth : Turing.Dir) (source : Nat)
      (register : Register) (ifZero ifPositive : Nat)
      (progress : ResumedRouteEnd resumed growth source bodySearchBase
        (bodyDirectBase + 1) (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
  | decrementShift (growth : Turing.Dir) (source : Nat)
      (register : Register) (ifZero ifPositive : Nat)
      (rule_mem : (source, .decrement register ifZero ifPositive) ∈
        GlobalSourceProgram.program)
      (command_mem : resumed.selectedRaw ∈
        decrementShiftCommands growth source register)
  | zeroRecovery (growth : Turing.Dir) (source : Nat)
      (register : Register) (ifZero ifPositive : Nat)
      (progress : ResumedRouteEnd resumed growth source zeroSearchBase
        zeroDirectBase (.logical growth ifZero)
        (AnchoredCounterGeometry.routeFromZero register))

private theorem progressedRoute
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (CounterControlParentContinuation.foundCfg resumed.next))
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    (hroute : resumed.selectedRaw ∈
      routeCommandsAux growth source searchSlot directSlot after route)
    (hcommands : ∀ command,
      command ∈ routeCommandsAux growth source searchSlot directSlot
          after route → command ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source searchSlot directSlot
          route → rule ∈ rawDirectRules) :
    Nonempty (ResumedRouteEnd resumed growth source searchSlot directSlot
      after route) := by
  have hsuccess := resumed.reaches_selectedRaw_success
  have htape := exactSuccessTape_eq_of_mem_routeCommandsAux growth source
    searchSlot directSlot after route hroute resumed.parentFoundTape
  rw [htape] at hsuccess
  have himmortalSuccess := immortalFrom_of_reaches base c himmortal hsuccess
  have htarget : RawTargetMatches resumed.selectedRaw
      resumed.parentFoundTape :=
    rawTargetMatches_of_compiled base c resumed.selectedRaw
      resumed.selectedRaw_mem resumed.parentFoundTape
      resumed.selectedRaw_target_matches_parentFoundTape
  rcases reaches_routeSuffix_of_immortal base c hmortal growth source
      searchSlot directSlot after route resumed.selectedRaw hroute hcommands
      hcontinuations resumed.parentFoundTape htarget himmortalSuccess with
    ⟨suffix⟩
  exact ⟨⟨suffix, hsuccess.trans suffix.reaches⟩⟩

/-- Four of the seven generated caller families advance all the way through
their remaining preserving route. -/
theorem progresses_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (CounterControlParentContinuation.foundCfg resumed.next)) :
    Nonempty (Outcome resumed) := by
  cases classify resumed.selectedRaw resumed.selectedRaw_mem with
  | validation growth source instruction hrule hcommand =>
      have hcommands : ∀ command,
          command ∈ validationCommands growth source instruction →
            command ∈ rawCommands := by
        intro command hmem
        apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
          growth hrule
        simp only [commandsForRule, List.mem_append]
        exact Or.inl hmem
      have hcontinuations : ∀ rule,
          rule ∈ routeContinuationRules growth source validationSearchBase
              validationDirectBase MarkerValidation.sweep →
            rule ∈ rawDirectRules := by
        intro rule hmem
        apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
          growth hrule
        simp [directRulesForRule, validationRules, hmem]
      rcases progressedRoute base c hmortal resumed himmortal growth source
          validationSearchBase validationDirectBase
          (bodyEntry growth source instruction) MarkerValidation.sweep
          (by simpa [validationCommands] using hcommand)
          (by simpa [validationCommands] using hcommands)
          hcontinuations with ⟨progress⟩
      exact ⟨.validation growth source instruction progress⟩
  | incrementShift growth source register next hrule hcommand =>
      exact ⟨.incrementShift growth source register next hrule hcommand⟩
  | incrementRecovery growth source register next hrule hcommand =>
      have hcommands : ∀ command,
          command ∈ routeCommandsAux growth source secondarySearchBase
              (bodyDirectBase + 2) (.logical growth next)
              (AnchoredCounterGeometry.routeFromIncrement register) →
            command ∈ rawCommands := by
        intro command hmem
        exact CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
          growth hrule (by simp [commandsForRule, incrementCommands, hmem])
      have hcontinuations : ∀ rule,
          rule ∈ routeContinuationRules growth source secondarySearchBase
              (bodyDirectBase + 2)
              (AnchoredCounterGeometry.routeFromIncrement register) →
            rule ∈ rawDirectRules := by
        intro rule hmem
        apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
          growth hrule
        simp [directRulesForRule, incrementRules, hmem]
      rcases progressedRoute base c hmortal resumed himmortal growth source
          secondarySearchBase (bodyDirectBase + 2) (.logical growth next)
          (AnchoredCounterGeometry.routeFromIncrement register) hcommand
          hcommands hcontinuations with ⟨progress⟩
      exact ⟨.incrementRecovery growth source register next progress⟩
  | cleanup growth source register next hrule hcommand =>
      exact ⟨.cleanup growth source register next hrule hcommand⟩
  | decrementEntry growth source register ifZero ifPositive hrule hcommand =>
      have hcommands : ∀ command,
          command ∈ routeCommandsAux growth source bodySearchBase
              (bodyDirectBase + 1) (directRef growth source testDirectSlot)
              (AnchoredCounterGeometry.routeToDecrementStart register) →
            command ∈ rawCommands := by
        intro command hmem
        exact CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
          growth hrule (by simp [commandsForRule, decrementCommands, hmem])
      have hcontinuations : ∀ rule,
          rule ∈ routeContinuationRules growth source bodySearchBase
              (bodyDirectBase + 1)
              (AnchoredCounterGeometry.routeToDecrementStart register) →
            rule ∈ rawDirectRules := by
        intro rule hmem
        apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
          growth hrule
        simp [directRulesForRule, decrementRules, hmem]
      rcases progressedRoute base c hmortal resumed himmortal growth source
          bodySearchBase (bodyDirectBase + 1)
          (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) hcommand
          hcommands hcontinuations with ⟨progress⟩
      exact ⟨.decrementEntry growth source register ifZero ifPositive
        progress⟩
  | decrementShift growth source register ifZero ifPositive hrule hcommand =>
      exact ⟨.decrementShift growth source register ifZero ifPositive
        hrule hcommand⟩
  | zeroRecovery growth source register ifZero ifPositive hrule hcommand =>
      have hcommands : ∀ command,
          command ∈ routeCommandsAux growth source zeroSearchBase
              zeroDirectBase (.logical growth ifZero)
              (AnchoredCounterGeometry.routeFromZero register) →
            command ∈ rawCommands := by
        intro command hmem
        exact CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
          growth hrule (by simp [commandsForRule, decrementCommands, hmem])
      have hcontinuations : ∀ rule,
          rule ∈ routeContinuationRules growth source zeroSearchBase
              zeroDirectBase
              (AnchoredCounterGeometry.routeFromZero register) →
            rule ∈ rawDirectRules := by
        intro rule hmem
        apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
          growth hrule
        simp [directRulesForRule, decrementRules, hmem]
      rcases progressedRoute base c hmortal resumed himmortal growth source
          zeroSearchBase zeroDirectBase (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) hcommand
          hcommands hcontinuations with ⟨progress⟩
      exact ⟨.zeroRecovery growth source register ifZero ifPositive
        progress⟩

end

end CounterControlResumedRouteProgress
end Hooper
end Kari
end LeanWang
