/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedCoordinates
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding

/-!
# Embedding guarded preserving-route callers

A guarded generated search can select any command in a preserving route.
This file advances the selected command through the remaining route while
retaining exact tape coordinates.  Recovery routes then reconstruct their
advertised logical endpoint and prove that the guarded search lies strictly
inside that logical core.

Unlike the earlier resumed-search interface, the statements here depend only
on `CounterControlGuardedSearch.GuardedSearch`.  The increment and zero
recovery entry points also retain the source-program rule which generated the
route, so their logical target bounds do not need to be recovered later.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedRouteEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedParentContinuation
open CounterControlParentContinuation CounterControlParentEmbedding
open CounterControlSearchSystem
open CounterControlRouteSuffixMortality
open CounterControlResumedRouteEmbedding

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩




/-- A guarded route endpoint is the ordinary endpoint of its underlying
genuine search. -/
abbrev GuardedRouteEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg) : Type :=
  CounterControlGenuineRouteEmbedding.GenuineRouteEnd current.current growth
    source searchSlot directSlot after route

/-- Advance any guarded selected preserving-route command through the exact
remaining route suffix. -/
theorem progressedRoute
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg)
    (hroute : current.selectedRaw ∈
      routeCommandsAux growth source searchSlot directSlot after route)
    (hcommands : ∀ command,
      command ∈ routeCommandsAux growth source searchSlot directSlot
          after route → command ∈ rawCommands)
    (hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source searchSlot directSlot
          route → rule ∈ rawDirectRules) :
    Nonempty (GuardedRouteEnd current growth source searchSlot directSlot
      after route) := by
  have hsuccess := current.reaches_selectedRaw_success
  have htape :=
    CounterControlRouteSuffixMortality.exactSuccessTape_eq_of_mem_routeCommandsAux
      growth source searchSlot directSlot after route hroute current.foundTape
  rw [htape] at hsuccess
  have himmortalSuccess := FullTM0.ImmortalFrom.of_reaches himmortal hsuccess
  have htarget : RawTargetMatches current.selectedRaw current.foundTape :=
    CounterControlRouteSuffixMortality.rawTargetMatches_of_compiled base c
      current.selectedRaw current.selectedRaw_mem current.foundTape
      current.selectedRaw_target_matches_foundTape
  rcases reaches_routeSuffix_of_immortal base c hmortal growth source
      searchSlot directSlot after route current.selectedRaw hroute hcommands
      hcontinuations current.foundTape htarget himmortalSuccess with
    ⟨suffix⟩
  exact ⟨⟨suffix, hsuccess.trans suffix.reaches⟩⟩

/-! ## Recovery routes reach a containing logical core -/

/-- A consecutive rightward guarded recovery suffix ending at logical
boundary `4` reconstructs a core which strictly contains the current gap. -/
theorem logical_of_toFour_endpoint
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source searchSlot directSlot targetState : Nat)
    (route : List MarkerValidation.Leg)
    (progress : GuardedRouteEnd current growth source searchSlot directSlot
      (.logical growth targetState) route)
    (htargetState : targetState < logicalSpan)
    (hroute : ∃ routeSource : Fin 5, ToFour routeSource route) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases
      CounterControlGenuineRouteEmbedding.certificate_of_toFour_endpoint
        base c hmortal current.current himmortal growth source searchSlot
        directSlot targetState route progress htargetState hroute with
    ⟨certificate⟩
  exact ⟨.logical certificate.core certificate.reaches certificate.inside⟩

/-- A guarded increment-recovery caller reaches a containing logical core.
The source rule supplies the target-state bound. -/
theorem incrementRecovery_logical_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source secondarySearchBase
        (bodyDirectBase + 2) (.logical growth next)
        (AnchoredCounterGeometry.routeFromIncrement register)) :
    Nonempty (FoundGuardedParentOutcome current) := by
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
  rcases progressedRoute base c hmortal current himmortal growth source
      secondarySearchBase (bodyDirectBase + 2) (.logical growth next)
      (AnchoredCounterGeometry.routeFromIncrement register) hcommand
      hcommands hcontinuations with ⟨progress⟩
  apply logical_of_toFour_endpoint base c hmortal current himmortal growth
    source secondarySearchBase (bodyDirectBase + 2) next
    (AnchoredCounterGeometry.routeFromIncrement register) progress
  · exact state_lt_logicalSpan
      (CounterControlAbstractTrace.target_mem_programStates hrule
        (by simp [instructionTargets]))
  · exact routeFromIncrement_toFour register

/-- A guarded zero-recovery caller reaches a containing logical core.  The
source rule supplies the target-state bound. -/
theorem zeroRecovery_logical_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source zeroSearchBase zeroDirectBase
        (.logical growth ifZero)
        (AnchoredCounterGeometry.routeFromZero register)) :
    Nonempty (FoundGuardedParentOutcome current) := by
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
  rcases progressedRoute base c hmortal current himmortal growth source
      zeroSearchBase zeroDirectBase (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register) hcommand
      hcommands hcontinuations with ⟨progress⟩
  apply logical_of_toFour_endpoint base c hmortal current himmortal growth
    source zeroSearchBase zeroDirectBase ifZero
    (AnchoredCounterGeometry.routeFromZero register) progress
  · exact state_lt_logicalSpan
      (CounterControlAbstractTrace.target_mem_programStates hrule
        (by simp [instructionTargets]))
  · exact routeFromZero_toFour register

end

end CounterControlGuardedRouteEmbedding
end Hooper
end Kari
end LeanWang
