/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedCoordinates
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding

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
    CounterControlExactCommandContinuation.exactSuccessTape raw T = T := by
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

/-- A selected guarded route caller, advanced from its exact found state to
the route's advertised endpoint. -/
structure GuardedRouteEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg) : Type where
  suffix : RouteSuffixReached base c growth source searchSlot directSlot
    after route current.selectedRaw current.foundTape
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨resolve base c after, suffix.finish⟩

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
  have htape := exactSuccessTape_eq_of_mem_routeCommandsAux growth source
    searchSlot directSlot after route hroute current.foundTape
  rw [htape] at hsuccess
  have himmortalSuccess := immortalFrom_of_reaches base c himmortal hsuccess
  have htarget : RawTargetMatches current.selectedRaw current.foundTape :=
    rawTargetMatches_of_compiled base c current.selectedRaw
      current.selectedRaw_mem current.foundTape
      current.selectedRaw_target_matches_foundTape
  rcases reaches_routeSuffix_of_immortal base c hmortal growth source
      searchSlot directSlot after route current.selectedRaw hroute hcommands
      hcontinuations current.foundTape htarget himmortalSuccess with
    ⟨suffix⟩
  exact ⟨⟨suffix, hsuccess.trans suffix.reaches⟩⟩

/-! ## Exact guarded route coordinates -/

/-- The selected route command reads the boundary named by its retained
route position at the guarded found tape. -/
theorem GuardedRouteEnd.current_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GuardedRouteEnd current growth source searchSlot directSlot
      after route) :
    current.foundTape.read =
      boundarySymbol progress.suffix.current.target := by
  have htarget := current.selectedRaw_target_matches_foundTape
  rw [CounterControlCommandAt.compileRawCommand_spec] at htarget
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    Target.Matches, compileNavigationAction] using htarget

/-- The guarded search is exactly the selected route leg. -/
theorem GuardedRouteEnd.current_gap
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GuardedRouteEnd current growth source searchSlot directSlot
      after route) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary progress.suffix.current.target).Matches
      current.current.outer
      (orient growth progress.suffix.current.direction)
      current.current.distance := by
  have hgap := current.current.gap
  rw [← current.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    Command.searchDirection, compileNavigationAction] using hgap

/-- Resolving the guarded gap reaches `foundTape`, in the selected route
leg's physical direction. -/
theorem GuardedRouteEnd.current_foundTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GuardedRouteEnd current growth source searchSlot directSlot
      after route) :
    current.current.outer.moveN
      (orient growth progress.suffix.current.direction)
        current.current.distance = current.foundTape := by
  have hdirection : orient growth progress.suffix.current.direction =
      current.direction := by
    calc
      orient growth progress.suffix.current.direction =
          (CounterControlCommandAt.compileRawCommand base c
            current.selectedRaw current.selectedRaw_mem).searchDirection := by
        rw [CounterControlCommandAt.compileRawCommand_spec]
        simp [progress.suffix.raw_eq,
          CounterControlCommandAt.compileRawAtTag, Command.searchDirection]
      _ = current.direction := current.selectedRaw_direction_eq
  exact congrArg
    (fun direction => current.current.outer.moveN direction
      current.current.distance) hdirection

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
  rcases hroute with ⟨routeSource, hroute⟩
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have himmortalLogical := immortalFrom_of_reaches base c himmortal
    progress.reaches
  change FullTM0.ImmortalFrom
    (CounterControlNestingBridge.machine base c)
    ⟨logicalState base c growth targetState, progress.suffix.finish⟩
      at himmortalLogical
  rcases CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
      base c hmortal growth targetState htargetState progress.suffix.finish
      himmortalLogical with
    ⟨instruction, registers, coreTape, limit, target, _hrule, hcore,
      hcoreBefore, hrunway, htarget, hcenter, _hbody⟩
  let represented : CoreTargetRepresents registers growth limit target
      coreTape := {
    toCorePrefixRepresents := {
      toCoreRepresents := hcore
      core_before_limit := hcoreBefore
      runway := hrunway }
    target_matches := htarget }
  let core : LogicalCore base c := {
    growth := growth
    source := targetState
    source_lt := htargetState
    registers := registers
    tape := coreTape
    limit := limit
    target := target
    represented := represented }
  have hread : current.foundTape.read = boundarySymbol i.succ := by
    have hread' := progress.current_read
    rw [hcurrent] at hread'
    exact hread'
  have hfoundBoundary : current.foundTape =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    exact htail.start_eq hcore hread progress.suffix.tailGaps hcenter
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary i.succ).Matches current.current.outer
      (orient growth .right) current.current.distance := by
    have hgap' := progress.current_gap
    rw [hcurrent] at hgap'
    exact hgap'
  have hfound : current.current.outer.moveN (orient growth .right)
        current.current.distance =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    have hfound' := progress.current_foundTape
    rw [hcurrent] at hfound'
    exact hfound'.trans hfoundBoundary
  have hinside : current.current.distance < layoutEnd registers :=
    rightGap_distance_lt_layoutEnd hcore i current.current.distance hgap
      hfound
  have hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) core.cfg := by
    have hrun := progress.reaches
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨logicalState base c growth targetState,
        progress.suffix.finish⟩ at hrun
    rw [hcenter] at hrun
    simpa [core, LogicalCore.cfg, LogicalCore.frame,
      LogicalCore.abstract, prefixLogicalCfg] using hrun
  exact ⟨FoundGuardedParentOutcome.logical core hreaches hinside⟩

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
