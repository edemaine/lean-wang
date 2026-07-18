/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineCoordinates
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlResumedRouteEmbedding

/-!
# Embedding guard-free preserving-route callers

An arbitrary genuine generated search may select a command partway through a
preserving recovery route.  Navigation commands have no collision branch, so
their exact found-state continuation does not require the one-cell guard used
for marker shifts.  This file advances such a command through the remaining
route, reconstructs its logical endpoint, and retains the comparison needed
for monotone guarded re-entry.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineRouteEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting
open CounterControlGuardedParentContinuation
open CounterControlParentContinuation CounterControlParentEmbedding
open CounterControlSearchSystem
open CounterControlRouteSuffixMortality
open CounterControlResumedRouteEmbedding
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩





/-- A selected guard-free route caller, advanced from its exact found state
to the route's advertised endpoint. -/
structure GenuineRouteEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source searchSlot directSlot : Nat)
    (after : ControlRef) (route : List MarkerValidation.Leg) : Type where
  suffix : RouteSuffixReached base c growth source searchSlot directSlot
    after route current.selectedRaw current.foundTape
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    ⟨resolve base c after, suffix.finish⟩

/-- Advance any selected preserving-route command through the exact
remaining route suffix.  Exact success is unconditional here because every
route command is a preserving boundary navigation. -/
theorem progressedRoute
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
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
    Nonempty (GenuineRouteEnd current growth source searchSlot directSlot
      after route) := by
  have hfree : ¬ ShiftDestinationOccupied current.selectedRaw
      current.foundTape :=
    CounterControlRouteSuffixMortality.destinationFree_of_mem_routeCommandsAux
      growth source searchSlot directSlot after route hroute current.foundTape
  have hsuccess : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨resolve base c (rawSuccessRef current.selectedRaw),
        exactSuccessTape current.selectedRaw current.foundTape⟩ := by
    rw [current.foundCfg_eq]
    exact current.foundContinuationOutcome.reachesSuccess_of_destinationFree
      hfree
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

/-! ## Exact route coordinates -/

/-- The selected route command reads the boundary named by its retained
route position at the found tape. -/
theorem GenuineRouteEnd.current_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GenuineRouteEnd current growth source searchSlot directSlot
      after route) :
    current.foundTape.read =
      boundarySymbol progress.suffix.current.target := by
  have htarget := current.selectedRaw_target_matches_foundTape
  rw [CounterControlCommandAt.compileRawCommand_spec] at htarget
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    Target.Matches, compileNavigationAction] using htarget

/-- The genuine search is exactly the selected route leg. -/
theorem GenuineRouteEnd.current_gap
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GenuineRouteEnd current growth source searchSlot directSlot
      after route) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary progress.suffix.current.target).Matches
      current.outer
      (orient growth progress.suffix.current.direction)
      current.distance := by
  have hgap := current.gap
  rw [← current.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [progress.suffix.raw_eq,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    Command.searchDirection, compileNavigationAction] using hgap

/-- Resolving the genuine gap reaches `foundTape`, in the selected route
leg's physical direction. -/
theorem GenuineRouteEnd.current_foundTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source searchSlot directSlot : Nat}
    {after : ControlRef} {route : List MarkerValidation.Leg}
    (progress : GenuineRouteEnd current growth source searchSlot directSlot
      after route) :
    current.outer.moveN
      (orient growth progress.suffix.current.direction) current.distance =
        current.foundTape := by
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
    (fun direction => current.outer.moveN direction current.distance)
    hdirection

/-! ## Recovery routes reach a containing logical core -/

/-- The proof-neutral result of reconstructing a logical core from a
rightward route suffix.  Genuine and guarded callers package the same strict
geometric containment into different global outcomes. -/
structure RouteLogicalCertificate
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) : Type where
  core : LogicalCore base c
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) core.cfg
  inside : current.distance < layoutEnd core.registers

/-- A consecutive rightward guard-free recovery suffix ending at logical
boundary `4` reconstructs a neutral core-and-containment certificate. -/
theorem certificate_of_toFour_endpoint
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source searchSlot directSlot targetState : Nat)
    (route : List MarkerValidation.Leg)
    (progress : GenuineRouteEnd current growth source searchSlot directSlot
      (.logical growth targetState) route)
    (htargetState : targetState < logicalSpan)
    (hroute : ∃ routeSource : Fin 5, ToFour routeSource route) :
    Nonempty (RouteLogicalCertificate current) := by
  rcases hroute with ⟨routeSource, hroute⟩
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have himmortalLogical := FullTM0.ImmortalFrom.of_reaches himmortal
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
      (Target.boundary i.succ).Matches current.outer
      (orient growth .right) current.distance := by
    have hgap' := progress.current_gap
    rw [hcurrent] at hgap'
    exact hgap'
  have hfound : current.outer.moveN (orient growth .right)
        current.distance =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    have hfound' := progress.current_foundTape
    rw [hcurrent] at hfound'
    exact hfound'.trans hfoundBoundary
  have hinside : current.distance < layoutEnd registers :=
    rightGap_distance_lt_layoutEnd hcore i current.distance hgap hfound
  have hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) core.cfg := by
    have hrun := progress.reaches
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨logicalState base c growth targetState,
        progress.suffix.finish⟩ at hrun
    rw [hcenter] at hrun
    simpa [core, LogicalCore.cfg, LogicalCore.frame,
      LogicalCore.abstract, prefixLogicalCfg] using hrun
  exact ⟨⟨core, hreaches, hinside⟩⟩

/-- A consecutive rightward guard-free recovery suffix ending at logical
boundary `4` reaches a core containing the current gap. -/
theorem logical_of_toFour_endpoint
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source searchSlot directSlot targetState : Nat)
    (route : List MarkerValidation.Leg)
    (progress : GenuineRouteEnd current growth source searchSlot directSlot
      (.logical growth targetState) route)
    (htargetState : targetState < logicalSpan)
    (hroute : ∃ routeSource : Fin 5, ToFour routeSource route) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  rcases certificate_of_toFour_endpoint base c hmortal current himmortal
      growth source searchSlot directSlot targetState route progress
      htargetState hroute with ⟨certificate⟩
  exact ⟨.logical certificate.core certificate.reaches certificate.inside.le⟩

/-- A guard-free increment-recovery caller reaches a containing logical
core.  The source rule supplies the target-state bound. -/
theorem incrementRecovery_logical_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source secondarySearchBase
        (bodyDirectBase + 2) (.logical growth next)
        (AnchoredCounterGeometry.routeFromIncrement register)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
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

/-- A guard-free zero-recovery caller reaches a containing logical core.  The
source rule supplies the target-state bound. -/
theorem zeroRecovery_logical_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source zeroSearchBase zeroDirectBase
        (.logical growth ifZero)
        (AnchoredCounterGeometry.routeFromZero register)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
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

end CounterControlGenuineRouteEmbedding
end Hooper
end Kari
end LeanWang
