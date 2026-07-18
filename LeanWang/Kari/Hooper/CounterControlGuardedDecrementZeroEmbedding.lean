/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementBranchSearch
import LeanWang.Kari.Hooper.CounterControlGuardedInwardRouteMargin
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding

/-!
# Embedding the guarded decrement zero branch

The zero branch does not move any marker.  Its rightward recovery therefore
reconstructs the same canonical core in which the original guarded caller
was following the leftward decrement-entry route.  Reversing that retained
inward route supplies strict containment for the original caller, even
though the intermediate zero-branch search itself has distance zero and no
guard.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedDecrementZeroEmbedding

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation CounterControlParentEmbedding
open CounterControlGuardedParentContinuation
open CounterControlGuardedDecrementBranchSearch
open CounterControlGuardedDecrementEntry
open CounterControlGuardedInwardRouteMargin
open CounterControlResumedRouteEmbedding

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Reconstructed zero-branch endpoint with the original inward-route
coordinate and strict margin retained. -/
structure ZeroRecoveryCenteredEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (entry : ZeroSearchHandoff current growth source register
      ifZero ifPositive) : Type where
  core : LogicalCore base c
  core_represents : CoreRepresents core.registers growth core.tape
  route_finish : entry.route.route.suffix.finish =
    atLogical growth core.tape
      (boundaryOffset core.registers
        (MarkerSchedule.decrementStartBoundary register))
  reaches : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    (foundCfg current.current) core.cfg
  strictly_inside : current.current.distance < layoutEnd core.registers

/-- The zero recovery reconstructs a core containing the original guarded
decrement-entry caller, not merely its distance-zero branch search. -/
theorem zeroRecoveryCenteredEnd_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : ZeroSearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (ZeroRecoveryCenteredEnd current growth source register
      ifZero ifPositive entry) := by
  have himmortalEntry := zero_immortalFrom base c entry himmortal
  have himmortalFound := immortalFrom_foundCfg entry.next himmortalEntry
  have hcommands : ∀ command,
      command ∈ routeCommandsAux growth source zeroSearchBase
          zeroDirectBase (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) →
        command ∈ rawCommands := by
    intro command hmem
    exact CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth entry.route.rule_mem
        (by simp [commandsForRule, decrementCommands, hmem])
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source zeroSearchBase
          zeroDirectBase
          (AnchoredCounterGeometry.routeFromZero register) →
        rule ∈ rawDirectRules := by
    intro rule hmem
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth entry.route.rule_mem
    simp [directRulesForRule, decrementRules, hmem]
  rcases CounterControlGenuineRouteEmbedding.progressedRoute base c hmortal
      entry.next himmortalFound growth source zeroSearchBase zeroDirectBase
      (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register)
      (zero_command_mem entry) hcommands hcontinuations with
    ⟨progress⟩
  have himmortalLogical := FullTM0.ImmortalFrom.of_reaches himmortalFound
    progress.reaches
  change FullTM0.ImmortalFrom
    (CounterControlNestingBridge.machine base c)
    ⟨logicalState base c growth ifZero, progress.suffix.finish⟩
      at himmortalLogical
  have htargetState : ifZero < logicalSpan :=
    state_lt_logicalSpan
      (CounterControlAbstractTrace.target_mem_programStates
        entry.route.rule_mem (by simp [instructionTargets]))
  rcases CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
      base c hmortal growth ifZero htargetState progress.suffix.finish
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
    source := ifZero
    source_lt := htargetState
    registers := registers
    tape := coreTape
    limit := limit
    target := target
    represented := represented }
  rcases routeFromZero_toFour register with ⟨routeSource, hroute⟩
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have hread : entry.next.foundTape.read = boundarySymbol i.succ := by
    have hread' := progress.current_read
    rw [hcurrent] at hread'
    exact hread'
  have hentryFound : entry.next.foundTape =
      entry.route.route.suffix.finish := by
    rw [CounterControlGlobalUnnesting.GenuineSearch.foundTape,
      entry.distance_eq, FullTM0.Tape.moveN_zero, entry.outer_eq]
    cases growth <;>
      simp [branchTape, orient, FullTM0.Tape.move]
  have hstartLabel : i.succ =
      MarkerSchedule.decrementStartBoundary register := by
    apply (boundarySymbol_injective _ _).mp
    exact hread.symm.trans
      ((congrArg FullTM0.Tape.read hentryFound).trans
        (decrementEntry_finish_read entry.route.route))
  have hfoundBoundary : entry.next.foundTape =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    exact htail.start_eq hcore hread progress.suffix.tailGaps hcenter
  have hrouteFinish : entry.route.route.suffix.finish =
      atLogical growth coreTape
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register)) := by
    rw [← hentryFound, hfoundBoundary, hstartLabel]
  have hmargin : current.current.distance + 1 < layoutEnd registers :=
    parentDistance_lt_layoutEnd_of_toBoundary_endpoint current
      entry.route.route hcore hrouteFinish
        (routeToDecrementStart_toBoundary register)
  have hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current) core.cfg := by
    have hfound := reaches_foundCfg_of_immortal entry.next himmortalEntry
    have hrun := entry.reaches.trans (hfound.trans progress.reaches)
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨logicalState base c growth ifZero,
        progress.suffix.finish⟩ at hrun
    rw [hcenter] at hrun
    simpa [core, LogicalCore.cfg, LogicalCore.frame,
      LogicalCore.abstract, prefixLogicalCfg] using hrun
  refine ⟨⟨core, hcore, hrouteFinish, hreaches, ?_⟩⟩
  change current.current.distance < layoutEnd registers
  omega

/-- Consumer-facing guarded-parent outcome for the complete zero branch. -/
theorem zeroRecovery_foundGuardedParentOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : ZeroSearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedParentOutcome current) := by
  rcases zeroRecoveryCenteredEnd_of_immortal base c entry hmortal himmortal
      with ⟨endpoint⟩
  exact ⟨FoundGuardedParentOutcome.logical endpoint.core endpoint.reaches
    endpoint.strictly_inside⟩

end

end CounterControlGuardedDecrementZeroEmbedding
end Hooper
end Kari
end LeanWang
