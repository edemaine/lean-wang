/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlLooseFrameTotal

/-!
# Unconditional resolution of direction-free finite counter envelopes

An arbitrary validated counter core can carry any tag at logical coordinate
zero.  Its direction need not agree with the direction of the active frame,
so cleanup cannot yet be followed through the shared return dispatcher to a
resumed search.  The cleanup itself is nevertheless direction independent:
it erases the finite core and reaches the shared return state.

This file repeats the loose-frame mortality argument with that weaker final
outcome.  It is the interface needed by the arbitrary-entry converse, where
the generic controller normalization theorem classifies the return tag only
after the finite frame has been erased.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLooseEnvelopeTotal

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open OrientedMarkerTape
open CounterControlPlan CounterControlSearchSystem
open CounterControlBridge
open CounterControlFrameBacking CounterControlInstructionResolution
open CounterControlInstructionSemantics CounterControlSearchResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Stable data of a finite frame, without any relationship between the
saved tag and the active growth direction. -/
structure LooseEnvelope (base : Nat) (c : Nat.Partrec.Code) where
  growth : Turing.Dir
  returnTag : Fin numTags
  outerDistance : Nat
  outerTarget : Target numTags
  outer : FullTM0.Tape (Symbol numTags)

/-- Active finite-frame specification at the current register payload. -/
def looseSpec {base : Nat} {c : Nat.Partrec.Code}
    (frame : LooseEnvelope base c) (registers : Registers)
    (hcore : layoutEnd registers < frame.outerDistance) : Spec numTags where
  growth := frame.growth
  returnTag := frame.returnTag
  registers := registers
  outerDistance := frame.outerDistance
  outerTarget := frame.outerTarget
  core_before_target := hcore

/-- Concrete logical configuration inside a direction-free loose envelope. -/
def logicalCfg (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseEnvelope base c) (abstract : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨logicalState base c frame.growth abstract.state,
    atLogical frame.growth T (layoutEnd abstract.registers)⟩

/-- Exact finite-envelope invariant during the abstract counter trace. -/
inductive LooseLogical (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseEnvelope base c) (abstract : CounterMachine.Cfg)
    (concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop where
  | intro
      (core_before_target :
        layoutEnd abstract.registers < frame.outerDistance)
      (tape : FullTM0.Tape (Symbol numTags))
      (backed : BackedBy
        (looseSpec frame abstract.registers core_before_target)
        tape frame.outer)
      (concrete_eq : concrete = logicalCfg base c frame abstract tape)
      (state_lt : abstract.state < logicalSpan)

/-- The finite envelope has been erased and control has reached the shared
return dispatcher.  The resulting tape is existential because no dispatch
claim is made here. -/
def ReachesReturn (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseEnvelope base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ U : FullTM0.Tape (Symbol numTags),
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
      ⟨controllerReturn base c frame.growth, U⟩

/-- From the exact outward-collision endpoint, direction-independent cleanup
either reaches the shared return dispatcher or halts. -/
theorem machine_reaches_collisionReturn_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (source : Nat)
    {spec : Spec numTags}
    {T outer : FullTM0.Tape (Symbol numTags)}
    (hback : BackedBy spec T outer)
    (hcollision : layoutEnd spec.registers + 1 = spec.outerDistance)
    (hshort : ShortResolves base c spec.outerDistance)
    (hentry : CounterControlCleanupSemantics.cleanupEntryRule
      spec.growth source ∈ rawDirectRules)
    (hcommands : ∀ raw, raw ∈ cleanupCommands spec.growth source →
      raw ∈ rawCommands) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩
        ⟨controllerReturn base c spec.growth,
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterZero spec T) 0⟩ ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef spec.growth source testDirectSlot),
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterFour spec T)
            spec.outerDistance⟩ := by
  have h := hback.represents
  have htargetRead :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance).read =
        logicalTape spec.growth T spec.outerDistance := by
    rw [atLogical_read]
    simp only [CounterControlCleanupSemantics.afterFour,
      CounterControlCleanupSemantics.clearBoundary]
    apply writeLogical_of_ne
    rw [boundaryOffset_four]
    omega
  have htargetNonblank :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance).read ≠ blankSymbol := by
    rw [htargetRead]
    intro hblank
    exact target_not_blank spec.outerTarget (hblank ▸ h.target)
  have hentryRunLocal :=
    CounterControlDirectSemantics.reaches_directRule base c
      (CounterControlCleanupSemantics.cleanupEntryRule spec.growth source)
      hentry
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance) htargetNonblank
  have hmove :
      (atLogical spec.growth
        (CounterControlCleanupSemantics.afterFour spec T)
        spec.outerDistance).move (orient spec.growth .left) =
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          (layoutEnd spec.registers) := by
    rw [← hcollision, orient_eq_orientDirection, atLogical_move_left]
  have hentryRun : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef spec.growth source testDirectSlot),
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          spec.outerDistance⟩
      ⟨searchState base c ⟨spec.growth, source, cleanupSearchBase⟩,
        atLogical spec.growth
          (CounterControlCleanupSemantics.afterFour spec T)
          (layoutEnd spec.registers)⟩ := by
    simp only [CounterControlCleanupSemantics.cleanupEntryRule] at hentryRunLocal
    rw [hmove] at hentryRunLocal
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [CounterControlCleanupSemantics.cleanupEntryRule, searchRef,
      CounterControlPlan.resolve] using hentryRunLocal
  rcases machine_reaches_cleanup_return_or_halts base c
      spec.outerDistance source hshort h rfl hcommands with
    hreturn | hhalts
  · exact Or.inl (hentryRun.trans hreturn)
  · exact Or.inr (FullTM0.HaltsFrom.of_reaches hentryRun hhalts)

/-- One defined abstract instruction either advances the finite envelope,
reaches the shared return dispatcher after collision cleanup, or halts. -/
theorem oneStepResolves
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseEnvelope base c)
    {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (hlogical : LooseLogical base c frame current concrete) :
    (∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete nextConcrete ∧
      LooseLogical base c frame next nextConcrete) ∨
      ReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hlogical with ⟨hcore, T, hback, rfl, _hstate⟩
  let spec := looseSpec frame current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_resolves_counterStep base c current next
    (spec := spec) hback (by simp [spec, looseSpec]) hstep
    (CounterControlLooseFrameMortality.shortResolves_all
      base c spec.outerDistance)
  rcases hrun with hnext | hcollision | hhalts
  · rcases hnext with ⟨hnextCore, nextTape, hreach, hnextBack⟩
    have hnextCore' : layoutEnd next.registers < frame.outerDistance := by
      simpa [spec, looseSpec] using hnextCore
    have hnextBack' : BackedBy
        (looseSpec frame next.registers hnextCore')
        nextTape frame.outer := by
      simpa [spec, looseSpec, updateSpec] using hnextBack
    let nextConcrete := logicalCfg base c frame next nextTape
    left
    refine ⟨nextConcrete, ?_, ?_⟩
    · simpa [nextConcrete, logicalCfg, spec, looseSpec] using hreach
    · exact ⟨hnextCore', nextTape, hnextBack', rfl,
        CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep⟩
  · rcases hcollision with
      ⟨register, target, hrule, hcollision, hcollisionReach⟩
    have hentry : CounterControlCleanupSemantics.cleanupEntryRule
        spec.growth current.state ∈ rawDirectRules := by
      apply directRule_mem_rawDirectRules_of_rule spec.growth hrule
      change CounterControlCleanupSemantics.cleanupEntryRule
          spec.growth current.state ∈
        validationRules spec.growth current.state ++
          incrementRules spec.growth current.state target register
      apply List.mem_append_right
      simp [CounterControlCleanupSemantics.cleanupEntryRule, incrementRules]
    have hcleanupCommands : ∀ raw,
        raw ∈ cleanupCommands spec.growth current.state →
          raw ∈ rawCommands := by
      intro raw hraw
      apply command_mem_rawCommands_of_rule spec.growth hrule
      simp [commandsForRule, incrementCommands, hraw]
    have hcleanup := machine_reaches_collisionReturn_or_halts base c
      current.state hback hcollision
      (CounterControlLooseFrameMortality.shortResolves_all
        base c spec.outerDistance)
      hentry hcleanupCommands
    rcases hcleanup with hreturn | hhalts
    · right
      left
      refine ⟨atLogical spec.growth
          (CounterControlCleanupSemantics.afterZero spec T) 0, ?_⟩
      have hcombined := hcollisionReach.trans hreturn
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c frame.growth current.state,
          atLogical frame.growth T (layoutEnd current.registers)⟩
        ⟨controllerReturn base c frame.growth,
          atLogical spec.growth
            (CounterControlCleanupSemantics.afterZero spec T) 0⟩
      exact hcombined
    · right
      right
      simpa [logicalCfg, spec, looseSpec] using
        (FullTM0.HaltsFrom.of_reaches hcollisionReach hhalts)
  · right
    right
    simpa [logicalCfg, spec, looseSpec] using hhalts

/-- The direction-free one-step law lifts over a finite abstract trace. -/
theorem reaches_loose_or_return_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseEnvelope base c)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (CounterMachine.step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      LooseLogical base c frame finish finishConcrete) ∨
      ReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hprefix hlast ih =>
      rcases ih hlogical with hcurrent | hreturn | hhalts
      · rcases hcurrent with
          ⟨currentConcrete, hprefixConcrete, hcurrent⟩
        have hlast' : CounterMachine.step GlobalSourceProgram.program
            current = some next := by
          simpa using hlast
        rcases oneStepResolves base c frame hlast' hcurrent with
          hnext | hreturn | hhalts
        · rcases hnext with ⟨nextConcrete, hstepConcrete, hnext⟩
          exact Or.inl
            ⟨nextConcrete, hprefixConcrete.trans hstepConcrete, hnext⟩
        · right
          left
          rcases hreturn with ⟨U, hreturn⟩
          exact ⟨U, hprefixConcrete.trans hreturn⟩
        · exact Or.inr (Or.inr
            (FullTM0.HaltsFrom.of_reaches hprefixConcrete hhalts))
      · exact Or.inr (Or.inl hreturn)
      · exact Or.inr (Or.inr hhalts)

/-- A mortal abstract trace in a finite envelope either reaches the shared
return dispatcher or reaches a concrete halt. -/
theorem return_or_halts_of_abstract_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseEnvelope base c)
    {start : CounterMachine.Cfg}
    (hhalts : CounterLiveness.HaltsFrom
      GlobalSourceProgram.program start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    ReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  rcases reaches_loose_or_return_or_halts base c frame hterminalReach
      hlogical with hfinish | hreturn | hhalts
  · rcases hfinish with
      ⟨finishConcrete, hfinishReach, hfinishLogical⟩
    rcases hfinishLogical with ⟨_hcore, T, _hback, rfl, hstate⟩
    right
    apply FullTM0.HaltsFrom.of_reaches hfinishReach
    refine ⟨logicalCfg base c frame terminal T,
      Relation.ReflTransGen.refl, ?_⟩
    simpa [logicalCfg] using
      (CounterControlTerminalSemantics.machine_step_eq_none_of_counter_step_none
        base c frame.growth terminal
        (atLogical frame.growth T (layoutEnd terminal.registers))
        hstate hterminal)
  · exact Or.inl hreturn
  · exact Or.inr hhalts

/-- An immortal abstract counter run cannot remain forever inside one finite
envelope: unbounded clock growth contradicts its strict geometric bound. -/
theorem return_or_halts_of_abstract_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseEnvelope base c)
    {start : CounterMachine.Cfg}
    (himmortal : Dynamics.ImmortalFrom
      (CounterMachine.step GlobalSourceProgram.program) start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    ReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases GlobalSourceLiveness.cycleLaws
      |>.exists_reachable_logical_clock_ge_of_immortalFrom
        himmortal frame.outerDistance with
    ⟨finish, hreach, _hfinishLogical, hclock⟩
  rcases reaches_loose_or_return_or_halts base c frame hreach hlogical with
    hfinish | hreturn | hhalts
  · rcases hfinish with
      ⟨_finishConcrete, _hfinishReach, hfinishLoose⟩
    rcases hfinishLoose with
      ⟨hcore, _tape, _backed, _concreteEq, _stateLt⟩
    have hclockEnd := clock_lt_layoutEnd finish.registers
    omega
  · exact Or.inl hreturn
  · exact Or.inr hhalts

/-- Every direction-free finite envelope, from an arbitrary abstract
configuration, eventually reaches the shared return dispatcher or halts. -/
theorem return_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseEnvelope base c)
    {start : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    ReachesReturn base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases CounterLiveness.haltsFrom_or_immortalFrom
      GlobalSourceProgram.program start with hhalts | himmortal
  · exact return_or_halts_of_abstract_haltsFrom base c frame
      hhalts hlogical
  · exact return_or_halts_of_abstract_immortalFrom base c frame
      himmortal hlogical

end

end CounterControlLooseEnvelopeTotal
end Hooper
end Kari
end LeanWang
