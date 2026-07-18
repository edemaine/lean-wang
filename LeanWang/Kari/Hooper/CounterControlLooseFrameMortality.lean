/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFiniteConverse
import LeanWang.Kari.Hooper.CounterControlInstructionResolution
import LeanWang.Kari.Hooper.GlobalSourceMortality

/-!
# Mortality inside loose finite counter frames

For the ordinary converse Basic Lemma, a suspended outer symbol must match
the target of the search which created the frame.  The mortality argument
needs less: the outer symbol may be any nonblank symbol.  A mortal canonical
counter trace either halts inside such a loose frame or collides with its
outer boundary and restores the saved search.

This file factors that target-independent statement from the later induction
on a wrong search gap.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLooseFrameMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameBacking CounterControlInstructionResolution
open CounterControlInstructionSemantics CounterControlSearchResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Stable data of a finite frame whose outer target need not be the target
selected by its return tag. -/
structure LooseFrame (base : Nat) (c : Nat.Partrec.Code) where
  growth : Turing.Dir
  returnTag : Fin numTags
  outerDistance : Nat
  outerTarget : Target numTags
  outer : FullTM0.Tape (Symbol numTags)
  returnDirection :
    (compileCommand base c returnTag).searchDirection = growth

/-- Active finite-frame specification at the current register payload. -/
def looseSpec {base : Nat} {c : Nat.Partrec.Code}
    (frame : LooseFrame base c) (registers : Registers)
    (hcore : layoutEnd registers < frame.outerDistance) : Spec numTags where
  growth := frame.growth
  returnTag := frame.returnTag
  registers := registers
  outerDistance := frame.outerDistance
  outerTarget := frame.outerTarget
  core_before_target := hcore

/-- Concrete logical configuration inside a loose frame. -/
def logicalCfg (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseFrame base c) (abstract : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨logicalState base c frame.growth abstract.state,
    atLogical frame.growth T (layoutEnd abstract.registers)⟩

/-- Exact loose-frame invariant during the abstract counter trace. -/
inductive LooseLogical (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseFrame base c) (abstract : CounterMachine.Cfg)
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

/-- Exact restored configuration of the search selected by the saved tag. -/
def boundaryCfg (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseFrame base c) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨resumeState (CanonicalInitializer.radius c)
      (CounterControlSearchSystem.commandOffset base c frame.returnTag),
    frame.outer⟩

/-- The loose computation has restored its saved outer tape and search. -/
def ReachesBoundary (base : Nat) (c : Nat.Partrec.Code)
    (frame : LooseFrame base c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
    (boundaryCfg base c frame)

/-- Every shorter genuine compiled search resolves, uniformly in the loose
frame distance. -/
theorem shortResolves_all (base : Nat) (c : Nat.Partrec.Code)
    (limit : Nat) : ShortResolves base c limit := by
  intro distance _hdistance
  exact CounterControlFiniteConverse.resolves_all base c distance

/-- One defined abstract instruction either advances the loose frame,
restores its outer search after a collision, or halts. -/
theorem oneStepResolves
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseFrame base c)
    {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    (hlogical : LooseLogical base c frame current concrete) :
    (∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete nextConcrete ∧
      LooseLogical base c frame next nextConcrete) ∨
      ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hlogical with ⟨hcore, T, hback, rfl, _hstate⟩
  let spec := looseSpec frame current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_resolves_counterStep base c current next
    (spec := spec) hback (by simp [spec, looseSpec]) hstep
    (shortResolves_all base c spec.outerDistance)
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
    have hreturnDirection :
        (compileCommand base c spec.returnTag).searchDirection =
          spec.growth := by
      simpa [spec, looseSpec] using frame.returnDirection
    have hcleanup := machine_reaches_collisionCleanup_or_halts base c
      current.state hback hreturnDirection hcollision
      (shortResolves_all base c spec.outerDistance) hentry hcleanupCommands
    rcases hcleanup with hboundary | hhalts
    · right
      left
      have hcombined : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c spec.growth current.state,
            atLogical spec.growth T (layoutEnd spec.registers)⟩
          ⟨resumeState (CanonicalInitializer.radius c)
              (searchState base c
                (rawCommands.get spec.returnTag).address), frame.outer⟩ :=
        hcollisionReach.trans hboundary
      simpa [ReachesBoundary, boundaryCfg, logicalCfg, spec, looseSpec,
        CounterControlSearchSystem.commandOffset] using hcombined
    · right
      right
      simpa [logicalCfg, spec, looseSpec] using
        (FullTM0.HaltsFrom.of_reaches hcollisionReach hhalts)
  · right
    right
    simpa [logicalCfg, spec, looseSpec] using hhalts

/-- The loose one-step law lifts over a finite abstract trace. -/
theorem reaches_loose_or_boundary_or_halts
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseFrame base c)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (CounterMachine.step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      LooseLogical base c frame finish finishConcrete) ∨
      ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hprefix hlast ih =>
      rcases ih hlogical with hcurrent | hboundary | hhalts
      · rcases hcurrent with
          ⟨currentConcrete, hprefixConcrete, hcurrent⟩
        have hlast' : CounterMachine.step GlobalSourceProgram.program
            current = some next := by
          simpa using hlast
        rcases oneStepResolves base c frame hlast' hcurrent with
          hnext | hboundary | hhalts
        · rcases hnext with ⟨nextConcrete, hstepConcrete, hnext⟩
          exact Or.inl
            ⟨nextConcrete, hprefixConcrete.trans hstepConcrete, hnext⟩
        · exact Or.inr (Or.inl (hprefixConcrete.trans hboundary))
        · exact Or.inr (Or.inr
            (FullTM0.HaltsFrom.of_reaches hprefixConcrete hhalts))
      · exact Or.inr (Or.inl hboundary)
      · exact Or.inr (Or.inr hhalts)

/-- A mortal abstract trace in a loose frame either restores the saved outer
search or reaches a concrete halt. -/
theorem boundary_or_halts_of_abstract_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (frame : LooseFrame base c)
    {start : CounterMachine.Cfg}
    (hhalts : CounterLiveness.HaltsFrom
      GlobalSourceProgram.program start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame start concrete) :
    ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  rcases reaches_loose_or_boundary_or_halts base c frame hterminalReach
      hlogical with hfinish | hboundary | hhalts
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
  · exact Or.inl hboundary
  · exact Or.inr hhalts

/-- Under source mortality, every loose representation of the designated
canonical counter input either unwinds or halts. -/
theorem not_fixedNonhalting_boundary_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (frame : LooseFrame base c)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LooseLogical base c frame
      (GlobalSourceSemantics.canonicalCounterCfg c) concrete) :
    ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  exact boundary_or_halts_of_abstract_haltsFrom base c frame
    (GlobalSourceMortality.not_fixedNonhalting_haltsFrom hmortal) hlogical

end

end CounterControlLooseFrameMortality
end Hooper
end Kari
end LeanWang
