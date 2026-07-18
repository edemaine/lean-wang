/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlFrameSimulation
import LeanWang.Kari.Hooper.CounterLiveness
import LeanWang.Kari.Hooper.CounterControlTerminalSemantics

/-!
# Lifting abstract counter traces through one framed computation

This file separates Hooper's induction over counter instructions from the
compiled implementation of any particular instruction.  A one-step forward
law may either advance the exact logical frame or clean it up to the suspended
search boundary.  Its resolving counterpart has one additional outcome: the
concrete controller halts.

Both laws lift over arbitrary finite abstract traces.  Two endpoint lemmas
then package the uses needed by the Basic Lemma and its converse: an abstract
clock at least the frame distance forces cleanup, while an abstract terminal
configuration forces concrete cleanup or halting.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlTraceSimulation

open Turing CounterMachine
open BoundedMarkerProgram
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameSimulation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The concrete computation has restored the exact boundary of its suspended
search frame. -/
def ReachesBoundary (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ boundary,
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start boundary ∧
    BoundaryAt base c frame boundary

/-- Forward implementation obligation for one defined abstract counter step
inside a fixed suspended frame. -/
def OneStepGrows (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) : Prop :=
  ∀ {current next : CounterMachine.Cfg}
      {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    step GlobalSourceProgram.program current = some next →
    LogicalFrame base c frame current concrete →
      (∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        LogicalFrame base c frame next nextConcrete) ∨
      ReachesBoundary base c frame concrete

/-- Resolving implementation obligation for one defined abstract counter
step.  Failed shorter searches are allowed to expose a concrete halt. -/
def OneStepResolves (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) : Prop :=
  ∀ {current next : CounterMachine.Cfg}
      {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    step GlobalSourceProgram.program current = some next →
    LogicalFrame base c frame current concrete →
      (∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        LogicalFrame base c frame next nextConcrete) ∨
      ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) concrete

/-- Collision-free one-step law.  This is the form used when a uniform bound
shows that every layout in a finite abstract trace stays strictly inside the
suspended target. -/
def OneStepContinues (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) : Prop :=
  ∀ {current next : CounterMachine.Cfg}
      {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    step GlobalSourceProgram.program current = some next →
    LogicalFrame base c frame current concrete →
      ∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        LogicalFrame base c frame next nextConcrete

/-- Halting-aware collision-free law used for a bounded mortal abstract
trace. -/
def OneStepContinuesOrHalts (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) : Prop :=
  ∀ {current next : CounterMachine.Cfg}
      {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State},
    step GlobalSourceProgram.program current = some next →
    LogicalFrame base c frame current concrete →
      (∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        LogicalFrame base c frame next nextConcrete) ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) concrete

/-! ## Finite trace lifting -/

/-- A forward one-step law lifts over every finite abstract counter trace. -/
theorem reaches_logical_or_boundary
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepGrows base c frame)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      LogicalFrame base c frame finish finishConcrete) ∨
    ReachesBoundary base c frame concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hpath hstep ih =>
      rcases ih hlogical with hcurrent | hboundary
      · rcases hcurrent with ⟨currentConcrete, hprefix, hcurrent⟩
        have hstep' : step GlobalSourceProgram.program current = some next := by
          simpa using hstep
        rcases hlaw hstep' hcurrent with hnext | hboundary
        · rcases hnext with ⟨nextConcrete, hlast, hnext⟩
          exact Or.inl ⟨nextConcrete, hprefix.trans hlast, hnext⟩
        · rcases hboundary with ⟨boundary, hlast, hboundary⟩
          exact Or.inr ⟨boundary, hprefix.trans hlast, hboundary⟩
      · exact Or.inr hboundary

/-- The resolving one-step law similarly lifts over every finite trace, with
concrete halting propagated back across the already executed prefix. -/
theorem reaches_logical_or_boundary_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepResolves base c frame)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      LogicalFrame base c frame finish finishConcrete) ∨
    ReachesBoundary base c frame concrete ∨
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hpath hstep ih =>
      rcases ih hlogical with hcurrent | hboundary | hhalts
      · rcases hcurrent with ⟨currentConcrete, hprefix, hcurrent⟩
        have hstep' : step GlobalSourceProgram.program current = some next := by
          simpa using hstep
        rcases hlaw hstep' hcurrent with hnext | hboundary | hhalts
        · rcases hnext with ⟨nextConcrete, hlast, hnext⟩
          exact Or.inl ⟨nextConcrete, hprefix.trans hlast, hnext⟩
        · rcases hboundary with ⟨boundary, hlast, hboundary⟩
          exact Or.inr (Or.inl
            ⟨boundary, hprefix.trans hlast, hboundary⟩)
        · exact Or.inr (Or.inr
            (FullTM0.HaltsFrom.of_reaches hprefix hhalts))
      · exact Or.inr (Or.inl hboundary)
      · exact Or.inr (Or.inr hhalts)

/-- A collision-free one-step law lifts to an exact represented endpoint over
every finite abstract trace. -/
theorem reaches_logical
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepContinues base c frame)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    ∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      LogicalFrame base c frame finish finishConcrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hpath hstep ih =>
      rcases ih hlogical with ⟨currentConcrete, hprefix, hcurrent⟩
      have hstep' : step GlobalSourceProgram.program current = some next := by
        simpa using hstep
      rcases hlaw hstep' hcurrent with
        ⟨nextConcrete, hlast, hnext⟩
      exact ⟨nextConcrete, hprefix.trans hlast, hnext⟩

/-- Halting-aware collision-free semantics likewise lifts over a finite
abstract trace. -/
theorem reaches_logical_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepContinuesOrHalts base c frame)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    (∃ finishConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete finishConcrete ∧
      LogicalFrame base c frame finish finishConcrete) ∨
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      concrete := by
  induction hreach generalizing concrete with
  | refl =>
      exact Or.inl ⟨concrete, Relation.ReflTransGen.refl, hlogical⟩
  | @tail current next hpath hstep ih =>
      rcases ih hlogical with hcurrent | hhalts
      · rcases hcurrent with ⟨currentConcrete, hprefix, hcurrent⟩
        have hstep' : step GlobalSourceProgram.program current = some next := by
          simpa using hstep
        rcases hlaw hstep' hcurrent with hnext | hhalts
        · rcases hnext with ⟨nextConcrete, hlast, hnext⟩
          exact Or.inl ⟨nextConcrete, hprefix.trans hlast, hnext⟩
        · exact Or.inr (FullTM0.HaltsFrom.of_reaches hprefix hhalts)
      · exact Or.inr hhalts

/-! ## Endpoint eliminations -/

/-- If a forward abstract trace reaches a clock at least the suspended-search
distance, concrete cleanup must have occurred somewhere along the trace. -/
theorem reachesBoundary_of_clock_ge
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepGrows base c frame)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish)
    (hclock : frame.distance ≤ finish.registers.clock)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    ReachesBoundary base c frame concrete := by
  rcases reaches_logical_or_boundary base c hlaw hreach hlogical with
    hfinish | hboundary
  · rcases hfinish with ⟨finishConcrete, _hfinishReach, hfinish⟩
    exact False.elim (hfinish.not_distance_le_clock hclock)
  · exact hboundary

/-- Resolving counterpart: a large abstract clock forces concrete cleanup or
concrete halting. -/
theorem reachesBoundary_or_halts_of_clock_ge
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepResolves base c frame)
    {start finish : CounterMachine.Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish)
    (hclock : frame.distance ≤ finish.registers.clock)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases reaches_logical_or_boundary_or_halts base c hlaw hreach hlogical with
    hfinish | hboundary | hhalts
  · rcases hfinish with ⟨finishConcrete, _hfinishReach, hfinish⟩
    exact False.elim (hfinish.not_distance_le_clock hclock)
  · exact Or.inl hboundary
  · exact Or.inr hhalts

/-- If the abstract counter trace reaches a genuine terminal configuration,
the resolving concrete trace either cleans up first or reaches a terminal
full-tape configuration at the represented logical endpoint. -/
theorem reachesBoundary_or_halts_of_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepResolves base c frame)
    {start : CounterMachine.Cfg}
    (hhalts : CounterLiveness.HaltsFrom
      GlobalSourceProgram.program start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    ReachesBoundary base c frame concrete ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        concrete := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  rcases reaches_logical_or_boundary_or_halts base c hlaw hterminalReach
      hlogical with hfinish | hboundary | hhalts
  · rcases hfinish with ⟨finishConcrete, hfinishReach, hfinish⟩
    rcases hfinish with ⟨hcore, T, _hback, rfl, hstate⟩
    right
    refine ⟨logicalCfg base c frame terminal T, hfinishReach, ?_⟩
    simpa [logicalCfg] using
      (CounterControlTerminalSemantics.machine_step_eq_none_of_counter_step_none
        base c (frameGrowth base c frame) terminal
        (FramedMarkerTape.atLogical (frameGrowth base c frame) T
          (FramedMarkerTape.layoutEnd terminal.registers))
        hstate hterminal)
  · exact Or.inl hboundary
  · exact Or.inr hhalts

/-- If collision has been excluded throughout a finite abstract halting run,
the concrete controller itself reaches a terminal configuration. -/
theorem haltsFrom_of_abstract_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hlaw : OneStepContinuesOrHalts base c frame)
    {start : CounterMachine.Cfg}
    (hhalts : CounterLiveness.HaltsFrom
      GlobalSourceProgram.program start)
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hlogical : LogicalFrame base c frame start concrete) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      concrete := by
  rcases hhalts with ⟨terminal, hterminalReach, hterminal⟩
  rcases reaches_logical_or_halts base c hlaw hterminalReach hlogical with
    hfinish | hhalts
  · rcases hfinish with ⟨finishConcrete, hfinishReach, hfinish⟩
    rcases hfinish with ⟨_hcore, T, _hback, rfl, hstate⟩
    apply FullTM0.HaltsFrom.of_reaches hfinishReach
    refine ⟨logicalCfg base c frame terminal T,
      Relation.ReflTransGen.refl, ?_⟩
    simpa [logicalCfg] using
      (CounterControlTerminalSemantics.machine_step_eq_none_of_counter_step_none
        base c (frameGrowth base c frame) terminal
        (FramedMarkerTape.atLogical (frameGrowth base c frame) T
          (FramedMarkerTape.layoutEnd terminal.registers))
        hstate hterminal)
  · exact hhalts

end

end CounterControlTraceSimulation
end Hooper
end Kari
end LeanWang
