/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlInstructionOutcome
import LeanWang.Kari.Hooper.CounterControlTraceSimulation

/-!
# Forward simulation of compiled counter instructions

This module connects the instruction-sized execution theorem for the
compiled counter controller to the proof-neutral framed trace interface.
Solved shorter searches make every defined abstract step either reach its
exact backed successor frame or clean up an increment which has reached the
suspended outer target.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInstructionSimulation

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameBacking CounterControlInstructionSemantics
open CounterControlFrameSimulation CounterControlTraceSimulation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Solved shorter searches implement one defined abstract counter step in a
fixed logical frame.  The collision outcome is packaged as the exact
suspended-search boundary. -/
theorem stepGrows
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortSearches base c frame.distance)
    {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : step GlobalSourceProgram.program current = some next)
    (hlogical : LogicalFrame base c frame current concrete) :
      (∃ nextConcrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          concrete nextConcrete ∧
        LogicalFrame base c frame next nextConcrete) ∨
      ReachesBoundary base c frame concrete := by
  rcases hlogical with
    ⟨hcore, T, hback, rfl, _hstate, hframe⟩
  let spec := activeSpec base c frame current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_reaches_abstractStep_solved base c current.state
    (spec := spec) hback
    (by
      simp [spec, activeSpec, frameGrowth,
        CounterControlSearchSystem.command])
    (by simpa [spec] using hstep)
    (by simpa [spec] using hshort)
  cases hrun with
  | logical hnextCore nextTape first hfirst hremaining hnextBack =>
      have hnextCore' : layoutEnd next.registers < frame.distance := by
        simpa [spec] using hnextCore
      have hnextBack' : BackedBy
          (activeSpec base c frame next.registers hnextCore')
          nextTape frame.outer := by
        simpa [spec, activeSpec, updateSpec] using hnextBack
      let nextConcrete := logicalCfg base c frame next nextTape
      have hnextFrame : LogicalFrame base c frame next nextConcrete := by
        exact ⟨hnextCore', nextTape, hnextBack', rfl,
          CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep,
          hframe⟩
      left
      refine ⟨nextConcrete, ?_, hnextFrame⟩
      have hfirst' : FullTM0.step
          (CounterControlNestingBridge.machine base c)
          (logicalCfg base c frame current T) = some first := by
        simpa [logicalCfg, spec, activeSpec] using hfirst
      have hremaining' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) first nextConcrete := by
        simpa [nextConcrete, logicalCfg, spec, activeSpec] using hremaining
      exact (Relation.ReflTransGen.single (by simpa using hfirst')).trans
        hremaining'
  | boundary _hcollision first hfirst hremaining =>
      right
      let boundary : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨resumeState (CanonicalInitializer.radius c)
            (commandOffset base c frame.saved),
          frame.outer⟩
      have hboundary : BoundaryAt base c frame boundary :=
        ⟨hframe, rfl⟩
      refine ⟨boundary, ?_, hboundary⟩
      have hfirst' : FullTM0.step
          (CounterControlNestingBridge.machine base c)
          (logicalCfg base c frame current T) = some first := by
        simpa [logicalCfg, spec, activeSpec] using hfirst
      have hremaining' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) first boundary := by
        simpa [boundary, spec, activeSpec,
          CounterControlSearchSystem.command,
          CounterControlSearchSystem.commandOffset] using hremaining
      exact (Relation.ReflTransGen.single (by simpa using hfirst')).trans
        hremaining'

/-- The compiled counter instructions satisfy the generic forward one-step
law in every frame whose shorter searches have already been solved. -/
theorem oneStepGrows
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortSearches base c frame.distance) :
    OneStepGrows base c frame := by
  intro current next concrete hstep hlogical
  exact stepGrows base c frame hshort hstep hlogical

/-- If the exact successor layout still fits before the suspended target,
the collision branch is impossible and the compiled instruction reaches the
exact logical successor frame. -/
theorem stepContinues_of_room
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortSearches base c frame.distance)
    {current next : CounterMachine.Cfg}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hstep : step GlobalSourceProgram.program current = some next)
    (hroom : layoutEnd next.registers < frame.distance)
    (hlogical : LogicalFrame base c frame current concrete) :
    ∃ nextConcrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        concrete nextConcrete ∧
      LogicalFrame base c frame next nextConcrete := by
  rcases hlogical with
    ⟨hcore, T, hback, rfl, _hstate, hframe⟩
  let spec := activeSpec base c frame current.registers hcore
  change BackedBy spec T frame.outer at hback
  have hrun := machine_reaches_abstractStep_solved base c current.state
    (spec := spec) hback
    (by
      simp [spec, activeSpec, frameGrowth,
        CounterControlSearchSystem.command])
    (by simpa [spec] using hstep)
    (by simpa [spec] using hshort)
  cases hrun with
  | logical hnextCore nextTape first hfirst hremaining hnextBack =>
      have hnextCore' : layoutEnd next.registers < frame.distance := by
        simpa [spec] using hnextCore
      have hnextBack' : BackedBy
          (activeSpec base c frame next.registers hnextCore')
          nextTape frame.outer := by
        simpa [spec, activeSpec, updateSpec] using hnextBack
      let nextConcrete := logicalCfg base c frame next nextTape
      refine ⟨nextConcrete, ?_, ?_⟩
      · have hfirst' : FullTM0.step
            (CounterControlNestingBridge.machine base c)
            (logicalCfg base c frame current T) = some first := by
          simpa [logicalCfg, spec, activeSpec] using hfirst
        have hremaining' : FullTM0.Reaches
            (CounterControlNestingBridge.machine base c) first
              nextConcrete := by
          simpa [nextConcrete, logicalCfg, spec, activeSpec] using hremaining
        exact (Relation.ReflTransGen.single (by simpa using hfirst')).trans
          hremaining'
      · exact ⟨hnextCore', nextTape, hnextBack', rfl,
          CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep,
          hframe⟩
  | boundary hcollision _first _hfirst _hremaining =>
      have hcollision' : layoutEnd next.registers = frame.distance := by
        simpa [spec] using hcollision.hitsTarget
      omega

/-- Uniform room hypotheses turn the room-conditional bridge into the
collision-free one-step law expected by exact finite-trace lifting. -/
theorem oneStepContinues
    (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (hshort : ShortSearches base c frame.distance)
    (hroom : ∀ {current next : CounterMachine.Cfg},
      step GlobalSourceProgram.program current = some next →
      layoutEnd next.registers < frame.distance) :
    OneStepContinues base c frame := by
  intro current next concrete hstep hlogical
  exact stepContinues_of_room base c frame hshort hstep (hroom hstep)
    hlogical

end

end CounterControlInstructionSimulation
end Hooper
end Kari
end LeanWang
