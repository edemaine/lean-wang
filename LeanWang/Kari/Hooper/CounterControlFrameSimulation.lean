/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlStepGeometry
import LeanWang.Kari.Hooper.CounterControlSearchSystem

/-!
# Logical counter configurations inside one suspended search frame

The instruction compiler changes the represented registers and the concrete
tape, while the suspended search itself remains fixed.  This file packages
that stable outer data into a single relation between an abstract counter
configuration and a concrete full-tape configuration.

The relation is proof-neutral: it mentions neither the route used to execute
an instruction nor whether shorter searches solve or resolve.  It also
identifies the canonical nested configuration created by the initializer as
the first logical frame, ready for induction over an abstract counter trace.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlFrameSimulation

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlFrameBacking CounterControlStepGeometry

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Physical orientation selected by the command whose failed search owns a
nested frame. -/
def frameGrowth (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) : Turing.Dir :=
  (command base c frame.saved).searchDirection

/-- The active frame specification after replacing only the represented
register payload.  All suspended-search data is copied from `frame`. -/
def activeSpec (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) (registers : Registers)
    (hcore : layoutEnd registers < frame.distance) : Spec numTags where
  growth := frameGrowth base c frame
  returnTag := (command base c frame.saved).returnTag
  registers := registers
  outerDistance := frame.distance
  outerTarget := (command base c frame.saved).target
  core_before_target := hcore

@[simp] theorem activeSpec_growth (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) (registers : Registers)
    (hcore : layoutEnd registers < frame.distance) :
    (activeSpec base c frame registers hcore).growth =
      frameGrowth base c frame := rfl

@[simp] theorem activeSpec_registers (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search) (registers : Registers)
    (hcore : layoutEnd registers < frame.distance) :
    (activeSpec base c frame registers hcore).registers = registers := rfl

@[simp] theorem activeSpec_outerDistance (base : Nat)
    (c : Nat.Partrec.Code) (frame : Frame (Symbol numTags) Search)
    (registers : Registers)
    (hcore : layoutEnd registers < frame.distance) :
    (activeSpec base c frame registers hcore).outerDistance =
      frame.distance := rfl

@[simp] theorem activeSpec_outerTarget (base : Nat)
    (c : Nat.Partrec.Code) (frame : Frame (Symbol numTags) Search)
    (registers : Registers)
    (hcore : layoutEnd registers < frame.distance) :
    (activeSpec base c frame registers hcore).outerTarget =
      (command base c frame.saved).target := rfl

/-- Concrete logical-boundary configuration for a represented abstract
counter configuration. -/
def logicalCfg (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (cfg : CounterMachine.Cfg)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨logicalState base c (frameGrowth base c frame) cfg.state,
    atLogical (frameGrowth base c frame) T (layoutEnd cfg.registers)⟩

/-- Exact invariant carried while the canonical nested computation executes.
The current core is an overlay on the original outer tape, and the abstract
control state remains inside the compiled logical-state interval. -/
inductive LogicalFrame (base : Nat) (c : Nat.Partrec.Code)
    (frame : Frame (Symbol numTags) Search)
    (abstract : CounterMachine.Cfg)
    (concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop where
  | intro
      (core_before_target : layoutEnd abstract.registers < frame.distance)
      (tape : FullTM0.Tape (Symbol numTags))
      (backed : BackedBy
        (activeSpec base c frame abstract.registers core_before_target)
        tape frame.outer)
      (concrete_eq : concrete = logicalCfg base c frame abstract tape)
      (state_lt : abstract.state < logicalSpan)

namespace LogicalFrame

variable {base : Nat} {c : Nat.Partrec.Code}
variable {frame : Frame (Symbol numTags) Search}
variable {abstract : CounterMachine.Cfg}
variable {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}

/-- Every represented finite frame has clock strictly below the suspended
search distance. -/
theorem clock_lt_distance
    (h : LogicalFrame base c frame abstract concrete) :
    abstract.registers.clock < frame.distance := by
  rcases h with ⟨hcore, _T, _hback, _hconcrete, _hstate⟩
  exact (clock_lt_layoutEnd abstract.registers).trans hcore

/-- Contradiction form used at the endpoint of the growth argument. -/
theorem not_distance_le_clock
    (h : LogicalFrame base c frame abstract concrete) :
    ¬ frame.distance ≤ abstract.registers.clock :=
  Nat.not_le_of_gt h.clock_lt_distance

end LogicalFrame

/-! ## Initial and terminal frame interfaces -/

/-- The exact nested configuration produced by the shared initializer is the
logical representation of the canonical abstract counter input. -/
theorem logicalFrame_of_nestedAt (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    {concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hnested : NestedAt base c frame concrete) :
    LogicalFrame base c frame
      (GlobalSourceSemantics.canonicalCounterCfg c) concrete := by
  rcases hnested with ⟨hframe, rfl⟩
  let selected := command base c frame.saved
  have hfar : NestingMachine.bound (CanonicalInitializer.radius c) <
      frame.distance := hframe.2
  have hcore : layoutEnd (CanonicalInitializer.registers c) <
      frame.distance :=
    (frameSpec c selected frame.distance hfar).core_before_target
  let T := initializeTape c selected frame.outer
  refine ⟨?_, T, ?_, ?_,
    CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan c⟩
  · simpa [CanonicalInitializer.registers] using hcore
  · have hback := initializeTape_backedBy c selected frame.outer
        frame.distance hframe.1 hfar
    constructor
    · simpa [activeSpec, frameGrowth, selected, command, frameSpec,
        CanonicalInitializer.registers, T] using hback.installed
    · simpa [activeSpec, frameGrowth, selected, command, frameSpec,
        CanonicalInitializer.registers] using hback.searchGap
  · have hend : layoutEnd (CanonicalInitializer.registers c) =
        CanonicalInitializer.span c := by
      simpa [layoutEnd] using CanonicalInitializer.clockBoundary_registers c
    have hposition :
        layoutEnd (GlobalSourceSemantics.canonicalCounterCfg c).registers =
          CanonicalInitializerProgram.inputGap c + 5 := by
      rw [← CanonicalInitializerFrame.span_eq_inputGap c]
      simpa [CanonicalInitializer.registers] using hend
    simp [CounterControlNestingBridge.nestedCfg, logicalCfg, frameGrowth,
      selected, command, canonicalEntry, hposition, T]

/-- Packaging of the exact resume configuration expected by the search
system's boundary predicate. -/
theorem boundaryAt_resume (base : Nat) (c : Nat.Partrec.Code)
    {frame : Frame (Symbol numTags) Search}
    (hframe : FrameWellFormed base c frame) :
    BoundaryAt base c frame
      ⟨resumeState (CanonicalInitializer.radius c)
          (commandOffset base c frame.saved),
        frame.outer⟩ :=
  ⟨hframe, rfl⟩

end

end CounterControlFrameSimulation
end Hooper
end Kari
end LeanWang
