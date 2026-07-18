/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CanonicalInitializerFrame
import LeanWang.Kari.Hooper.CounterControlBridge
import LeanWang.Kari.Hooper.CounterControlWellFormed

/-!
# Failed counter searches launch a framed canonical computation

This file closes the semantic link between a symbolic counter command and the
shared canonical initializer.  A command selected by its raw enumeration tag
first exhausts the bounded-search prefix, writes that tag, and enters the
shared core.  The tag-selected initializer then restores the original search
head, installs the canonical five-boundary input in the command's physical
orientation, and enters the corresponding oriented counter state.

The endpoint is stated using `FramedMarkerTape.initializeTape`, so the finite
frame invariant is available alongside the reachability proof.  A final
dichotomy packages the nearby found-state execution and the far nested launch.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlNestingBridge

open Turing
open BoundedMarkerProgram CounterControlPlan

noncomputable section

/-- The complete counter-controller machine, including the shared initializer
and both oriented copies of the direct counter glue. -/
abbrev machine (base : Nat) (c : Nat.Partrec.Code) :=
  BoundedMarkerProgram.machine base (CanonicalInitializer.radius c)
    (commands base c) (coreTable base c)

/-- Endpoint of a failed compiled search after its selected canonical
initializer has finished on boundary `4`. -/
def nestedCfg (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length)
    (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  let command := compileCommand base c tag
  ⟨canonicalEntry base c command.searchDirection,
    FramedMarkerTape.atLogical command.searchDirection
      (FramedMarkerTape.initializeTape c command outer)
      (CanonicalInitializer.span c)⟩

/-- The initializer table runs inside the complete controller table.  This is
the state-allocation bridge: initializer sources begin at the shared core
entry, strictly after every bounded-controller source. -/
theorem initializer_reaches_in_machine
    (base : Nat) (c : Nat.Partrec.Code)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hreach : FullTM0.Reaches
      (FiniteTM0.machine (initializerTable base c)) start finish) :
    FullTM0.Reaches (machine base c) start finish := by
  have hcontrollerInitializer : FullTM0.Reaches
      (FiniteTM0.machine
        (BoundedMarkerProgram.controllerTable base
            (CanonicalInitializer.radius c) (commands base c) ++
          initializerTable base c)) start finish := by
    apply FiniteTM0Path.reaches_append_right_of_source_separate
      (BoundedMarkerProgram.controllerTable base
        (CanonicalInitializer.radius c) (commands base c))
      (initializerTable base c)
    · intro state hinitializer hcontroller
      have hi := CanonicalInitializerProgram.source_mem_table hinitializer
      have hc := BoundedMarkerProgram.source_mem_controllerTable hcontroller
      rw [controllerCoreEntry_eq base c] at hc
      exact Nat.not_lt_of_ge hi.1 hc
    · exact hreach
  have hfull := FiniteTM0Program.reaches_append_left
    (BoundedMarkerProgram.controllerTable base
      (CanonicalInitializer.radius c) (commands base c) ++
        initializerTable base c)
    (directTable base c) hcontrollerInitializer
  simpa [machine, BoundedMarkerProgram.machine, BoundedMarkerProgram.table,
    coreTable, List.append_assoc] using hfull

/-- A far search by the command at raw tag `tag` reaches the exact framed
canonical input in the correct oriented counter copy.  The second conjunct
retains the frame invariant on the tag-centered tape (before the endpoint is
recentered on boundary `4`). -/
theorem machine_reaches_nested
    (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileCommand base c tag).target.Matches outer
      (compileCommand base c tag).searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    FullTM0.Reaches (machine base c)
        ⟨searchState base c (rawCommands.get tag).address, outer⟩
        (nestedCfg base c tag outer) ∧
      FramedMarkerTape.Represents
        (FramedMarkerTape.frameSpec c (compileCommand base c tag)
          distance hfar)
        (FramedMarkerTape.initializeTape c (compileCommand base c tag)
          outer) := by
  let command := compileCommand base c tag
  have hat := CounterControlWellFormed.compileCommand_commandAt base c tag
  have htoCore := BoundedMarkerProgram.machine_reaches_core_native
    (coreTable base c) hat outer distance hgap hfar
  have hframed :=
    CanonicalInitializerFrame.instructions_executes_after_clear_framed
      c command outer distance hgap hfar
  rcases hframed with ⟨hexec, hrep⟩
  have hgrowth : initializerGrowth tag = command.searchDirection := by
    simp [command, initializerGrowth]
  have hinitializerLocal : FullTM0.Reaches
      (FiniteTM0.machine (initializerTable base c))
      ⟨controllerCoreEntry base c,
        taggedFrameTapeNative (CanonicalInitializer.radius c) command outer⟩
      ⟨initializerExitFor base c tag,
        FramedMarkerTape.atLogical command.searchDirection
          (FramedMarkerTape.initializeTape c command outer)
          (CanonicalInitializer.span c)⟩ := by
    apply CanonicalInitializerProgram.table_reaches_exit
      (controllerCoreEntry base c) c initializerGrowth
      (initializerExitFor base c) tag
    · simp [taggedFrameTapeNative, command]
    · simpa [hgrowth, command] using hexec
    · have hboundary := hrep.read_boundary_four
      simpa [FramedMarkerTape.frameSpec, FramedMarkerTape.layoutEnd,
        CanonicalInitializer.radius, CanonicalInitializer.span,
        CanonicalInitializerProgram.inputGap] using hboundary
  have hinitializer := initializer_reaches_in_machine base c hinitializerLocal
  constructor
  · have htoCore' : FullTM0.Reaches (machine base c)
        ⟨searchState base c (rawCommands.get tag).address, outer⟩
        ⟨controllerCoreEntry base c,
          taggedFrameTapeNative (CanonicalInitializer.radius c) command outer⟩ := by
      simpa [machine, command, controllerCoreEntry_eq,
        BoundedMarkerProgram.entryState] using htoCore
    have hall : FullTM0.Reaches (machine base c)
        ⟨searchState base c (rawCommands.get tag).address, outer⟩
        ⟨initializerExitFor base c tag,
          FramedMarkerTape.atLogical command.searchDirection
            (FramedMarkerTape.initializeTape c command outer)
            (CanonicalInitializer.span c)⟩ :=
      htoCore'.trans hinitializer
    simpa [nestedCfg, command, initializerExitFor, hgrowth] using hall
  · simpa [command] using hrep

/-- Every compiled bounded search either reaches its nearby found-state
handoff, or launches the exact framed canonical input.  Keeping the far
inequality in the existential makes the dependent frame specification
available to callers. -/
theorem machine_reaches_found_or_nests
    (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileCommand base c tag).target.Matches outer
      (compileCommand base c tag).searchDirection distance) :
    FullTM0.Reaches (machine base c)
        ⟨searchState base c (rawCommands.get tag).address, outer⟩
        ⟨BoundedMarkerProgram.foundState (CanonicalInitializer.radius c)
            (searchState base c (rawCommands.get tag).address),
          outer.moveN (compileCommand base c tag).searchDirection distance⟩ ∨
      ∃ hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance,
        FullTM0.Reaches (machine base c)
            ⟨searchState base c (rawCommands.get tag).address, outer⟩
            (nestedCfg base c tag outer) ∧
          FramedMarkerTape.Represents
            (FramedMarkerTape.frameSpec c (compileCommand base c tag)
              distance hfar)
            (FramedMarkerTape.initializeTape c (compileCommand base c tag)
              outer) := by
  rcases le_or_gt distance
      (NestingMachine.bound (CanonicalInitializer.radius c)) with
    hnear | hfar
  · left
    exact BoundedMarkerProgram.machine_reaches_found_native
      (coreTable base c)
      (CounterControlWellFormed.compileCommand_commandAt base c tag)
      outer distance hgap hnear
  · right
    exact ⟨hfar, machine_reaches_nested base c tag outer distance hgap hfar⟩

/-- For a compiled navigation command, the nearby branch includes its found
continuation and reaches the advertised external success state.  The far
branch is the same exact framed canonical launch as above. -/
theorem machine_reaches_navigation_or_nests
    (base : Nat) (c : Nat.Partrec.Code)
    (tag : Fin rawCommands.length)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (target : Target numTags) (direction : Turing.Dir)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (hcommand : compileCommand base c tag =
      Command.navigateTarget target direction successState returnTag)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      target.Matches outer direction distance) :
    FullTM0.Reaches (machine base c)
        ⟨searchState base c (rawCommands.get tag).address, outer⟩
        ⟨successState, outer.moveN direction distance⟩ ∨
      ∃ hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance,
        FullTM0.Reaches (machine base c)
            ⟨searchState base c (rawCommands.get tag).address, outer⟩
            (nestedCfg base c tag outer) ∧
          FramedMarkerTape.Represents
            (FramedMarkerTape.frameSpec c (compileCommand base c tag)
              distance hfar)
            (FramedMarkerTape.initializeTape c (compileCommand base c tag)
              outer) := by
  have hcompiledGap : SearchGap (fun symbol => symbol = blankSymbol)
      (compileCommand base c tag).target.Matches outer
      (compileCommand base c tag).searchDirection distance := by
    rw [hcommand]
    cases target <;>
      simpa [Command.navigateTarget, Command.target,
        Command.searchDirection] using hgap
  rcases le_or_gt distance
      (NestingMachine.bound (CanonicalInitializer.radius c)) with
    hnear | hfar
  · left
    have hat := CounterControlWellFormed.compileCommand_commandAt base c tag
    rw [hcommand] at hat
    simpa [machine, BoundedMarkerProgram.entryState] using
      (CounterControlBridge.machine_reaches_navigation
        (coreTable base c) target direction successState returnTag hat
        outer distance hgap hnear)
  · right
    exact ⟨hfar,
      machine_reaches_nested base c tag outer distance hcompiledGap hfar⟩

end

end CounterControlNestingBridge
end Hooper
end Kari
end LeanWang
