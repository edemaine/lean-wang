/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedExactContinuation
import LeanWang.Kari.Hooper.CounterControlCleanupSuffixProgress

/-!
# The cleanup branch of resumed parent continuation

The generated-caller classifier identifies every erasing caller as one of
the four cleanup commands of an increment rule.  The exact resumed backing
then supplies precisely the found configuration and gap expected by the
cleanup-suffix theorem.  This module performs that dependent conversion and
packages its strictly larger resumed search as a
`FoundParentEmbeddingOutcome.nextSearch`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlResumedCleanupProgress

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlPrefixResume CounterControlPrefixInstructionResolution
open CounterControlCleanupRoute

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem compileRawCommand_congr
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : RawCommand} (heq : first = second)
    (hfirst : first ∈ rawCommands) (hsecond : second ∈ rawCommands) :
    CounterControlCommandAt.compileRawCommand base c first hfirst =
      CounterControlCommandAt.compileRawCommand base c second hsecond := by
  subst second
  rfl

/-- A resumed caller classified into the cleanup list completes that suffix
and reaches a strictly larger genuine generated search. -/
theorem foundParentEmbeddingOutcome_of_cleanup
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {frame : PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hcleanup : resumed.selectedRaw ∈ cleanupCommands growth source)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg resumed.next)) :
    Nonempty (FoundParentEmbeddingOutcome resumed.next) := by
  rcases exists_stage_of_mem_cleanupCommands hcleanup with ⟨stage, hstage⟩
  have hstageRaw : command growth source stage ∈ rawCommands :=
    command_mem_rawCommands_of_increment growth source register targetState
      hrule stage
  have hcompiled :
      CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
          resumed.selectedRaw_mem =
        CounterControlCommandAt.compileRawCommand base c
          (command growth source stage) hstageRaw := by
    exact compileRawCommand_congr base c hstage
      resumed.selectedRaw_mem hstageRaw
  have htarget :
      (command base c resumed.next.search).target =
        Target.boundary stage.expected := by
    rw [← resumed.compileRawCommand_selectedRaw, hcompiled]
    exact compile_command_target base c growth source stage hstageRaw
  have hdirection :
      (command base c resumed.next.search).searchDirection =
        orient growth .left := by
    rw [← resumed.compileRawCommand_selectedRaw, hcompiled]
    exact compile_command_searchDirection base c growth source stage hstageRaw
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches resumed.next.outer
      (orient growth .left) resumed.next.distance := by
    simpa only [htarget, hdirection] using resumed.next.gap
  have hrawGet : rawCommands.get resumed.next.search =
      command growth source stage := by
    change resumed.selectedRaw = command growth source stage
    exact hstage
  have hfound : foundCfg resumed.next =
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        resumed.next.outer.moveN (orient growth .left)
          resumed.next.distance⟩ := by
    change
      (⟨foundState (CanonicalInitializer.radius c)
          (searchState base c (rawCommands.get resumed.next.search).address),
        resumed.next.outer.moveN
          (command base c resumed.next.search).searchDirection
          resumed.next.distance⟩ :
        FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    rw [hrawGet, hdirection, command_address]
  have himmortalFound : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        resumed.next.outer.moveN (orient growth .left)
          resumed.next.distance⟩ := by
    rw [← hfound]
    exact himmortal
  rcases
      CounterControlCleanupSuffixProgress.found_stage_reaches_larger_genuineSearch
        base c hmortal growth source register targetState hrule stage
        resumed.next.outer resumed.next.distance hgap himmortalFound with
    ⟨finish, hreach, hdistance⟩
  refine ⟨.nextSearch finish ?_ hdistance⟩
  rw [hfound]
  exact hreach

end

end CounterControlResumedCleanupProgress
end Hooper
end Kari
end LeanWang
