/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitrarySearch
import LeanWang.Kari.Hooper.CounterControlCanonicalOpenMortality
import LeanWang.Kari.Hooper.BoundedMarkerContinuation

/-!
# Exhausted searches on an infinite blank ray

An exhausted private search writes its return tag at the end of the bounded
scan and enters the shared initializer.  If the searched ray is blank
forever, the initializer can retreat across the exhausted prefix, install the
canonical five-boundary counter core, and leave an infinite blank runway.
Thus the result is a target-free open logical configuration.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlBlankLaunch

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlArbitrarySearch CounterControlSearchSystem
open CounterControlCanonicalOpenMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Installing a canonical tagged core over a tape with a blank ray in the
growth direction produces an open frame. -/
theorem install_openRepresents_of_blankRay
    {registers : Registers} {growth : Turing.Dir} {tag : Fin numTags}
    {outer : FullTM0.Tape (Symbol numTags)}
    (hblank : BlankRay (fun symbol => symbol = blankSymbol) outer growth) :
    CounterControlOpenFrame.OpenRepresents registers growth tag
      (FramedMarkerTape.install registers growth tag outer) := by
  constructor
  · exact FramedMarkerTape.install_tag registers growth tag outer
  · intro position hposition
    exact FramedMarkerTape.install_core registers growth tag outer
      position hposition
  · intro position hpast
    rw [FramedMarkerTape.logicalTape_apply]
    rw [FramedMarkerTape.install_of_layoutEnd_lt registers growth tag outer
      hpast]
    simpa using hblank position

/-- The initializer path is enabled whenever the complete private scan
prefix is blank.  No outer target is needed. -/
theorem instructions_executes_of_blankPrefix
    (c : Nat.Partrec.Code) (command : Command numTags)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤
      NestingMachine.bound (CanonicalInitializer.radius c),
      (outer.moveN command.searchDirection position).read = blankSymbol) :
    FiniteTM0Path.Executes
      (CanonicalInitializerProgram.instructions c command.searchDirection
        command.returnTag)
      (((outer.moveN command.searchDirection
          (NestingMachine.bound (CanonicalInitializer.radius c))).write
            (tagSymbol command.returnTag)).write blankSymbol)
      (CanonicalInitializerProgram.resultTape c command.searchDirection
        command.returnTag outer) := by
  let prefixLength := NestingMachine.bound (CanonicalInitializer.radius c)
  have hfarBlank :
      (outer.moveN command.searchDirection prefixLength).read = blankSymbol := by
    exact hblank prefixLength (by simp [prefixLength])
  have hcleared :
      ((outer.moveN command.searchDirection prefixLength).write
          (tagSymbol command.returnTag)).write blankSymbol =
        outer.moveN command.searchDirection prefixLength := by
    rw [show ((outer.moveN command.searchDirection prefixLength).write
          (tagSymbol command.returnTag)).write blankSymbol =
        (outer.moveN command.searchDirection prefixLength).write blankSymbol by
      funext position
      by_cases hposition : position = 0 <;>
        simp [FullTM0.Tape.write, hposition]]
    exact CanonicalInitializerProgram.write_eq_self_of_read_eq
      (outer.moveN command.searchDirection prefixLength) blankSymbol hfarBlank
  have hretreatBlank : ∀ i < prefixLength,
      ((outer.moveN command.searchDirection prefixLength).moveN
        (NestingMachine.opposite command.searchDirection) i).read =
          blankSymbol := by
    intro i hi
    have hle : i ≤ prefixLength := Nat.le_of_lt hi
    have hsource := hblank (prefixLength - i) (by
      simp [prefixLength])
    cases hdirection : command.searchDirection with
    | left =>
        rw [hdirection] at hsource
        simp only [NestingMachine.opposite_left, FullTM0.Tape.read_eq,
          FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_right, zero_add,
          FullTM0.Tape.offset_left] at hsource ⊢
        rw [Nat.cast_sub hle] at hsource
        convert hsource using 1
        all_goals ring_nf
    | right =>
        rw [hdirection] at hsource
        simp only [NestingMachine.opposite_right, FullTM0.Tape.read_eq,
          FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left, zero_add,
          FullTM0.Tape.offset_right] at hsource ⊢
        rw [Nat.cast_sub hle] at hsource
        convert hsource using 1
        all_goals ring_nf
  have hretreat := CanonicalInitializerProgram.blankMoves_executes
    (NestingMachine.opposite command.searchDirection) prefixLength
    (outer.moveN command.searchDirection prefixLength) hretreatBlank
  rw [CanonicalInitializerProgram.moveN_opposite] at hretreat
  have hprefixBlank : ∀ position ≤ CanonicalInitializer.span c,
      (outer.moveN command.searchDirection position).read = blankSymbol := by
    intro position hposition
    apply hblank position
    exact hposition.trans (by
      simp [CanonicalInitializer.radius, NestingMachine.bound])
  have hplace := CanonicalInitializerProgram.placement_executes c
    command.searchDirection command.returnTag outer hprefixBlank
  rw [hcleared]
  simpa [CanonicalInitializerProgram.instructions, prefixLength] using
    CanonicalInitializerProgram.executes_append hretreat hplace

/-- Infinite blank rays supply the finite blank prefix required by the
initializer. -/
theorem instructions_executes_of_blankRay
    (c : Nat.Partrec.Code) (command : Command numTags)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : BlankRay (fun symbol => symbol = blankSymbol) outer
      command.searchDirection) :
    FiniteTM0Path.Executes
      (CanonicalInitializerProgram.instructions c command.searchDirection
        command.returnTag)
      (((outer.moveN command.searchDirection
          (NestingMachine.bound (CanonicalInitializer.radius c))).write
            (tagSymbol command.returnTag)).write blankSymbol)
      (CanonicalInitializerProgram.resultTape c command.searchDirection
        command.returnTag outer) := by
  apply instructions_executes_of_blankPrefix c command outer
  intro position _hposition
  simpa [FullTM0.Tape.read] using hblank position

/-- Tape installed by the shared initializer after the selected search has
exhausted its private scan. -/
def initializedTape (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Tape (Symbol numTags) :=
  FramedMarkerTape.install (CanonicalInitializer.registers c)
    (command base c search).searchDirection
    (command base c search).returnTag outer

/-- Exact canonical logical endpoint of a completed selected initializer. -/
def initializedCfg (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
  ⟨canonicalEntry base c (command base c search).searchDirection,
    FramedMarkerTape.atLogical (command base c search).searchDirection
      (initializedTape base c search outer) (CanonicalInitializer.span c)⟩

/-- A blank private-scan prefix is sufficient to carry an exact launch
through tag dispatch and canonical initialization. -/
theorem launch_reaches_initialized_of_blankPrefix
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤
      NestingMachine.bound (CanonicalInitializer.radius c),
      (outer.moveN (command base c search).searchDirection position).read =
        blankSymbol) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (exhaustedLaunchCfg base c search outer)
      (initializedCfg base c search outer) := by
  let radius := CanonicalInitializer.radius c
  let commandOffset := CounterControlSearchSystem.commandOffset base c search
  let selected := command base c search
  let bound := NestingMachine.bound radius
  let launchTape := outer.moveN selected.searchDirection bound
  have hat : CommandAt radius base commandOffset selected (commands base c) := by
    simpa [radius, commandOffset, selected, command,
      CounterControlSearchSystem.commandOffset] using
      (CounterControlWellFormed.compileCommand_commandAt base c search)
  have hlaunchBlank : launchTape.read = blankSymbol := by
    simpa [launchTape, selected, bound, radius] using
      hblank (NestingMachine.bound (CanonicalInitializer.radius c))
        (Nat.le_refl _)
  have hcontinuationLocal :=
    BoundedMarkerProgram.continuation_reaches_core_native radius commandOffset
      (BoundedMarkerProgram.coreEntry base radius (commands base c)) selected
      launchTape hlaunchBlank
  have hcontinuation :=
    BoundedMarkerContinuation.machine_reaches_of_continuation
      (coreTable base c) hat hcontinuationLocal
  have htoCore : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (exhaustedLaunchCfg base c search outer)
      ⟨controllerCoreEntry base c,
        launchTape.write (tagSymbol selected.returnTag)⟩ := by
    simpa [exhaustedLaunchCfg, launchTape, selected, commandOffset, radius,
      bound, CounterControlNestingBridge.machine,
      controllerCoreEntry_eq base c] using hcontinuation
  have hexec : FiniteTM0Path.Executes
      (CanonicalInitializerProgram.instructions c selected.searchDirection
        selected.returnTag)
      ((launchTape.write (tagSymbol selected.returnTag)).write blankSymbol)
      (CanonicalInitializerProgram.resultTape c selected.searchDirection
        selected.returnTag outer) := by
    simpa [launchTape, selected, bound, radius] using
      instructions_executes_of_blankPrefix c selected outer (by
        simpa [selected] using hblank)
  have hgrowth : initializerGrowth selected.returnTag =
      selected.searchDirection := by
    dsimp [selected, command]
    rw [compileCommand_returnTag]
    exact (compileCommand_searchDirection base c search).symm
  have hinitializerLocal : FullTM0.Reaches
      (FiniteTM0.machine (initializerTable base c))
      ⟨controllerCoreEntry base c,
        launchTape.write (tagSymbol selected.returnTag)⟩
      ⟨initializerExitFor base c selected.returnTag,
        CanonicalInitializerProgram.resultTape c selected.searchDirection
          selected.returnTag outer⟩ := by
    apply CanonicalInitializerProgram.table_reaches_exit
      (controllerCoreEntry base c) c initializerGrowth
      (initializerExitFor base c) selected.returnTag
    · simp
    · rw [hgrowth]
      exact hexec
    · simp [CanonicalInitializerProgram.resultTape]
  have hinitializer :=
    CounterControlNestingBridge.initializer_reaches_in_machine base c
      hinitializerLocal
  have hprefixBlank : ∀ position ≤ CanonicalInitializer.span c,
      (outer.moveN selected.searchDirection position).read = blankSymbol := by
    intro position hposition
    apply hblank position
    exact hposition.trans (by
      simp [CanonicalInitializer.radius, NestingMachine.bound])
  have hresult :
      CanonicalInitializerProgram.resultTape c selected.searchDirection
          selected.returnTag outer =
        FramedMarkerTape.atLogical selected.searchDirection
          (initializedTape base c search outer)
          (CanonicalInitializer.span c) := by
    simpa [initializedTape, selected] using
      (CanonicalInitializerFrame.resultTape_eq_atLogical_install c
        selected.searchDirection selected.returnTag outer hprefixBlank)
  have htarget : initializedCfg base c search outer =
      ⟨initializerExitFor base c selected.returnTag,
        CanonicalInitializerProgram.resultTape c selected.searchDirection
          selected.returnTag outer⟩ := by
    simp [initializedCfg, selected, initializerExitFor, hgrowth, hresult]
  have hinitializer' := hinitializer
  rw [← htarget] at hinitializer'
  exact htoCore.trans hinitializer'

/-- From the exact launch state of a blank-ray search, the complete linked
machine reaches the canonical target-free open logical configuration. -/
theorem launch_reaches_openLogical
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : BlankRay (fun symbol => symbol = blankSymbol) outer
      (command base c search).searchDirection) :
    ∃ concrete,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        (exhaustedLaunchCfg base c search outer) concrete ∧
      OpenLogical base c (command base c search).searchDirection
        (GlobalSourceSemantics.canonicalCounterCfg c) concrete := by
  let radius := CanonicalInitializer.radius c
  let commandOffset := CounterControlSearchSystem.commandOffset base c search
  let selected := command base c search
  let bound := NestingMachine.bound radius
  let launchTape := outer.moveN selected.searchDirection bound
  have hat : CommandAt radius base commandOffset selected (commands base c) := by
    simpa [radius, commandOffset, selected, command,
      CounterControlSearchSystem.commandOffset] using
      (CounterControlWellFormed.compileCommand_commandAt base c search)
  have hlaunchBlank : launchTape.read = blankSymbol := by
    simpa [launchTape, selected, bound, radius, FullTM0.Tape.read] using
      hblank (NestingMachine.bound (CanonicalInitializer.radius c))
  have hcontinuationLocal :=
    BoundedMarkerProgram.continuation_reaches_core_native radius commandOffset
      (BoundedMarkerProgram.coreEntry base radius (commands base c)) selected
      launchTape hlaunchBlank
  have hcontinuation :=
    BoundedMarkerContinuation.machine_reaches_of_continuation
      (coreTable base c) hat hcontinuationLocal
  have htoCore : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (exhaustedLaunchCfg base c search outer)
      ⟨controllerCoreEntry base c,
        launchTape.write (tagSymbol selected.returnTag)⟩ := by
    simpa [exhaustedLaunchCfg, launchTape, selected, commandOffset, radius,
      bound, CounterControlNestingBridge.machine,
      controllerCoreEntry_eq base c] using hcontinuation
  have hexec : FiniteTM0Path.Executes
      (CanonicalInitializerProgram.instructions c selected.searchDirection
        selected.returnTag)
      ((launchTape.write (tagSymbol selected.returnTag)).write blankSymbol)
      (CanonicalInitializerProgram.resultTape c selected.searchDirection
        selected.returnTag outer) := by
    simpa [launchTape, selected, bound, radius] using
      instructions_executes_of_blankRay c selected outer (by
        simpa [selected] using hblank)
  have hgrowth : initializerGrowth selected.returnTag =
      selected.searchDirection := by
    dsimp [selected, command]
    rw [compileCommand_returnTag]
    exact (compileCommand_searchDirection base c search).symm
  have hinitializerLocal : FullTM0.Reaches
      (FiniteTM0.machine (initializerTable base c))
      ⟨controllerCoreEntry base c,
        launchTape.write (tagSymbol selected.returnTag)⟩
      ⟨initializerExitFor base c selected.returnTag,
        CanonicalInitializerProgram.resultTape c selected.searchDirection
          selected.returnTag outer⟩ := by
    apply CanonicalInitializerProgram.table_reaches_exit
      (controllerCoreEntry base c) c initializerGrowth
      (initializerExitFor base c) selected.returnTag
    · simp
    · rw [hgrowth]
      exact hexec
    · simp [CanonicalInitializerProgram.resultTape]
  have hinitializer :=
    CounterControlNestingBridge.initializer_reaches_in_machine base c
      hinitializerLocal
  let installed := FramedMarkerTape.install
    (CanonicalInitializer.registers c) selected.searchDirection
      selected.returnTag outer
  let concrete : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
    ⟨canonicalEntry base c selected.searchDirection,
      FramedMarkerTape.atLogical selected.searchDirection installed
        (CanonicalInitializer.span c)⟩
  have hprefixBlank : ∀ position ≤ CanonicalInitializer.span c,
      (outer.moveN selected.searchDirection position).read = blankSymbol := by
    intro position _hposition
    simpa [FullTM0.Tape.read, selected] using hblank position
  have hresult :
      CanonicalInitializerProgram.resultTape c selected.searchDirection
          selected.returnTag outer =
        FramedMarkerTape.atLogical selected.searchDirection installed
          (CanonicalInitializer.span c) := by
    simpa [installed] using
      (CanonicalInitializerFrame.resultTape_eq_atLogical_install c
        selected.searchDirection selected.returnTag outer hprefixBlank)
  have hall : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (exhaustedLaunchCfg base c search outer) concrete := by
    have hconcrete : concrete =
        ⟨initializerExitFor base c selected.returnTag,
          CanonicalInitializerProgram.resultTape c selected.searchDirection
            selected.returnTag outer⟩ := by
      simp [concrete, initializerExitFor, hgrowth, hresult]
    have hinitializer' := hinitializer
    rw [← hconcrete] at hinitializer'
    exact htoCore.trans hinitializer'
  refine ⟨concrete, hall, ?_⟩
  have hopen : CounterControlOpenFrame.OpenRepresents
      (CanonicalInitializer.registers c) selected.searchDirection
      selected.returnTag installed := by
    apply install_openRepresents_of_blankRay
    simpa [selected] using hblank
  change OpenLogical base c selected.searchDirection
    (GlobalSourceSemantics.canonicalCounterCfg c) concrete
  refine ⟨installed, CounterControlTagFreeOpen.CoreOpenRepresents.ofOpen hopen,
    ?_, CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan c⟩
  have hend : FramedMarkerTape.layoutEnd
      (GlobalSourceSemantics.canonicalCounterCfg c).registers =
        CanonicalInitializer.span c := by
    simpa [CanonicalInitializer.registers, FramedMarkerTape.layoutEnd] using
      CanonicalInitializer.clockBoundary_registers c
  simp [concrete, canonicalEntry, hend]

/-- A canonical search entry on a blank ray either already halts or reaches
an open logical representation of the designated counter input. -/
theorem search_reaches_openLogical_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (search : Search)
    (outer : FullTM0.Tape (Symbol numTags))
    (hblank : BlankRay (fun symbol => symbol = blankSymbol) outer
      (command base c search).searchDirection) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ((searchSystem base c).startCfg search outer) ∨
      ∃ concrete,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ((searchSystem base c).startCfg search outer) concrete ∧
        OpenLogical base c (command base c search).searchDirection
          (GlobalSourceSemantics.canonicalCounterCfg c) concrete := by
  have hprefix : ∀ i ≤ NestingMachine.bound
      (CanonicalInitializer.radius c),
      outer (FullTM0.Tape.offset
        (command base c search).searchDirection i) = blankSymbol := by
    intro i _hi
    exact hblank i
  rcases reaches_exhaustedLaunch_or_haltsFrom base c search outer hprefix with
    hhalts | hlaunch
  · exact Or.inl hhalts
  · right
    rcases launch_reaches_openLogical base c search outer hblank with
      ⟨concrete, hopen, hlogical⟩
    exact ⟨concrete, hlaunch.trans hopen, hlogical⟩

end

end CounterControlBlankLaunch
end Hooper
end Kari
end LeanWang
