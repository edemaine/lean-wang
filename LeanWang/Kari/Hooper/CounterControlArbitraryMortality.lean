/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryEntrySemantics
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality
import LeanWang.Kari.Hooper.CounterControlCommandAtConverse
import LeanWang.Kari.Hooper.CounterControlControllerNormalization
import LeanWang.Kari.Hooper.CounterControlDirectNormalization
import LeanWang.Kari.Hooper.CounterControlImmortalSearch
import LeanWang.Kari.Hooper.CounterControlLogicalEntry
import LeanWang.Kari.Hooper.CounterControlOpenStepLaw

/-!
# A global arbitrary-entry frontier for the counter controller

This file assembles the finite, tape-independent normalization results for
the three disjoint compiler regions.  On an immortal orbit, initializer and
direct entries can be advanced to logical control or to a compiled search;
controller entries advance to one of the continuation's honest macro
handoffs.  Logical control itself immediately launches the first validation
search.  Under source mortality, the unconditional open one-step law forces
every compiled search reached in this way to have a genuine finite matching
gap.

The resulting frontier is the state-local part of Hooper's mortality
argument.  Reconstructing an open counter core still requires chaining the
four successful outward validation searches from an arbitrary continuation
handoff.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlArbitraryMortality

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlArbitraryEntry
open CounterControlSearchSystem

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Global finite normalization -/

/-- The first global frontier after finite, tape-independent normalization.
A direct exit is either logical control or a symbolic search entry; a
controller exit is one of the exact compiler handoffs classified by
`ControllerExit.state_cases`. -/
def CompilerHandoff (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  CounterControlControllerNormalization.ControllerExit base c cfg.q ∨
    CounterControlDirectNormalization.Exit base c cfg

/-- A controller exit other than the shared initializer entry.  The selected
command and its exact relocated block are retained. -/
def CommandHandoff (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ commandOffset command,
    CommandAt (CanonicalInitializer.radius c) base commandOffset command
        (commands base c) ∧
      (cfg.q = entryState (CanonicalInitializer.radius c) commandOffset ∨
        cfg.q = command.successState ∨
        ∃ (move : MarkerProgram.Move) (success : FiniteTM0.State)
            (returnTag : Fin numTags) (departure : Option Turing.Dir)
            (collision : FiniteTM0.State),
          command = .markerShift move success returnTag departure
            (some collision) ∧
          cfg.q = collision)

/-- The residual controller handoffs after command entries have been
recognized as genuine searches. -/
def CommandContinuationHandoff (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ commandOffset command,
    CommandAt (CanonicalInitializer.radius c) base commandOffset command
        (commands base c) ∧
      (cfg.q = command.successState ∨
        ∃ (move : MarkerProgram.Move) (success : FiniteTM0.State)
            (returnTag : Fin numTags) (departure : Option Turing.Dir)
            (collision : FiniteTM0.State),
          command = .markerShift move success returnTag departure
            (some collision) ∧
          cfg.q = collision)

theorem compilerHandoff_cases
    (base : Nat) (c : Nat.Partrec.Code)
    {cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hhandoff : CompilerHandoff base c cfg) :
    CounterControlDirectNormalization.Exit base c cfg ∨
      cfg.q = controllerCoreEntry base c ∨
      CommandHandoff base c cfg := by
  rcases hhandoff with hcontroller | hdirect
  · rcases CounterControlControllerNormalization.ControllerExit.state_cases
        base c hcontroller with hcore | hcommand
    · exact Or.inr (Or.inl hcore)
    · exact Or.inr (Or.inr hcommand)
  · exact Or.inl hdirect

/-- Every immortal arbitrary configuration finitely reaches a genuine
compiler handoff.  This is the global assembly of the three disjoint source
regions; all immediate-halting alternatives disappear by immortality. -/
theorem reaches_compilerHandoff_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start finish ∧
      CompilerHandoff base c finish := by
  have hnotHalts : ¬ FullTM0.HaltsFrom
      (CounterControlNestingBridge.machine base c) start :=
    (FullTM0.HaltsFrom.immortalFrom_iff_not
      (CounterControlNestingBridge.machine base c) start).mp himmortal
  cases sourceRegion_of_immortalFrom base c start himmortal with
  | controller hsource =>
      rcases CounterControlControllerNormalization.controller_normalizes_arbitrary_entry
          base c start.q start.tape hsource with
        hhalts | ⟨finish, hreach, hexit⟩
      · exact False.elim (hnotHalts hhalts)
      · exact ⟨finish, hreach, Or.inl hexit⟩
  | initializer hsource =>
      rcases CounterControlArbitraryEntrySemantics.initializer_normalizes_arbitrary_entry
          base c start hsource with
        hhalts | ⟨tag, U, hreach, _hread⟩
      · exact False.elim (hnotHalts hhalts)
      · refine ⟨⟨canonicalEntry base c (initializerGrowth tag), U⟩,
          hreach, Or.inr ?_⟩
        simpa [canonicalEntry] using
          (CounterControlDirectNormalization.Exit.logical
            (base := base) (c := c) (initializerGrowth tag)
            (GlobalSourceSemantics.canonicalCounterCfg c).state
            (CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan c)
            U)
  | direct hsource =>
      rcases CounterControlDirectNormalization.normalizes_arbitrary_entry
          base c start hsource with
        hhalts | ⟨finish, hreach, hexit⟩
      · exact False.elim (hnotHalts hhalts)
      · exact ⟨finish, hreach, Or.inr hexit⟩

/-! ## Logical entries reach genuine validation searches -/

/-- A reached compiled search together with the genuine finite gap forced by
immortality and source mortality. -/
def GenuineSearchFrontier (base : Nat) (c : Nat.Partrec.Code)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ search : Search, ∃ outer : FullTM0.Tape (Symbol numTags), ∃ distance,
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        start ((searchSystem base c).startCfg search outer) ∧
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches outer
        (command base c search).searchDirection distance

/-! ## Removing two finite-controller handoffs -/

/-- A logical-state-shaped configuration on an immortal orbit is owned by
the direct table.  The controller and initializer regions lie strictly
below every logical-state allocation. -/
theorem direct_source_of_immortal_logical
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (state : Nat) (T : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth state, T⟩) :
    logicalState base c growth state ∈
      FiniteTM0.sourceStates (directTable base c) := by
  have hlower : initializerEnd base c ≤
      logicalState base c growth state := by
    cases growth with
    | left =>
        simp [logicalState, logicalBase, leftLogicalBase, rightLogicalBase,
          rightDirectBase]
        omega
    | right => simp [logicalState, logicalBase, rightLogicalBase]
  cases sourceRegion_of_immortalFrom base c
      ⟨logicalState base c growth state, T⟩ himmortal with
  | controller hsource =>
      have hupper : logicalState base c growth state <
          controllerCoreEntry base c :=
        controller_lt_coreEntry base c hsource
      have hcore : controllerCoreEntry base c < initializerEnd base c := by
        simp only [initializerEnd, CanonicalInitializerProgram.exitState]
        omega
      omega
  | initializer hsource =>
      have hupper : logicalState base c growth state <
          initializerEnd base c := (initializer_bounds base c hsource).2
      omega
  | direct hsource => exact hsource

/-- The entry alternative of an arbitrary controller handoff is an actual
generated compiled search, not merely a numerically plausible command
offset.  Immortality then forces its search to have a genuine matching gap. -/
theorem genuineSearch_of_reachable_command_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (commandOffset : Nat) (selected : Command numTags)
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      selected (commands base c))
    (hentry : cfg.q =
      entryState (CanonicalInitializer.radius c) commandOffset)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start cfg) :
    GenuineSearchFrontier base c start := by
  rcases CounterControlCommandAtConverse.exists_raw_of_commandAt
      base c hat with ⟨raw, hraw, _hselected, hoffset⟩
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  let outer := cfg.tape
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hraw
  have hcommandOffset :
      CounterControlSearchSystem.commandOffset base c search =
        commandOffset := by
    unfold CounterControlSearchSystem.commandOffset
    rw [hget, hoffset]
  have hsearchReach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ((searchSystem base c).startCfg search outer) := by
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨CounterControlSearchSystem.commandOffset base c search, outer⟩
    rw [hcommandOffset]
    have hcfg : cfg = ⟨commandOffset, outer⟩ := by
      rcases cfg with ⟨q, tape⟩
      have hq : q = commandOffset := by
        simpa [entryState] using hentry
      subst q
      rfl
    rw [← hcfg]
    exact hreach
  rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
      base c hmortal (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
      himmortal hsearchReach with ⟨distance, hgap⟩
  exact ⟨search, outer, distance, hsearchReach, hgap⟩

/-- Resolve one reached preserving boundary search and immediately traverse
the generated direct continuation into the next symbolic search.  This is
the reusable induction step for reconstructing validation routes from an
immortal arbitrary orbit. -/
theorem reaches_nextSearch_of_immortal_boundary_preserve
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (handoff : ControlRef)
    (nextAddress : SearchAddress) (nextDirection : Turing.Dir)
    (hraw : RawCommand.boundaryNavigation address expected direction handoff
      .preserve ∈ rawCommands)
    (hcontinuation : RawDirectRule.mk address.growth handoff
      (.boundary expected) (.search nextAddress) nextDirection ∈
        rawDirectRules)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨searchState base c address, outer⟩) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary expected).Matches outer
          (orient address.growth direction) distance ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨searchState base c nextAddress,
            (outer.moveN (orient address.growth direction) distance).move
              (orient address.growth nextDirection)⟩ := by
  rcases CounterControlImmortalSearch.reaches_boundary_preserve_of_immortal
      base c hmortal
      (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
      himmortal address expected direction handoff hraw outer hreach with
    ⟨distance, hgap, hhandoff⟩
  let found := outer.moveN (orient address.growth direction) distance
  let continuation : RawDirectRule :=
    ⟨address.growth, handoff, .boundary expected, .search nextAddress,
      nextDirection⟩
  have hmatch : continuation.read.Matches found.read := by
    change found.read = boundarySymbol expected
    simpa [found, FullTM0.Tape.read, Target.Matches] using hgap.marked
  have hlocal := CounterControlDirectSemantics.reaches_directRule
    base c continuation hcontinuation found hmatch
  have hnext : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c handoff, found⟩
      ⟨searchState base c nextAddress,
        found.move (orient address.growth nextDirection)⟩ := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table,
      continuation, CounterControlPlan.resolve] using hlocal
  have hboth : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c nextAddress,
        found.move (orient address.growth nextDirection)⟩ := by
    unfold FullTM0.Reaches at hhandoff hnext ⊢
    exact hhandoff.trans hnext
  exact ⟨distance, hgap, by simpa [found] using hboth⟩

/-- Every bounded logical configuration on an immortal orbit immediately
enters the first validation command, and that search has a genuine finite
gap. -/
theorem genuine_validationSearch_of_reachable_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (state : Nat) (hstate : state < logicalSpan)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : logicalState base c growth state ∈
      FiniteTM0.sourceStates (directTable base c))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨logicalState base c growth state, T⟩) :
    GenuineSearchFrontier base c start := by
  let M := CounterControlNestingBridge.machine base c
  have himmortalLogical : FullTM0.ImmortalFrom M
      ⟨logicalState base c growth state, T⟩ := by
    rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
    intro hhalts
    exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)
  rcases CounterControlLogicalEntry.reaches_validationFirst_of_immortalFrom
      base c growth state hstate T hsource himmortalLogical with
    ⟨instruction, hprogram, _hread, hvalidation⟩
  let raw := CounterControlLargeClock.validationFirst growth state
  have hraw : raw ∈ rawCommands :=
    CounterControlLargeClock.validationFirst_mem growth state instruction
      hprogram
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  let outer := T.move (orient growth .left)
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hraw
  have hoffset : CounterControlSearchSystem.commandOffset base c search =
      searchState base c ⟨growth, state, validationSearchBase⟩ := by
    unfold CounterControlSearchSystem.commandOffset
    rw [hget]
    rfl
  have hsearchReach : FullTM0.Reaches M start
      ((searchSystem base c).startCfg search outer) := by
    change FullTM0.Reaches M start
      ⟨CounterControlSearchSystem.commandOffset base c search, outer⟩
    rw [hoffset]
    have htail : FullTM0.Reaches M
        ⟨logicalState base c growth state, T⟩
        ⟨searchState base c ⟨growth, state, validationSearchBase⟩,
          outer⟩ := by
      simpa [outer] using hvalidation
    exact hreach.trans htail
  rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
      base c hmortal (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
      himmortal hsearchReach with ⟨distance, hgap⟩
  exact ⟨search, outer, distance, hsearchReach, hgap⟩

/-- Source ownership need not be supplied separately for a bounded logical
configuration reached on an immortal orbit: immortality and the numeric
separation of compiler regions recover it. -/
theorem genuine_validationSearch_of_reachable_bounded_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (growth : Turing.Dir) (state : Nat) (hstate : state < logicalSpan)
    (T : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨logicalState base c growth state, T⟩) :
    GenuineSearchFrontier base c start := by
  have himmortalLogical : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth state, T⟩ := by
    rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
    intro hhalts
    exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)
  exact genuine_validationSearch_of_reachable_logical base c hmortal
    himmortal growth state hstate T
    (direct_source_of_immortal_logical base c growth state T
      himmortalLogical)
    hreach

/-- The shared initializer entry is not a genuine infinite-control
alternative.  On an immortal orbit its arbitrary tape either would halt in
the finite initializer, or reaches the canonical bounded logical state and
therefore the first genuine validation search. -/
theorem genuine_validationSearch_of_reachable_controllerCore
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (T : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start ⟨controllerCoreEntry base c, T⟩) :
    GenuineSearchFrontier base c start := by
  have himmortalCore : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨controllerCoreEntry base c, T⟩ := by
    rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
    intro hhalts
    exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)
  have hinitializer : controllerCoreEntry base c ∈
      FiniteTM0.sourceStates (initializerTable base c) := by
    cases sourceRegion_of_immortalFrom base c
        ⟨controllerCoreEntry base c, T⟩ himmortalCore with
    | controller hsource =>
        exact False.elim
          ((Nat.lt_irrefl (controllerCoreEntry base c))
            (controller_lt_coreEntry base c hsource))
    | initializer hsource => exact hsource
    | direct hsource =>
        have hlower : initializerEnd base c ≤ controllerCoreEntry base c :=
          initializerEnd_le_direct base c hsource
        have hupper : controllerCoreEntry base c < initializerEnd base c := by
          simp only [initializerEnd, CanonicalInitializerProgram.exitState]
          omega
        omega
  rcases CounterControlArbitraryEntrySemantics.initializer_normalizes_arbitrary_entry
      base c
        ⟨controllerCoreEntry base c, T⟩ hinitializer with
    hhalts | ⟨tag, U, hinitializerReach, _hread⟩
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨controllerCoreEntry base c, T⟩).mp himmortalCore hhalts)
  · apply genuine_validationSearch_of_reachable_bounded_logical
      base c hmortal himmortal (initializerGrowth tag)
      (GlobalSourceSemantics.canonicalCounterCfg c).state
      (CounterControlAbstractTrace.canonicalCounterCfg_state_lt_logicalSpan c)
      U
    have htail : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨controllerCoreEntry base c, T⟩
        ⟨logicalState base c (initializerGrowth tag)
            (GlobalSourceSemantics.canonicalCounterCfg c).state, U⟩ := by
      simpa [canonicalEntry] using hinitializerReach
    exact hreach.trans htail

/-! ## The assembled global frontier -/

/-- A reached compiler handoff on an immortal orbit is either already a
direct logical/search exit, reaches a genuine generated search, or is one of
the two residual command-continuation exits.  In particular, neither the
shared initializer entry nor a command entry remains as a frontier case. -/
theorem compilerHandoff_reduces_to_genuineSearch_or_residual
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (hreach : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      start cfg)
    (hhandoff : CompilerHandoff base c cfg) :
    GenuineSearchFrontier base c start ∨
      CounterControlDirectNormalization.Exit base c cfg ∨
      CommandContinuationHandoff base c cfg := by
  rcases compilerHandoff_cases base c hhandoff with
    hdirect | hcore | hcommand
  · exact Or.inr (Or.inl hdirect)
  · left
    rcases cfg with ⟨q, T⟩
    have hq : q = controllerCoreEntry base c := by simpa using hcore
    subst q
    exact genuine_validationSearch_of_reachable_controllerCore
      base c hmortal himmortal T hreach
  · rcases hcommand with
      ⟨commandOffset, command, hat, hentry | hsuccess | hcollision⟩
    · left
      exact genuineSearch_of_reachable_command_entry base c hmortal
        himmortal commandOffset command hat hentry hreach
    · exact Or.inr (Or.inr
        ⟨commandOffset, command, hat, Or.inl hsuccess⟩)
    · exact Or.inr (Or.inr
        ⟨commandOffset, command, hat, Or.inr hcollision⟩)

/-- Every immortal arbitrary configuration reaches the reduced global
frontier.  This is the current tape-independent endpoint of the converse:
the remaining continuation exits must be threaded through the generated
validation/control graph, while direct exits retain their symbolic form. -/
theorem reaches_genuineSearch_or_residual_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    GenuineSearchFrontier base c start ∨
      ∃ finish,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            start finish ∧
          (CounterControlDirectNormalization.Exit base c finish ∨
            CommandContinuationHandoff base c finish) := by
  rcases reaches_compilerHandoff_of_immortalFrom base c start himmortal with
    ⟨finish, hreach, hhandoff⟩
  rcases compilerHandoff_reduces_to_genuineSearch_or_residual
      base c hmortal himmortal hreach hhandoff with
    hgenuine | hdirect | hcontinuation
  · exact Or.inl hgenuine
  · exact Or.inr ⟨finish, hreach, Or.inl hdirect⟩
  · exact Or.inr ⟨finish, hreach, Or.inr hcontinuation⟩

end

end CounterControlArbitraryMortality
end Hooper
end Kari
end LeanWang
