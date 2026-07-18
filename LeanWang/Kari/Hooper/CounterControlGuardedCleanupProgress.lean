/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCleanupRoute
import LeanWang.Kari.Hooper.CounterControlCleanupEraseProgress
import LeanWang.Kari.Hooper.CounterControlGeneratedSearchGap
import LeanWang.Kari.Hooper.CounterControlCleanupSuffixGeometry
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlGuardedResume
import LeanWang.Kari.Hooper.CounterControlParentContinuation

/-!
# Guarded progress through a collision-cleanup suffix

The ordinary cleanup-suffix theorem records only the genuine generated search
reached after the final shared return.  Here we retain the additional fact
that the dispatcher erased the cell immediately behind that search.  Thus a
guarded cleanup caller reaches a strictly larger `GuardedSearch`, keeping the
invariant needed to iterate Hooper's global unnesting argument.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedCleanupProgress

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedSearch CounterControlCleanupRoute
open CounterControlCleanupSuffixGeometry
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem opposite_orient_left (growth : Turing.Dir) :
    NestingMachine.opposite (orient growth .left) = growth := by
  cases growth <;> rfl

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {start finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start finish) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) finish := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-! ## A shared return retaining both growth and the guard -/

/-- An immortal shared return which reverses an inward cleanup direction
reaches a guarded generated search beyond every accumulated blank cell. -/
theorem reaches_guardedSearch_beyond_blankBehind
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir)
    (length : Nat) (hbehind : BlankBehind T inward length)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩
        next.current.cfg ∧
      length ≤ next.current.distance := by
  rcases CounterControlReturnFrontier.reaches_generated_search_of_immortal_return
      base c (NestingMachine.opposite inward) T himmortal with
    ⟨raw, hraw, _hread, hdirection, hreach⟩
  let outer := (T.write blankSymbol).move
    (NestingMachine.opposite inward)
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hraw
  have hstartCfg : (searchSystem base c).startCfg search outer =
      ⟨searchState base c raw.address, outer⟩ := by
    change (⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    unfold CounterControlSearchSystem.commandOffset
    rw [hget]
  have hsearchReach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩
      ((searchSystem base c).startCfg search outer) := by
    rw [hstartCfg]
    simpa [outer] using hreach
  rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
      base c hmortal
      (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
      himmortal hsearchReach with
    ⟨distance, hgap⟩
  have hcommand : command base c search =
      CounterControlCommandAt.compileRawCommand base c raw hraw := by
    rfl
  have hsearchDirection :
      (command base c search).searchDirection =
        NestingMachine.opposite inward := by
    rw [hcommand]
    exact hdirection
  have hgapReturn : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (NestingMachine.opposite inward) distance := by
    rw [← hsearchDirection]
    exact hgap
  have hdistance : length ≤ distance :=
    CounterControlCleanupSuffixGeometry.distance_ge_of_blankBehind_return
      (fun symbol hmatch hblank =>
        target_not_blank (command base c search).target (hblank ▸ hmatch))
      hbehind (by simpa [outer] using hgapReturn)
  let current : GenuineSearch base c := {
    search := search
    outer := outer
    distance := distance
    gap := hgap }
  let next : GuardedSearch base c := {
    current := current
    guard := by
      change (outer.move
        (NestingMachine.opposite
          (command base c search).searchDirection)).read = blankSymbol
      rw [hsearchDirection]
      cases inward <;>
        simp [outer, NestingMachine.opposite, FullTM0.Tape.read,
          FullTM0.Tape.move, FullTM0.Tape.write] }
  refine ⟨next, ?_, hdistance⟩
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩
    ((searchSystem base c).startCfg search outer)
  exact hsearchReach

/-! ## Exact progress through the four cleanup stages -/

private theorem reaches_stage_success_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (stage : Stage) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩
      ⟨resolve base c (stage.successRef growth source),
        eraseDepart outer (orient growth .left) distance⟩ := by
  have hraw := command_mem_rawCommands_of_increment
    growth source register next hrule stage
  have hrun :=
    CounterControlCleanupEraseProgress.machine_reaches_boundary_erase_of_immortal
      base c ⟨growth, source, stage.slot⟩ stage.expected .left
      (stage.successRef growth source) (some .left)
      (by simpa [CounterControlCleanupRoute.command] using hraw)
      outer distance hgap himmortal
  simpa [eraseDepart] using hrun

private theorem gap_stage_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (stage : Stage) (outer : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, stage.slot⟩, outer⟩) :
    ∃ distance, SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches outer
      (orient growth .left) distance := by
  have hraw := command_mem_rawCommands_of_increment
    growth source register next hrule stage
  exact CounterControlGeneratedSearchGap.boundaryNavigation_gap_of_immortal
    base c hmortal ⟨growth, source, stage.slot⟩ stage.expected .left
    (stage.successRef growth source) (.erase (some .left))
    (by simpa [CounterControlCleanupRoute.command] using hraw)
    outer himmortal

private theorem zero_from_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance previous : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary Stage.zero.expected).Matches outer
      (orient growth .left) distance)
    (hbehind : BlankBehind outer (orient growth .left) previous)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.zero.slot⟩, outer⟩) :
    ∃ finish : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.zero.slot⟩, outer⟩
        finish.current.cfg ∧
      distance + 1 + previous ≤ finish.current.distance := by
  have herase := reaches_stage_success_of_immortal base c growth source
    register next hrule .zero outer distance hgap himmortal
  rw [resolve_success_zero] at herase
  let returnTape := eraseDepart outer (orient growth .left) distance
  have hbehindReturn : BlankBehind returnTape (orient growth .left)
      (distance + 1 + previous) :=
    blankBehind_eraseDepart hgap hbehind
  have himmortalReturn : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c growth, returnTape⟩ := by
    apply immortalFrom_of_reaches base c himmortal
    simpa [returnTape] using herase
  have himmortalReturn' : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c
          (NestingMachine.opposite (orient growth .left)), returnTape⟩ := by
    rw [opposite_orient_left]
    exact himmortalReturn
  rcases reaches_guardedSearch_beyond_blankBehind
      base c hmortal returnTape (orient growth .left)
      (distance + 1 + previous) hbehindReturn himmortalReturn' with
    ⟨finish, hreturn, hdistance⟩
  refine ⟨finish, ?_, hdistance⟩
  rw [opposite_orient_left] at hreturn
  exact herase.trans hreturn

private theorem one_from_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance previous : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary Stage.one.expected).Matches outer
      (orient growth .left) distance)
    (hbehind : BlankBehind outer (orient growth .left) previous)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.one.slot⟩, outer⟩) :
    ∃ finish : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.one.slot⟩, outer⟩
        finish.current.cfg ∧
      distance + 1 + previous ≤ finish.current.distance := by
  have herase := reaches_stage_success_of_immortal base c growth source
    register next hrule .one outer distance hgap himmortal
  rw [resolve_success_one] at herase
  let nextOuter := eraseDepart outer (orient growth .left) distance
  have hbehindNext : BlankBehind nextOuter (orient growth .left)
      (distance + 1 + previous) :=
    blankBehind_eraseDepart hgap hbehind
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.zero.slot⟩, nextOuter⟩ := by
    apply immortalFrom_of_reaches base c himmortal
    simpa [nextOuter] using herase
  rcases gap_stage_of_immortal base c hmortal growth source register next
      hrule .zero nextOuter himmortalNext with ⟨nextDistance, hnextGap⟩
  rcases zero_from_entry base c hmortal growth source register next hrule
      nextOuter nextDistance (distance + 1 + previous) hnextGap hbehindNext
      himmortalNext with ⟨finish, hfinish, hbound⟩
  refine ⟨finish, herase.trans hfinish, ?_⟩
  omega

private theorem two_from_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance previous : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary Stage.two.expected).Matches outer
      (orient growth .left) distance)
    (hbehind : BlankBehind outer (orient growth .left) previous)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.two.slot⟩, outer⟩) :
    ∃ finish : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.two.slot⟩, outer⟩
        finish.current.cfg ∧
      distance + 1 + previous ≤ finish.current.distance := by
  have herase := reaches_stage_success_of_immortal base c growth source
    register next hrule .two outer distance hgap himmortal
  rw [resolve_success_two] at herase
  let nextOuter := eraseDepart outer (orient growth .left) distance
  have hbehindNext : BlankBehind nextOuter (orient growth .left)
      (distance + 1 + previous) :=
    blankBehind_eraseDepart hgap hbehind
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.one.slot⟩, nextOuter⟩ := by
    apply immortalFrom_of_reaches base c himmortal
    simpa [nextOuter] using herase
  rcases gap_stage_of_immortal base c hmortal growth source register next
      hrule .one nextOuter himmortalNext with ⟨nextDistance, hnextGap⟩
  rcases one_from_entry base c hmortal growth source register next hrule
      nextOuter nextDistance (distance + 1 + previous) hnextGap hbehindNext
      himmortalNext with ⟨finish, hfinish, hbound⟩
  refine ⟨finish, herase.trans hfinish, ?_⟩
  omega

private theorem three_from_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (register : Register) (next : Nat)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance previous : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary Stage.three.expected).Matches outer
      (orient growth .left) distance)
    (hbehind : BlankBehind outer (orient growth .left) previous)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.three.slot⟩, outer⟩) :
    ∃ finish : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.three.slot⟩, outer⟩
        finish.current.cfg ∧
      distance + 1 + previous ≤ finish.current.distance := by
  have herase := reaches_stage_success_of_immortal base c growth source
    register next hrule .three outer distance hgap himmortal
  rw [resolve_success_three] at herase
  let nextOuter := eraseDepart outer (orient growth .left) distance
  have hbehindNext : BlankBehind nextOuter (orient growth .left)
      (distance + 1 + previous) :=
    blankBehind_eraseDepart hgap hbehind
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, Stage.two.slot⟩, nextOuter⟩ := by
    apply immortalFrom_of_reaches base c himmortal
    simpa [nextOuter] using herase
  rcases gap_stage_of_immortal base c hmortal growth source register next
      hrule .two nextOuter himmortalNext with ⟨nextDistance, hnextGap⟩
  rcases two_from_entry base c hmortal growth source register next hrule
      nextOuter nextDistance (distance + 1 + previous) hnextGap hbehindNext
      himmortalNext with ⟨finish, hfinish, hbound⟩
  refine ⟨finish, herase.trans hfinish, ?_⟩
  omega

/-! ## The guarded cleanup-caller API -/

private theorem compileRawCommand_congr
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : RawCommand} (heq : first = second)
    (hfirst : first ∈ rawCommands) (hsecond : second ∈ rawCommands) :
    CounterControlCommandAt.compileRawCommand base c first hfirst =
      CounterControlCommandAt.compileRawCommand base c second hsecond := by
  subst second
  rfl

/-- From the exact found state of an arbitrary genuine cleanup caller, the
remaining erase suffix and shared return reach a strictly larger guarded
search.  In particular, this is the comparison-preserving guarded re-entry
needed after an intermediate unguarded replay. -/
theorem found_reaches_larger_guardedSearch_of_genuine_cleanup
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hcleanup : rawCommands.get current.search ∈
      cleanupCommands growth source)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current)) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        (foundCfg current) next.current.cfg ∧
      current.distance < next.current.distance := by
  rcases exists_stage_of_mem_cleanupCommands hcleanup with ⟨stage, hstage⟩
  have hselectedMem : rawCommands.get current.search ∈ rawCommands :=
    List.get_mem rawCommands current.search
  have hstageRaw : CounterControlCleanupRoute.command growth source stage ∈
      rawCommands :=
    command_mem_rawCommands_of_increment growth source register targetState
      hrule stage
  have hcompiled :
      CounterControlCommandAt.compileRawCommand base c
          (rawCommands.get current.search) hselectedMem =
        CounterControlCommandAt.compileRawCommand base c
          (CounterControlCleanupRoute.command growth source stage) hstageRaw := by
    exact compileRawCommand_congr base c hstage hselectedMem hstageRaw
  have hcommandSelected : CounterControlSearchSystem.command base c
      current.search =
      CounterControlCommandAt.compileRawCommand base c
        (rawCommands.get current.search) hselectedMem := by
    unfold CounterControlSearchSystem.command
      CounterControlCommandAt.compileRawCommand
    have htag : CounterControlCommandAt.rawTag
        (rawCommands.get current.search) hselectedMem =
        current.search := by
      apply CounterControlCommandAt.rawTag_eq_of_get_eq
      rfl
    rw [htag]
  have htarget :
      (command base c current.search).target =
        Target.boundary stage.expected := by
    rw [hcommandSelected, hcompiled]
    exact compile_command_target base c growth source stage hstageRaw
  have hdirection :
      (command base c current.search).searchDirection =
        orient growth .left := by
    rw [hcommandSelected, hcompiled]
    exact compile_command_searchDirection base c growth source stage hstageRaw
  have hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary stage.expected).Matches current.outer
      (orient growth .left) current.distance := by
    simpa only [htarget, hdirection] using current.gap
  have hrawGet : rawCommands.get current.search =
      CounterControlCleanupRoute.command growth source stage := hstage
  have hfound : foundCfg current =
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        current.outer.moveN (orient growth .left)
          current.distance⟩ := by
    change
      (⟨foundState (CanonicalInitializer.radius c)
          (searchState base c
            (rawCommands.get current.search).address),
        current.outer.moveN
          (command base c current.search).searchDirection
          current.distance⟩ :
        FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    rw [hrawGet, hdirection, command_address]
  have himmortalFound : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        current.outer.moveN (orient growth .left)
          current.distance⟩ := by
    rw [← hfound]
    exact himmortal
  have hread :
      (current.outer.moveN (orient growth .left)
        current.distance).read = boundarySymbol stage.expected := by
    simpa [Target.Matches, FullTM0.Tape.read_moveN] using hgap.marked
  have herase := found_reaches_success base c growth source stage hstageRaw
    (current.outer.moveN (orient growth .left)
      current.distance) hread
  let nextOuter := eraseDepart current.outer
    (orient growth .left) current.distance
  have herase' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        current.outer.moveN (orient growth .left)
          current.distance⟩
      ⟨resolve base c (stage.successRef growth source), nextOuter⟩ := by
    simpa [nextOuter, eraseDepart] using herase
  have hbehindNext : BlankBehind nextOuter (orient growth .left)
      (current.distance + 1) := by
    dsimp [nextOuter]
    simpa using blankBehind_eraseDepart hgap
      (blankBehind_zero current.outer (orient growth .left))
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (stage.successRef growth source), nextOuter⟩ :=
    immortalFrom_of_reaches base c himmortalFound herase'
  have finish : ∃ finish : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c ⟨growth, source, stage.slot⟩),
          current.outer.moveN (orient growth .left)
            current.distance⟩
        finish.current.cfg ∧
      current.distance < finish.current.distance := by
    cases stage with
    | zero =>
        rw [resolve_success_zero] at herase' himmortalNext
        have himmortalReturn : FullTM0.ImmortalFrom
            (CounterControlNestingBridge.machine base c)
            ⟨controllerReturn base c
                (NestingMachine.opposite (orient growth .left)), nextOuter⟩ := by
          rw [opposite_orient_left]
          exact himmortalNext
        rcases reaches_guardedSearch_beyond_blankBehind
            base c hmortal nextOuter (orient growth .left)
            (current.distance + 1) hbehindNext himmortalReturn with
          ⟨finish, hfinish, hbound⟩
        rw [opposite_orient_left] at hfinish
        exact ⟨finish, herase'.trans hfinish, by omega⟩
    | one =>
        rw [resolve_success_one] at herase' himmortalNext
        rcases gap_stage_of_immortal base c hmortal growth source register
            targetState hrule .zero nextOuter himmortalNext with
          ⟨nextDistance, hnextGap⟩
        rcases zero_from_entry base c hmortal growth source register
            targetState hrule nextOuter nextDistance
            (current.distance + 1) hnextGap hbehindNext
            himmortalNext with ⟨finish, hfinish, hbound⟩
        exact ⟨finish, herase'.trans hfinish, by omega⟩
    | two =>
        rw [resolve_success_two] at herase' himmortalNext
        rcases gap_stage_of_immortal base c hmortal growth source register
            targetState hrule .one nextOuter himmortalNext with
          ⟨nextDistance, hnextGap⟩
        rcases one_from_entry base c hmortal growth source register
            targetState hrule nextOuter nextDistance
            (current.distance + 1) hnextGap hbehindNext
            himmortalNext with ⟨finish, hfinish, hbound⟩
        exact ⟨finish, herase'.trans hfinish, by omega⟩
    | three =>
        rw [resolve_success_three] at herase' himmortalNext
        rcases gap_stage_of_immortal base c hmortal growth source register
            targetState hrule .two nextOuter himmortalNext with
          ⟨nextDistance, hnextGap⟩
        rcases two_from_entry base c hmortal growth source register
            targetState hrule nextOuter nextDistance
            (current.distance + 1) hnextGap hbehindNext
            himmortalNext with ⟨finish, hfinish, hbound⟩
        exact ⟨finish, herase'.trans hfinish, by omega⟩
  rcases finish with ⟨next, hreach, hgrowth⟩
  refine ⟨next, ?_, hgrowth⟩
  rw [hfound]
  exact hreach

/-- Guarded compatibility wrapper for the exact-found-state cleanup API. -/
theorem found_reaches_larger_guardedSearch_of_cleanup
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hcleanup : rawCommands.get current.current.search ∈
      cleanupCommands growth source)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        (foundCfg current.current) next.current.cfg ∧
      current.current.distance < next.current.distance := by
  exact found_reaches_larger_guardedSearch_of_genuine_cleanup
    base c hmortal current.current growth source register targetState hrule
    hcleanup himmortal

/-- Cleanup callers directly satisfy the monotone found-state re-entry
classification: the cleanup suffix actually increases the advertised gap. -/
theorem foundMonotoneGuardedEntryOutcome_of_cleanup
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hcleanup : rawCommands.get current.search ∈
      cleanupCommands growth source)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  rcases found_reaches_larger_guardedSearch_of_genuine_cleanup
      base c hmortal current growth source register targetState hrule
      hcleanup himmortal with ⟨next, hreach, hdistance⟩
  exact ⟨FoundMonotoneGuardedEntryOutcome.nextSearch next hreach
    hdistance.le⟩

/-- Entry-state form of guard-free cleanup progress, obtained by prepending
the finite generated-search resolution. -/
theorem reaches_larger_guardedSearch_of_genuine_cleanup
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hcleanup : rawCommands.get current.search ∈
      cleanupCommands growth source)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.cfg) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        current.cfg next.current.cfg ∧
      current.distance < next.current.distance := by
  have hfound := reaches_foundCfg_of_immortal current himmortal
  have himmortalFound := immortalFrom_foundCfg current himmortal
  rcases found_reaches_larger_guardedSearch_of_genuine_cleanup
      base c hmortal current
      growth source register targetState hrule hcleanup himmortalFound with
    ⟨next, htail, hgrowth⟩
  exact ⟨next, hfound.trans htail, hgrowth⟩

/-- Guarded compatibility wrapper for entry-state cleanup progress. -/
theorem reaches_larger_guardedSearch_of_cleanup
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (targetState : Nat)
    (hrule : (source, .increment register targetState) ∈
      GlobalSourceProgram.program)
    (hcleanup : rawCommands.get current.current.search ∈
      cleanupCommands growth source)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) current.current.cfg) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        current.current.cfg next.current.cfg ∧
      current.current.distance < next.current.distance := by
  exact reaches_larger_guardedSearch_of_genuine_cleanup
    base c hmortal current.current growth source register targetState hrule
    hcleanup himmortal

end

end CounterControlGuardedCleanupProgress
end Hooper
end Kari
end LeanWang
