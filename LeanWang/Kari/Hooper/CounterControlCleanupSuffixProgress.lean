/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCleanupRoute
import LeanWang.Kari.Hooper.CounterControlCleanupEraseProgress
import LeanWang.Kari.Hooper.CounterControlGeneratedSearchGap
import LeanWang.Kari.Hooper.CounterControlCleanupSuffixGeometry
import LeanWang.Kari.Hooper.CounterControlCleanupReturnGrowth

/-!
# Immortal progress through any suffix of collision cleanup

A suspended parent command can resume at any of the four generated cleanup
searches.  This module follows the remaining erase commands one by one.  At
each search, source mortality supplies a genuine finite gap; exact command
resolution erases the boundary and departs inward; and the tape-geometry
invariant concatenates the newly traversed gap with all earlier blank cells.

After boundary `0`, the shared dispatcher reverses direction.  Its next
generated target therefore lies beyond the whole accumulated blank interval.
In particular it lies strictly farther away than the gap of the cleanup
search at which this suffix began.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupSuffixProgress

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting
open CounterControlCleanupRoute CounterControlCleanupSuffixGeometry

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

/-- Exact erase-and-depart progress for one cleanup stage, starting at its
generated search entry. -/
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
      (by simpa [command] using hraw) outer distance hgap himmortal
  simpa [eraseDepart] using hrun

/-- Every later cleanup search reached on the immortal orbit has a genuine
finite boundary gap. -/
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
    (by simpa [command] using hraw) outer himmortal

/-! ## Bottom-up progress through the four fixed stages -/

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
    ∃ finish : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.zero.slot⟩, outer⟩
        finish.cfg ∧
      distance + 1 + previous ≤ finish.distance := by
  have herase := reaches_stage_success_of_immortal base c growth source
    register next hrule .zero outer distance hgap himmortal
  rw [resolve_success_zero] at herase
  let returnTape := eraseDepart outer (orient growth .left) distance
  have hbehindReturn : BlankBehind returnTape (orient growth .left)
      (distance + 1 + previous) := by
    exact blankBehind_eraseDepart hgap hbehind
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
  rcases
      CounterControlCleanupReturnGrowth.reaches_genuineSearch_beyond_blankBehind
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
    ∃ finish : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.one.slot⟩, outer⟩
        finish.cfg ∧
      distance + 1 + previous ≤ finish.distance := by
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
    ∃ finish : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.two.slot⟩, outer⟩
        finish.cfg ∧
      distance + 1 + previous ≤ finish.distance := by
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
    ∃ finish : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨searchState base c ⟨growth, source, Stage.three.slot⟩, outer⟩
        finish.cfg ∧
      distance + 1 + previous ≤ finish.distance := by
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

/-! ## Starting after the resumed caller has already found its target -/

/-- From the exact found state of any cleanup command, the remaining cleanup
suffix and shared return reach a genuine generated search with strictly
larger gap than the cleanup search which just finished. -/
theorem found_stage_reaches_larger_genuineSearch
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
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
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        outer.moveN (orient growth .left) distance⟩) :
    ∃ finish : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c ⟨growth, source, stage.slot⟩),
          outer.moveN (orient growth .left) distance⟩
        finish.cfg ∧
      distance < finish.distance := by
  have hraw := command_mem_rawCommands_of_increment
    growth source register next hrule stage
  have hread : (outer.moveN (orient growth .left) distance).read =
      boundarySymbol stage.expected := by
    simpa [Target.Matches, FullTM0.Tape.read_moveN] using hgap.marked
  have herase := found_reaches_success base c growth source stage hraw
    (outer.moveN (orient growth .left) distance) hread
  let nextOuter := eraseDepart outer (orient growth .left) distance
  have herase' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, source, stage.slot⟩),
        outer.moveN (orient growth .left) distance⟩
      ⟨resolve base c (stage.successRef growth source), nextOuter⟩ := by
    simpa [nextOuter, eraseDepart] using herase
  have hbehindNext : BlankBehind nextOuter (orient growth .left)
      (distance + 1) := by
    dsimp [nextOuter]
    simpa using blankBehind_eraseDepart hgap
      (blankBehind_zero outer (orient growth .left))
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (stage.successRef growth source), nextOuter⟩ :=
    immortalFrom_of_reaches base c himmortal herase'
  cases stage with
  | zero =>
      rw [resolve_success_zero] at herase' himmortalNext
      have himmortalReturn : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨controllerReturn base c
              (NestingMachine.opposite (orient growth .left)), nextOuter⟩ := by
        rw [opposite_orient_left]
        exact himmortalNext
      rcases
          CounterControlCleanupReturnGrowth.reaches_genuineSearch_beyond_blankBehind
            base c hmortal nextOuter (orient growth .left) (distance + 1)
            hbehindNext himmortalReturn with
        ⟨finish, hfinish, hbound⟩
      rw [opposite_orient_left] at hfinish
      exact ⟨finish, herase'.trans hfinish, by omega⟩
  | one =>
      rw [resolve_success_one] at herase' himmortalNext
      have himmortalEntry : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, Stage.zero.slot⟩,
            nextOuter⟩ := by
        exact himmortalNext
      rcases gap_stage_of_immortal base c hmortal growth source register next
          hrule .zero nextOuter himmortalEntry with
        ⟨nextDistance, hnextGap⟩
      rcases zero_from_entry base c hmortal growth source register next hrule
          nextOuter nextDistance (distance + 1) hnextGap hbehindNext
          himmortalEntry with ⟨finish, hfinish, hbound⟩
      exact ⟨finish, herase'.trans hfinish, by omega⟩
  | two =>
      rw [resolve_success_two] at herase' himmortalNext
      have himmortalEntry : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, Stage.one.slot⟩,
            nextOuter⟩ := by
        exact himmortalNext
      rcases gap_stage_of_immortal base c hmortal growth source register next
          hrule .one nextOuter himmortalEntry with
        ⟨nextDistance, hnextGap⟩
      rcases one_from_entry base c hmortal growth source register next hrule
          nextOuter nextDistance (distance + 1) hnextGap hbehindNext
          himmortalEntry with ⟨finish, hfinish, hbound⟩
      exact ⟨finish, herase'.trans hfinish, by omega⟩
  | three =>
      rw [resolve_success_three] at herase' himmortalNext
      have himmortalEntry : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨searchState base c ⟨growth, source, Stage.two.slot⟩,
            nextOuter⟩ := by
        exact himmortalNext
      rcases gap_stage_of_immortal base c hmortal growth source register next
          hrule .two nextOuter himmortalEntry with
        ⟨nextDistance, hnextGap⟩
      rcases two_from_entry base c hmortal growth source register next hrule
          nextOuter nextDistance (distance + 1) hnextGap hbehindNext
          himmortalEntry with ⟨finish, hfinish, hbound⟩
      exact ⟨finish, herase'.trans hfinish, by omega⟩

end

end CounterControlCleanupSuffixProgress
end Hooper
end Kari
end LeanWang
