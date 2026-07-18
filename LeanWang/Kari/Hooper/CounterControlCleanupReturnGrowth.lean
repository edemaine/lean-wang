/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCleanupSuffixGeometry
import LeanWang.Kari.Hooper.CounterControlReturnFrontier
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality
import LeanWang.Kari.Hooper.CounterControlGlobalUnnesting

/-!
# Strict gap growth after a cleanup return

An erase-and-depart cleanup suffix leaves a contiguous blank interval behind
its inward-facing head.  The shared return dispatcher clears the saved tag
and reverses direction.  On an immortal orbit with mortal source, the
selected generated search has a genuine finite target.  Since generated
targets are nonblank, that target must lie beyond the entire blank interval.

This module deliberately knows nothing about the four cleanup commands.  It
turns their eventual tape invariant into the strict-distance conclusion used
by the parent-continuation proof.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupReturnGrowth

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlCommandAt
open CounterControlGlobalUnnesting
open CounterControlCleanupSuffixGeometry

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An immortal shared return which reverses an inward cleanup direction
reaches a genuine generated search beyond every accumulated blank cell. -/
theorem reaches_genuineSearch_beyond_blankBehind
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (T : FullTM0.Tape (Symbol numTags)) (inward : Turing.Dir)
    (length : Nat) (hbehind : BlankBehind T inward length)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩) :
    ∃ next : GenuineSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩
        next.cfg ∧
      length ≤ next.distance := by
  rcases CounterControlReturnFrontier.reaches_generated_search_of_immortal_return
      base c (NestingMachine.opposite inward) T himmortal with
    ⟨raw, hraw, _hread, hdirection, hreach⟩
  let outer := (T.write blankSymbol).move
    (NestingMachine.opposite inward)
  let search : Search := rawTag raw hraw
  have hget : rawCommands.get search = raw :=
    rawCommands_get_rawTag raw hraw
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
      compileRawCommand base c raw hraw := by
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
    distance_ge_of_blankBehind_return
      (fun symbol hmatch hblank =>
        target_not_blank (command base c search).target (hblank ▸ hmatch))
      hbehind (by simpa [outer] using hgapReturn)
  let next : GenuineSearch base c := {
    search := search
    outer := outer
    distance := distance
    gap := hgap }
  refine ⟨next, ?_, hdistance⟩
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨controllerReturn base c (NestingMachine.opposite inward), T⟩
    ((searchSystem base c).startCfg search outer)
  exact hsearchReach

end

end CounterControlCleanupReturnGrowth
end Hooper
end Kari
end LeanWang
