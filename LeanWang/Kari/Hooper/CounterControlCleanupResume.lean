/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGlobalUnnesting
import LeanWang.Kari.Hooper.CounterControlCleanupFirstObstruction
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality

/-!
# Resuming a generated search after tag-free cleanup

Once collision cleanup has erased the five counter boundaries, its shared
return state is centered on logical coordinate `0`.  On an immortal orbit the
symbol there must be a recognized return tag.  The dispatcher erases it and
the selected command moves one cell in the counter's growth direction before
restarting its bounded search.

The old first obstruction was at distance `outerDistance` from coordinate
`0`.  This module retains the exact resumed tape and proves that immortality
forces the restarted generated search to have genuine gap distance exactly
`outerDistance - 1`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCleanupResume

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlArbitraryEntry
open CounterControlBridge
open CounterControlCleanupSemantics
open CounterControlControllerNormalization
open CounterControlGlobalUnnesting

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- An immortal shared-return entry on a cleaned tag-free counter prefix
recognizes an actual generated command.  After erasing its tag and moving one
cell outward, that command restarts with the old first obstruction at the
unique distance `outerDistance - 1`. -/
theorem reaches_resumed_search_at_first_obstruction_sub_one
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {spec : Spec numTags} {T : FullTM0.Tape (Symbol numTags)}
    (hcore : CoreRepresents spec.registers spec.growth T)
    (hrunway : ∀ position, layoutEnd spec.registers < position →
      position < spec.outerDistance →
        logicalTape spec.growth T position = blankSymbol)
    (htarget : spec.outerTarget.Matches
      (logicalTape spec.growth T spec.outerDistance))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c spec.growth,
        atLogical spec.growth (afterZero spec T) 0⟩) :
    ∃ search distance,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c spec.growth,
          atLogical spec.growth (afterZero spec T) 0⟩
        ((searchSystem base c).startCfg search
          ((afterTag spec T).move spec.growth)) ∧
      (command base c search).searchDirection = spec.growth ∧
      SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches
        ((afterTag spec T).move spec.growth) spec.growth distance ∧
      distance = spec.outerDistance - 1 := by
  let returnTape := atLogical spec.growth (afterZero spec T) 0
  let start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
    ⟨controllerReturn base c spec.growth, returnTape⟩
  have hnotHalts : ¬ FullTM0.HaltsFrom
      (CounterControlNestingBridge.machine base c) start := by
    exact (FullTM0.HaltsFrom.immortalFrom_iff_not
      (CounterControlNestingBridge.machine base c) start).mp
        (by simpa [start, returnTape] using himmortal)
  rcases return_step_or_haltsFrom base c spec.growth returnTape with
    hhalts | ⟨before, selected, after, hlist, hdirection, _hread, hstep⟩
  · exact False.elim (hnotHalts hhalts)
  · let radius := CanonicalInitializer.radius c
    let selectedOffset :=
      base + before.length * blockWidth radius
    have hat : CommandAt radius base selectedOffset selected
        (commands base c) := by
      rw [hlist]
      exact commandAt_append radius base before selected after
    have hone : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) start
        ⟨resumeState radius selectedOffset,
          returnTape.write blankSymbol⟩ := by
      apply Relation.ReflTransGen.single
      simpa [start, radius, selectedOffset] using hstep
    have hresume : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resumeState radius selectedOffset,
          returnTape.write blankSymbol⟩
        ⟨entryState radius selectedOffset,
          (returnTape.write blankSymbol).move
            selected.searchDirection⟩ := by
      change FullTM0.Reaches
        (BoundedMarkerProgram.machine base radius (commands base c)
          (coreTable base c)) _ _
      exact machine_resume_reaches (coreTable base c) hat
        (returnTape.write blankSymbol)
        (FullTM0.Tape.read_write blankSymbol returnTape)
    have herase : returnTape.write blankSymbol = afterTag spec T := by
      change (atLogical spec.growth (afterZero spec T) 0).write
          blankSymbol = afterTag spec T
      rw [atLogical_write]
      simp [afterTag, atLogical]
    have houter :
        (returnTape.write blankSymbol).move selected.searchDirection =
          (afterTag spec T).move spec.growth := by
      rw [hdirection, herase]
    have hentry : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) start
        ⟨entryState radius selectedOffset,
          (afterTag spec T).move spec.growth⟩ := by
      have hchain := hone.trans hresume
      rw [houter] at hchain
      exact hchain
    rcases CounterControlCommandAtConverse.exists_raw_of_commandAt
        base c (by simpa [radius, selectedOffset] using hat) with
      ⟨raw, hraw, hselected, hoffset⟩
    let search : Search := CounterControlCommandAt.rawTag raw hraw
    have hget : rawCommands.get search = raw :=
      CounterControlCommandAt.rawCommands_get_rawTag raw hraw
    have hselectedSearch :
        selected = command base c search := by
      simpa [search, command, CounterControlCommandAt.compileRawCommand]
        using hselected
    have hsearchDirection :
        (command base c search).searchDirection = spec.growth := by
      rw [← hselectedSearch]
      exact hdirection
    have hcommandOffset : CounterControlSearchSystem.commandOffset
        base c search = selectedOffset := by
      unfold CounterControlSearchSystem.commandOffset
      rw [hget, ← hoffset]
    have hsearchReach : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) start
        ((searchSystem base c).startCfg search
          ((afterTag spec T).move spec.growth)) := by
      simpa [searchSystem, SearchSystem.startCfg,
        BoundedMarkerProgram.entryState, hcommandOffset, radius]
        using hentry
    rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
        base c hmortal
        (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
        (by simpa [start, returnTape] using himmortal) hsearchReach with
      ⟨distance, hgapRaw⟩
    have hgap : SearchGap (fun symbol => symbol = blankSymbol)
        (command base c search).target.Matches
        ((afterTag spec T).move spec.growth) spec.growth distance := by
      simpa only [hsearchDirection] using hgapRaw
    have hfirstTarget :=
      afterTag_searchGap_of_coreTarget hcore hrunway htarget
    have hfirst : SearchGap (fun symbol => symbol = blankSymbol)
        (fun symbol => symbol ≠ blankSymbol)
        (afterTag spec T) spec.growth spec.outerDistance :=
      CounterControlCleanupFirstObstruction.SearchGap.map_mark
        hfirstTarget fun symbol hmatch hblank =>
          target_not_blank spec.outerTarget (hblank ▸ hmatch)
    have hpositive : 0 < spec.outerDistance := by
      have hendPositive : 0 < layoutEnd spec.registers := by
        simp [layoutEnd]
      exact hendPositive.trans spec.core_before_target
    have hdistance : distance = spec.outerDistance - 1 :=
      CounterControlCleanupFirstObstruction.target_distance_eq_sub_one_of_first_nonblank
        hfirst hpositive hgap
    exact ⟨search, distance,
      by simpa [start, returnTape] using hsearchReach,
      hsearchDirection, hgap, hdistance⟩

end

end CounterControlCleanupResume
end Hooper
end Kari
end LeanWang
