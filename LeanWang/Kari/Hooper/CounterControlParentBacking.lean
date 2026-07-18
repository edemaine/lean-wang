/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlRecoveredFrame
import LeanWang.Kari.Hooper.CounterControlReturnFrontier
import LeanWang.Kari.Hooper.CounterControlCleanupFirstObstruction
import LeanWang.Kari.Hooper.CounterControlArbitrarySearchMortality
import LeanWang.Kari.Hooper.CounterControlBridge

/-!
# Recovering the suspended parent frame after prefix cleanup

A tag-free finite-prefix proof deliberately forgets which generated search
owns the surrounding frame.  At the exact shared-return configuration, an
immortal orbit recovers that information from the physical tag.  This file
shows that the recovered command is not merely direction-compatible: its
target is exactly the first obstruction retained by the prefix.

Consequently the collision-time prefix upgrades to an honest recovered
frame and `CounterControlFrameBacking.BackedBy`.  Its canonical outer tape
is the cleanup tape, and the dispatcher reaches the recovered command on
precisely that outer tape after one outward move.  This is the
tape-preserving parent link needed before following the command's success
continuation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlParentBacking

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlSearchSystem
open CounterControlCoreFrame CounterControlFrameBacking
open CounterControlCleanupSemantics
open CounterControlPrefixInstructionResolution
open CounterControlRecoveredFrame
open CounterControlBridge

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Recovering the exact parent backing -/

/-- An immortal return from a represented tag-free prefix reveals an actual
generated command whose saved tag was already present at logical coordinate
zero.  Its target is forced to be the prefix's first obstruction.  Thus the
prefix is an honest exact frame backed by its canonical cleanup tape, and the
dispatcher resumes the selected command on that tape after one outward move.

The returned backing is the outer tape of `recoveredFrame`; the final search
gap states that the selected command itself owns that parent frame at the
original distance `limit`. -/
theorem recovers_parent_backing_of_immortal_return
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {registers : Registers} {growth : Turing.Dir} {limit : Nat}
    {target : Target numTags} {T : FullTM0.Tape (Symbol numTags)}
    (h : CoreTargetRepresents registers growth limit target T)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c growth,
        atLogical growth
          (afterZero
            (prefixSpec registers growth limit target
              h.core_before_limit) T) 0⟩) :
    ∃ (raw : RawCommand) (hraw : raw ∈ rawCommands),
      let search : Search := CounterControlCommandAt.rawTag raw hraw
      let frame := recoveredFrame search registers growth limit target
        h.core_before_limit T
      logicalTape growth T 0 = tagSymbol search ∧
        (CounterControlCommandAt.compileRawCommand base c raw hraw).target =
          target ∧
        (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection =
          growth ∧
        BackedBy
          (recoveredSpec search registers growth limit target
            h.core_before_limit) T frame.outer ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨controllerReturn base c growth,
            atLogical growth
              (afterZero
                (prefixSpec registers growth limit target
                  h.core_before_limit) T) 0⟩
          ⟨searchState base c raw.address, frame.outer.move growth⟩ ∧
        SearchGap (fun symbol => symbol = blankSymbol)
          (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
          frame.outer growth limit := by
  let tagFreeSpec := prefixSpec registers growth limit target
    h.core_before_limit
  let returnTape := atLogical growth (afterZero tagFreeSpec T) 0
  let start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
    ⟨controllerReturn base c growth, returnTape⟩
  rcases CounterControlReturnFrontier.reaches_generated_search_of_immortal_return
      base c growth returnTape
      (by simpa [start, returnTape, tagFreeSpec] using himmortal) with
    ⟨raw, hraw, hread, hdirection, hresume⟩
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  let frame := recoveredFrame search registers growth limit target
    h.core_before_limit T
  have htag : logicalTape growth T 0 = tagSymbol search := by
    have htag' := CounterControlRecoveredFrame.tag_eq_of_afterZero_read
      (spec := tagFreeSpec) T search (by
        simpa [tagFreeSpec, prefixSpec, returnTape, search] using hread)
    simpa [tagFreeSpec] using htag'
  have hback : BackedBy
      (recoveredSpec search registers growth limit target
        h.core_before_limit) T frame.outer := by
    simpa [frame, recoveredFrame] using
      (CounterControlRecoveredFrame.backedBy_recoveredSpec search h htag)
  have herased : returnTape.write blankSymbol = frame.outer := by
    change (atLogical growth (afterZero tagFreeSpec T) 0).write blankSymbol = _
    rw [atLogical_write]
    change atLogical growth (afterTag tagFreeSpec T) 0 = _
    have hspec : afterTag tagFreeSpec T = afterTag
        (recoveredSpec search registers growth limit target
          h.core_before_limit) T := by
      rfl
    rw [hspec, CounterControlFrameBacking.afterTag_eq_outer hback]
    simp [atLogical]
  have hresume' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c raw.address, frame.outer.move growth⟩ := by
    simpa [herased] using hresume
  have hstartSearch : (searchSystem base c).startCfg search
        (frame.outer.move growth) =
      ⟨searchState base c raw.address, frame.outer.move growth⟩ := by
    change (⟨searchState base c (rawCommands.get search).address,
      frame.outer.move growth⟩ :
        FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    rw [CounterControlCommandAt.rawCommands_get_rawTag raw hraw]
  have hsearchReach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ((searchSystem base c).startCfg search
        (frame.outer.move growth)) := by
    rw [hstartSearch]
    exact hresume'
  rcases
      CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
        base c hmortal
        (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
        (by simpa [start, returnTape, tagFreeSpec] using himmortal)
        hsearchReach with
    ⟨distance, hgap⟩
  have hgapRaw' : SearchGap (fun symbol => symbol = blankSymbol)
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      (frame.outer.move growth)
      (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection
      distance := by
    simpa only [search, CounterControlSearchSystem.command,
      CounterControlCommandAt.compileRawCommand] using hgap
  have hgapRaw : SearchGap (fun symbol => symbol = blankSymbol)
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      (frame.outer.move growth) growth distance := by
    rw [hdirection] at hgapRaw'
    exact hgapRaw'
  have hpositive : 0 < limit := by
    have hendPositive : 0 < layoutEnd registers := by
      simp [layoutEnd]
    exact hendPositive.trans h.core_before_limit
  have houterGap : SearchGap (fun symbol => symbol = blankSymbol)
      target.Matches frame.outer growth limit := by
    simpa [frame, recoveredFrame, recoveredSpec] using hback.searchGap
  have hfirst : SearchGap (fun symbol => symbol = blankSymbol)
      (fun symbol => symbol ≠ blankSymbol) frame.outer growth limit :=
    CounterControlCleanupFirstObstruction.SearchGap.map_mark
      houterGap fun symbol hmatch hblank =>
        target_not_blank target (hblank ▸ hmatch)
  have hdistance : distance = limit - 1 :=
    CounterControlCleanupFirstObstruction.target_distance_eq_sub_one_of_first_nonblank
      hfirst hpositive hgapRaw
  have hmoveOne : frame.outer.move growth =
      frame.outer.moveN growth 1 := by
    simpa using (FullTM0.Tape.move_moveN frame.outer growth 0)
  have hgapTail : SearchGap (fun symbol => symbol = blankSymbol)
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      (frame.outer.moveN growth 1) growth distance := by
    rw [← hmoveOne]
    exact hgapRaw
  have hprefixBlank : ∀ i < 1,
      frame.outer (FullTM0.Tape.offset growth i) = blankSymbol := by
    intro i hi
    have hiZero : i = 0 := by omega
    subst i
    exact houterGap.blank hpositive
  have hselectedFull : SearchGap (fun symbol => symbol = blankSymbol)
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      frame.outer growth limit := by
    have hfull := CounterControlArbitrarySearch.SearchGap.prepend_moveN
      hprefixBlank hgapTail
    have hlength : 1 + distance = limit := by omega
    simpa [hlength] using hfull
  have htargetEq :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target =
        target :=
    CounterControlTargetUniqueness.target_eq_of_matches
      hselectedFull.marked houterGap.marked
  refine ⟨raw, hraw, ?_⟩
  dsimp only
  refine ⟨htag, htargetEq, hdirection, ?_, ?_, hselectedFull⟩
  · simpa [frame] using hback
  · simpa [start, returnTape, tagFreeSpec, frame] using hresume'

end

end CounterControlParentBacking
end Hooper
end Kari
end LeanWang
