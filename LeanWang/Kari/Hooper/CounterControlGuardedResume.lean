/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedSearch
import LeanWang.Kari.Hooper.CounterControlResumedBacking
import LeanWang.Kari.Hooper.CounterControlReturnFrontier
import LeanWang.Kari.Hooper.CounterControlGeneratedSearchGap

/-!
# Guarded searches produced by counter-control returns

The shared return dispatcher erases the recognized tag before moving to the
selected generated search.  This file records the resulting one-cell guard
both for the rich `PrefixResumedSearch` API and directly for an arbitrary
immortal shared-return configuration.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedResume

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlPrefixResume CounterControlReturnFrontier
open CounterControlGeneratedSearchGap

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- The level-aware result of finite-prefix cleanup carries the smaller
guarded-search invariant. -/
def PrefixResumedSearch.toGuardedSearch
    {base : Nat} {c : Nat.Partrec.Code}
    {frame : CounterControlPrefixInstructionResolution.PrefixEnvelope}
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (resumed : PrefixResumedSearch base c frame start) :
    GuardedSearch base c where
  current := resumed.next
  guard := by
    have hparentBlank : resumed.parentFrame.outer.read = blankSymbol := by
      have hblank := resumed.parent_backedBy.searchGap.blank
        resumed.limit_pos
      simpa [FullTM0.Tape.read, FullTM0.Tape.offset] using hblank
    rw [resumed.direction_eq, resumed.next_outer_eq]
    cases frame.growth <;>
      simpa [NestingMachine.opposite] using hparentBlank

/-- Every immortal shared return with mortal source reaches a guarded
genuine generated search.  No represented child core is needed: the guard
is exactly the tag cell erased by the dispatcher. -/
theorem reaches_guardedSearch_of_immortal_return
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨controllerReturn base c direction, T⟩) :
    ∃ next : GuardedSearch base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩ next.current.cfg := by
  rcases reaches_generated_search_of_immortal_return
      base c direction T himmortal with
    ⟨raw, hraw, _htag, hdirection, hreach⟩
  let outer := (T.write blankSymbol).move direction
  have himmortalSearch : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c raw.address, outer⟩ :=
    immortalFrom_of_reaches base c himmortal (by simpa [outer] using hreach)
  rcases gap_of_reachable_search_on_immortal_orbit
      base c hmortal raw hraw outer himmortalSearch with
    ⟨distance, hgap⟩
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hraw
  let current : GenuineSearch base c := {
    search := search
    outer := outer
    distance := distance
    gap := by
      change SearchGap (fun symbol => symbol = blankSymbol)
        (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
        outer
        (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection
        distance
      exact hgap }
  let next : GuardedSearch base c := {
    current := current
    guard := by
      change (outer.move
        (NestingMachine.opposite
          (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection)).read =
        blankSymbol
      rw [hdirection]
      cases direction <;>
        simp [outer, NestingMachine.opposite, FullTM0.Tape.read,
          FullTM0.Tape.move, FullTM0.Tape.write] }
  refine ⟨next, ?_⟩
  change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    ⟨controllerReturn base c direction, T⟩
    ((searchSystem base c).startCfg search outer)
  have hcfg : (searchSystem base c).startCfg search outer =
      ⟨searchState base c raw.address, outer⟩ := by
    change (⟨searchState base c (rawCommands.get search).address, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    rw [hget]
  rw [hcfg]
  simpa [outer] using hreach

end

end CounterControlGuardedResume
end Hooper
end Kari
end LeanWang
