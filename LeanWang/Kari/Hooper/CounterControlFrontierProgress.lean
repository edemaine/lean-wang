/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGlobalFrontier
import LeanWang.Kari.Hooper.CounterControlLongSearchMortality

/-!
# Progress from generated-search frontier states

On an immortal orbit with a mortal source computation, every generated
search frontier has a genuine finite gap.  The converse Basic Lemma consumes
that search, after which arbitrary-entry normalization reaches the global
frontier again.  Moreover, all such consumed gaps share the uniform bound
supplied by long-search mortality.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlFrontierProgress

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlSearchSystem
open CounterControlCommandAt
open CounterControlCommandContinuationMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The search index canonically recovered from a generated raw command. -/
def rawSearch (raw : RawCommand) (hraw : raw ∈ rawCommands) : Search :=
  CounterControlCommandAt.rawTag raw hraw

@[simp] theorem rawCommands_get_rawSearch
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    rawCommands.get (rawSearch raw hraw) = raw :=
  CounterControlCommandAt.rawCommands_get_rawTag raw hraw

@[simp] theorem rawSearch_address
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    (rawCommands.get (rawSearch raw hraw)).address = raw.address := by
  rw [rawCommands_get_rawSearch]

/-- Consuming one generated search records both its genuine gap and the
strictly later successful found configuration before normalization returns
to the global frontier. -/
theorem advances_search_frontier
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩) :
    ∃ (distance : Nat)
        (final : FullTM0.Cfg (Symbol numTags) FiniteTM0.State),
      SearchGap (fun symbol => symbol = blankSymbol)
          (compileRawCommand base c raw hraw).target.Matches outer
          (compileRawCommand base c raw hraw).searchDirection distance ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c raw.address, outer⟩
          ⟨foundState (CanonicalInitializer.radius c)
              (searchState base c raw.address),
            outer.moveN
              (compileRawCommand base c raw hraw).searchDirection distance⟩ ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨foundState (CanonicalInitializer.radius c)
              (searchState base c raw.address),
            outer.moveN
              (compileRawCommand base c raw hraw).searchDirection distance⟩
          final ∧
        Frontier base c final := by
  let search := rawSearch raw hraw
  have hget : rawCommands.get search = raw := by
    exact rawCommands_get_rawSearch raw hraw
  have hstart : (searchSystem base c).startCfg search outer =
      ⟨searchState base c raw.address, outer⟩ := by
    change (⟨searchState base c (rawCommands.get search).address, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    rw [hget]
  have himmortalSearch : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ((searchSystem base c).startCfg search outer) := by
    simpa [hstart] using himmortal
  rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
      base c hmortal (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
      himmortalSearch (search := search) (outer := outer)
      Relation.ReflTransGen.refl with ⟨distance, hgap⟩
  rcases CounterControlFiniteConverse.resolves_all base c distance search
      outer hgap with hfound | hhalts
  · have hfoundCfg : (searchSystem base c).successCfg search outer distance =
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          outer.moveN
            (compileRawCommand base c raw hraw).searchDirection distance⟩ := by
      change (⟨foundState (CanonicalInitializer.radius c)
          (searchState base c (rawCommands.get search).address),
        outer.moveN
          (compileCommand base c search).searchDirection distance⟩ :
          FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
      rw [hget]
      simp [search, rawSearch, compileRawCommand]
    have hfound' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          outer.moveN
            (compileRawCommand base c raw hraw).searchDirection distance⟩ := by
      rw [hstart, hfoundCfg] at hfound
      simpa [searchSystem] using hfound
    have himmortalFound : FullTM0.ImmortalFrom
        (CounterControlNestingBridge.machine base c)
        ⟨foundState (CanonicalInitializer.radius c)
            (searchState base c raw.address),
          outer.moveN
            (compileRawCommand base c raw hraw).searchDirection distance⟩ := by
      rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
      intro hterminal
      exact himmortal (FullTM0.HaltsFrom.of_reaches hfound' hterminal)
    rcases CounterControlGlobalFrontier.reaches_frontier_of_immortalFrom
        base c hmortal _ himmortalFound with
      ⟨final, htail, hfrontier⟩
    refine ⟨distance, final, ?_, hfound', htail, hfrontier⟩
    simpa [search, rawSearch, CounterControlSearchSystem.command,
      compileRawCommand] using hgap
  · have hhalts' : FullTM0.HaltsFrom
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩ := by
      rw [hstart] at hhalts
      simpa [searchSystem] using hhalts
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨searchState base c raw.address, outer⟩).mp himmortal hhalts')

/-- Under source mortality, one bound controls the gap at every generated
search frontier lying on an immortal orbit. -/
theorem exists_uniform_bound_for_immortal_search_frontiers
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c) :
    ∃ bound : Nat, ∀ (raw : RawCommand) (hraw : raw ∈ rawCommands)
        (outer : FullTM0.Tape (Symbol numTags)),
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          ⟨searchState base c raw.address, outer⟩ →
        ∃ distance ≤ bound,
          SearchGap (fun symbol => symbol = blankSymbol)
            (compileRawCommand base c raw hraw).target.Matches outer
            (compileRawCommand base c raw hraw).searchDirection distance := by
  rcases CounterControlLongSearchMortality.exists_bound_halts_search
      base c hmortal with ⟨bound, hbound⟩
  refine ⟨bound, ?_⟩
  intro raw hraw outer himmortal
  let search := rawSearch raw hraw
  have hget : rawCommands.get search = raw := by
    exact rawCommands_get_rawSearch raw hraw
  have hstart : (searchSystem base c).startCfg search outer =
      ⟨searchState base c raw.address, outer⟩ := by
    change (⟨searchState base c (rawCommands.get search).address, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    rw [hget]
  have himmortalSearch : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ((searchSystem base c).startCfg search outer) := by
    simpa [hstart] using himmortal
  rcases CounterControlArbitrarySearchMortality.gap_of_reachable_search_on_immortal_orbit
      base c hmortal (CounterControlOpenStepLaw.openStepContinuesOrHalts base c)
      himmortalSearch (search := search) (outer := outer)
      Relation.ReflTransGen.refl with ⟨distance, hgap⟩
  have hle : distance ≤ bound := by
    by_contra hnot
    have hhalts := hbound (search := search) (outer := outer)
      (distance := distance) (by omega) hgap
    exact (FullTM0.HaltsFrom.immortalFrom_iff_not
      (CounterControlNestingBridge.machine base c)
      ((searchSystem base c).startCfg search outer)).mp
        himmortalSearch hhalts
  refine ⟨distance, hle, ?_⟩
  simpa [search, rawSearch, CounterControlSearchSystem.command,
    compileRawCommand] using hgap

end

end CounterControlFrontierProgress
end Hooper
end Kari
end LeanWang
