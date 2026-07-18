/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandContinuationMortality

/-!
# A single global frontier for arbitrary immortal controller entries

The three compiler regions previously normalized to several partly symbolic
handoffs.  Command-success and collision continuations are now eliminable,
and direct normalization records the bound on every logical target.  This
file packages the result: every immortal arbitrary configuration reaches
either bounded logical control or the entry of an actually generated search.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGlobalFrontier

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlArbitraryMortality
open CounterControlCommandContinuationMortality

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

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

/-- A genuine search frontier is, in particular, the entry of the generated
raw command indexed by that search. -/
theorem frontier_of_genuineSearch
    (base : Nat) (c : Nat.Partrec.Code)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hsearch : GenuineSearchFrontier base c start) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          start finish ∧
        Frontier base c finish := by
  rcases hsearch with
    ⟨search, outer, _distance, hreach, _hgap⟩
  let raw := rawCommands.get search
  have hraw : raw ∈ rawCommands := List.get_mem rawCommands search
  refine ⟨(CounterControlSearchSystem.searchSystem base c).startCfg
      search outer, hreach, ?_⟩
  simpa [CounterControlSearchSystem.searchSystem, SearchSystem.startCfg,
    CounterControlSearchSystem.commandOffset, raw] using
      (Frontier.search (base := base) (c := c) raw hraw outer)

/-- Every immortal configuration of the complete counter controller reaches
the final bounded-logical/generated-search frontier. -/
theorem reaches_frontier_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          start finish ∧
        Frontier base c finish := by
  rcases reaches_genuineSearch_or_residual_of_immortalFrom
      base c hmortal start himmortal with
    hsearch | ⟨finish, hreach, hdirect | hcontinuation⟩
  · exact frontier_of_genuineSearch base c hsearch
  · cases hdirect with
    | logical growth state hstate T =>
        exact ⟨⟨logicalState base c growth state, T⟩, hreach,
          .logical growth state hstate T⟩
    | search address T =>
        have himmortalFinish := immortalFrom_of_reaches base c
          himmortal hreach
        rcases reaches_frontier_of_immortal_searchRef base c address T
            himmortalFinish with ⟨final, htail, hfrontier⟩
        exact ⟨final, hreach.trans htail, hfrontier⟩
  · exact reaches_frontier_of_commandContinuationHandoff
      base c himmortal hreach hcontinuation

end

end CounterControlGlobalFrontier
end Hooper
end Kari
end LeanWang
