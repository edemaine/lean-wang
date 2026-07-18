/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Finite normalization of arbitrary direct-control entries

The generated one-cell glue has only two genuine internal bridges:
increment recovery may pass through `bodyDirectBase + 1`, and a decrement
test may pass through `branchDirectSlot`.  Every outgoing rule from either
bridge enters a bounded search.  Hence an arbitrary direct-region entry
halts or leaves direct control after at most two enabled steps.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlDirectNormalization

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlArbitraryEntry

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The only generated direct-rule targets which remain in internal direct
control are the increment-recovery and decrement-branch bridges. -/
theorem target_logical_search_or_bridge
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules) :
    (∃ growth state, rule.target = .logical growth state) ∨
    (∃ address, rule.target = .search address) ∨
    (∃ growth state,
      rule.target = directRef growth state (bodyDirectBase + 1)) ∨
    ∃ growth state,
      rule.target = directRef growth state branchDirectSlot := by
  simp only [rawDirectRules, rawDirectRulesFor, List.mem_append,
    List.mem_flatMap] at hrule
  rcases hrule with ⟨programRule, hprogram, hlocal⟩ |
      ⟨programRule, hprogram, hlocal⟩
  · rcases programRule with ⟨source, instruction⟩
    cases instruction with
    | increment register target =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, incrementRules,
            AnchoredCounterGeometry.routeFromIncrement,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *
    | decrement register ifZero ifPositive =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, decrementRules,
            AnchoredCounterGeometry.routeToDecrementStart,
            AnchoredCounterGeometry.routeFromZero,
            AnchoredCounterGeometry.registerGap,
            MarkerSchedule.decrementStartBoundary,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *
  · rcases programRule with ⟨source, instruction⟩
    cases instruction with
    | increment register target =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, incrementRules,
            AnchoredCounterGeometry.routeFromIncrement,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *
    | decrement register ifZero ifPositive =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, decrementRules,
            AnchoredCounterGeometry.routeToDecrementStart,
            AnchoredCounterGeometry.routeFromZero,
            AnchoredCounterGeometry.registerGap,
            MarkerSchedule.decrementStartBoundary,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *

/-- A rule whose source is one of the two internal bridges always exits to a
bounded search; it cannot remain in direct control. -/
theorem bridge_source_targets_search
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (growth : Turing.Dir) (state : Nat)
    (hsource : rule.source = directRef growth state (bodyDirectBase + 1) ∨
      rule.source = directRef growth state branchDirectSlot) :
    ∃ address, rule.target = .search address := by
  simp only [rawDirectRules, rawDirectRulesFor, List.mem_append,
    List.mem_flatMap] at hrule
  rcases hrule with ⟨programRule, hprogram, hlocal⟩ |
      ⟨programRule, hprogram, hlocal⟩
  · rcases programRule with ⟨source, instruction⟩
    cases instruction with
    | increment register target =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, incrementRules,
            AnchoredCounterGeometry.routeFromIncrement,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *
    | decrement register ifZero ifPositive =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, decrementRules,
            AnchoredCounterGeometry.routeToDecrementStart,
            AnchoredCounterGeometry.routeFromZero,
            AnchoredCounterGeometry.registerGap,
            MarkerSchedule.decrementStartBoundary,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *
  · rcases programRule with ⟨source, instruction⟩
    cases instruction with
    | increment register target =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, incrementRules,
            AnchoredCounterGeometry.routeFromIncrement,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *
    | decrement register ifZero ifPositive =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, decrementRules,
            AnchoredCounterGeometry.routeToDecrementStart,
            AnchoredCounterGeometry.routeFromZero,
            AnchoredCounterGeometry.registerGap,
            MarkerSchedule.decrementStartBoundary,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop <;>
          norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
            finishDirectSlot] at *

private theorem localRule_mem_rawDirectRules
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (hprogram : programRule ∈ GlobalSourceProgram.program)
    (rule : RawDirectRule)
    (hlocal : rule ∈ directRulesForRule growth programRule) :
    rule ∈ rawDirectRules := by
  have horiented : rule ∈ rawDirectRulesFor growth := by
    rw [rawDirectRulesFor, List.mem_flatMap]
    exact ⟨programRule, hprogram, hlocal⟩
  cases growth with
  | right => exact List.mem_append_left _ horiented
  | left => exact List.mem_append_right _ horiented

private theorem local_body_bridge_target_is_source
    (orientation : Turing.Dir) (programRule : CounterMachine.Rule)
    (rule : RawDirectRule)
    (hlocal : rule ∈ directRulesForRule orientation programRule)
    (growth : Turing.Dir) (state : Nat)
    (htarget : rule.target =
      directRef growth state (bodyDirectBase + 1)) :
    ∃ next ∈ directRulesForRule orientation programRule,
      next.source = rule.target := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register target =>
      cases orientation <;> cases growth <;> cases register <;>
        simp_all [directRulesForRule, validationRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, incrementRules,
          AnchoredCounterGeometry.routeFromIncrement,
          MarkerValidation.sweep, directRef, searchRef] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot] at * <;> aesop
  | decrement register ifZero ifPositive =>
      cases orientation <;> cases growth <;> cases register <;>
        simp_all [directRulesForRule, validationRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, decrementRules,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero,
          AnchoredCounterGeometry.registerGap,
          MarkerSchedule.decrementStartBoundary,
          MarkerValidation.sweep, directRef, searchRef] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, zeroDirectBase] at * <;> aesop

private theorem local_branch_bridge_target_is_source
    (orientation : Turing.Dir) (programRule : CounterMachine.Rule)
    (rule : RawDirectRule)
    (hlocal : rule ∈ directRulesForRule orientation programRule)
    (growth : Turing.Dir) (state : Nat)
    (htarget : rule.target = directRef growth state branchDirectSlot) :
    ∃ next ∈ directRulesForRule orientation programRule,
      next.source = rule.target := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register target =>
      cases orientation <;> cases growth <;> cases register <;>
        simp_all [directRulesForRule, validationRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, incrementRules,
          AnchoredCounterGeometry.routeFromIncrement,
          MarkerValidation.sweep, directRef, searchRef] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot] at * <;> aesop
  | decrement register ifZero ifPositive =>
      cases orientation <;> cases growth <;> cases register <;>
        simp_all [directRulesForRule, validationRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, decrementRules,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero,
          AnchoredCounterGeometry.registerGap,
          MarkerSchedule.decrementStartBoundary,
          MarkerValidation.sweep, directRef, searchRef] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, zeroDirectBase] at * <;> aesop

/-- Each internal bridge target is itself a generated direct source. -/
theorem bridge_target_is_source
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (growth : Turing.Dir) (state slot : Nat)
    (hslot : slot = bodyDirectBase + 1 ∨ slot = branchDirectSlot)
    (htarget : rule.target = directRef growth state slot) :
    ∃ next ∈ rawDirectRules, next.source = rule.target := by
  simp only [rawDirectRules, rawDirectRulesFor, List.mem_append,
    List.mem_flatMap] at hrule
  rcases hrule with ⟨programRule, hprogram, hlocal⟩ |
      ⟨programRule, hprogram, hlocal⟩
  · rcases hslot with rfl | rfl
    · rcases local_body_bridge_target_is_source .right programRule rule
          hlocal growth state htarget with ⟨next, hnext, hsource⟩
      exact ⟨next,
        localRule_mem_rawDirectRules .right programRule hprogram next hnext,
        hsource⟩
    · rcases local_branch_bridge_target_is_source .right programRule rule
          hlocal growth state htarget with ⟨next, hnext, hsource⟩
      exact ⟨next,
        localRule_mem_rawDirectRules .right programRule hprogram next hnext,
        hsource⟩
  · rcases hslot with rfl | rfl
    · rcases local_body_bridge_target_is_source .left programRule rule
          hlocal growth state htarget with ⟨next, hnext, hsource⟩
      exact ⟨next,
        localRule_mem_rawDirectRules .left programRule hprogram next hnext,
        hsource⟩
    · rcases local_branch_bridge_target_is_source .left programRule rule
          hlocal growth state htarget with ⟨next, hnext, hsource⟩
      exact ⟨next,
        localRule_mem_rawDirectRules .left programRule hprogram next hnext,
        hsource⟩

/-- Internal bridge targets lie in the injective part of the symbolic state
allocation. -/
theorem bridge_target_wellFormed
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (growth : Turing.Dir) (state slot : Nat)
    (hslot : slot = bodyDirectBase + 1 ∨ slot = branchDirectSlot)
    (htarget : rule.target = directRef growth state slot) :
    CounterControlDeterministic.WellFormedSource rule.target := by
  rcases bridge_target_is_source rule hrule growth state slot hslot htarget with
    ⟨next, hnext, hsource⟩
  rw [← hsource]
  exact rawDirectRule_source_wellFormed next hnext

/-- Honest macro endpoints after leaving the finite direct-glue graph. -/
inductive Exit (base : Nat) (c : Nat.Partrec.Code) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop
  | logical (growth : Turing.Dir) (state : Nat)
      (T : FullTM0.Tape (Symbol numTags)) :
      Exit base c ⟨logicalState base c growth state, T⟩
  | search (address : SearchAddress)
      (T : FullTM0.Tape (Symbol numTags)) :
      Exit base c ⟨searchState base c address, T⟩

/-- Every arbitrary direct-region configuration either halts or reaches a
logical/search endpoint in at most two enabled direct steps. -/
theorem normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (hsource : cfg.q ∈ FiniteTM0.sourceStates (directTable base c)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) cfg ∨
      ∃ finish,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          cfg finish ∧ Exit base c finish := by
  rcases direct_step_or_haltsFrom base c cfg.q cfg.tape hsource with
    hhalts | ⟨rule, hrule, hstate, hmatch, hstep⟩
  · exact Or.inl hhalts
  · have hone : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) cfg
        ⟨resolve base c rule.target,
          cfg.tape.move (orient rule.growth rule.direction)⟩ := by
      apply Relation.ReflTransGen.single
      simpa using hstep
    rcases target_logical_search_or_bridge rule hrule with
      ⟨growth, state, htarget⟩ | ⟨address, htarget⟩ |
        ⟨growth, state, htarget⟩ | ⟨growth, state, htarget⟩
    · right
      refine ⟨_, hone, ?_⟩
      simpa [htarget, resolve] using
        (Exit.logical (base := base) (c := c) growth state
          (cfg.tape.move (orient rule.growth rule.direction)))
    · right
      refine ⟨_, hone, ?_⟩
      simpa [htarget, resolve] using
        (Exit.search (base := base) (c := c) address
          (cfg.tape.move (orient rule.growth rule.direction)))
    · have hnextSource : resolve base c rule.target ∈
          FiniteTM0.sourceStates (directTable base c) := by
        rw [htarget]
        simp only [directRef, resolve]
        have hkey : ∃ next ∈ rawDirectRules,
            next.source = directRef growth state (bodyDirectBase + 1) := by
          rcases bridge_target_is_source rule hrule growth state
              (bodyDirectBase + 1) (Or.inl rfl) htarget with
            ⟨next, hnext, hsourceNext⟩
          exact ⟨next, hnext, hsourceNext.trans htarget⟩
        rcases hkey with ⟨next, hnext, hsourceNext⟩
        simp only [directTable, FiniteTM0.sourceStates, List.map_flatMap,
          List.mem_flatMap]
        refine ⟨next, hnext, ?_⟩
        simp only [directRuleTable, List.map_map, List.mem_map,
          FiniteTM0.Rule.mk, Function.comp_apply]
        rcases next.read with _ | label | _
        · refine ⟨blankSymbol, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext, resolve, directRef]
        · refine ⟨boundarySymbol label, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext, resolve, directRef]
        · refine ⟨boundarySymbol ⟨0, by decide⟩, by
            simp [symbolsForRead, nonblankSymbols], ?_⟩
          simpa [hsourceNext, resolve, directRef]
      rcases direct_step_or_haltsFrom base c _ _ hnextSource with
        hhalts | ⟨next, hnext, hnextState, hnextMatch, hnextStep⟩
      · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone hhalts)
      · have hbridge : next.source =
            directRef growth state (bodyDirectBase + 1) := by
          have htargetWell := bridge_target_wellFormed rule hrule growth state
            (bodyDirectBase + 1) (Or.inl rfl) htarget
          have htargetCounter :
              CounterControlDeterministic.IsCounterSource rule.target := by
            simp [htarget, directRef,
              CounterControlDeterministic.IsCounterSource]
          have hnextCounter :
              CounterControlDeterministic.IsCounterSource next.source :=
            CounterControlDeterministic.rawDirectRules_counter_sources next hnext
          have hoffset : CounterControlDeterministic.sourceOffset rule.target =
              CounterControlDeterministic.sourceOffset next.source := by
            apply Nat.add_left_cancel
            calc
              rightLogicalBase base c +
                    CounterControlDeterministic.sourceOffset rule.target =
                  resolve base c rule.target :=
                (CounterControlDeterministic.resolve_eq_add_sourceOffset
                  base c htargetCounter).symm
              _ = resolve base c next.source := hnextState
              _ = rightLogicalBase base c +
                    CounterControlDeterministic.sourceOffset next.source :=
                CounterControlDeterministic.resolve_eq_add_sourceOffset
                  base c hnextCounter
          have heq : rule.target = next.source :=
            CounterControlDeterministic.sourceOffset_injective_on
              htargetWell (rawDirectRule_source_wellFormed next hnext) hoffset
          rw [← heq, htarget]
        rcases bridge_source_targets_search next hnext growth state
            (Or.inl hbridge) with ⟨address, htargetNext⟩
        right
        refine ⟨_, hone.trans (Relation.ReflTransGen.single hnextStep), ?_⟩
        simpa [htargetNext, resolve] using
          (Exit.search (base := base) (c := c) address
            ((cfg.tape.move (orient rule.growth rule.direction)).move
              (orient next.growth next.direction)))
    · have hnextSource : resolve base c rule.target ∈
          FiniteTM0.sourceStates (directTable base c) := by
        rcases bridge_target_is_source rule hrule growth state
            branchDirectSlot (Or.inr rfl) htarget with
          ⟨next, hnext, hsourceNext⟩
        simp only [directTable, FiniteTM0.sourceStates, List.map_flatMap,
          List.mem_flatMap]
        refine ⟨next, hnext, ?_⟩
        simp only [directRuleTable, List.map_map, List.mem_map,
          FiniteTM0.Rule.mk, Function.comp_apply]
        rcases next.read with _ | label | _
        · refine ⟨blankSymbol, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext]
        · refine ⟨boundarySymbol label, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext]
        · refine ⟨boundarySymbol ⟨0, by decide⟩, by
            simp [symbolsForRead, nonblankSymbols], ?_⟩
          simpa [hsourceNext]
      rcases direct_step_or_haltsFrom base c _ _ hnextSource with
        hhalts | ⟨next, hnext, hnextState, hnextMatch, hnextStep⟩
      · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone hhalts)
      · have htargetWell := bridge_target_wellFormed rule hrule growth state
          branchDirectSlot (Or.inr rfl) htarget
        have htargetCounter :
            CounterControlDeterministic.IsCounterSource rule.target := by
          simp [htarget, directRef,
            CounterControlDeterministic.IsCounterSource]
        have hnextCounter :
            CounterControlDeterministic.IsCounterSource next.source :=
          CounterControlDeterministic.rawDirectRules_counter_sources next hnext
        have hoffset : CounterControlDeterministic.sourceOffset rule.target =
            CounterControlDeterministic.sourceOffset next.source := by
          apply Nat.add_left_cancel
          calc
            rightLogicalBase base c +
                  CounterControlDeterministic.sourceOffset rule.target =
                resolve base c rule.target :=
              (CounterControlDeterministic.resolve_eq_add_sourceOffset
                base c htargetCounter).symm
            _ = resolve base c next.source := hnextState
            _ = rightLogicalBase base c +
                  CounterControlDeterministic.sourceOffset next.source :=
              CounterControlDeterministic.resolve_eq_add_sourceOffset
                base c hnextCounter
        have heq : rule.target = next.source :=
          CounterControlDeterministic.sourceOffset_injective_on
            htargetWell (rawDirectRule_source_wellFormed next hnext) hoffset
        have hbridge : next.source =
            directRef growth state branchDirectSlot := by
          rw [← heq, htarget]
        rcases bridge_source_targets_search next hnext growth state
            (Or.inr hbridge) with ⟨address, htargetNext⟩
        right
        refine ⟨_, hone.trans (Relation.ReflTransGen.single hnextStep), ?_⟩
        simpa [htargetNext, resolve] using
          (Exit.search (base := base) (c := c) address
            ((cfg.tape.move (orient rule.growth rule.direction)).move
              (orient next.growth next.direction)))

end

end CounterControlDirectNormalization
end Hooper
end Kari
end LeanWang
