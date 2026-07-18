/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Exact classification of arbitrary logical entries

Every generated direct rule at a logical counter state is the first rule of
the mandatory validation sweep.  Thus an arbitrary tape at an allocated
logical source either halts immediately or enters the search for boundary
`3`, and the enabled branch also recovers the corresponding source-program
instruction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlLogicalEntry

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlArbitraryEntry

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A generated direct rule with a logical source is exactly the first
validation departure for a source instruction of the global counter
program. -/
theorem rawDirectRule_of_logical_source
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (growth : Turing.Dir) (state : Nat)
    (hsource : rule.source = .logical growth state) :
    ∃ instruction,
      (state, instruction) ∈ GlobalSourceProgram.program ∧
      rule =
        ⟨growth, .logical growth state, .boundary 4,
          searchRef growth state validationSearchBase, .left⟩ := by
  rcases (mem_rawDirectRules_iff rule).1 hrule with
    ⟨orientation, programRule, hprogram, hlocal⟩
  cases orientation
  all_goals
    rcases programRule with ⟨source, instruction⟩
    cases growth <;> cases instruction with
    | increment register target =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, incrementRules,
            AnchoredCounterGeometry.routeFromIncrement,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop
    | decrement register ifZero ifPositive =>
        cases register <;>
          simp_all [directRulesForRule, validationRules,
            routeEntryRules, routeContinuationRules,
            routeContinuationRulesFrom, decrementRules,
            AnchoredCounterGeometry.routeToDecrementStart,
            AnchoredCounterGeometry.routeFromZero,
            AnchoredCounterGeometry.registerGap,
            MarkerSchedule.decrementStartBoundary,
            MarkerValidation.sweep, directRef, searchRef] <;> aesop

/-- At an allocated logical source, the arbitrary scanned symbol either
disables the complete machine or enables the unique first validation step. -/
theorem logical_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (state : Nat) (hstate : state < logicalSpan)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : logicalState base c growth state ∈
      FiniteTM0.sourceStates (directTable base c)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth state, T⟩ ∨
      ∃ instruction,
        (state, instruction) ∈ GlobalSourceProgram.program ∧
        T.read = boundarySymbol 4 ∧
        FullTM0.step (CounterControlNestingBridge.machine base c)
            ⟨logicalState base c growth state, T⟩ =
          some ⟨searchState base c
              ⟨growth, state, validationSearchBase⟩,
            T.move (orient growth .left)⟩ := by
  rcases direct_step_or_haltsFrom base c
      (logicalState base c growth state) T hsource with
    hhalts | ⟨rule, hrule, hnumeric, hmatch, hstep⟩
  · exact Or.inl hhalts
  · have hruleCounter :
        CounterControlDeterministic.IsCounterSource rule.source :=
      CounterControlDeterministic.rawDirectRules_counter_sources rule hrule
    have hlogicalCounter : CounterControlDeterministic.IsCounterSource
        (.logical growth state) := by
      simp [CounterControlDeterministic.IsCounterSource]
    have hoffset : CounterControlDeterministic.sourceOffset rule.source =
        CounterControlDeterministic.sourceOffset (.logical growth state) := by
      apply Nat.add_left_cancel
      calc
        rightLogicalBase base c +
              CounterControlDeterministic.sourceOffset rule.source =
            resolve base c rule.source :=
          (CounterControlDeterministic.resolve_eq_add_sourceOffset
            base c hruleCounter).symm
        _ = logicalState base c growth state := hnumeric.symm
        _ = resolve base c (.logical growth state) := rfl
        _ = rightLogicalBase base c +
              CounterControlDeterministic.sourceOffset (.logical growth state) :=
          CounterControlDeterministic.resolve_eq_add_sourceOffset
            base c hlogicalCounter
    have hsymbolic : rule.source = .logical growth state :=
      CounterControlDeterministic.sourceOffset_injective_on
        (rawDirectRule_source_wellFormed rule hrule)
        (by simpa [CounterControlDeterministic.WellFormedSource] using hstate)
        hoffset
    rcases rawDirectRule_of_logical_source rule hrule growth state hsymbolic with
      ⟨instruction, hprogram, rfl⟩
    right
    refine ⟨instruction, hprogram, ?_, ?_⟩
    · simpa [RawRead.Matches] using hmatch
    · simpa [resolve, searchRef] using hstep

/-- An immortal arbitrary configuration at a bounded logical source must
take the first validation step; the immediate-halting alternative is
impossible. -/
theorem reaches_validationFirst_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (state : Nat) (hstate : state < logicalSpan)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : logicalState base c growth state ∈
      FiniteTM0.sourceStates (directTable base c))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth state, T⟩) :
    ∃ instruction,
      (state, instruction) ∈ GlobalSourceProgram.program ∧
      T.read = boundarySymbol 4 ∧
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth state, T⟩
        ⟨searchState base c ⟨growth, state, validationSearchBase⟩,
          T.move (orient growth .left)⟩ := by
  rcases logical_step_or_haltsFrom base c growth state hstate T hsource with
    hhalts | ⟨instruction, hprogram, hread, hstep⟩
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨logicalState base c growth state, T⟩).mp himmortal hhalts)
  · exact ⟨instruction, hprogram, hread,
      Relation.ReflTransGen.single hstep⟩

end

end CounterControlLogicalEntry
end Hooper
end Kari
end LeanWang
