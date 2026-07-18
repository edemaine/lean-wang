/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlStepGeometry

/-!
# Monotone continuation from a reconstructed instruction body

An arbitrary validation suffix may reconstruct a finite counter core only
after it has already entered the selected instruction body.  This file
packages the common continuation from that point.  If the instruction fits,
its represented successor still contains every gap strictly inside the old
core.  If an increment collides with the saved target, exact cleanup resumes
a guarded caller beyond the old core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlBodyMonotone

open Turing CounterMachine CounterProgram
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCoreFrame
open CounterControlPrefixInstructionResolution CounterControlPrefixResume
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedResume CounterControlParentEmbedding
open CounterControlParentContinuation CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A rule of the deterministic global program defines one primitive
counter step for every register valuation. -/
private theorem exists_step_of_rule
    (source : Nat) (instruction : Instruction) (registers : Registers)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program) :
    ∃ next : CounterMachine.Cfg,
      CounterMachine.step GlobalSourceProgram.program
        ⟨source, registers⟩ = some next := by
  have hlookup : lookupInstruction GlobalSourceProgram.program source =
      some instruction :=
    (lookupInstruction_eq_some_iff_of_deterministic
      GlobalSourceProgram.program_deterministic).2 hrule
  cases instruction with
  | increment register next =>
      exact ⟨⟨next, registers.increment register⟩,
        step_of_lookup_increment hlookup⟩
  | decrement register ifZero ifPositive =>
      by_cases hzero : registers.get register = 0
      · exact ⟨⟨ifZero, registers⟩,
          step_of_lookup_decrement_zero hlookup hzero⟩
      · have hpositive : 0 < registers.get register :=
          Nat.pos_of_ne_zero hzero
        exact ⟨⟨ifPositive, registers.decrement register⟩,
          step_of_lookup_decrement_positive hlookup hpositive⟩

/-- Losing at most one marker in a primitive counter step turns strict
containment in the old core into weak containment in its successor. -/
private theorem distance_le_next_layoutEnd_of_step
    {current next : CounterMachine.Cfg}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    {distance : Nat} (hinside : distance < layoutEnd current.registers) :
    distance ≤ layoutEnd next.registers := by
  cases CounterControlStepGeometry.stepCase_of_step_eq_some hstep with
  | increment register target _hlookup hnext =>
      subst next
      rw [layoutEnd_increment]
      omega
  | decrementZero register ifZero ifPositive _hlookup _hzero hnext =>
      subst next
      exact hinside.le
  | decrementPositive register ifZero ifPositive _hlookup hpositive hnext =>
      subst next
      change distance ≤ layoutEnd (current.registers.decrement register)
      have hend := layoutEnd_decrement_add_one current.registers register
        hpositive
      omega

/-- With one additional blank cell of margin, containment remains strict
even across a positive decrement, whose layout shrinks by one. -/
private theorem distance_lt_next_layoutEnd_of_step
    {current next : CounterMachine.Cfg}
    (hstep : CounterMachine.step GlobalSourceProgram.program current =
      some next)
    {distance : Nat}
    (hinside : distance + 1 < layoutEnd current.registers) :
    distance < layoutEnd next.registers := by
  cases CounterControlStepGeometry.stepCase_of_step_eq_some hstep with
  | increment register target _hlookup hnext =>
      subst next
      rw [layoutEnd_increment]
      omega
  | decrementZero register ifZero ifPositive _hlookup _hzero hnext =>
      subst next
      change distance < layoutEnd current.registers
      omega
  | decrementPositive register ifZero ifPositive _hlookup hpositive hnext =>
      subst next
      change distance < layoutEnd (current.registers.decrement register)
      have hend := layoutEnd_decrement_add_one current.registers register
        hpositive
      omega

/-- Continue an immortal exact body configuration to either a represented
successor core or the guarded caller exposed by collision cleanup.  The
original genuine search is only required to lie strictly inside the
reconstructed pre-step core; the result preserves the weak comparison used
by alternating guarded unnesting. -/
theorem foundMonotoneGuardedEntryOutcome_of_body
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (instruction : Instruction)
    (registers : Registers) (limit : Nat) (target : Target numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (represented : CoreTargetRepresents registers growth limit target T)
    (hbody : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      (bodyCfg base c growth ⟨source, registers⟩ instruction T))
    (hinside : current.distance < layoutEnd registers)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  rcases exists_step_of_rule source instruction registers hrule with
    ⟨next, hstep⟩
  have hlookup : lookupInstruction GlobalSourceProgram.program source =
      some instruction :=
    (lookupInstruction_eq_some_iff_of_deterministic
      GlobalSourceProgram.program_deterministic).2 hrule
  rcases body_resolves_counterStep base c ⟨source, registers⟩ next
      instruction hlookup hstep represented with
    hlogical | hreturn | hhalts
  · rcases hlogical with ⟨nextTape, hreach, hnext⟩
    let core : LogicalCore base c := {
      growth := growth
      source := next.state
      source_lt :=
        CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep
      registers := next.registers
      tape := nextTape
      limit := limit
      target := target
      represented := hnext }
    have hreaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current) core.cfg := by
      have hrun := hbody.trans hreach
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        (foundCfg current)
        ⟨logicalState base c growth next.state,
          atLogical growth nextTape (layoutEnd next.registers)⟩
      exact hrun
    exact ⟨.logical core hreaches
      (distance_le_next_layoutEnd_of_step hstep hinside)⟩
  · let frame : PrefixEnvelope := ⟨growth, limit, target⟩
    let start := bodyCfg base c growth ⟨source, registers⟩ instruction T
    have hreturn' : PrefixReachesReturn base c frame start := by
      refine ⟨registers, T, represented, ?_, ?_⟩
      · have hcore := represented.core_before_limit
        change layoutEnd registers ≤ limit - 1
        omega
      · simpa [frame, start, BodyReturnReached] using hreturn
    have himmortalBody : FullTM0.ImmortalFrom
        (CounterControlNestingBridge.machine base c) start :=
      FullTM0.ImmortalFrom.of_reaches himmortal hbody
    rcases PrefixReachesReturn.resumes_of_immortal base c hmortal hreturn'
        himmortalBody with ⟨resumed⟩
    let next : GuardedSearch base c :=
      CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
    refine ⟨.nextSearch next (hbody.trans resumed.reaches) ?_⟩
    change current.distance ≤ resumed.next.distance
    have hdistance : resumed.next.distance = limit - 1 := by
      simpa [frame] using resumed.distance_eq
    rw [hdistance]
    have hcore := represented.core_before_limit
    omega
  · have hhaltsFound := FullTM0.HaltsFrom.of_reaches hbody hhalts
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        (foundCfg current)).mp himmortal hhaltsFound)

/-- Guarded callers use the stronger two-cell-margin geometry supplied by
their erased predecessor cell.  That margin survives a possible decrement,
so body execution yields a strict parent outcome rather than merely a
monotone first-entry outcome. -/
theorem foundGuardedEscapeOutcome_of_body
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (instruction : Instruction)
    (registers : Registers) (limit : Nat) (target : Target numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (represented : CoreTargetRepresents registers growth limit target T)
    (hbody : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      (bodyCfg base c growth ⟨source, registers⟩ instruction T))
    (hinside : current.current.distance + 1 < layoutEnd registers)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases exists_step_of_rule source instruction registers hrule with
    ⟨next, hstep⟩
  have hlookup : lookupInstruction GlobalSourceProgram.program source =
      some instruction :=
    (lookupInstruction_eq_some_iff_of_deterministic
      GlobalSourceProgram.program_deterministic).2 hrule
  rcases body_resolves_counterStep base c ⟨source, registers⟩ next
      instruction hlookup hstep represented with
    hlogical | hreturn | hhalts
  · rcases hlogical with ⟨nextTape, hreach, hnext⟩
    let core : LogicalCore base c := {
      growth := growth
      source := next.state
      source_lt :=
        CounterControlAbstractTrace.state_lt_logicalSpan_of_step hstep
      registers := next.registers
      tape := nextTape
      limit := limit
      target := target
      represented := hnext }
    have hreaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current) core.cfg := by
      have hrun := hbody.trans hreach
      change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
        (foundCfg current.current)
        ⟨logicalState base c growth next.state,
          atLogical growth nextTape (layoutEnd next.registers)⟩
      exact hrun
    exact ⟨.parent (.logical core hreaches
      (distance_lt_next_layoutEnd_of_step hstep hinside))⟩
  · let frame : PrefixEnvelope := ⟨growth, limit, target⟩
    let start := bodyCfg base c growth ⟨source, registers⟩ instruction T
    have hreturn' : PrefixReachesReturn base c frame start := by
      refine ⟨registers, T, represented, ?_, ?_⟩
      · have hcore := represented.core_before_limit
        change layoutEnd registers ≤ limit - 1
        omega
      · simpa [frame, start, BodyReturnReached] using hreturn
    have himmortalBody : FullTM0.ImmortalFrom
        (CounterControlNestingBridge.machine base c) start :=
      FullTM0.ImmortalFrom.of_reaches himmortal hbody
    rcases PrefixReachesReturn.resumes_of_immortal base c hmortal hreturn'
        himmortalBody with ⟨resumed⟩
    let guarded : GuardedSearch base c :=
      CounterControlGuardedResume.PrefixResumedSearch.toGuardedSearch resumed
    refine ⟨.parent (.nextSearch guarded (hbody.trans resumed.reaches) ?_)⟩
    change current.current.distance < resumed.next.distance
    have hdistance : resumed.next.distance = limit - 1 := by
      simpa [frame] using resumed.distance_eq
    rw [hdistance]
    have hcore := represented.core_before_limit
    omega
  · have hhaltsFound := FullTM0.HaltsFrom.of_reaches hbody hhalts
    exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current)).mp himmortal hhaltsFound)

end

end CounterControlBodyMonotone
end Hooper
end Kari
end LeanWang
