/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SourceRegisterSemantics
import LeanWang.Kari.Hooper.GlobalSourceProgram

/-!
# Designated semantics of the global source program

This file combines the designated source-machine semantics with the single
finite counter program constructed in `GlobalSourceProgram`.  Fixed
nonhalting gives counter-program checkpoints at every prescribed clock value,
and hence an immortal primitive counter run from the canonical encoding.

This is deliberately only the **forward, designated-start direction**.  It
does not say that every immortal counter configuration decodes to a source
run, nor does it establish the arbitrary-entry converse needed later in
Hooper's construction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace GlobalSourceSemantics

open CounterMachine SourceProgram

noncomputable section

/-- Canonical physical configuration of the one global counter program.
The source code is stored in the two encoded tape registers; both scratch
registers start at zero. -/
def canonicalCounterCfg (c : Nat.Partrec.Code) : CounterMachine.Cfg :=
  ⟨controlCode (SourceRegisterSemantics.canonical c).state
      (SourceRegisterSemantics.canonical c).tape.head,
    logicalRegisters (SourceRegisterSemantics.canonical c).tape 0⟩

@[simp]
theorem canonicalCounterCfg_temp (c : Nat.Partrec.Code) :
    (canonicalCounterCfg c).registers.temp = 0 :=
  rfl

@[simp]
theorem canonicalCounterCfg_clock (c : Nat.Partrec.Code) :
    (canonicalCounterCfg c).registers.clock = 0 :=
  rfl

/-! ## Two elementary primitive-run bounds -/

/-- A defined long iterate supplies every shorter prefix. -/
private theorem survives_of_le
    {alpha : Type*} {step : alpha → Option alpha} {start : alpha}
    {short long : Nat} (hle : short ≤ long)
    (hlong : Dynamics.Survives step start long) :
    Dynamics.Survives step start short := by
  induction long generalizing short start with
  | zero =>
      have hshort : short = 0 := Nat.eq_zero_of_le_zero hle
      subst short
      exact Dynamics.survives_zero step start
  | succ long ih =>
      by_cases htop : short = long + 1
      · subst short
        exact hlong
      · have hshort : short ≤ long := by omega
        rcases hlong with ⟨finish, hfinish⟩
        rw [Dynamics.iterate_succ] at hfinish
        cases hprefix : Dynamics.iterate step long start with
        | none => simp [hprefix] at hfinish
        | some middle =>
            exact ih hshort ⟨middle, hprefix⟩

/-- One primitive counter instruction raises the clock by at most one. -/
private theorem clock_le_add_one_of_step
    {program : CounterMachine.Program}
    {cfg nextCfg : CounterMachine.Cfg}
    (hstep : CounterMachine.step program cfg = some nextCfg) :
    nextCfg.registers.clock ≤ cfg.registers.clock + 1 := by
  cases hlookup : CounterMachine.lookupInstruction program cfg.state with
  | none =>
      simp [CounterMachine.step, hlookup] at hstep
  | some instruction =>
      cases instruction with
      | increment register target =>
          rw [CounterMachine.step, hlookup] at hstep
          cases Option.some.inj hstep
          cases register <;>
            simp [CounterMachine.Registers.increment,
              CounterMachine.Registers.set, CounterMachine.Registers.get]
      | decrement register ifZero ifPositive =>
          rw [CounterMachine.step, hlookup] at hstep
          by_cases hzero : cfg.registers.get register = 0
          · simp only [hzero, if_pos] at hstep
            cases Option.some.inj hstep
            change cfg.registers.clock ≤ cfg.registers.clock + 1
            omega
          · simp only [hzero, if_false] at hstep
            cases Option.some.inj hstep
            cases register <;>
              simp [CounterMachine.Registers.decrement,
                CounterMachine.Registers.set, CounterMachine.Registers.get]
            all_goals omega

/-- After `steps` primitive counter instructions, the clock has increased by
at most `steps`. -/
private theorem clock_le_add_steps_of_iterate
    {program : CounterMachine.Program} (steps : Nat)
    {start finish : CounterMachine.Cfg}
    (hiterate : Dynamics.iterate (CounterMachine.step program) steps start =
      some finish) :
    finish.registers.clock ≤ start.registers.clock + steps := by
  induction steps generalizing start finish with
  | zero =>
      simp only [Dynamics.iterate_zero] at hiterate
      cases Option.some.inj hiterate
      omega
  | succ steps ih =>
      rw [Dynamics.iterate_succ] at hiterate
      cases hprefix :
          Dynamics.iterate (CounterMachine.step program) steps start with
      | none => simp [hprefix] at hiterate
      | some middle =>
          have hlast : CounterMachine.step program middle = some finish := by
            simpa [hprefix] using hiterate
          have hprefixClock := ih hprefix
          have hlastClock := clock_le_add_one_of_step hlast
          omega

/-! ## Designated forward semantics -/

/-- If the fixed source computation does not halt, then the single global
counter program reaches a canonical source boundary with every prescribed
clock value. -/
theorem fixedNonhalting_has_clock_checkpoints
    {c : Nat.Partrec.Code} (h : DominoProblem.FixedNonhalting c) (n : Nat) :
    ∃ nextCfg : SourceControl.RegisterCfg,
      StateTransition.Reaches
        (CounterMachine.step GlobalSourceProgram.program)
        (canonicalCounterCfg c)
        ⟨controlCode nextCfg.state nextCfg.tape.head,
          logicalRegisters nextCfg.tape n⟩ := by
  have himmortal :=
    (SourceRegisterSemantics.fixedNonhalting_iff_immortalFrom c).1 h
  rcases himmortal n with ⟨nextCfg, hiterate⟩
  refine ⟨nextCfg, ?_⟩
  simpa [canonicalCounterCfg] using
    (GlobalSourceProgram.iterate_registerStep_reaches n hiterate 0)

/-- Designated forward implication: fixed nonhalting makes the primitive run
of the one global counter program immortal from its canonical encoding.

The clock checkpoints rule out a finite primitive run: reaching clock `n`
from clock zero requires at least `n` primitive instructions, and an exact run
of that length contains every shorter prefix. -/
theorem fixedNonhalting_immortalFrom
    {c : Nat.Partrec.Code} (h : DominoProblem.FixedNonhalting c) :
    Dynamics.ImmortalFrom
      (CounterMachine.step GlobalSourceProgram.program)
      (canonicalCounterCfg c) := by
  intro depth
  rcases fixedNonhalting_has_clock_checkpoints h depth with
    ⟨nextCfg, hcheckpoint⟩
  rcases Dynamics.exists_iterate_eq_some_of_reaches hcheckpoint with
    ⟨runtime, hruntime⟩
  have hclock := clock_le_add_steps_of_iterate runtime hruntime
  have hdepth : depth ≤ runtime := by
    change depth ≤ 0 + runtime at hclock
    simpa using hclock
  exact survives_of_le hdepth ⟨_, hruntime⟩

/-- Existential immortality corollary, witnessed by the canonical encoding.
This still asserts only the designated forward direction. -/
theorem fixedNonhalting_immortal
    {c : Nat.Partrec.Code} (h : DominoProblem.FixedNonhalting c) :
    Dynamics.Immortal (CounterMachine.step GlobalSourceProgram.program) :=
  ⟨canonicalCounterCfg c, fixedNonhalting_immortalFrom h⟩

end

end GlobalSourceSemantics
end Hooper
end Kari
end LeanWang
