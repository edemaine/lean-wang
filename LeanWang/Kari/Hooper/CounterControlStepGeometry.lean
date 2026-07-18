/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlAbstractTrace
import LeanWang.Kari.Hooper.CounterControlFrameBacking

/-!
# Abstract counter steps inside a finite frame

The operational controller has three genuinely different one-instruction
cases: increment, zero decrement, and positive decrement.  This file exposes
that trichotomy directly from an equation for `CounterMachine.step`, without
mentioning any compiled search or finite-control state.

For an increment, the current frame invariant leaves only two geometric
possibilities.  The enlarged core either still lies strictly before the saved
outer target, or its new boundary `4` is exactly that target.  The latter is
the collision which triggers Hooper's cleanup and unwind path.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlStepGeometry

open CounterMachine CounterProgram
open FramedMarkerTape FramedCounterGeometry

noncomputable section

/-- Complete case analysis of one defined primitive counter transition.  The
lookup equation is retained so callers can recover the corresponding rule in
the explicit global program. -/
inductive StepCase (program : Program) (cfg nextCfg : Cfg) : Prop where
  | increment (register : Register) (next : State)
      (lookup : lookupInstruction program cfg.state =
        some (.increment register next))
      (nextCfg_eq : nextCfg =
        ⟨next, cfg.registers.increment register⟩) :
      StepCase program cfg nextCfg
  | decrementZero (register : Register) (ifZero ifPositive : State)
      (lookup : lookupInstruction program cfg.state =
        some (.decrement register ifZero ifPositive))
      (zero : cfg.registers.get register = 0)
      (nextCfg_eq : nextCfg = ⟨ifZero, cfg.registers⟩) :
      StepCase program cfg nextCfg
  | decrementPositive (register : Register) (ifZero ifPositive : State)
      (lookup : lookupInstruction program cfg.state =
        some (.decrement register ifZero ifPositive))
      (positive : 0 < cfg.registers.get register)
      (nextCfg_eq : nextCfg =
        ⟨ifPositive, cfg.registers.decrement register⟩) :
      StepCase program cfg nextCfg

/-- Every successful primitive counter step belongs to exactly one of the
three operational cases needed by the concrete controller simulation. -/
theorem stepCase_of_step_eq_some {program : Program} {cfg nextCfg : Cfg}
    (hstep : step program cfg = some nextCfg) :
    StepCase program cfg nextCfg := by
  cases hlookup : lookupInstruction program cfg.state with
  | none => simp [step, hlookup] at hstep
  | some instruction =>
      cases instruction with
      | increment register next =>
          have hnext : nextCfg =
              ⟨next, cfg.registers.increment register⟩ := by
            rw [step, hlookup] at hstep
            exact (Option.some.inj hstep).symm
          exact .increment register next hlookup hnext
      | decrement register ifZero ifPositive =>
          by_cases hzero : cfg.registers.get register = 0
          · have hnext : nextCfg = ⟨ifZero, cfg.registers⟩ := by
              rw [step, hlookup] at hstep
              simp only [hzero, if_pos] at hstep
              exact (Option.some.inj hstep).symm
            exact .decrementZero register ifZero ifPositive hlookup hzero hnext
          · have hpositive : 0 < cfg.registers.get register :=
              Nat.pos_of_ne_zero hzero
            have hnext : nextCfg =
                ⟨ifPositive, cfg.registers.decrement register⟩ := by
              rw [step, hlookup] at hstep
              simp only [hzero, if_false] at hstep
              exact (Option.some.inj hstep).symm
            exact .decrementPositive register ifZero ifPositive hlookup
              hpositive hnext

/-- The lookup retained by an abstract step case names a genuine rule of the
finite counter program. -/
theorem rule_mem_of_stepCase {program : Program} {cfg nextCfg : Cfg}
    (hcase : StepCase program cfg nextCfg) :
    ∃ instruction,
      (cfg.state, instruction) ∈ program ∧
        lookupInstruction program cfg.state = some instruction := by
  cases hcase with
  | increment register next hlookup _ =>
      exact ⟨.increment register next,
        rule_mem_of_lookupInstruction_eq_some hlookup, hlookup⟩
  | decrementZero register ifZero ifPositive hlookup _ _ =>
      exact ⟨.decrement register ifZero ifPositive,
        rule_mem_of_lookupInstruction_eq_some hlookup, hlookup⟩
  | decrementPositive register ifZero ifPositive hlookup _ _ =>
      exact ⟨.decrement register ifZero ifPositive,
        rule_mem_of_lookupInstruction_eq_some hlookup, hlookup⟩

/-! ## Uniform layout growth -/

/-- One primitive counter instruction enlarges the five-boundary layout by at
most one cell.  Zero tests preserve it and positive decrements shrink it. -/
theorem layoutEnd_next_le_add_one_of_step_eq_some
    {program : Program} {cfg nextCfg : Cfg}
    (hstep : step program cfg = some nextCfg) :
    layoutEnd nextCfg.registers ≤ layoutEnd cfg.registers + 1 := by
  cases stepCase_of_step_eq_some hstep with
  | increment register next _ hnext =>
      subst nextCfg
      simp
  | decrementZero register ifZero ifPositive _ _ hnext =>
      subst nextCfg
      change layoutEnd cfg.registers ≤ layoutEnd cfg.registers + 1
      omega
  | decrementPositive register ifZero ifPositive _ hpositive hnext =>
      subst nextCfg
      change layoutEnd (cfg.registers.decrement register) ≤
        layoutEnd cfg.registers + 1
      have hshrink := layoutEnd_decrement_lt cfg.registers register hpositive
      omega

/-- After `steps` exact primitive counter transitions, the represented layout
has grown by at most `steps` cells. -/
theorem layoutEnd_le_add_of_iterate
    {program : Program} (steps : Nat) {start finish : Cfg}
    (hiterate : Dynamics.iterate (step program) steps start = some finish) :
    layoutEnd finish.registers ≤ layoutEnd start.registers + steps := by
  induction steps generalizing finish with
  | zero =>
      simp only [Dynamics.iterate_zero] at hiterate
      cases Option.some.inj hiterate
      exact Nat.le_refl _
  | succ steps ih =>
      rw [Dynamics.iterate_succ] at hiterate
      cases hprefix : Dynamics.iterate (step program) steps start with
      | none => simp [hprefix] at hiterate
      | some current =>
          have hlast : step program current = some finish := by
            simpa [hprefix] using hiterate
          have hprefixBound := ih hprefix
          have hlastBound :=
            layoutEnd_next_le_add_one_of_step_eq_some hlast
          omega

/-! ## The only outward-frame dichotomy -/

/-- Since the current core already lies strictly before the suspended target,
an increment either leaves another blank runway cell or lands exactly on the
target.  Overshooting is impossible. -/
theorem increment_room_or_collision {numTags : Nat}
    (spec : Spec numTags) (register : Register) :
    layoutEnd (spec.registers.increment register) < spec.outerDistance ∨
      layoutEnd spec.registers + 1 = spec.outerDistance := by
  rw [layoutEnd_increment]
  exact lt_or_eq_of_le (Nat.succ_le_iff.mpr spec.core_before_target)

/-- Equivalent formulation with the collision written using the enlarged
layout endpoint. -/
theorem increment_room_or_hits_target {numTags : Nat}
    (spec : Spec numTags) (register : Register) :
    layoutEnd (spec.registers.increment register) < spec.outerDistance ∨
      layoutEnd (spec.registers.increment register) = spec.outerDistance := by
  rcases increment_room_or_collision spec register with hroom | hcollision
  · exact Or.inl hroom
  · exact Or.inr (by simpa using hcollision)

/-- Every positive decrement remains strictly inside the same suspended
outer target. -/
theorem decrement_has_room {numTags : Nat} (spec : Spec numTags)
    (register : Register) (hpositive : 0 < spec.registers.get register) :
    layoutEnd (spec.registers.decrement register) < spec.outerDistance :=
  (layoutEnd_decrement_lt spec.registers register hpositive).trans
    spec.core_before_target

/-- The clock stored by every active finite frame is smaller than its saved
outer-search distance.  This is the contradiction used after abstract
liveness produces a clock at least that distance. -/
theorem clock_lt_outerDistance {numTags : Nat} (spec : Spec numTags) :
    spec.registers.clock < spec.outerDistance :=
  (clock_lt_layoutEnd spec.registers).trans spec.core_before_target

/-- No active finite frame can represent a counter configuration whose clock
has already reached the suspended target distance. -/
theorem not_outerDistance_le_clock {numTags : Nat} (spec : Spec numTags) :
    ¬ spec.outerDistance ≤ spec.registers.clock :=
  Nat.not_le_of_gt (clock_lt_outerDistance spec)

end

end CounterControlStepGeometry
end Hooper
end Kari
end LeanWang
