/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.CounterProgram
import LeanWang.Kari.Hooper.RegisterLayout

/-!
# Liveness of finite counter-program assemblies

Hooper's converse argument must exclude an immortal computation trapped inside
an arithmetic or bounded-search subroutine.  Appendix VII supplies the relevant
dichotomy for the concrete machine: a nested bounded search either returns to
the suspended logical computation or halts.  The arithmetic assembly needs the
same property for every control state, including malformed initial register
values.

This file isolates that finite-control obligation from the later concrete
linker.  `CycleLaws` says that every configuration settles at a logical-cycle
boundary or reaches a halting configuration, and that a logical boundary either
completes one cycle while incrementing `clock`, or reaches a halt.  Determinism
then makes immortality rule out every halting alternative.  Consequently an
arbitrary immortal starting configuration reaches infinitely many completed
logical cycles, with clock values (and hence sparse clock-search gaps) growing
without bound.

The laws deliberately use reachability rather than a fixed running-time bound:
the verified arithmetic macros take time depending on their input registers.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterLiveness

open Turing
open CounterMachine CounterProgram

/-- A configuration is at a logical-cycle boundary when its control state is
one of the finitely many designated boundary states of the assembly. -/
def IsLogical (logicalStates : List State) (cfg : Cfg) : Prop :=
  cfg.state ∈ logicalStates

/-- Starting at `start`, the counter program can reach a configuration where
its partial transition function is undefined. -/
def HaltsFrom (program : Program) (start : Cfg) : Prop :=
  ∃ terminal,
    StateTransition.Reaches (step program) start terminal ∧
      step program terminal = none

/-- The two global progress obligations for an assembled finite counter
program.

`settle` is the arbitrary-entry property: even a malformed initial register
valuation cannot run forever inside an arithmetic block.  `advance` is the
logical-step property: a well-formed cycle boundary either completes one whole
cycle and ticks `clock` exactly once, or encounters a genuine halt. -/
structure CycleLaws (program : Program) where
  logicalStates : List State
  deterministic : CounterProgram.Deterministic program
  settle : ∀ start,
    (∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        IsLogical logicalStates finish) ∨
      HaltsFrom program start
  advance : ∀ start, IsLogical logicalStates start →
    (∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        IsLogical logicalStates finish ∧
          finish.registers.clock = start.registers.clock + 1) ∨
      HaltsFrom program start

/-- An immortal deterministic orbit cannot reach a halting configuration. -/
theorem not_haltsFrom_of_immortalFrom
    {program : Program} {start : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start) :
    ¬ HaltsFrom program start := by
  rintro ⟨terminal, hreach, hterminal⟩
  rcases Dynamics.exists_iterate_eq_some_of_reaches hreach with ⟨n, hn⟩
  rcases himmortal (n + 1) with ⟨next, hnext⟩
  simp [Dynamics.iterate_succ, hn, hterminal] at hnext

/-- No configuration reachable from an immortal start can itself reach a
halt. -/
theorem not_haltsFrom_of_reachable_immortalFrom
    {program : Program} {start current : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start)
    (hcurrent : StateTransition.Reaches (step program) start current) :
    ¬ HaltsFrom program current := by
  rintro ⟨terminal, hterminalReach, hterminal⟩
  exact not_haltsFrom_of_immortalFrom himmortal
    ⟨terminal, hcurrent.trans hterminalReach, hterminal⟩

namespace CycleLaws

variable {program : Program} (laws : CycleLaws program)

/-- Immortality eliminates the halting side of `settle`, even for an arbitrary
initial counter configuration. -/
theorem exists_logical_reachable_of_immortalFrom
    {start : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start) :
    ∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        IsLogical laws.logicalStates finish := by
  rcases laws.settle start with hlogical | hhalts
  · exact hlogical
  · exact False.elim (not_haltsFrom_of_immortalFrom himmortal hhalts)

/-- Every reachable logical boundary of an immortal orbit completes another
whole logical cycle and increments the clock once. -/
theorem exists_next_logical_of_immortalFrom
    {start current : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start)
    (hcurrent : StateTransition.Reaches (step program) start current)
    (hlogical : IsLogical laws.logicalStates current) :
    ∃ finish,
      StateTransition.Reaches (step program) current finish ∧
        IsLogical laws.logicalStates finish ∧
          finish.registers.clock = current.registers.clock + 1 := by
  rcases laws.advance current hlogical with hnext | hhalts
  · exact hnext
  · exact False.elim
      (not_haltsFrom_of_reachable_immortalFrom himmortal hcurrent hhalts)

/-- From an arbitrary immortal configuration, first settle at a logical
boundary and then complete any prescribed number of logical cycles.  The
clock at the resulting boundary is exactly the initial logical clock plus the
number of completed cycles. -/
theorem exists_logical_cycles_of_immortalFrom
    {start : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start) :
    ∃ first,
      StateTransition.Reaches (step program) start first ∧
        IsLogical laws.logicalStates first ∧
          ∀ cycles, ∃ finish,
            StateTransition.Reaches (step program) start finish ∧
              IsLogical laws.logicalStates finish ∧
                finish.registers.clock = first.registers.clock + cycles := by
  rcases laws.exists_logical_reachable_of_immortalFrom himmortal with
    ⟨first, hfirstReach, hfirstLogical⟩
  refine ⟨first, hfirstReach, hfirstLogical, ?_⟩
  intro cycles
  induction cycles with
  | zero =>
      exact ⟨first, hfirstReach, hfirstLogical, by omega⟩
  | succ cycles ih =>
      rcases ih with ⟨current, hcurrentReach, hcurrentLogical, hclock⟩
      rcases laws.exists_next_logical_of_immortalFrom himmortal
          hcurrentReach hcurrentLogical with
        ⟨finish, hfinishReach, hfinishLogical, hfinishClock⟩
      refine ⟨finish, hcurrentReach.trans hfinishReach,
        hfinishLogical, ?_⟩
      omega

/-- In particular, the clock values attained at reachable logical boundaries
of an immortal orbit are unbounded. -/
theorem exists_reachable_logical_clock_ge_of_immortalFrom
    {start : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start)
    (bound : Nat) :
    ∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        IsLogical laws.logicalStates finish ∧
          bound ≤ finish.registers.clock := by
  rcases laws.exists_logical_cycles_of_immortalFrom himmortal with
    ⟨first, _hfirstReach, _hfirstLogical, hcycles⟩
  rcases hcycles bound with
    ⟨finish, hfinishReach, hfinishLogical, hclock⟩
  refine ⟨finish, hfinishReach, hfinishLogical, ?_⟩
  omega

/-- Sparse-layout form of the growth conclusion.  Every requested distance is
eventually bounded by the exact rightward search gap representing `clock` at a
reachable logical boundary. -/
theorem exists_reachable_large_clock_searchGap_of_immortalFrom
    {start : Cfg}
    (himmortal : Dynamics.ImmortalFrom (step program) start)
    (bound : Nat) :
    ∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        IsLogical laws.logicalStates finish ∧
          bound ≤ finish.registers.clock ∧
            SearchGap
              (CounterLayout.IsBlank
                (RegisterLayout.values finish.registers))
              (CounterLayout.IsBoundary
                (RegisterLayout.values finish.registers))
              (CounterLayout.firstGapCellTape
                (RegisterLayout.values finish.registers) 3)
              .right finish.registers.clock := by
  rcases laws.exists_reachable_logical_clock_ge_of_immortalFrom
      himmortal bound with
    ⟨finish, hfinishReach, hfinishLogical, hclock⟩
  exact ⟨finish, hfinishReach, hfinishLogical, hclock,
    RegisterLayout.searchGap_clock_right finish.registers⟩

/-- Existential machine-level packaging: any immortal assembled counter
program has an arbitrary starting configuration whose reachable logical clock
gaps are unbounded. -/
theorem immortal_has_unbounded_clock_searchGaps
    (himmortal : Dynamics.Immortal (step program)) :
    ∃ start, ∀ bound, ∃ finish,
      StateTransition.Reaches (step program) start finish ∧
        IsLogical laws.logicalStates finish ∧
          bound ≤ finish.registers.clock ∧
            SearchGap
              (CounterLayout.IsBlank
                (RegisterLayout.values finish.registers))
              (CounterLayout.IsBoundary
                (RegisterLayout.values finish.registers))
              (CounterLayout.firstGapCellTape
                (RegisterLayout.values finish.registers) 3)
              .right finish.registers.clock := by
  rcases himmortal with ⟨start, hstart⟩
  exact ⟨start, fun bound =>
    laws.exists_reachable_large_clock_searchGap_of_immortalFrom hstart bound⟩

end CycleLaws

end CounterLiveness
end Hooper
end Kari
end LeanWang
