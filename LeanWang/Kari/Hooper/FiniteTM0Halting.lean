/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BasicLemmaConverse
import LeanWang.Kari.Hooper.FiniteTM0

/-!
# Generic arbitrary-entry facts for finite TM0 tables

A `FiniteTM0` table has natural-number control states, but only finitely many
of them occur as rule sources.  This file records the corresponding semantic
fact in the unrestricted full-tape model: a configuration whose state is not
in that finite source list halts immediately, independently of its tape.

Consequently every state on an immortal orbit, including every state reached
after an arbitrary finite prefix, belongs to the table's finite source list.
These facts are the first, machine-independent step in Hooper's
arbitrary-entry argument.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FiniteTM0Halting

open Turing

variable {numSymbols : Nat}

/-- A configuration at a state absent from the table's source list has no
outgoing full-tape transition. -/
theorem step_eq_none_of_state_not_mem
    (rules : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State)
    (hstate : cfg.q ∉ FiniteTM0.sourceStates rules) :
    FullTM0.step (FiniteTM0.machine rules) cfg = none := by
  unfold FullTM0.step
  rw [FiniteTM0.machine_eq_none_of_state_not_mem hstate cfg.tape.read]
  rfl

/-- A state absent from the table's source list is terminal on every
unrestricted tape. -/
theorem haltsFrom_of_state_not_mem
    (rules : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State)
    (hstate : cfg.q ∉ FiniteTM0.sourceStates rules) :
    FullTM0.HaltsFrom (FiniteTM0.machine rules) cfg := by
  exact ⟨cfg, Relation.ReflTransGen.refl,
    step_eq_none_of_state_not_mem rules cfg hstate⟩

/-- Every arbitrary configuration is either in the finite set of possible
source states or already terminal. -/
theorem state_mem_or_haltsFrom
    (rules : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State) :
    cfg.q ∈ FiniteTM0.sourceStates rules ∨
      FullTM0.HaltsFrom (FiniteTM0.machine rules) cfg := by
  classical
  by_cases hstate : cfg.q ∈ FiniteTM0.sourceStates rules
  · exact Or.inl hstate
  · exact Or.inr (haltsFrom_of_state_not_mem rules cfg hstate)

/-- An immortal configuration must start in one of the table's finitely many
source states. -/
theorem state_mem_of_immortalFrom
    (rules : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom (FiniteTM0.machine rules) cfg) :
    cfg.q ∈ FiniteTM0.sourceStates rules := by
  classical
  by_contra hstate
  exact ((FullTM0.HaltsFrom.immortalFrom_iff_not
    (FiniteTM0.machine rules) cfg).mp himmortal)
      (haltsFrom_of_state_not_mem rules cfg hstate)

/-- Immortality is inherited by every configuration on a finite forward
execution. -/
theorem immortalFrom_of_reaches
    (rules : FiniteTM0.Table numSymbols)
    {start current :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom (FiniteTM0.machine rules) start)
    (hreach : FullTM0.Reaches (FiniteTM0.machine rules) start current) :
    FullTM0.ImmortalFrom (FiniteTM0.machine rules) current := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- Every configuration reached from an immortal arbitrary entry remains in
the finite source-state set. -/
theorem reachable_state_mem_of_immortalFrom
    (rules : FiniteTM0.Table numSymbols)
    {start current :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom (FiniteTM0.machine rules) start)
    (hreach : FullTM0.Reaches (FiniteTM0.machine rules) start current) :
    current.q ∈ FiniteTM0.sourceStates rules :=
  state_mem_of_immortalFrom rules current
    (immortalFrom_of_reaches rules himmortal hreach)

end FiniteTM0Halting
end Hooper
end Kari
end LeanWang
