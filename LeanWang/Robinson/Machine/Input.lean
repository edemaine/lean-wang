/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Machine
import Mathlib.Computability.StateTransition

/-!
# Finite-input semantics for the concrete machine model

The original machine-to-Wang construction starts every machine on a blank
tape.  For the fixed-universal-machine reduction, the simpler interface is a
fixed machine whose finite input word is placed directly on the initial tape.
-/

namespace LeanWang
namespace MachineInput

/-- A finite word followed by the machine's blank symbol. -/
def tape (blank : Nat) (input : List Nat) (position : Nat) : Nat :=
  input[position]?.getD blank

/-- The standard initial configuration carrying a finite input word. -/
def initialID (M : Machine) (input : List Nat) : ID where
  tape := tape M.blank input
  head := 0
  state := M.start

/-- Run `M` from the finite input word rather than the empty tape. -/
def run (M : Machine) (input : List Nat) (steps : Nat) : ID :=
  Nat.iterate M.nextID steps (initialID M input)

/-- Halting of `M` on a finite input word. -/
def Halts (M : Machine) (input : List Nat) : Prop :=
  ∃ steps, (run M input steps).state = M.halt

/-- Iterate a machine until its next step enters the absorbing halt state. -/
def transition (M : Machine) (id : ID) : Option ID :=
  let next := M.nextID id
  if next.state = M.halt then none else some next

theorem transition_eq_none_iff (M : Machine) (id : ID) :
    transition M id = none ↔ (M.nextID id).state = M.halt := by
  simp [transition]

theorem mem_transition_nextID {M : Machine} {current next : ID}
    (hnext : next ∈ transition M current) :
    next = M.nextID current := by
  by_cases hhalt : (M.nextID current).state = M.halt
  · simp [transition, hhalt] at hnext
  · have hnext' : M.nextID current = next := by
      simpa [transition, hhalt] using hnext
    exact hnext'.symm

/-- Every symbol supplied on the input belongs to the machine alphabet. -/
def Supported (M : Machine) (input : List Nat) : Prop :=
  ∀ symbol ∈ input, symbol ∈ M.symbols

@[simp] theorem run_zero (M : Machine) (input : List Nat) :
    run M input 0 = initialID M input :=
  rfl

@[simp] theorem run_succ (M : Machine) (input : List Nat) (steps : Nat) :
    run M input (steps + 1) = M.nextID (run M input steps) := by
  unfold run
  rw [Function.iterate_succ_apply']

@[simp] theorem tape_eq_blank_of_length_le
    {blank : Nat} {input : List Nat} {position : Nat}
    (hposition : input.length ≤ position) :
    tape blank input position = blank := by
  simp [tape, List.getElem?_eq_none_iff.mpr hposition]

theorem run_state_ne_halt_of_not_halts {M : Machine} {input : List Nat}
    (notHalts : ¬ Halts M input) (steps : Nat) :
    (run M input steps).state ≠ M.halt := by
  intro hhalt
  exact notHalts ⟨steps, hhalt⟩

theorem run_state_eq_halt_of_le {M : Machine} {input : List Nat}
    {first second : Nat} (hle : first ≤ second)
    (hhalt : (run M input first).state = M.halt) :
    (run M input second).state = M.halt := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extra, rfl⟩
  clear hle
  induction extra with
  | zero => simpa using hhalt
  | succ extra ih =>
      rw [show first + (extra + 1) = first + extra + 1 by omega, run_succ]
      rw [Machine.nextID_of_halt M _ ih]
      exact ih

theorem transition_reaches_run_of_ne_halt {M : Machine} {input : List Nat}
    {steps : Nat} (hne : (run M input steps).state ≠ M.halt) :
    StateTransition.Reaches (transition M)
      (initialID M input) (run M input steps) := by
  induction steps with
  | zero => exact Relation.ReflTransGen.refl
  | succ steps ih =>
      have hprevious : (run M input steps).state ≠ M.halt := by
        intro hhalt
        exact hne (run_state_eq_halt_of_le (Nat.le_succ steps) hhalt)
      have hnextNe : (M.nextID (run M input steps)).state ≠ M.halt := by
        simpa [run_succ] using hne
      have hnext : transition M (run M input steps) =
          some (run M input (steps + 1)) := by
        rw [run_succ]
        simp [transition, hnextNe]
      exact Relation.ReflTransGen.tail (ih hprevious) hnext

theorem reaches_transition_eq_run {M : Machine} {input : List Nat} {id : ID}
    (hreaches : StateTransition.Reaches (transition M)
      (initialID M input) id) :
    ∃ steps, id = run M input steps := by
  induction hreaches with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨steps, rfl⟩
      have hid := mem_transition_nextID hstep
      refine ⟨steps + 1, ?_⟩
      rw [run_succ]
      exact hid

theorem transition_eval_dom_iff_halts (M : Machine) (input : List Nat) :
    (StateTransition.eval (transition M) (initialID M input)).Dom ↔
      Halts M input := by
  constructor
  · intro hdom
    rcases Part.dom_iff_mem.1 hdom with ⟨terminal, hterminal⟩
    rcases StateTransition.mem_eval.1 hterminal with ⟨hreaches, hnone⟩
    rcases reaches_transition_eq_run hreaches with ⟨steps, rfl⟩
    refine ⟨steps + 1, ?_⟩
    rw [run_succ]
    exact (transition_eq_none_iff M _).1 hnone
  · rintro ⟨steps, hhalt⟩
    induction steps with
    | zero =>
        have hinitial : (initialID M input).state = M.halt := by
          simpa using hhalt
        apply Part.dom_iff_mem.2
        refine ⟨initialID M input, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
        · exact Relation.ReflTransGen.refl
        · apply (transition_eq_none_iff M _).2
          rw [Machine.nextID_of_halt M _ hinitial]
          exact hinitial
    | succ steps ih =>
        by_cases hprevious : (run M input steps).state = M.halt
        · exact ih hprevious
        · apply Part.dom_iff_mem.2
          refine ⟨run M input steps, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
          · exact transition_reaches_run_of_ne_halt hprevious
          · apply (transition_eq_none_iff M _).2
            simpa [run_succ] using hhalt

end MachineInput
end LeanWang
