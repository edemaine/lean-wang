/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Machine

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

end MachineInput
end LeanWang
