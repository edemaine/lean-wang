/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Basic
import Mathlib.Logic.Function.Iterate

/-!
Concrete one-tape machines for the Wang-tile simulation layer.

This is intentionally a small target language. A later file can prove that
Mathlib's partial-recursive codes compile to this model, while the tiling
construction only has to reason about the local successor relation below.
-/

namespace LeanWang

/-- Head movement for a one-tape machine. -/
inductive Move where
  | left
  | right
deriving DecidableEq, Repr

namespace Move

/-- Move a one-sided tape head. A left move at the boundary stays at `0`. -/
def apply : Move → Nat → Nat
  | left, i => i.pred
  | right, i => i + 1

end Move

/--
A deterministic one-tape machine over natural-number symbols and states.

The lists `symbols` and `states` are the intended finite supports. The transition
function is total; semantic theorems can add hypotheses that it preserves those
supports away from halting states.
-/
structure Machine where
  symbols : List Nat
  states : List Nat
  blank : Nat
  start : Nat
  halt : Nat
  step : Nat → Nat → Nat × Nat × Move
  blank_mem : blank ∈ symbols
  start_mem : start ∈ states
  halt_mem : halt ∈ states
  step_symbol_mem : ∀ q a, q ∈ states → a ∈ symbols → (step q a).1 ∈ symbols
  step_state_mem : ∀ q a, q ∈ states → a ∈ symbols → (step q a).2.1 ∈ states

/-- An instantaneous description of a one-tape machine. -/
structure ID where
  tape : Nat → Nat
  head : Nat
  state : Nat

namespace Machine

/-- Initial configuration on the empty input. -/
def initialID (M : Machine) : ID where
  tape := fun _ => M.blank
  head := 0
  state := M.start

/-- One machine step. Halting configurations are fixed points. -/
def nextID (M : Machine) (c : ID) : ID :=
  if c.state = M.halt then
    c
  else
    let read := c.tape c.head
    let (write, state', move) := M.step c.state read
    { tape := fun i => if i = c.head then write else c.tape i
      head := move.apply c.head
      state := state' }

/-- The configuration after `n` steps from the empty input. -/
def runEmpty (M : Machine) (n : Nat) : ID :=
  Nat.iterate M.nextID n M.initialID

/-- The empty-input halting predicate for the concrete machine model. -/
def HaltsEmpty (M : Machine) : Prop :=
  ∃ n : Nat, (M.runEmpty n).state = M.halt

@[simp]
theorem runEmpty_zero (M : Machine) :
    M.runEmpty 0 = M.initialID := by
  rfl

@[simp]
theorem runEmpty_succ (M : Machine) (n : Nat) :
    M.runEmpty (n + 1) = M.nextID (M.runEmpty n) := by
  unfold runEmpty
  rw [Function.iterate_succ_apply']

@[simp]
theorem nextID_of_halt (M : Machine) (c : ID) (h : c.state = M.halt) :
    M.nextID c = c := by
  simp [nextID, h]

theorem nextID_of_ne_halt {M : Machine} {c : ID} (h : c.state ≠ M.halt) :
    M.nextID c =
      let read := c.tape c.head
      let (write, state', move) := M.step c.state read
      { tape := fun i => if i = c.head then write else c.tape i
        head := move.apply c.head
        state := state' } := by
  simp [nextID, h]

theorem nextID_state_of_ne_halt {M : Machine} {c : ID} (h : c.state ≠ M.halt) :
    (M.nextID c).state = (M.step c.state (c.tape c.head)).2.1 := by
  rw [nextID_of_ne_halt h]

theorem nextID_head_of_ne_halt {M : Machine} {c : ID} (h : c.state ≠ M.halt) :
    (M.nextID c).head = (M.step c.state (c.tape c.head)).2.2.apply c.head := by
  rw [nextID_of_ne_halt h]

theorem nextID_tape_head_of_ne_halt {M : Machine} {c : ID} (h : c.state ≠ M.halt) :
    (M.nextID c).tape c.head = (M.step c.state (c.tape c.head)).1 := by
  rw [nextID_of_ne_halt h]
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  simp [hstep]

theorem nextID_tape_of_ne_head {M : Machine} {c : ID} {i : Nat} (hi : i ≠ c.head) :
    (M.nextID c).tape i = c.tape i := by
  by_cases h : c.state = M.halt
  · simp [nextID, h]
  · rw [nextID_of_ne_halt h]
    rcases M.step c.state (c.tape c.head) with ⟨write, state', move⟩
    simp [hi]

end Machine

end LeanWang
