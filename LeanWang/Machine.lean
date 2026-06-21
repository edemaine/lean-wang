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

/-- Interpret a movement as a displacement of the integer tape head. -/
def delta : Move → Int
  | left => -1
  | right => 1

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

/-- An instantaneous description of a one-tape machine. -/
structure ID where
  tape : Int → Nat
  head : Int
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
      head := c.head + move.delta
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

end Machine

end LeanWang
