/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Machine

/-!
One-sided Post/TM0-style machines.

This is deliberately closer to Mathlib's `TM0` than the older `TableProgram`
target: each transition either moves the head or writes one symbol, and halting
is represented by absence of a transition. The only deliberate difference from
Mathlib TM0 is that the tape is one-sided, matching the current quarter-plane
computation geometry.
-/

namespace LeanWang

/-- One Post/TM0 command: either move the head or write at the current head. -/
inductive PostStmt where
  | move : Move → PostStmt
  | write : Nat → PostStmt
deriving DecidableEq, Repr

namespace PostStmt

def toSum : PostStmt → Move ⊕ Nat
  | move m => Sum.inl m
  | write a => Sum.inr a

def ofSum : Move ⊕ Nat → PostStmt
  | Sum.inl m => move m
  | Sum.inr a => write a

def equivSum : PostStmt ≃ Move ⊕ Nat where
  toFun := toSum
  invFun := ofSum
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

end PostStmt

instance instPrimcodablePostStmt : Primcodable PostStmt :=
  Primcodable.ofEquiv (Move ⊕ Nat) PostStmt.equivSum

/-- One finite transition row for a Post/TM0-style machine. -/
structure PostTransition where
  state : Nat
  read : Nat
  next : Nat
  stmt : PostStmt
deriving DecidableEq, Repr

namespace PostTransition

def matchesInput (e : PostTransition) (q a : Nat) : Bool :=
  e.state == q && e.read == a

def toTuple (e : PostTransition) : Nat × Nat × Nat × PostStmt :=
  (e.state, e.read, e.next, e.stmt)

def ofTuple (p : Nat × Nat × Nat × PostStmt) : PostTransition where
  state := p.1
  read := p.2.1
  next := p.2.2.1
  stmt := p.2.2.2

def equivTuple : PostTransition ≃ Nat × Nat × Nat × PostStmt where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro e
    cases e
    rfl
  right_inv := by
    intro p
    cases p with
    | mk state rest =>
      cases rest with
      | mk read rest =>
        cases rest with
        | mk next stmt => rfl

end PostTransition

instance instPrimcodablePostTransition : Primcodable PostTransition :=
  Primcodable.ofEquiv (Nat × Nat × Nat × PostStmt) PostTransition.equivTuple

/-- Raw finite data for a one-sided Post/TM0-style machine. -/
structure PostProgram where
  symbols : List Nat
  states : List Nat
  blank : Nat
  start : Nat
  table : List PostTransition
deriving DecidableEq, Repr

namespace PostProgram

def toTuple (P : PostProgram) : List Nat × List Nat × Nat × Nat × List PostTransition :=
  (P.symbols, P.states, P.blank, P.start, P.table)

def ofTuple (p : List Nat × List Nat × Nat × Nat × List PostTransition) : PostProgram where
  symbols := p.1
  states := p.2.1
  blank := p.2.2.1
  start := p.2.2.2.1
  table := p.2.2.2.2

def equivTuple : PostProgram ≃ List Nat × List Nat × Nat × Nat × List PostTransition where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro p
    cases p with
    | mk symbols rest =>
      cases rest with
      | mk states rest =>
        cases rest with
        | mk blank rest =>
          cases rest with
          | mk start table => rfl

def transition? (P : PostProgram) (q a : Nat) : Option PostTransition :=
  P.table.find? fun e => e.matchesInput q a

/--
Guarded finite-table semantics.

Malformed rows halt. For `write`, the written symbol must be in the declared
alphabet; for both commands, the next state must be in the declared state list.
-/
def step (P : PostProgram) (q a : Nat) : Option (Nat × PostStmt) :=
  match P.transition? q a with
  | none => none
  | some e =>
      if _hnext : e.next ∈ P.states then
        match e.stmt with
        | PostStmt.move m => some (e.next, PostStmt.move m)
        | PostStmt.write b =>
            if b ∈ P.symbols then some (e.next, PostStmt.write b) else none
      else
        none

end PostProgram

instance instPrimcodablePostProgram : Primcodable PostProgram :=
  Primcodable.ofEquiv
    (List Nat × List Nat × Nat × Nat × List PostTransition)
    PostProgram.equivTuple

/-- Instantaneous description for a one-sided Post/TM0-style machine. -/
structure PostID where
  tape : Nat → Nat
  head : Nat
  state : Option Nat

namespace PostProgram

def initialID (P : PostProgram) : PostID where
  tape := fun _ => P.blank
  head := 0
  state := some P.start

def applyStmt (stmt : PostStmt) (tape : Nat → Nat) (head : Nat) : (Nat → Nat) × Nat :=
  match stmt with
  | PostStmt.move m => (tape, m.apply head)
  | PostStmt.write b => (Function.update tape head b, head)

/-- One execution step, stuttering after halt. -/
def nextID (P : PostProgram) (c : PostID) : PostID :=
  match c.state with
  | none => c
  | some q =>
      match P.step q (c.tape c.head) with
      | none => { c with state := none }
      | some (q', stmt) =>
          let r := applyStmt stmt c.tape c.head
          { tape := r.1, head := r.2, state := some q' }

def runEmpty (P : PostProgram) (n : Nat) : PostID :=
  Nat.iterate P.nextID n P.initialID

def HaltsEmpty (P : PostProgram) : Prop :=
  ∃ n : Nat, (P.runEmpty n).state = none

@[simp]
theorem runEmpty_zero (P : PostProgram) :
    P.runEmpty 0 = P.initialID := by
  rfl

theorem runEmpty_succ (P : PostProgram) (n : Nat) :
    P.runEmpty (n + 1) = P.nextID (P.runEmpty n) := by
  unfold runEmpty
  rw [Function.iterate_succ_apply']

@[simp]
theorem nextID_of_halt (P : PostProgram) (c : PostID) (h : c.state = none) :
    P.nextID c = c := by
  cases c with
  | mk tape head state =>
    cases state with
    | none => simp [nextID]
    | some q => cases h

theorem nextID_of_running {P : PostProgram} {c : PostID} {q : Nat}
    (h : c.state = some q) :
    P.nextID c =
      match P.step q (c.tape c.head) with
      | none => { c with state := none }
      | some (q', stmt) =>
          let r := applyStmt stmt c.tape c.head
          { tape := r.1, head := r.2, state := some q' } := by
  cases c with
  | mk tape head state =>
    cases h
    simp [nextID]

end PostProgram

end LeanWang
