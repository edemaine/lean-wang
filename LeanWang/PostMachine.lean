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

/-!
## Compilation to the older table-machine target

The current Wang-tile layer consumes `TableProgram`, whose transitions always
write and move. A Post `move` command compiles to one table transition. A Post
`write` command compiles to two table transitions: write the symbol and move
right to an auxiliary state, then move left while restoring the symbol under the
head.
-/

/-- Encoded table state for a running Post state. -/
def tableRunState (q : Nat) : Nat :=
  2 * q + 1

/-- Encoded table state used to return left after simulating a Post write. -/
def tableWriteState (q : Nat) : Nat :=
  2 * q + 2

/-- Distinguished table halt state. -/
def tableHalt : Nat :=
  0

theorem tableHalt_ne_tableRunState (q : Nat) :
    tableHalt ≠ tableRunState q := by
  unfold tableHalt tableRunState
  omega

theorem tableHalt_ne_tableWriteState (q : Nat) :
    tableHalt ≠ tableWriteState q := by
  unfold tableHalt tableWriteState
  omega

theorem tableRunState_ne_tableWriteState (q r : Nat) :
    tableRunState q ≠ tableWriteState r := by
  unfold tableRunState tableWriteState
  omega

/-- Explicit finite table alphabet: Post write symbols plus all transition read symbols. -/
def tableSymbols (P : PostProgram) : List Nat :=
  P.symbols ++ P.table.map PostTransition.read

/-- Supported symbols of the compiled table machine. -/
def tableSupportedSymbols (P : PostProgram) : List Nat :=
  P.blank :: P.tableSymbols

/-- A table transition that halts from the encoded running state of `e.state`. -/
def haltRow (P : PostProgram) (e : PostTransition) : TableTransition where
  state := tableRunState e.state
  read := e.read
  write := P.blank
  next := tableHalt
  move := Move.right

/-- Return-left rows used after a simulated Post write to next state `q`. -/
def writeReturnRows (P : PostProgram) (q : Nat) : List TableTransition :=
  (tableSupportedSymbols P).map fun a =>
    { state := tableWriteState q
      read := a
      write := a
      next := tableRunState q
      move := Move.left }

/--
Rows generated by one Post transition.

Malformed Post rows compile to an explicit halting row. This preserves
`PostProgram.step`, whose guarded semantics halts when the first matching row
has an unsupported next state or writes an unsupported symbol.
-/
def rowsForTransition (P : PostProgram) (e : PostTransition) : List TableTransition :=
  if e.next ∈ P.states then
    match e.stmt with
    | PostStmt.move m =>
        [{
          state := tableRunState e.state
          read := e.read
          write := e.read
          next := tableRunState e.next
          move := m
        }]
    | PostStmt.write b =>
        if b ∈ P.symbols then
          [{
            state := tableRunState e.state
            read := e.read
            write := b
            next := tableWriteState e.next
            move := Move.right
          }] ++ writeReturnRows P e.next
        else
          [haltRow P e]
  else
    [haltRow P e]

/-- Full table row list generated from a Post program. -/
def tableRows (P : PostProgram) : List TableTransition :=
  P.table.flatMap (rowsForTransition P)

/-- Table support states generated from rows, including both sources and targets. -/
def tableStates (P : PostProgram) : List Nat :=
  (P.tableRows.map TableTransition.state) ++
    (P.tableRows.map TableTransition.next)

/-- Compile a one-sided Post/TM0 program to the older always-write-and-move table model. -/
def toTableProgram (P : PostProgram) : TableProgram where
  symbols := P.tableSymbols
  states := tableStates P
  blank := P.blank
  start := tableRunState P.start
  halt := tableHalt
  table := tableRows P

@[simp]
theorem toTableProgram_blank (P : PostProgram) :
    P.toTableProgram.blank = P.blank := rfl

@[simp]
theorem toTableProgram_start (P : PostProgram) :
    P.toTableProgram.start = tableRunState P.start := rfl

@[simp]
theorem toTableProgram_halt (P : PostProgram) :
    P.toTableProgram.halt = tableHalt := rfl

@[simp]
theorem toTableProgram_table (P : PostProgram) :
    P.toTableProgram.table = tableRows P := rfl

@[simp]
theorem toTableProgram_supportedSymbols (P : PostProgram) :
    P.toTableProgram.supportedSymbols = tableSupportedSymbols P := rfl

theorem mem_tableStates_of_mem_row_state {P : PostProgram} {e : TableTransition}
    (h : e ∈ tableRows P) : e.state ∈ tableStates P := by
  unfold tableStates
  exact List.mem_append_left _ (List.mem_map_of_mem h)

theorem mem_tableStates_of_mem_row_next {P : PostProgram} {e : TableTransition}
    (h : e ∈ tableRows P) : e.next ∈ tableStates P := by
  unfold tableStates
  exact List.mem_append_right _ (List.mem_map_of_mem h)

theorem row_next_mem_toTableProgram_supportedStates {P : PostProgram} {e : TableTransition}
    (h : e ∈ tableRows P) :
    e.next ∈ P.toTableProgram.supportedStates := by
  simp [TableProgram.supportedStates, toTableProgram, mem_tableStates_of_mem_row_next h]

theorem write_mem_supportedSymbols_of_mem_writeReturnRows
    {P : PostProgram} {q : Nat} {e : TableTransition}
    (h : e ∈ writeReturnRows P q) :
    e.write ∈ tableSupportedSymbols P := by
  rw [writeReturnRows, List.mem_map] at h
  rcases h with ⟨a, ha, he⟩
  rw [← he]
  exact ha

set_option linter.flexible false in
theorem write_mem_supportedSymbols_of_mem_rowsForTransition
    {P : PostProgram} {pe : PostTransition} {e : TableTransition}
    (hpe : pe ∈ P.table)
    (h : e ∈ rowsForTransition P pe) :
    e.write ∈ tableSupportedSymbols P := by
  rcases pe with ⟨pstate, pread, pnext, pstmt⟩
  by_cases hnext : pnext ∈ P.states
  · cases pstmt with
    | move m =>
        simp [rowsForTransition, hnext] at h
        rcases h with rfl
        simp [tableSupportedSymbols, tableSymbols]
        apply Or.inr
        apply Or.inr
        exact ⟨⟨pstate, pread, pnext, PostStmt.move m⟩, hpe, rfl⟩
    | write b =>
        by_cases hb : b ∈ P.symbols
        · simp [rowsForTransition, hnext, hb] at h
          rcases h with (rfl | hret)
          · simp [tableSupportedSymbols, tableSymbols, hb]
          · exact write_mem_supportedSymbols_of_mem_writeReturnRows hret
        · simp [rowsForTransition, hnext, hb] at h
          rcases h with rfl
          simp [haltRow, tableSupportedSymbols]
  · simp [rowsForTransition, hnext] at h
    rcases h with rfl
    simp [haltRow, tableSupportedSymbols]

theorem row_write_mem_toTableProgram_supportedSymbols {P : PostProgram} {e : TableTransition}
    (h : e ∈ tableRows P) :
    e.write ∈ P.toTableProgram.supportedSymbols := by
  rw [toTableProgram_supportedSymbols]
  rw [tableRows, List.mem_flatMap] at h
  rcases h with ⟨pe, _hpe, he⟩
  exact write_mem_supportedSymbols_of_mem_rowsForTransition _hpe he

end PostProgram

end LeanWang
