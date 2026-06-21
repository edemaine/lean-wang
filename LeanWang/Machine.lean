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

def toBool : Move → Bool
  | left => false
  | right => true

def ofBool : Bool → Move
  | false => left
  | true => right

def equivBool : Move ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := by
    intro m
    cases m <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

end Move

instance instPrimcodableMove : Primcodable Move :=
  Primcodable.ofEquiv Bool Move.equivBool

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

theorem runEmpty_state_eq_halt_of_le {M : Machine} {m n : Nat}
    (hmn : m ≤ n) (hm : (M.runEmpty m).state = M.halt) :
    (M.runEmpty n).state = M.halt := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  induction k with
  | zero =>
      simpa using hm
  | succ k ih =>
      rw [show m + (k + 1) = m + k + 1 by omega, runEmpty_succ]
      simp [nextID, ih]

theorem runEmpty_state_ne_halt_of_le {M : Machine} {m n : Nat}
    (hmn : m ≤ n) (hn : (M.runEmpty n).state ≠ M.halt) :
    (M.runEmpty m).state ≠ M.halt := by
  intro hm
  exact hn (runEmpty_state_eq_halt_of_le hmn hm)

end Machine

/-- One finite transition-table entry for the concrete machine model. -/
structure TableTransition where
  state : Nat
  read : Nat
  write : Nat
  next : Nat
  move : Move
deriving DecidableEq, Repr

namespace TableTransition

def toTuple (e : TableTransition) : Nat × Nat × Nat × Nat × Move :=
  (e.state, e.read, e.write, e.next, e.move)

def ofTuple (p : Nat × Nat × Nat × Nat × Move) : TableTransition where
  state := p.1
  read := p.2.1
  write := p.2.2.1
  next := p.2.2.2.1
  move := p.2.2.2.2

def equivTuple : TableTransition ≃ Nat × Nat × Nat × Nat × Move where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro e
    cases e
    rfl
  right_inv := by
    intro p
    rcases p with ⟨state, read, write, next, move⟩
    rfl

def matchesInput (e : TableTransition) (q a : Nat) : Bool :=
  e.state == q && e.read == a

def action (e : TableTransition) : Nat × Nat × Move :=
  (e.write, e.next, e.move)

end TableTransition

instance instPrimcodableTableTransition : Primcodable TableTransition :=
  Primcodable.ofEquiv (Nat × Nat × Nat × Nat × Move) TableTransition.equivTuple

/--
A finite transition-table presentation of the concrete machine model.

This is the intended target for future computable compilers: it contains only
finite data plus support proofs. The semantic `Machine` is still used by the
Wang-tile construction.
-/
structure TableMachine where
  symbols : List Nat
  states : List Nat
  blank : Nat
  start : Nat
  halt : Nat
  table : List TableTransition
  blank_mem : blank ∈ symbols
  start_mem : start ∈ states
  halt_mem : halt ∈ states

namespace TableMachine

def transition? (M : TableMachine) (q a : Nat) : Option TableTransition :=
  M.table.find? fun e => e.matchesInput q a

/--
The guarded transition function induced by a finite table.

Malformed table entries fall back to a supported halting transition. This keeps
the semantic `Machine` support obligations unconditional while later compiler
proofs can use `step_of_transition?_eq_some` for well-formed entries.
-/
def step (M : TableMachine) (q a : Nat) : Nat × Nat × Move :=
  match M.transition? q a with
  | none => (M.blank, M.halt, Move.right)
  | some e =>
      if e.write ∈ M.symbols then
        if e.next ∈ M.states then
          e.action
        else
          (M.blank, M.halt, Move.right)
      else
        (M.blank, M.halt, Move.right)

theorem step_symbol_mem (M : TableMachine) (q a : Nat) :
    (M.step q a).1 ∈ M.symbols := by
  unfold step
  cases h : M.transition? q a with
  | none =>
      exact M.blank_mem
  | some e =>
      by_cases hwrite : e.write ∈ M.symbols
      · by_cases hnext : e.next ∈ M.states
        · simp [hwrite, hnext, TableTransition.action]
        · simp [hwrite, hnext, M.blank_mem]
      · simp [hwrite, M.blank_mem]

theorem step_state_mem (M : TableMachine) (q a : Nat) :
    (M.step q a).2.1 ∈ M.states := by
  unfold step
  cases h : M.transition? q a with
  | none =>
      exact M.halt_mem
  | some e =>
      by_cases hwrite : e.write ∈ M.symbols
      · by_cases hnext : e.next ∈ M.states
        · simp [hwrite, hnext, TableTransition.action]
        · simp [hwrite, hnext, M.halt_mem]
      · simp [hwrite, M.halt_mem]

def toMachine (M : TableMachine) : Machine where
  symbols := M.symbols
  states := M.states
  blank := M.blank
  start := M.start
  halt := M.halt
  step := M.step
  blank_mem := M.blank_mem
  start_mem := M.start_mem
  halt_mem := M.halt_mem
  step_symbol_mem := by
    intro q a _hq _ha
    exact M.step_symbol_mem q a
  step_state_mem := by
    intro q a _hq _ha
    exact M.step_state_mem q a

@[simp]
theorem toMachine_step (M : TableMachine) :
    M.toMachine.step = M.step := rfl

@[simp]
theorem toMachine_blank (M : TableMachine) :
    M.toMachine.blank = M.blank := rfl

@[simp]
theorem toMachine_start (M : TableMachine) :
    M.toMachine.start = M.start := rfl

@[simp]
theorem toMachine_halt (M : TableMachine) :
    M.toMachine.halt = M.halt := rfl

theorem step_of_transition?_eq_some {M : TableMachine} {q a : Nat}
    {e : TableTransition} (h : M.transition? q a = some e)
    (hwrite : e.write ∈ M.symbols) (hnext : e.next ∈ M.states) :
    M.step q a = e.action := by
  simp [step, h, hwrite, hnext]

theorem step_of_transition?_eq_none {M : TableMachine} {q a : Nat}
    (h : M.transition? q a = none) :
    M.step q a = (M.blank, M.halt, Move.right) := by
  simp [step, h]

def HaltsEmpty (M : TableMachine) : Prop :=
  M.toMachine.HaltsEmpty

@[simp]
theorem haltsEmpty_iff (M : TableMachine) :
    M.HaltsEmpty ↔ M.toMachine.HaltsEmpty := by
  rfl

end TableMachine

/--
Raw finite machine data, without support proofs.

The compiler from computability syntax should ultimately produce this kind of
finite object. `toTableMachine` adds the distinguished blank/start/halt symbols
to the supports, and the guarded table semantics keeps all transitions inside
those finite supports.
-/
structure TableProgram where
  symbols : List Nat
  states : List Nat
  blank : Nat
  start : Nat
  halt : Nat
  table : List TableTransition
deriving DecidableEq, Repr

namespace TableProgram

def toTuple (P : TableProgram) :
    List Nat × List Nat × Nat × Nat × Nat × List TableTransition :=
  (P.symbols, P.states, P.blank, P.start, P.halt, P.table)

def ofTuple (p : List Nat × List Nat × Nat × Nat × Nat × List TableTransition) :
    TableProgram where
  symbols := p.1
  states := p.2.1
  blank := p.2.2.1
  start := p.2.2.2.1
  halt := p.2.2.2.2.1
  table := p.2.2.2.2.2

def equivTuple :
    TableProgram ≃ List Nat × List Nat × Nat × Nat × Nat × List TableTransition where
  toFun := toTuple
  invFun := ofTuple
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro p
    rcases p with ⟨symbols, states, blank, start, halt, table⟩
    rfl

def supportedSymbols (P : TableProgram) : List Nat :=
  P.blank :: P.symbols

def supportedStates (P : TableProgram) : List Nat :=
  P.start :: P.halt :: P.states

def toTableMachine (P : TableProgram) : TableMachine where
  symbols := P.supportedSymbols
  states := P.supportedStates
  blank := P.blank
  start := P.start
  halt := P.halt
  table := P.table
  blank_mem := by simp [supportedSymbols]
  start_mem := by simp [supportedStates]
  halt_mem := by simp [supportedStates]

def toMachine (P : TableProgram) : Machine :=
  P.toTableMachine.toMachine

@[simp]
theorem toTableMachine_symbols (P : TableProgram) :
    P.toTableMachine.symbols = P.supportedSymbols := rfl

@[simp]
theorem toTableMachine_states (P : TableProgram) :
    P.toTableMachine.states = P.supportedStates := rfl

@[simp]
theorem toTableMachine_step (P : TableProgram) :
    P.toTableMachine.step = P.toTableMachine.toMachine.step := rfl

end TableProgram

instance instPrimcodableTableProgram : Primcodable TableProgram :=
  Primcodable.ofEquiv
    (List Nat × List Nat × Nat × Nat × Nat × List TableTransition)
    TableProgram.equivTuple

end LeanWang
