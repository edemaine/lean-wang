/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic
import Mathlib.Logic.Function.Iterate

/-!
Concrete one-tape machines for the Wang-tile simulation layer.

This is intentionally a small target language. A later file can prove that
Mathlib's partial-recursive codes reduce to this model, by compiling them to
finite machine data, while the
tiling construction only has to reason about the local successor relation below.
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

/--
A machine whose start state, on blank input, writes blank, keeps the same state,
and moves right has a completely explicit empty-input run.
-/
theorem runEmpty_eq_right_blank_loop {M : Machine}
    (hstart : M.start ≠ M.halt)
    (hstep : M.step M.start M.blank = (M.blank, M.start, Move.right)) :
    ∀ n : Nat,
      M.runEmpty n = { tape := fun _ => M.blank, head := n, state := M.start }
  | 0 => by
      rfl
  | n + 1 => by
      rw [runEmpty_succ, runEmpty_eq_right_blank_loop hstart hstep n]
      rw [nextID_of_ne_halt (M := M) (c :=
        { tape := fun _ => M.blank, head := n, state := M.start }) hstart]
      simp [hstep, Move.apply]

theorem not_haltsEmpty_of_right_blank_loop {M : Machine}
    (hstart : M.start ≠ M.halt)
    (hstep : M.step M.start M.blank = (M.blank, M.start, Move.right)) :
    ¬ M.HaltsEmpty := by
  rintro ⟨n, hn⟩
  have hrun := runEmpty_eq_right_blank_loop (M := M) hstart hstep n
  rw [hrun] at hn
  exact hstart hn

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

namespace TableTransition

theorem toTuple_primrec : Primrec TableTransition.toTuple := by
  simpa [TableTransition.equivTuple] using
    (Primrec.of_equiv (e := TableTransition.equivTuple) :
      Primrec TableTransition.equivTuple)

theorem ofTuple_primrec : Primrec TableTransition.ofTuple := by
  simpa [TableTransition.equivTuple] using
    (Primrec.of_equiv_symm (e := TableTransition.equivTuple) :
      Primrec TableTransition.equivTuple.symm)

theorem state_primrec : Primrec TableTransition.state :=
  Primrec.fst.comp toTuple_primrec

theorem read_primrec : Primrec TableTransition.read :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem write_primrec : Primrec TableTransition.write :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem next_primrec : Primrec TableTransition.next :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))

theorem move_primrec : Primrec TableTransition.move :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))

theorem mk_primrec :
    Primrec (fun p : Nat × Nat × Nat × Nat × Move =>
      ({ state := p.1
         read := p.2.1
         write := p.2.2.1
         next := p.2.2.2.1
         move := p.2.2.2.2 } : TableTransition)) :=
  ofTuple_primrec

theorem action_primrec : Primrec TableTransition.action := by
  unfold action
  exact Primrec.pair write_primrec (Primrec.pair next_primrec move_primrec)

theorem matchesInput_primrec :
    Primrec (fun p : TableTransition × Nat × Nat =>
      p.1.matchesInput p.2.1 p.2.2) := by
  unfold matchesInput
  exact Primrec.and.comp
    (Primrec.beq.comp (state_primrec.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (Primrec.beq.comp (read_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

@[simp]
theorem matchesInput_mk_self (q a write next : Nat) (move : Move) :
    ({ state := q, read := a, write := write, next := next, move := move } :
      TableTransition).matchesInput q a = true := by
  simp [matchesInput]

theorem matchesInput_mk_of_state_ne {q q' a read write next : Nat} {move : Move}
    (h : q' ≠ q) :
    ({ state := q', read := read, write := write, next := next, move := move } :
      TableTransition).matchesInput q a = false := by
  simp [matchesInput, h]

theorem matchesInput_mk_of_read_ne {q a a' write next : Nat} {move : Move}
    (h : a' ≠ a) :
    ({ state := q, read := a', write := write, next := next, move := move } :
      TableTransition).matchesInput q a = false := by
  simp [matchesInput, h]

def lookup? (table : List TableTransition) (q a : Nat) : Option TableTransition :=
  (table.drop (table.findIdx fun e => e.matchesInput q a)).head?

theorem lookup?_eq_find? (table : List TableTransition) (q a : Nat) :
    lookup? table q a = table.find? fun e => e.matchesInput q a := by
  unfold lookup?
  induction table with
  | nil => rfl
  | cons e table ih =>
      by_cases h : e.matchesInput q a = true
      · simp [List.findIdx_cons, h]
      · simp [List.findIdx_cons, h, ih]

theorem lookup?_primrec :
    Primrec (fun p : List TableTransition × Nat × Nat =>
      lookup? p.1 p.2.1 p.2.2) := by
  unfold lookup?
  have hpred :
      Primrec₂ (fun p : List TableTransition × Nat × Nat =>
        fun e : TableTransition => e.matchesInput p.2.1 p.2.2) := by
    apply Primrec₂.mk
    exact matchesInput_primrec.comp
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hidx :
      Primrec (fun p : List TableTransition × Nat × Nat =>
        p.1.findIdx fun e => e.matchesInput p.2.1 p.2.2) :=
    Primrec.list_findIdx Primrec.fst hpred
  exact Primrec.list_head?.comp (Primrec.list_drop.comp hidx Primrec.fst)

theorem find?_primrec :
    Primrec (fun p : List TableTransition × Nat × Nat =>
      p.1.find? fun e => e.matchesInput p.2.1 p.2.2) :=
  lookup?_primrec.of_eq fun p => lookup?_eq_find? p.1 p.2.1 p.2.2

theorem find?_computable :
    Computable (fun p : List TableTransition × Nat × Nat =>
      p.1.find? fun e => e.matchesInput p.2.1 p.2.2) :=
  find?_primrec.to_comp

@[simp]
theorem find?_cons_of_matchesInput {e : TableTransition} {table : List TableTransition}
    {q a : Nat} (h : e.matchesInput q a = true) :
    (e :: table).find? (fun e => e.matchesInput q a) = some e := by
  simp [h]

@[simp]
theorem find?_cons_of_not_matchesInput {e : TableTransition} {table : List TableTransition}
    {q a : Nat} (h : e.matchesInput q a = false) :
    (e :: table).find? (fun e => e.matchesInput q a) =
      table.find? (fun e => e.matchesInput q a) := by
  simp [h]

end TableTransition

/--
A finite transition-table presentation of the concrete machine model.

This is the intended target for future computable reductions, implemented as
compilers to finite transition tables: it
contains only finite data plus support proofs. The semantic `Machine` is still
used by the Wang-tile construction.
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
the semantic `Machine` support obligations unconditional while later reduction
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

The computability reduction should ultimately produce this kind of finite
object, by compiling syntax to explicit machine data. `toTableMachine` adds the
distinguished blank/start/halt
symbols to the supports, and the guarded table semantics keeps all transitions
inside those finite supports.
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

theorem toMachine_step (P : TableProgram) :
    P.toMachine.step = P.toTableMachine.step := rfl

@[simp]
theorem toMachine_blank (P : TableProgram) :
    P.toMachine.blank = P.blank := rfl

@[simp]
theorem toMachine_start (P : TableProgram) :
    P.toMachine.start = P.start := rfl

@[simp]
theorem toMachine_halt (P : TableProgram) :
    P.toMachine.halt = P.halt := rfl

theorem toMachine_step_of_transition?_eq_some {P : TableProgram} {q a : Nat}
    {e : TableTransition} (h : P.toTableMachine.transition? q a = some e)
    (hwrite : e.write ∈ P.supportedSymbols) (hnext : e.next ∈ P.supportedStates) :
    P.toMachine.step q a = e.action :=
  TableMachine.step_of_transition?_eq_some h hwrite hnext

theorem toMachine_step_of_transition?_eq_none {P : TableProgram} {q a : Nat}
    (h : P.toTableMachine.transition? q a = none) :
    P.toMachine.step q a = (P.blank, P.halt, Move.right) :=
  TableMachine.step_of_transition?_eq_none h

theorem transition?_eq_some_of_table_head_matches {P : TableProgram}
    {e : TableTransition} {table : List TableTransition} {q a : Nat}
    (htable : P.table = e :: table) (hmatch : e.matchesInput q a = true) :
    P.toTableMachine.transition? q a = some e := by
  unfold TableMachine.transition?
  simp [TableProgram.toTableMachine, htable, hmatch]

theorem transition?_eq_tail_of_table_head_not_matches {P : TableProgram}
    {e : TableTransition} {table : List TableTransition} {q a : Nat}
    (htable : P.table = e :: table) (hmatch : e.matchesInput q a = false) :
    P.toTableMachine.transition? q a =
      table.find? fun e => e.matchesInput q a := by
  unfold TableMachine.transition?
  simp [TableProgram.toTableMachine, htable, hmatch]

theorem toMachine_nextID_of_transition?_eq_some {P : TableProgram} {c : ID}
    {e : TableTransition}
    (hstate : c.state ≠ P.halt)
    (hfind : P.toTableMachine.transition? c.state (c.tape c.head) = some e)
    (hwrite : e.write ∈ P.supportedSymbols) (hnext : e.next ∈ P.supportedStates) :
    P.toMachine.nextID c =
      { tape := fun i => if i = c.head then e.write else c.tape i
        head := e.move.apply c.head
        state := e.next } := by
  rw [Machine.nextID_of_ne_halt (M := P.toMachine) (by simpa using hstate)]
  simp [toMachine_step_of_transition?_eq_some hfind hwrite hnext,
    TableTransition.action]

theorem toMachine_runEmpty_one_of_initial_transition {P : TableProgram}
    {e : TableTransition}
    (hstart : P.start ≠ P.halt)
    (hfind : P.toTableMachine.transition? P.start P.blank = some e)
    (hwrite : e.write ∈ P.supportedSymbols) (hnext : e.next ∈ P.supportedStates) :
    P.toMachine.runEmpty 1 =
      { tape := fun i => if i = 0 then e.write else P.blank
        head := e.move.apply 0
        state := e.next } := by
  rw [Machine.runEmpty_succ, Machine.runEmpty_zero]
  simpa [Machine.initialID] using
    toMachine_nextID_of_transition?_eq_some
      (P := P) (c := P.toMachine.initialID) hstart hfind hwrite hnext

theorem toMachine_haltsEmpty_of_initial_transition_to_halt {P : TableProgram}
    {e : TableTransition}
    (hfind : P.toTableMachine.transition? P.start P.blank = some e)
    (hwrite : e.write ∈ P.supportedSymbols) (hnext : e.next ∈ P.supportedStates)
    (hhalt : e.next = P.halt) :
    P.toMachine.HaltsEmpty := by
  by_cases hstart : P.start = P.halt
  · exact ⟨0, by simp [Machine.initialID, hstart]⟩
  · refine ⟨1, ?_⟩
    rw [Machine.runEmpty_succ, Machine.runEmpty_zero]
    simp [Machine.nextID, Machine.initialID, hstart,
      toMachine_step_of_transition?_eq_some hfind hwrite hnext,
      TableTransition.action, hhalt]

theorem toMachine_runEmpty_eq_right_blank_loop {P : TableProgram} {e : TableTransition}
    (hstart : P.start ≠ P.halt)
    (hfind : P.toTableMachine.transition? P.start P.blank = some e)
    (hwrite : e.write ∈ P.supportedSymbols) (hnext : e.next ∈ P.supportedStates)
    (hloop : e.action = (P.blank, P.start, Move.right)) :
    ∀ n : Nat,
      P.toMachine.runEmpty n =
        { tape := fun _ => P.blank, head := n, state := P.start } := by
  apply Machine.runEmpty_eq_right_blank_loop
  · simpa using hstart
  · have hstep := toMachine_step_of_transition?_eq_some hfind hwrite hnext
    simpa [hloop] using hstep

theorem not_haltsEmpty_of_initial_right_blank_loop {P : TableProgram} {e : TableTransition}
    (hstart : P.start ≠ P.halt)
    (hfind : P.toTableMachine.transition? P.start P.blank = some e)
    (hwrite : e.write ∈ P.supportedSymbols) (hnext : e.next ∈ P.supportedStates)
    (hloop : e.action = (P.blank, P.start, Move.right)) :
    ¬ P.toMachine.HaltsEmpty :=
  Machine.not_haltsEmpty_of_right_blank_loop (by simpa using hstart) (by
    have hstep := toMachine_step_of_transition?_eq_some hfind hwrite hnext
    simpa [hloop] using hstep)

end TableProgram

instance instPrimcodableTableProgram : Primcodable TableProgram :=
  Primcodable.ofEquiv
    (List Nat × List Nat × Nat × Nat × Nat × List TableTransition)
    TableProgram.equivTuple

namespace Move

theorem toBool_primrec : Primrec Move.toBool := by
  simpa [Move.equivBool] using
    (Primrec.of_equiv (e := Move.equivBool) : Primrec Move.equivBool)

theorem ofBool_primrec : Primrec Move.ofBool := by
  simpa [Move.equivBool] using
    (Primrec.of_equiv_symm (e := Move.equivBool) : Primrec Move.equivBool.symm)

end Move

namespace TableProgram

theorem toTuple_primrec : Primrec TableProgram.toTuple := by
  simpa [TableProgram.equivTuple] using
    (Primrec.of_equiv (e := TableProgram.equivTuple) : Primrec TableProgram.equivTuple)

theorem ofTuple_primrec : Primrec TableProgram.ofTuple := by
  simpa [TableProgram.equivTuple] using
    (Primrec.of_equiv_symm (e := TableProgram.equivTuple) :
      Primrec TableProgram.equivTuple.symm)

theorem symbols_primrec : Primrec TableProgram.symbols :=
  Primrec.fst.comp toTuple_primrec

theorem states_primrec : Primrec TableProgram.states :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem blank_primrec : Primrec TableProgram.blank :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem start_primrec : Primrec TableProgram.start :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))

theorem halt_primrec : Primrec TableProgram.halt :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))))

theorem table_primrec : Primrec TableProgram.table :=
  Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))))

theorem mk_primrec :
    Primrec (fun p : List Nat × List Nat × Nat × Nat × Nat × List TableTransition =>
      ({ symbols := p.1
         states := p.2.1
         blank := p.2.2.1
         start := p.2.2.2.1
         halt := p.2.2.2.2.1
         table := p.2.2.2.2.2 } : TableProgram)) :=
  ofTuple_primrec

theorem supportedSymbols_primrec : Primrec TableProgram.supportedSymbols :=
  Primrec.list_cons.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))
    (Primrec.fst.comp toTuple_primrec)

theorem supportedStates_primrec : Primrec TableProgram.supportedStates := by
  unfold supportedStates
  exact Primrec.list_cons.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))))
    (Primrec.list_cons.comp
      (Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))))
      (Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)))

theorem supportedSymbols_computable : Computable TableProgram.supportedSymbols :=
  supportedSymbols_primrec.to_comp

theorem supportedStates_computable : Computable TableProgram.supportedStates :=
  supportedStates_primrec.to_comp

theorem transition?_primrec :
    Primrec (fun p : TableProgram × Nat × Nat =>
      p.1.toTableMachine.transition? p.2.1 p.2.2) := by
  unfold TableMachine.transition?
  exact TableTransition.find?_primrec.comp
    (Primrec.pair (table_primrec.comp Primrec.fst) Primrec.snd)

theorem transition?_computable :
    Computable (fun p : TableProgram × Nat × Nat =>
      p.1.toTableMachine.transition? p.2.1 p.2.2) :=
  transition?_primrec.to_comp

theorem nat_mem_list_primrecPred :
    PrimrecPred (fun p : List Nat × Nat => p.2 ∈ p.1) := by
  classical
  have hrel : PrimrecRel (fun x y : Nat => x = y) :=
    Primrec.eq
  exact (hrel.exists_mem_list.comp Primrec.fst Primrec.snd).of_eq fun p => by
    constructor
    · rintro ⟨x, hxmem, rfl⟩
      exact hxmem
    · intro hmem
      exact ⟨p.2, hmem, rfl⟩

theorem step_primrec :
    Primrec (fun p : TableProgram × Nat × Nat =>
      p.1.toTableMachine.step p.2.1 p.2.2) := by
  let fallback : TableProgram × Nat × Nat → Nat × Nat × Move := fun p =>
    (p.1.blank, p.1.halt, Move.right)
  have hfallback : Primrec fallback := by
    dsimp [fallback]
    exact Primrec.pair (blank_primrec.comp Primrec.fst)
      (Primrec.pair (halt_primrec.comp Primrec.fst) (Primrec.const Move.right))
  have hsome :
      Primrec₂ (fun p : TableProgram × Nat × Nat => fun e : TableTransition =>
        if e.write ∈ p.1.supportedSymbols then
          if e.next ∈ p.1.supportedStates then e.action else fallback p
        else fallback p) := by
    apply Primrec₂.mk
    have hwrite :
        PrimrecPred (fun p : (TableProgram × Nat × Nat) × TableTransition =>
          p.2.write ∈ p.1.1.supportedSymbols) :=
      nat_mem_list_primrecPred.comp
        (Primrec.pair (supportedSymbols_primrec.comp (Primrec.fst.comp Primrec.fst))
          (TableTransition.write_primrec.comp Primrec.snd))
    have hnext :
        PrimrecPred (fun p : (TableProgram × Nat × Nat) × TableTransition =>
          p.2.next ∈ p.1.1.supportedStates) :=
      nat_mem_list_primrecPred.comp
        (Primrec.pair (supportedStates_primrec.comp (Primrec.fst.comp Primrec.fst))
          (TableTransition.next_primrec.comp Primrec.snd))
    exact Primrec.ite hwrite
      (Primrec.ite hnext (TableTransition.action_primrec.comp Primrec.snd)
        (hfallback.comp Primrec.fst))
      (hfallback.comp Primrec.fst)
  exact (Primrec.option_casesOn transition?_primrec hfallback hsome).of_eq fun p => by
    unfold TableMachine.step fallback
    cases p.1.toTableMachine.transition? p.2.1 p.2.2 <;> rfl

theorem step_computable :
    Computable (fun p : TableProgram × Nat × Nat =>
      p.1.toTableMachine.step p.2.1 p.2.2) :=
  step_primrec.to_comp

end TableProgram

end LeanWang
