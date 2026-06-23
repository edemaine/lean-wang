/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Machine

/-!
Finite one-sided TM0-style machines.

This is deliberately closer to Mathlib's `TM0` than the older `TableProgram`
target: each transition either moves the head or writes one symbol, and halting
is represented by absence of a transition. The original Post-style names remain
for existing proofs; the preferred public name for the program type is
`FiniteTM0Program`.
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

instance instPrimcodable : Primcodable PostStmt :=
  Primcodable.ofEquiv (Move ⊕ Nat) PostStmt.equivSum

theorem toSum_primrec : Primrec PostStmt.toSum := by
  simpa [PostStmt.equivSum] using
    (Primrec.of_equiv (e := PostStmt.equivSum) : Primrec PostStmt.equivSum)

theorem ofSum_primrec : Primrec PostStmt.ofSum := by
  simpa [PostStmt.equivSum] using
    (Primrec.of_equiv_symm (e := PostStmt.equivSum) :
      Primrec PostStmt.equivSum.symm)

end PostStmt

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

instance instPrimcodable : Primcodable PostTransition :=
  Primcodable.ofEquiv (Nat × Nat × Nat × PostStmt) PostTransition.equivTuple

theorem toTuple_primrec : Primrec PostTransition.toTuple := by
  simpa [PostTransition.equivTuple] using
    (Primrec.of_equiv (e := PostTransition.equivTuple) :
      Primrec PostTransition.equivTuple)

theorem ofTuple_primrec : Primrec PostTransition.ofTuple := by
  simpa [PostTransition.equivTuple] using
    (Primrec.of_equiv_symm (e := PostTransition.equivTuple) :
      Primrec PostTransition.equivTuple.symm)

theorem state_primrec : Primrec PostTransition.state :=
  Primrec.fst.comp toTuple_primrec

theorem read_primrec : Primrec PostTransition.read :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem next_primrec : Primrec PostTransition.next :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem stmt_primrec : Primrec PostTransition.stmt :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem mk_primrec :
    Primrec (fun p : Nat × Nat × Nat × PostStmt =>
      ({ state := p.1
         read := p.2.1
         next := p.2.2.1
         stmt := p.2.2.2 } : PostTransition)) :=
  ofTuple_primrec

end PostTransition

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

instance instPrimcodable : Primcodable PostProgram :=
  Primcodable.ofEquiv
    (List Nat × List Nat × Nat × Nat × List PostTransition)
    PostProgram.equivTuple

theorem toTuple_primrec : Primrec PostProgram.toTuple := by
  simpa [PostProgram.equivTuple] using
    (Primrec.of_equiv (e := PostProgram.equivTuple) : Primrec PostProgram.equivTuple)

theorem ofTuple_primrec : Primrec PostProgram.ofTuple := by
  simpa [PostProgram.equivTuple] using
    (Primrec.of_equiv_symm (e := PostProgram.equivTuple) :
      Primrec PostProgram.equivTuple.symm)

theorem symbols_primrec : Primrec PostProgram.symbols :=
  Primrec.fst.comp toTuple_primrec

theorem states_primrec : Primrec PostProgram.states :=
  Primrec.fst.comp (Primrec.snd.comp toTuple_primrec)

theorem blank_primrec : Primrec PostProgram.blank :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec))

theorem start_primrec : Primrec PostProgram.start :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))

theorem table_primrec : Primrec PostProgram.table :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp toTuple_primrec)))

theorem mk_primrec :
    Primrec (fun p : List Nat × List Nat × Nat × Nat × List PostTransition =>
      ({ symbols := p.1
         states := p.2.1
         blank := p.2.2.1
         start := p.2.2.2.1
         table := p.2.2.2.2 } : PostProgram)) :=
  ofTuple_primrec

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
## Compatibility adapter to the current table-machine backend

The current Wang-tile layer consumes `TableProgram`, whose transitions always
write and move. A Post `move` command compiles to one table transition. A Post
`write` command compiles to two table transitions: write the symbol and move
right to an auxiliary state, then move left while restoring the symbol under the
head.
-/

/-- Encoded table state for a running Post state. -/
def tableRunState (q : Nat) : Nat :=
  2 * q + 1

/-- The running-state encoder is primitive recursive. -/
theorem tableRunState_primrec : Primrec tableRunState := by
  exact Primrec.nat_double_succ.of_eq fun q => by
    simp [tableRunState]

/-- Encoded table state used to return left after simulating a Post write. -/
def tableWriteState (q : Nat) : Nat :=
  2 * q + 2

/-- The write-return-state encoder is primitive recursive. -/
theorem tableWriteState_primrec : Primrec tableWriteState := by
  exact (Primrec.succ.comp Primrec.nat_double_succ).of_eq fun q => by
    simp [tableWriteState]

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

theorem tableRunState_injective : Function.Injective tableRunState := by
  intro q r h
  unfold tableRunState at h
  omega

theorem tableWriteState_injective : Function.Injective tableWriteState := by
  intro q r h
  unfold tableWriteState at h
  omega

/-- Explicit finite table alphabet: Post write symbols plus all transition read symbols. -/
def tableSymbols (P : PostProgram) : List Nat :=
  P.symbols ++ P.table.map PostTransition.read

/-- The explicit table alphabet generated from a Post program is primitive recursive. -/
theorem tableSymbols_primrec : Primrec tableSymbols := by
  unfold tableSymbols
  have hreads : Primrec (fun P : PostProgram => P.table.map PostTransition.read) := by
    refine Primrec.list_map table_primrec ?_
    apply Primrec₂.mk
    exact PostTransition.read_primrec.comp Primrec.snd
  exact Primrec.list_append.comp symbols_primrec hreads

/-- Supported symbols of the compiled table machine. -/
def tableSupportedSymbols (P : PostProgram) : List Nat :=
  P.blank :: P.tableSymbols

/-- The supported table-symbol list generated from a Post program is primitive recursive. -/
theorem tableSupportedSymbols_primrec : Primrec tableSupportedSymbols := by
  unfold tableSupportedSymbols
  exact Primrec.list_cons.comp blank_primrec tableSymbols_primrec

theorem blank_mem_tableSupportedSymbols (P : PostProgram) :
    P.blank ∈ tableSupportedSymbols P := by
  simp [tableSupportedSymbols]

theorem symbol_mem_tableSupportedSymbols {P : PostProgram} {a : Nat}
    (ha : a ∈ P.symbols) :
    a ∈ tableSupportedSymbols P := by
  simp [tableSupportedSymbols, tableSymbols, ha]

/-- Every cell of a Post/TM0 instantaneous description lies in the compiled table alphabet. -/
def TapeSupported (P : PostProgram) (c : PostID) : Prop :=
  ∀ i : Nat, c.tape i ∈ tableSupportedSymbols P

theorem initialID_tapeSupported (P : PostProgram) :
    TapeSupported P P.initialID := by
  intro i
  exact blank_mem_tableSupportedSymbols P

/-- A table transition that halts from the encoded running state of `e.state`. -/
def haltRow (P : PostProgram) (e : PostTransition) : TableTransition where
  state := tableRunState e.state
  read := e.read
  write := P.blank
  next := tableHalt
  move := Move.right

/-- The malformed-row halting row generator is primitive recursive. -/
theorem haltRow_primrec :
    Primrec (fun p : PostProgram × PostTransition => haltRow p.1 p.2) := by
  unfold haltRow
  exact TableTransition.mk_primrec.comp
    (Primrec.pair (tableRunState_primrec.comp (PostTransition.state_primrec.comp Primrec.snd))
      (Primrec.pair (PostTransition.read_primrec.comp Primrec.snd)
        (Primrec.pair (blank_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const tableHalt) (Primrec.const Move.right)))))

/-- Table row for a Post move command. -/
def moveRow (e : PostTransition) (m : Move) : TableTransition where
  state := tableRunState e.state
  read := e.read
  write := e.read
  next := tableRunState e.next
  move := m

/-- The table row generated by a Post move command is primitive recursive. -/
theorem moveRow_primrec :
    Primrec (fun p : PostTransition × Move => moveRow p.1 p.2) := by
  unfold moveRow
  exact TableTransition.mk_primrec.comp
    (Primrec.pair (tableRunState_primrec.comp (PostTransition.state_primrec.comp Primrec.fst))
      (Primrec.pair (PostTransition.read_primrec.comp Primrec.fst)
        (Primrec.pair (PostTransition.read_primrec.comp Primrec.fst)
          (Primrec.pair
            (tableRunState_primrec.comp (PostTransition.next_primrec.comp Primrec.fst))
            Primrec.snd))))

/-- First table row for a Post write command. -/
def writeStartRow (e : PostTransition) (b : Nat) : TableTransition where
  state := tableRunState e.state
  read := e.read
  write := b
  next := tableWriteState e.next
  move := Move.right

/-- The first table row generated by a Post write command is primitive recursive. -/
theorem writeStartRow_primrec :
    Primrec (fun p : PostTransition × Nat => writeStartRow p.1 p.2) := by
  unfold writeStartRow
  exact TableTransition.mk_primrec.comp
    (Primrec.pair (tableRunState_primrec.comp (PostTransition.state_primrec.comp Primrec.fst))
      (Primrec.pair (PostTransition.read_primrec.comp Primrec.fst)
        (Primrec.pair Primrec.snd
          (Primrec.pair
            (tableWriteState_primrec.comp (PostTransition.next_primrec.comp Primrec.fst))
            (Primrec.const Move.right)))))

@[simp]
theorem haltRow_matches_run (P : PostProgram) (e : PostTransition) (q a : Nat) :
    (haltRow P e).matchesInput (tableRunState q) a = e.matchesInput q a := by
  rcases e with ⟨state, read, next, stmt⟩
  by_cases hstate : state = q
  · subst q
    simp [haltRow, PostTransition.matchesInput, TableTransition.matchesInput]
  · have hrun : tableRunState state ≠ tableRunState q := fun h =>
      hstate (tableRunState_injective h)
    have hrunBool : (tableRunState state == tableRunState q) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hrun (beq_iff_eq.mp h)
    have hstateBool : (state == q) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hstate (beq_iff_eq.mp h)
    simp [haltRow, PostTransition.matchesInput, TableTransition.matchesInput,
      hrunBool, hstateBool]

@[simp]
theorem moveRow_matches_run (e : PostTransition) (m : Move) (q a : Nat) :
    (moveRow e m).matchesInput (tableRunState q) a = e.matchesInput q a := by
  rcases e with ⟨state, read, next, stmt⟩
  by_cases hstate : state = q
  · subst q
    simp [moveRow, PostTransition.matchesInput, TableTransition.matchesInput]
  · have hrun : tableRunState state ≠ tableRunState q := fun h =>
      hstate (tableRunState_injective h)
    have hrunBool : (tableRunState state == tableRunState q) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hrun (beq_iff_eq.mp h)
    have hstateBool : (state == q) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hstate (beq_iff_eq.mp h)
    simp [moveRow, PostTransition.matchesInput, TableTransition.matchesInput,
      hrunBool, hstateBool]

@[simp]
theorem writeStartRow_matches_run (e : PostTransition) (b q a : Nat) :
    (writeStartRow e b).matchesInput (tableRunState q) a = e.matchesInput q a := by
  rcases e with ⟨state, read, next, stmt⟩
  by_cases hstate : state = q
  · subst q
    simp [writeStartRow, PostTransition.matchesInput, TableTransition.matchesInput]
  · have hrun : tableRunState state ≠ tableRunState q := fun h =>
      hstate (tableRunState_injective h)
    have hrunBool : (tableRunState state == tableRunState q) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hrun (beq_iff_eq.mp h)
    have hstateBool : (state == q) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hstate (beq_iff_eq.mp h)
    simp [writeStartRow, PostTransition.matchesInput, TableTransition.matchesInput,
      hrunBool, hstateBool]

/-- Return-left rows used after a simulated Post write to next state `q`. -/
def writeReturnRow (q a : Nat) : TableTransition where
  state := tableWriteState q
  read := a
  write := a
  next := tableRunState q
  move := Move.left

/-- Return-left rows used after a simulated Post write to next state `q`. -/
def writeReturnRows (P : PostProgram) (q : Nat) : List TableTransition :=
  (tableSupportedSymbols P).map fun a => writeReturnRow q a

/-- The return-left rows generated after a Post write are primitive recursive. -/
theorem writeReturnRows_primrec :
    Primrec (fun p : PostProgram × Nat => writeReturnRows p.1 p.2) := by
  unfold writeReturnRows
  refine Primrec.list_map (tableSupportedSymbols_primrec.comp Primrec.fst) ?_
  apply Primrec₂.mk
  exact TableTransition.mk_primrec.comp
    (Primrec.pair (tableWriteState_primrec.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair Primrec.snd
        (Primrec.pair Primrec.snd
          (Primrec.pair (tableRunState_primrec.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.const Move.left)))))

@[simp]
theorem writeReturnRow_matches_self (q a : Nat) :
    (writeReturnRow q a).matchesInput (tableWriteState q) a = true := by
  simp [writeReturnRow, TableTransition.matchesInput]

theorem writeReturnRow_matches_run (q r a s : Nat) :
    (writeReturnRow r s).matchesInput (tableRunState q) a = false := by
  have hstate : tableWriteState r ≠ tableRunState q := by
    exact (tableRunState_ne_tableWriteState q r).symm
  simp [writeReturnRow, TableTransition.matchesInput, hstate]

theorem haltRow_matches_write (P : PostProgram) (e : PostTransition) (q a : Nat) :
    (haltRow P e).matchesInput (tableWriteState q) a = false := by
  rcases e with ⟨state, read, next, stmt⟩
  have hstate : tableRunState state ≠ tableWriteState q :=
    tableRunState_ne_tableWriteState state q
  simp [haltRow, TableTransition.matchesInput, hstate]

theorem moveRow_matches_write (e : PostTransition) (m : Move) (q a : Nat) :
    (moveRow e m).matchesInput (tableWriteState q) a = false := by
  rcases e with ⟨state, read, next, stmt⟩
  have hstate : tableRunState state ≠ tableWriteState q :=
    tableRunState_ne_tableWriteState state q
  simp [moveRow, TableTransition.matchesInput, hstate]

theorem writeStartRow_matches_write (e : PostTransition) (b q a : Nat) :
    (writeStartRow e b).matchesInput (tableWriteState q) a = false := by
  rcases e with ⟨state, read, next, stmt⟩
  have hstate : tableRunState state ≠ tableWriteState q :=
    tableRunState_ne_tableWriteState state q
  simp [writeStartRow, TableTransition.matchesInput, hstate]

theorem writeReturnRow_matchesInput_eq_true {q r a b : Nat}
    (h : (writeReturnRow r b).matchesInput (tableWriteState q) a = true) :
    r = q ∧ b = a := by
  have hparts :
      tableWriteState r = tableWriteState q ∧ b = a := by
    simpa [writeReturnRow, TableTransition.matchesInput] using h
  have hstate : tableWriteState r = tableWriteState q := hparts.1
  unfold tableWriteState at hstate
  have hrq : r = q := by omega
  exact ⟨hrq, hparts.2⟩

theorem writeReturnRow_action_of_matchesInput {q r a b : Nat}
    (h : (writeReturnRow r b).matchesInput (tableWriteState q) a = true) :
    (writeReturnRow r b).action = (a, tableRunState q, Move.left) := by
  rcases writeReturnRow_matchesInput_eq_true h with ⟨rfl, rfl⟩
  simp [writeReturnRow, TableTransition.action]

theorem writeReturnRows_find?_run (P : PostProgram) (q r a : Nat) :
    (writeReturnRows P r).find? (fun e => e.matchesInput (tableRunState q) a) = none := by
  unfold writeReturnRows
  induction tableSupportedSymbols P with
  | nil => rfl
  | cons s rest ih =>
      simp [writeReturnRow_matches_run q r a s, ih]

private theorem writeReturnRows_find?_write_aux (symbols : List Nat) {q a : Nat}
    (ha : a ∈ symbols) :
    (symbols.map (fun s => writeReturnRow q s)).find?
        (fun e => e.matchesInput (tableWriteState q) a) =
      some (writeReturnRow q a) := by
  induction symbols generalizing a with
  | nil =>
      cases ha
  | cons s rest ih =>
      have hcases : a = s ∨ a ∈ rest := by
        simpa using ha
      rcases hcases with has | haTail
      · subst a
        simp [writeReturnRow_matches_self]
      · by_cases hs : s = a
        · subst a
          simp [writeReturnRow_matches_self]
        · have hhead :
              (writeReturnRow q s).matchesInput (tableWriteState q) a = false := by
            simp [writeReturnRow, TableTransition.matchesInput, hs]
          simp [hhead, ih haTail]

theorem writeReturnRows_find?_write {P : PostProgram} {q a : Nat}
    (ha : a ∈ tableSupportedSymbols P) :
    (writeReturnRows P q).find? (fun e => e.matchesInput (tableWriteState q) a) =
      some (writeReturnRow q a) := by
  unfold writeReturnRows
  exact writeReturnRows_find?_write_aux (tableSupportedSymbols P) ha

theorem writeReturnRow_mem_writeReturnRows {P : PostProgram} {q a : Nat}
    (ha : a ∈ tableSupportedSymbols P) :
    writeReturnRow q a ∈ writeReturnRows P q := by
  unfold writeReturnRows
  exact List.mem_map_of_mem ha

theorem mem_writeReturnRows_matches_write_eq
    {P : PostProgram} {q r a : Nat} {row : TableTransition}
    (hmem : row ∈ writeReturnRows P r)
    (hmatch : row.matchesInput (tableWriteState q) a = true) :
    row = writeReturnRow q a := by
  rw [writeReturnRows, List.mem_map] at hmem
  rcases hmem with ⟨b, _hb, rfl⟩
  rcases writeReturnRow_matchesInput_eq_true hmatch with ⟨rfl, rfl⟩
  rfl

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
        [moveRow e m]
    | PostStmt.write b =>
        if b ∈ P.symbols then
          [writeStartRow e b] ++ writeReturnRows P e.next
        else
          [haltRow P e]
  else
    [haltRow P e]

/-- The first running-state table row generated by a Post transition. -/
def firstRowForTransition (P : PostProgram) (e : PostTransition) : TableTransition :=
  if e.next ∈ P.states then
    match e.stmt with
    | PostStmt.move m => moveRow e m
    | PostStmt.write b =>
        if b ∈ P.symbols then writeStartRow e b else haltRow P e
  else
    haltRow P e

/-- Rows generated by one Post transition are primitive recursive. -/
theorem rowsForTransition_primrec :
    Primrec (fun p : PostProgram × PostTransition => rowsForTransition p.1 p.2) := by
  unfold rowsForTransition
  let hhalt : Primrec (fun p : PostProgram × PostTransition => [haltRow p.1 p.2]) :=
    Primrec.list_cons.comp haltRow_primrec (Primrec.const ([] : List TableTransition))
  have hnext :
      PrimrecPred (fun p : PostProgram × PostTransition => p.2.next ∈ p.1.states) :=
    TableProgram.nat_mem_list_primrecPred.comp
      (Primrec.pair (states_primrec.comp Primrec.fst)
        (PostTransition.next_primrec.comp Primrec.snd))
  have hstmt :
      Primrec (fun p : PostProgram × PostTransition => PostStmt.toSum p.2.stmt) :=
    PostStmt.toSum_primrec.comp (PostTransition.stmt_primrec.comp Primrec.snd)
  have hcases :
      Primrec (fun p : PostProgram × PostTransition =>
        match p.2.stmt with
        | PostStmt.move m => [moveRow p.2 m]
        | PostStmt.write b =>
            if b ∈ p.1.symbols then
              [writeStartRow p.2 b] ++ writeReturnRows p.1 p.2.next
            else
              [haltRow p.1 p.2]) := by
    refine (Primrec.sumCasesOn
      (α := PostProgram × PostTransition) (β := Move) (γ := Nat)
      (σ := List TableTransition)
      (f := fun p : PostProgram × PostTransition => PostStmt.toSum p.2.stmt)
      (g := fun p m => [moveRow p.2 m])
      (h := fun p b =>
        if b ∈ p.1.symbols then
          [writeStartRow p.2 b] ++ writeReturnRows p.1 p.2.next
        else
          [haltRow p.1 p.2])
      hstmt ?_ ?_).of_eq ?_
    · apply Primrec₂.mk
      exact Primrec.list_cons.comp
        (moveRow_primrec.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
        (Primrec.const ([] : List TableTransition))
    · apply Primrec₂.mk
      have hsymbol :
          PrimrecPred (fun p : (PostProgram × PostTransition) × Nat =>
            p.2 ∈ p.1.1.symbols) :=
        TableProgram.nat_mem_list_primrecPred.comp
          (Primrec.pair (symbols_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      have hwriteStart :
          Primrec (fun p : (PostProgram × PostTransition) × Nat =>
            [writeStartRow p.1.2 p.2]) :=
        Primrec.list_cons.comp
          (writeStartRow_primrec.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
          (Primrec.const ([] : List TableTransition))
      have hreturns :
          Primrec (fun p : (PostProgram × PostTransition) × Nat =>
            writeReturnRows p.1.1 p.1.2.next) :=
        writeReturnRows_primrec.comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst)
            (PostTransition.next_primrec.comp (Primrec.snd.comp Primrec.fst)))
      have hgood :
          Primrec (fun p : (PostProgram × PostTransition) × Nat =>
            [writeStartRow p.1.2 p.2] ++ writeReturnRows p.1.1 p.1.2.next) :=
        Primrec.list_append.comp hwriteStart hreturns
      have hbad : Primrec (fun p : (PostProgram × PostTransition) × Nat =>
            [haltRow p.1.1 p.1.2]) :=
        Primrec.list_cons.comp
          (haltRow_primrec.comp
            (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))
          (Primrec.const ([] : List TableTransition))
      exact Primrec.ite hsymbol hgood hbad
    · intro p
      cases p.2.stmt <;> rfl
  exact (Primrec.ite hnext hcases hhalt).of_eq fun p => by
    rcases p with ⟨P, e⟩
    cases e.stmt <;> by_cases h : e.next ∈ P.states <;> simp [h]

@[simp]
theorem firstRowForTransition_matches_run
    (P : PostProgram) (e : PostTransition) (q a : Nat) :
    (firstRowForTransition P e).matchesInput (tableRunState q) a =
      e.matchesInput q a := by
  unfold firstRowForTransition
  by_cases hnext : e.next ∈ P.states
  · rcases e with ⟨state, read, next, stmt⟩
    cases stmt with
    | move m =>
        simp [hnext]
    | write b =>
        by_cases hb : b ∈ P.symbols <;> simp [hnext, hb]
  · simp [hnext]

theorem rowsForTransition_find?_run_of_matches {P : PostProgram} {e : PostTransition}
    {q a : Nat} (h : e.matchesInput q a = true) :
    (rowsForTransition P e).find? (fun r => r.matchesInput (tableRunState q) a) =
      some (firstRowForTransition P e) := by
  unfold rowsForTransition firstRowForTransition
  by_cases hnext : e.next ∈ P.states
  · cases e.stmt with
    | move m =>
        simp [hnext, h]
    | write b =>
        by_cases hb : b ∈ P.symbols
        · simp [hnext, hb, h]
        · simp [hnext, hb, h]
  · simp [hnext, h]

theorem rowsForTransition_find?_run_of_not_matches {P : PostProgram} {e : PostTransition}
    {q a : Nat} (h : e.matchesInput q a = false) :
    (rowsForTransition P e).find? (fun r => r.matchesInput (tableRunState q) a) = none := by
  unfold rowsForTransition
  by_cases hnext : e.next ∈ P.states
  · cases e.stmt with
    | move m =>
        simp [hnext, h]
    | write b =>
        by_cases hb : b ∈ P.symbols
        · simp [hnext, hb, h, writeReturnRows_find?_run]
        · simp [hnext, hb, h]
  · simp [hnext, h]

/-- Full table row list generated from a Post program. -/
def tableRows (P : PostProgram) : List TableTransition :=
  P.table.flatMap (rowsForTransition P)

private theorem find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hp : p x = true
      · have hx : x = a := by
          simpa [hp] using h
        subst a
        simp [hp]
      · have htail : xs.find? p = some a := by
          simpa [hp] using h
        simp [hp, htail]

private theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      by_cases hp : p x = true
      · simp [hp] at h
      · have htail : xs.find? p = none := by
          simpa [hp] using h
        simpa [hp] using ih htail

private theorem find?_flatMap_rowsForTransition_of_find?_eq_some
    (P : PostProgram) (rows : List PostTransition) {q a : Nat} {e : PostTransition}
    (h : rows.find? (fun row => row.matchesInput q a) = some e) :
    (rows.flatMap (rowsForTransition P)).find?
        (fun r => r.matchesInput (tableRunState q) a) =
      some (firstRowForTransition P e) := by
  induction rows with
  | nil =>
      simp at h
  | cons row rows ih =>
      by_cases hrow : row.matchesInput q a = true
      · have heq : row = e := by
          simpa [hrow] using h
        subst e
        rw [List.flatMap_cons]
        exact find?_append_of_eq_some (rowsForTransition_find?_run_of_matches hrow)
      · have hrowFalse : row.matchesInput q a = false := Bool.eq_false_iff.2 hrow
        have htail : rows.find? (fun row => row.matchesInput q a) = some e := by
          simpa [hrowFalse] using h
        rw [List.flatMap_cons]
        rw [find?_append_of_eq_none (rowsForTransition_find?_run_of_not_matches hrowFalse)]
        exact ih htail

private theorem find?_flatMap_rowsForTransition_eq_none_of_find?_eq_none
    (P : PostProgram) (rows : List PostTransition) {q a : Nat}
    (h : rows.find? (fun row => row.matchesInput q a) = none) :
    (rows.flatMap (rowsForTransition P)).find?
        (fun r => r.matchesInput (tableRunState q) a) = none := by
  induction rows with
  | nil =>
      rfl
  | cons row rows ih =>
      by_cases hrow : row.matchesInput q a = true
      · simp [hrow] at h
      · have hrowFalse : row.matchesInput q a = false := Bool.eq_false_iff.2 hrow
        have htail : rows.find? (fun row => row.matchesInput q a) = none := by
          simpa [hrowFalse] using h
        rw [List.flatMap_cons]
        rw [find?_append_of_eq_none (rowsForTransition_find?_run_of_not_matches hrowFalse)]
        exact ih htail

theorem tableRows_find?_run_of_transition?_eq_some {P : PostProgram} {q a : Nat}
    {e : PostTransition} (h : P.transition? q a = some e) :
    (tableRows P).find? (fun r => r.matchesInput (tableRunState q) a) =
      some (firstRowForTransition P e) := by
  unfold transition? at h
  unfold tableRows
  exact find?_flatMap_rowsForTransition_of_find?_eq_some P P.table h

theorem tableRows_find?_run_eq_none_of_transition?_eq_none {P : PostProgram} {q a : Nat}
    (h : P.transition? q a = none) :
    (tableRows P).find? (fun r => r.matchesInput (tableRunState q) a) = none := by
  unfold transition? at h
  unfold tableRows
  exact find?_flatMap_rowsForTransition_eq_none_of_find?_eq_none P P.table h

theorem writeReturnRow_mem_rowsForTransition_of_write
    {P : PostProgram} {e : PostTransition} {b a : Nat}
    (hnext : e.next ∈ P.states) (hstmt : e.stmt = PostStmt.write b)
    (hb : b ∈ P.symbols) (ha : a ∈ tableSupportedSymbols P) :
    writeReturnRow e.next a ∈ rowsForTransition P e := by
  unfold rowsForTransition
  rw [hstmt]
  simp [hnext, hb, writeReturnRow_mem_writeReturnRows ha]

set_option linter.flexible false in
theorem mem_rowsForTransition_matches_write_eq
    {P : PostProgram} {e : PostTransition} {q a : Nat} {row : TableTransition}
    (hmem : row ∈ rowsForTransition P e)
    (hmatch : row.matchesInput (tableWriteState q) a = true) :
    row = writeReturnRow q a := by
  unfold rowsForTransition at hmem
  by_cases hnext : e.next ∈ P.states
  · cases hstmt : e.stmt with
    | move m =>
        simp [hnext, hstmt] at hmem
        rcases hmem with rfl
        simp [moveRow_matches_write] at hmatch
    | write b =>
        by_cases hb : b ∈ P.symbols
        · simp [hnext, hstmt, hb] at hmem
          rcases hmem with rfl | hret
          · simp [writeStartRow_matches_write] at hmatch
          · exact mem_writeReturnRows_matches_write_eq hret hmatch
        · simp [hnext, hstmt, hb] at hmem
          rcases hmem with rfl
          simp [haltRow_matches_write] at hmatch
  · simp [hnext] at hmem
    rcases hmem with rfl
    simp [haltRow_matches_write] at hmatch

theorem mem_tableRows_matches_write_eq
    {P : PostProgram} {q a : Nat} {row : TableTransition}
    (hmem : row ∈ tableRows P)
    (hmatch : row.matchesInput (tableWriteState q) a = true) :
    row = writeReturnRow q a := by
  rw [tableRows, List.mem_flatMap] at hmem
  rcases hmem with ⟨e, _he, hrow⟩
  exact mem_rowsForTransition_matches_write_eq hrow hmatch

/-- The full table row list generated from a Post program is primitive recursive. -/
theorem tableRows_primrec : Primrec tableRows := by
  unfold tableRows
  refine Primrec.list_flatMap table_primrec ?_
  apply Primrec₂.mk
  exact rowsForTransition_primrec.comp (Primrec.pair Primrec.fst Primrec.snd)

/-- Table support states generated from rows, including both sources and targets. -/
def tableStates (P : PostProgram) : List Nat :=
  (P.tableRows.map TableTransition.state) ++
    (P.tableRows.map TableTransition.next)

/-- The table support-state list generated from a Post program is primitive recursive. -/
theorem tableStates_primrec : Primrec tableStates := by
  unfold tableStates
  have hrowStates : Primrec (fun P : PostProgram => P.tableRows.map TableTransition.state) := by
    refine Primrec.list_map tableRows_primrec ?_
    apply Primrec₂.mk
    exact TableTransition.state_primrec.comp Primrec.snd
  have hrowNexts : Primrec (fun P : PostProgram => P.tableRows.map TableTransition.next) := by
    refine Primrec.list_map tableRows_primrec ?_
    apply Primrec₂.mk
    exact TableTransition.next_primrec.comp Primrec.snd
  exact Primrec.list_append.comp hrowStates hrowNexts

/--
Reduce a one-sided Post/TM0 program to the older always-write-and-move table
model consumed by the current Wang-tile layer.
-/
def toTableProgram (P : PostProgram) : TableProgram where
  symbols := P.tableSymbols
  states := tableStates P
  blank := P.blank
  start := tableRunState P.start
  halt := tableHalt
  table := tableRows P

/-- The finite-TM0-to-table data compiler is primitive recursive. -/
theorem toTableProgram_primrec : Primrec toTableProgram := by
  unfold toTableProgram
  exact TableProgram.mk_primrec.comp
    (Primrec.pair tableSymbols_primrec
      (Primrec.pair tableStates_primrec
        (Primrec.pair blank_primrec
          (Primrec.pair (tableRunState_primrec.comp start_primrec)
            (Primrec.pair (Primrec.const tableHalt) tableRows_primrec)))))

/-- The finite-TM0-to-table data compiler is computable. -/
theorem toTableProgram_computable : Computable toTableProgram :=
  toTableProgram_primrec.to_comp

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
          · simp [writeStartRow, tableSupportedSymbols, tableSymbols, hb]
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

private theorem find?_eq_some_mem {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) :
    a ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa : x = a := by
          simpa [hx] using h
        simp [hxa]
      · have hxFalse : p x = false := Bool.eq_false_iff.2 hx
        have htail : xs.find? p = some a := by
          simpa [hxFalse] using h
        exact List.mem_cons_of_mem x (ih htail)

private theorem find?_eq_some_pred {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) :
    p a = true := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa : x = a := by
          simpa [hx] using h
        simpa [← hxa] using hx
      · have hxFalse : p x = false := Bool.eq_false_iff.2 hx
        have htail : xs.find? p = some a := by
          simpa [hxFalse] using h
        exact ih htail

private theorem find?_eq_some_of_mem_unique {α : Type} {xs : List α} {p : α → Bool}
    {a : α} (hmem : a ∈ xs) (hpred : p a = true)
    (huniq : ∀ b, b ∈ xs → p b = true → b = a) :
    xs.find? p = some a := by
  induction xs with
  | nil =>
      cases hmem
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa : x = a := huniq x (by simp) hx
        subst x
        simp [hpred]
      · have hxFalse : p x = false := Bool.eq_false_iff.2 hx
        have hmemTail : a ∈ xs := by
          have hcases : a = x ∨ a ∈ xs := by
            simpa using hmem
          rcases hcases with hax | htail
          · subst a
            exact False.elim (hx hpred)
          · exact htail
        have huniqTail : ∀ b, b ∈ xs → p b = true → b = a := by
          intro b hb hpb
          exact huniq b (List.mem_cons_of_mem x hb) hpb
        simpa [hxFalse] using ih hmemTail huniqTail

theorem transition?_eq_some_mem {P : PostProgram} {q a : Nat} {e : PostTransition}
    (h : P.transition? q a = some e) :
    e ∈ P.table := by
  unfold transition? at h
  exact find?_eq_some_mem h

theorem transition?_eq_some_matchesInput {P : PostProgram} {q a : Nat} {e : PostTransition}
    (h : P.transition? q a = some e) :
    e.matchesInput q a = true := by
  unfold transition? at h
  exact find?_eq_some_pred (xs := P.table) (p := fun e => e.matchesInput q a) h

theorem toTableProgram_transition?_run_of_transition?_eq_some
    {P : PostProgram} {q a : Nat} {e : PostTransition}
    (h : P.transition? q a = some e) :
    P.toTableProgram.toTableMachine.transition? (tableRunState q) a =
      some (firstRowForTransition P e) := by
  unfold TableMachine.transition?
  simp [TableProgram.toTableMachine, toTableProgram,
    tableRows_find?_run_of_transition?_eq_some h]

theorem toTableProgram_transition?_run_eq_none_of_transition?_eq_none
    {P : PostProgram} {q a : Nat}
    (h : P.transition? q a = none) :
    P.toTableProgram.toTableMachine.transition? (tableRunState q) a = none := by
  unfold TableMachine.transition?
  simp [TableProgram.toTableMachine, toTableProgram,
    tableRows_find?_run_eq_none_of_transition?_eq_none h]

theorem firstRowForTransition_mem_rowsForTransition
    (P : PostProgram) (e : PostTransition) :
    firstRowForTransition P e ∈ rowsForTransition P e := by
  rcases e with ⟨state, read, next, stmt⟩
  unfold firstRowForTransition rowsForTransition
  by_cases hnext : next ∈ P.states
  · cases stmt with
    | move m =>
        simp [hnext]
    | write b =>
        by_cases hb : b ∈ P.symbols <;> simp [hnext, hb]
  · simp [hnext]

theorem firstRowForTransition_mem_tableRows {P : PostProgram} {e : PostTransition}
    (hmem : e ∈ P.table) :
    firstRowForTransition P e ∈ tableRows P := by
  unfold tableRows
  rw [List.mem_flatMap]
  exact ⟨e, hmem, firstRowForTransition_mem_rowsForTransition P e⟩

theorem firstRowForTransition_write_mem_supportedSymbols
    {P : PostProgram} {e : PostTransition} (hmem : e ∈ P.table) :
    (firstRowForTransition P e).write ∈ P.toTableProgram.supportedSymbols := by
  exact row_write_mem_toTableProgram_supportedSymbols
    (firstRowForTransition_mem_tableRows hmem)

theorem firstRowForTransition_next_mem_supportedStates
    {P : PostProgram} {e : PostTransition} (hmem : e ∈ P.table) :
    (firstRowForTransition P e).next ∈ P.toTableProgram.supportedStates := by
  exact row_next_mem_toTableProgram_supportedStates
    (firstRowForTransition_mem_tableRows hmem)

theorem toTableProgram_step_run (P : PostProgram) (q a : Nat) :
    P.toTableProgram.toTableMachine.step (tableRunState q) a =
      match P.step q a with
      | none => (P.blank, tableHalt, Move.right)
      | some (q', PostStmt.move m) => (a, tableRunState q', m)
      | some (q', PostStmt.write b) => (b, tableWriteState q', Move.right) := by
  cases h : P.transition? q a with
  | none =>
      have hfind := toTableProgram_transition?_run_eq_none_of_transition?_eq_none h
      have hstep := TableMachine.step_of_transition?_eq_none (M := P.toTableProgram.toTableMachine)
        (q := tableRunState q) (a := a) hfind
      rw [hstep]
      simp [PostProgram.step, h, TableProgram.toTableMachine, toTableProgram, tableHalt]
  | some e =>
      have hmatch := transition?_eq_some_matchesInput h
      have hfind := toTableProgram_transition?_run_of_transition?_eq_some h
      have hmem : e ∈ P.table := transition?_eq_some_mem h
      have hwrite := firstRowForTransition_write_mem_supportedSymbols hmem
      have hnext := firstRowForTransition_next_mem_supportedStates hmem
      have hstep := TableMachine.step_of_transition?_eq_some
        (M := P.toTableProgram.toTableMachine) hfind hwrite hnext
      rcases e with ⟨state, read, next, stmt⟩
      have hstateRead : state = q ∧ read = a := by
        simpa [PostTransition.matchesInput] using hmatch
      by_cases hnextPost : next ∈ P.states
      · cases stmt with
        | move m =>
            rw [hstep]
            simp [PostProgram.step, h, hnextPost, firstRowForTransition, moveRow,
              TableTransition.action, hstateRead.2]
        | write b =>
            by_cases hb : b ∈ P.symbols
            · rw [hstep]
              simp [PostProgram.step, h, hnextPost, hb, firstRowForTransition,
                writeStartRow, TableTransition.action]
            · rw [hstep]
              simp [PostProgram.step, h, hnextPost, hb, firstRowForTransition,
                haltRow, TableTransition.action, tableHalt]
      · rw [hstep]
        simp [PostProgram.step, h, hnextPost, firstRowForTransition, haltRow,
          TableTransition.action, tableHalt]

/-- Encode a finite-TM0 instantaneous description as a table-machine ID. -/
def tableIDOfPostID (c : PostID) : ID where
  tape := c.tape
  head := c.head
  state :=
    match c.state with
    | none => tableHalt
    | some q => tableRunState q

@[simp]
theorem tableIDOfPostID_state_halt {c : PostID} (h : c.state = none) :
    (tableIDOfPostID c).state = tableHalt := by
  cases c with
  | mk tape head state =>
    cases state <;> simp [tableIDOfPostID] at h ⊢

@[simp]
theorem tableIDOfPostID_state_running {c : PostID} {q : Nat} (h : c.state = some q) :
    (tableIDOfPostID c).state = tableRunState q := by
  cases c with
  | mk tape head state =>
    cases h
    simp [tableIDOfPostID]

@[simp]
theorem tableIDOfPostID_head (c : PostID) :
    (tableIDOfPostID c).head = c.head := rfl

@[simp]
theorem tableIDOfPostID_tape (c : PostID) :
    (tableIDOfPostID c).tape = c.tape := rfl

theorem toTableProgram_toMachine_nextID_of_post_halt (P : PostProgram) (c : PostID)
    (h : c.state = none) :
    P.toTableProgram.toMachine.nextID (tableIDOfPostID c) = tableIDOfPostID c := by
  apply Machine.nextID_of_halt
  simp [tableIDOfPostID_state_halt h, toTableProgram_halt]

theorem toTableProgram_toMachine_nextID_of_post_step_none
    {P : PostProgram} {c : PostID} {q : Nat}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = none) :
    P.toTableProgram.toMachine.nextID (tableIDOfPostID c) =
      { tape := Function.update c.tape c.head P.blank
        head := c.head + 1
        state := tableHalt } := by
  have hnotHalt : (tableIDOfPostID c).state ≠ P.toTableProgram.halt := by
    simp [tableIDOfPostID_state_running hstate, toTableProgram_halt,
      (tableHalt_ne_tableRunState q).symm]
  rw [Machine.nextID_of_ne_halt (M := P.toTableProgram.toMachine) hnotHalt]
  have htableStep := toTableProgram_step_run P q (c.tape c.head)
  have hmachineStep :
      P.toTableProgram.toMachine.step (tableRunState q) (c.tape c.head) =
        (P.blank, tableHalt, Move.right) := by
    rw [TableProgram.toMachine_step]
    rw [htableStep, hstep]
  change P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head) =
    (P.blank, tableHalt, Move.right) at hmachineStep
  change
    (match P.toTableProgram.toMachine.step (tableIDOfPostID c).state
        ((tableIDOfPostID c).tape (tableIDOfPostID c).head) with
      | (write, state', move) =>
          (⟨(fun i => if i = (tableIDOfPostID c).head then write
              else (tableIDOfPostID c).tape i), move.apply c.head, state'⟩ : ID)) =
      { tape := Function.update c.tape c.head P.blank
        head := c.head + 1
        state := tableHalt }
  rw [tableIDOfPostID_state_running hstate]
  simp only [tableIDOfPostID_head, tableIDOfPostID_tape]
  have hwrite :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).1 = P.blank := by
    simpa using congrArg Prod.fst hmachineStep
  have hstate' :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).2.1 = tableHalt := by
    simpa using congrArg (fun x : Nat × Nat × Move => x.2.1) hmachineStep
  have hmove :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).2.2 = Move.right := by
    simpa using congrArg (fun x : Nat × Nat × Move => x.2.2) hmachineStep
  ext i <;> simp [Function.update, Move.apply, hwrite, hstate', hmove]

theorem toTableProgram_toMachine_nextID_of_post_move
    {P : PostProgram} {c : PostID} {q q' : Nat} {m : Move}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', PostStmt.move m)) :
    P.toTableProgram.toMachine.nextID (tableIDOfPostID c) =
      tableIDOfPostID
        { tape := c.tape
          head := m.apply c.head
          state := some q' } := by
  have hnotHalt : (tableIDOfPostID c).state ≠ P.toTableProgram.halt := by
    simp [tableIDOfPostID_state_running hstate, toTableProgram_halt,
      (tableHalt_ne_tableRunState q).symm]
  rw [Machine.nextID_of_ne_halt (M := P.toTableProgram.toMachine) hnotHalt]
  have htableStep := toTableProgram_step_run P q (c.tape c.head)
  have hmachineStep :
      P.toTableProgram.toMachine.step (tableRunState q) (c.tape c.head) =
        (c.tape c.head, tableRunState q', m) := by
    rw [TableProgram.toMachine_step]
    rw [htableStep, hstep]
  change P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head) =
    (c.tape c.head, tableRunState q', m) at hmachineStep
  change
    (match P.toTableProgram.toMachine.step (tableIDOfPostID c).state
        ((tableIDOfPostID c).tape (tableIDOfPostID c).head) with
      | (write, state', move) =>
          (⟨(fun i => if i = (tableIDOfPostID c).head then write
              else (tableIDOfPostID c).tape i),
            move.apply (tableIDOfPostID c).head, state'⟩ : ID)) =
      tableIDOfPostID
        { tape := c.tape
          head := m.apply c.head
          state := some q' }
  rw [tableIDOfPostID_state_running hstate]
  simp only [tableIDOfPostID_head, tableIDOfPostID_tape]
  have hwrite :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).1 = c.tape c.head := by
    simpa using congrArg Prod.fst hmachineStep
  have hstate' :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).2.1 =
        tableRunState q' := by
    simpa using congrArg (fun x : Nat × Nat × Move => x.2.1) hmachineStep
  have hmove :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).2.2 = m := by
    simpa using congrArg (fun x : Nat × Nat × Move => x.2.2) hmachineStep
  ext i
  · by_cases hi : i = c.head <;> simp [tableIDOfPostID, hi, hwrite]
  · simp [tableIDOfPostID, hmove]
  · simp [tableIDOfPostID, hstate']

theorem toTableProgram_toMachine_nextID_of_post_write_start
    {P : PostProgram} {c : PostID} {q q' b : Nat}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', PostStmt.write b)) :
    P.toTableProgram.toMachine.nextID (tableIDOfPostID c) =
      { tape := Function.update c.tape c.head b
        head := c.head + 1
        state := tableWriteState q' } := by
  have hnotHalt : (tableIDOfPostID c).state ≠ P.toTableProgram.halt := by
    simp [tableIDOfPostID_state_running hstate, toTableProgram_halt,
      (tableHalt_ne_tableRunState q).symm]
  rw [Machine.nextID_of_ne_halt (M := P.toTableProgram.toMachine) hnotHalt]
  have htableStep := toTableProgram_step_run P q (c.tape c.head)
  have hmachineStep :
      P.toTableProgram.toMachine.step (tableRunState q) (c.tape c.head) =
        (b, tableWriteState q', Move.right) := by
    rw [TableProgram.toMachine_step]
    rw [htableStep, hstep]
  change P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head) =
    (b, tableWriteState q', Move.right) at hmachineStep
  change
    (match P.toTableProgram.toMachine.step (tableIDOfPostID c).state
        ((tableIDOfPostID c).tape (tableIDOfPostID c).head) with
      | (write, state', move) =>
          (⟨(fun i => if i = (tableIDOfPostID c).head then write
              else (tableIDOfPostID c).tape i),
            move.apply (tableIDOfPostID c).head, state'⟩ : ID)) =
      { tape := Function.update c.tape c.head b
        head := c.head + 1
        state := tableWriteState q' }
  rw [tableIDOfPostID_state_running hstate]
  simp only [tableIDOfPostID_head, tableIDOfPostID_tape]
  have hwrite :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).1 = b := by
    simpa using congrArg Prod.fst hmachineStep
  have hstate' :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).2.1 =
        tableWriteState q' := by
    simpa using congrArg (fun x : Nat × Nat × Move => x.2.1) hmachineStep
  have hmove :
      (P.toTableProgram.toMachine.6 (tableRunState q) (c.tape c.head)).2.2 = Move.right := by
    simpa using congrArg (fun x : Nat × Nat × Move => x.2.2) hmachineStep
  ext i <;> simp [Function.update, Move.apply, hwrite, hstate', hmove]

theorem step_eq_some_write_exists_transition {P : PostProgram} {q a q' b : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b)) :
    ∃ e : PostTransition,
      P.transition? q a = some e ∧
        e.next = q' ∧ e.stmt = PostStmt.write b ∧
        e.next ∈ P.states ∧ b ∈ P.symbols := by
  unfold PostProgram.step at hstep
  cases hfind : P.transition? q a with
  | none =>
      simp [hfind] at hstep
  | some e =>
      by_cases hnext : e.next ∈ P.states
      · cases hstmt : e.stmt with
        | move m =>
            simp [hfind, hnext, hstmt] at hstep
        | write b' =>
            by_cases hb : b' ∈ P.symbols
            · have hpair : (e.next, PostStmt.write b') = (q', PostStmt.write b) := by
                simpa [hfind, hnext, hstmt, hb] using hstep
              rcases hpair with ⟨rfl, rfl⟩
              exact ⟨e, by simp, rfl, hstmt, hnext, hb⟩
            · simp [hfind, hnext, hstmt, hb] at hstep
      · simp [hfind, hnext] at hstep

theorem symbol_mem_of_step_eq_some_write {P : PostProgram} {q a q' b : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b)) :
    b ∈ P.symbols := by
  rcases step_eq_some_write_exists_transition hstep with
    ⟨_e, _hfind, _hnext, _hstmt, _hstate, hb⟩
  exact hb

theorem tapeSupported_update {P : PostProgram} {tape : Nat → Nat} {head b : Nat}
    (hsupp : ∀ i : Nat, tape i ∈ tableSupportedSymbols P)
    (hb : b ∈ tableSupportedSymbols P) :
    ∀ i : Nat, (Function.update tape head b) i ∈ tableSupportedSymbols P := by
  intro i
  by_cases hi : i = head
  · simp [Function.update, hi, hb]
  · simp [Function.update, hi, hsupp i]

theorem tapeSupported_nextID {P : PostProgram} {c : PostID}
    (hsupp : TapeSupported P c) :
    TapeSupported P (P.nextID c) := by
  intro i
  cases hstate : c.state with
  | none =>
      simpa [PostProgram.nextID, hstate] using hsupp i
  | some q =>
      rw [nextID_of_running hstate]
      cases hstep : P.step q (c.tape c.head) with
      | none =>
          simpa [hstep] using hsupp i
      | some step =>
          rcases step with ⟨q', stmt⟩
          cases stmt with
          | move m =>
              simpa [hstep, applyStmt] using hsupp i
          | write b =>
              have hb : b ∈ tableSupportedSymbols P :=
                symbol_mem_tableSupportedSymbols (symbol_mem_of_step_eq_some_write hstep)
              exact tapeSupported_update hsupp hb i

theorem runEmpty_tapeSupported (P : PostProgram) (n : Nat) :
    TapeSupported P (P.runEmpty n) := by
  induction n with
  | zero =>
      simpa using initialID_tapeSupported P
  | succ n ih =>
      rw [runEmpty_succ]
      exact tapeSupported_nextID ih

theorem writeReturnRow_mem_tableRows_of_post_write
    {P : PostProgram} {q a q' b ret : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b))
    (hret : ret ∈ tableSupportedSymbols P) :
    writeReturnRow q' ret ∈ tableRows P := by
  rcases step_eq_some_write_exists_transition hstep with
    ⟨e, hfind, hnext, hstmt, hstate, hb⟩
  have hmem : e ∈ P.table := transition?_eq_some_mem hfind
  have hrow : writeReturnRow e.next ret ∈ rowsForTransition P e :=
    writeReturnRow_mem_rowsForTransition_of_write hstate hstmt hb hret
  unfold tableRows
  rw [List.mem_flatMap]
  exact ⟨e, hmem, by simpa [hnext] using hrow⟩

theorem tableRows_find?_write_of_post_write
    {P : PostProgram} {q a q' b ret : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b))
    (hret : ret ∈ tableSupportedSymbols P) :
    (tableRows P).find? (fun row => row.matchesInput (tableWriteState q') ret) =
      some (writeReturnRow q' ret) := by
  have hmem := writeReturnRow_mem_tableRows_of_post_write hstep hret
  exact find?_eq_some_of_mem_unique hmem (writeReturnRow_matches_self q' ret)
    (fun row hrow hmatch => mem_tableRows_matches_write_eq hrow hmatch)

theorem toTableProgram_transition?_write_of_post_write
    {P : PostProgram} {q a q' b ret : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b))
    (hret : ret ∈ tableSupportedSymbols P) :
    P.toTableProgram.toTableMachine.transition? (tableWriteState q') ret =
      some (writeReturnRow q' ret) := by
  unfold TableMachine.transition?
  simpa [TableProgram.toTableMachine, toTableProgram] using
    tableRows_find?_write_of_post_write hstep hret

theorem toTableProgram_step_writeReturn_of_post_write
    {P : PostProgram} {q a q' b ret : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b))
    (hret : ret ∈ tableSupportedSymbols P) :
    P.toTableProgram.toTableMachine.step (tableWriteState q') ret =
      (ret, tableRunState q', Move.left) := by
  have hfind := toTableProgram_transition?_write_of_post_write hstep hret
  have hmem := writeReturnRow_mem_tableRows_of_post_write hstep hret
  have hwrite := row_write_mem_toTableProgram_supportedSymbols hmem
  have hnext := row_next_mem_toTableProgram_supportedStates hmem
  have hstepTable := TableMachine.step_of_transition?_eq_some
    (M := P.toTableProgram.toTableMachine) hfind hwrite hnext
  rw [hstepTable]
  simp [writeReturnRow, TableTransition.action]

theorem toTableProgram_toMachine_nextID_of_post_write_return
    {P : PostProgram} {tape : Nat → Nat} {head q q' a b : Nat}
    (hstep : P.step q a = some (q', PostStmt.write b))
    (hret : tape (head + 1) ∈ tableSupportedSymbols P) :
    P.toTableProgram.toMachine.nextID
        { tape := tape, head := head + 1, state := tableWriteState q' } =
      { tape := tape, head := head, state := tableRunState q' } := by
  let c : ID := { tape := tape, head := head + 1, state := tableWriteState q' }
  have hnotHalt : c.state ≠ P.toTableProgram.halt := by
    simp [c, toTableProgram_halt, (tableHalt_ne_tableWriteState q').symm]
  rw [Machine.nextID_of_ne_halt (M := P.toTableProgram.toMachine) (c := c) hnotHalt]
  have hmachineStep :
      P.toTableProgram.toMachine.step (tableWriteState q') (tape (head + 1)) =
        (tape (head + 1), tableRunState q', Move.left) := by
    rw [TableProgram.toMachine_step]
    exact toTableProgram_step_writeReturn_of_post_write hstep hret
  change
    (match P.toTableProgram.toMachine.step (tableWriteState q') (tape (head + 1)) with
      | (write, state', move) =>
          (⟨(fun i => if i = head + 1 then write else tape i),
            move.apply (head + 1), state'⟩ : ID)) =
      { tape := tape, head := head, state := tableRunState q' }
  rw [hmachineStep]
  ext i
  · by_cases hi : i = head + 1 <;> simp [hi]
  · simp [Move.apply]
  · rfl

theorem toTableProgram_toMachine_nextID_of_post_move_exact
    {P : PostProgram} {c : PostID} {q q' : Nat} {m : Move}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', PostStmt.move m)) :
    P.toTableProgram.toMachine.nextID (tableIDOfPostID c) =
      tableIDOfPostID (P.nextID c) := by
  rw [toTableProgram_toMachine_nextID_of_post_move hstate hstep]
  rw [nextID_of_running hstate]
  simp [hstep, applyStmt, tableIDOfPostID]

theorem toTableProgram_toMachine_nextID_two_of_post_write_exact
    {P : PostProgram} {c : PostID} {q q' b : Nat}
    (hsupp : TapeSupported P c)
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', PostStmt.write b)) :
    P.toTableProgram.toMachine.nextID
        (P.toTableProgram.toMachine.nextID (tableIDOfPostID c)) =
      tableIDOfPostID (P.nextID c) := by
  rw [toTableProgram_toMachine_nextID_of_post_write_start hstate hstep]
  have hb : b ∈ tableSupportedSymbols P :=
    symbol_mem_tableSupportedSymbols (symbol_mem_of_step_eq_some_write hstep)
  have hret :
      (Function.update c.tape c.head b) (c.head + 1) ∈ tableSupportedSymbols P :=
    tapeSupported_update hsupp hb (c.head + 1)
  rw [toTableProgram_toMachine_nextID_of_post_write_return
    (P := P) (q := q) (a := c.tape c.head) (b := b) hstep hret]
  rw [nextID_of_running hstate]
  simp [hstep, applyStmt, tableIDOfPostID]

theorem toTableProgram_toMachine_nextID_state_of_post_step_none
    {P : PostProgram} {c : PostID} {q : Nat}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = none) :
    (P.toTableProgram.toMachine.nextID (tableIDOfPostID c)).state =
      tableHalt := by
  rw [toTableProgram_toMachine_nextID_of_post_step_none hstate hstep]

theorem toTableProgram_toMachine_runEmpty_sync_or_halts
    (P : PostProgram) (n : Nat) :
    (∃ t : Nat,
        P.toTableProgram.toMachine.runEmpty t =
          tableIDOfPostID (P.runEmpty n)) ∨
      P.toTableProgram.toMachine.HaltsEmpty := by
  induction n with
  | zero =>
      left
      refine ⟨0, ?_⟩
      ext i <;> simp [Machine.runEmpty_zero, Machine.initialID,
        PostProgram.runEmpty_zero, PostProgram.initialID, tableIDOfPostID]
  | succ n ih =>
      rcases ih with ⟨t, hsync⟩ | hhalts
      · let c := P.runEmpty n
        cases hstate : c.state with
        | none =>
            right
            have hstateRun : (P.runEmpty n).state = none := by
              simpa [c] using hstate
            exact ⟨t, by
              rw [hsync]
              simp [tableIDOfPostID_state_halt hstateRun, toTableProgram_halt]⟩
        | some q =>
            cases hstep : P.step q (c.tape c.head) with
            | none =>
                right
                refine ⟨t + 1, ?_⟩
                rw [Machine.runEmpty_succ, hsync]
                have hhalt :=
                  toTableProgram_toMachine_nextID_state_of_post_step_none
                    (P := P) (c := c) hstate hstep
                simpa [toTableProgram_halt] using hhalt
            | some step =>
                rcases step with ⟨q', stmt⟩
                cases stmt with
                | move m =>
                    left
                    refine ⟨t + 1, ?_⟩
                    rw [Machine.runEmpty_succ, hsync, PostProgram.runEmpty_succ]
                    change
                      P.toTableProgram.toMachine.nextID (tableIDOfPostID c) =
                        tableIDOfPostID (P.nextID c)
                    exact toTableProgram_toMachine_nextID_of_post_move_exact
                      (P := P) (c := c) hstate hstep
                | write b =>
                    left
                    refine ⟨t + 2, ?_⟩
                    rw [show t + 2 = t + 1 + 1 by omega]
                    rw [Machine.runEmpty_succ, Machine.runEmpty_succ, hsync,
                      PostProgram.runEmpty_succ]
                    change
                      P.toTableProgram.toMachine.nextID
                          (P.toTableProgram.toMachine.nextID (tableIDOfPostID c)) =
                        tableIDOfPostID (P.nextID c)
                    have hsupp : TapeSupported P c := by
                      simpa [c] using runEmpty_tapeSupported P n
                    exact toTableProgram_toMachine_nextID_two_of_post_write_exact
                      (P := P) (c := c) hsupp hstate hstep
      · exact Or.inr hhalts

theorem toTableProgram_toMachine_haltsEmpty_of_haltsEmpty
    {P : PostProgram} (h : P.HaltsEmpty) :
    P.toTableProgram.toMachine.HaltsEmpty := by
  rcases h with ⟨n, hhalt⟩
  rcases toTableProgram_toMachine_runEmpty_sync_or_halts P n with ⟨t, hsync⟩ | hhalts
  · exact ⟨t, by
      rw [hsync]
      simp [tableIDOfPostID_state_halt hhalt, toTableProgram_halt]⟩
  · exact hhalts

/-- Table configurations reachable while simulating a nonhalting Post run. -/
def TableRunRel (P : PostProgram) (id : ID) : Prop :=
  (∃ n : Nat, id = tableIDOfPostID (P.runEmpty n)) ∨
    ∃ n q q' b : Nat,
      (P.runEmpty n).state = some q ∧
        P.step q ((P.runEmpty n).tape (P.runEmpty n).head) =
          some (q', PostStmt.write b) ∧
        id =
          { tape := Function.update (P.runEmpty n).tape (P.runEmpty n).head b
            head := (P.runEmpty n).head + 1
            state := tableWriteState q' }

theorem tableRunRel_initial (P : PostProgram) :
    TableRunRel P P.toTableProgram.toMachine.initialID := by
  left
  refine ⟨0, ?_⟩
  ext i <;> simp [Machine.initialID, PostProgram.runEmpty_zero,
    PostProgram.initialID, tableIDOfPostID]

theorem tableRunRel_state_ne_halt_of_not_halts
    {P : PostProgram} {id : ID}
    (hnot : ¬ P.HaltsEmpty) (hrel : TableRunRel P id) :
    id.state ≠ P.toTableProgram.toMachine.halt := by
  rcases hrel with ⟨n, hid⟩ | ⟨n, q, q', b, hstate, hstep, hid⟩
  · have hnotState : (P.runEmpty n).state ≠ none := by
      intro hhalt
      exact hnot ⟨n, hhalt⟩
    cases hrun : (P.runEmpty n).state with
    | none =>
        exact False.elim (hnotState hrun)
    | some q =>
        rw [hid]
        simp [tableIDOfPostID_state_running hrun, toTableProgram_halt,
          (tableHalt_ne_tableRunState q).symm]
  · rw [hid]
    simp [toTableProgram_halt, (tableHalt_ne_tableWriteState q').symm]

theorem tableRunRel_next_of_not_halts
    {P : PostProgram} {id : ID}
    (hnot : ¬ P.HaltsEmpty) (hrel : TableRunRel P id) :
    TableRunRel P (P.toTableProgram.toMachine.nextID id) := by
  rcases hrel with ⟨n, hid⟩ | ⟨n, q, q', b, hstate, hstep, hid⟩
  · let c := P.runEmpty n
    have hnotState : c.state ≠ none := by
      intro hhalt
      exact hnot ⟨n, by simpa [c] using hhalt⟩
    cases hstate : c.state with
    | none =>
        exact False.elim (hnotState hstate)
    | some q =>
        cases hstep : P.step q (c.tape c.head) with
        | none =>
            have hnextHalt : (P.runEmpty (n + 1)).state = none := by
              rw [runEmpty_succ]
              change (P.nextID c).state = none
              rw [nextID_of_running hstate]
              simp [hstep]
            exact False.elim (hnot ⟨n + 1, hnextHalt⟩)
        | some step =>
            rcases step with ⟨q', stmt⟩
            cases stmt with
            | move m =>
                left
                refine ⟨n + 1, ?_⟩
                rw [hid, runEmpty_succ]
                change
                  P.toTableProgram.toMachine.nextID (tableIDOfPostID c) =
                    tableIDOfPostID (P.nextID c)
                exact toTableProgram_toMachine_nextID_of_post_move_exact
                  (P := P) (c := c) hstate hstep
            | write b =>
                right
                refine ⟨n, q, q', b, ?_, ?_, ?_⟩
                · simpa [c] using hstate
                · simpa [c] using hstep
                · rw [hid]
                  exact toTableProgram_toMachine_nextID_of_post_write_start
                    (P := P) (c := c) hstate hstep
  · left
    refine ⟨n + 1, ?_⟩
    rw [hid, runEmpty_succ]
    have hb : b ∈ tableSupportedSymbols P :=
      symbol_mem_tableSupportedSymbols (symbol_mem_of_step_eq_some_write hstep)
    have hret :
        (Function.update (P.runEmpty n).tape (P.runEmpty n).head b)
            ((P.runEmpty n).head + 1) ∈ tableSupportedSymbols P :=
      tapeSupported_update (runEmpty_tapeSupported P n) hb ((P.runEmpty n).head + 1)
    rw [toTableProgram_toMachine_nextID_of_post_write_return
      (P := P) (q := q) (a := (P.runEmpty n).tape (P.runEmpty n).head)
      (b := b) hstep hret]
    rw [nextID_of_running hstate]
    simp [hstep, applyStmt, tableIDOfPostID]

theorem tableRunRel_runEmpty_of_not_halts
    {P : PostProgram} (hnot : ¬ P.HaltsEmpty) (t : Nat) :
    TableRunRel P (P.toTableProgram.toMachine.runEmpty t) := by
  induction t with
  | zero =>
      simpa [Machine.runEmpty_zero] using tableRunRel_initial P
  | succ t ih =>
      rw [Machine.runEmpty_succ]
      exact tableRunRel_next_of_not_halts hnot ih

theorem not_toTableProgram_toMachine_haltsEmpty_of_not_haltsEmpty
    {P : PostProgram} (hnot : ¬ P.HaltsEmpty) :
    ¬ P.toTableProgram.toMachine.HaltsEmpty := by
  rintro ⟨t, hhalt⟩
  have hrel := tableRunRel_runEmpty_of_not_halts hnot t
  exact tableRunRel_state_ne_halt_of_not_halts hnot hrel hhalt

theorem haltsEmpty_of_toTableProgram_toMachine_haltsEmpty
    {P : PostProgram} (h : P.toTableProgram.toMachine.HaltsEmpty) :
    P.HaltsEmpty := by
  by_contra hnot
  exact not_toTableProgram_toMachine_haltsEmpty_of_not_haltsEmpty hnot h

theorem toTableProgram_toMachine_haltsEmpty_iff (P : PostProgram) :
    P.toTableProgram.toMachine.HaltsEmpty ↔ P.HaltsEmpty :=
  ⟨haltsEmpty_of_toTableProgram_toMachine_haltsEmpty,
    toTableProgram_toMachine_haltsEmpty_of_haltsEmpty⟩

end PostProgram

/-- Preferred name for the local one-sided TM0 instruction syntax. -/
abbrev FiniteTM0Stmt : Type :=
  PostStmt

/-- Preferred name for one finite transition row in the local one-sided TM0 model. -/
abbrev FiniteTM0Transition : Type :=
  PostTransition

/--
Preferred name for the local finite one-sided TM0 program model.

The older `PostProgram` name is kept for existing proofs. Semantically this is
the finite data version of Mathlib's `Turing.TM0.Machine`, with natural-number
codes for the finite alphabet and state set, a one-sided tape, and halting by
absence of a matching transition.
-/
abbrev FiniteTM0Program : Type :=
  PostProgram

/-- Preferred name for instantaneous descriptions of local one-sided TM0 runs. -/
abbrev FiniteTM0ID : Type :=
  PostID

end LeanWang
