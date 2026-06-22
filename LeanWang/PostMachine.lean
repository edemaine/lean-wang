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

theorem writeReturnRow_matches_run (q r a s : Nat) :
    ({ state := tableWriteState r, read := s, write := s, next := tableRunState r,
       move := Move.left } : TableTransition).matchesInput (tableRunState q) a = false := by
  have hstate : tableWriteState r ≠ tableRunState q := by
    exact (tableRunState_ne_tableWriteState q r).symm
  simp [TableTransition.matchesInput, hstate]

/-- Return-left rows used after a simulated Post write to next state `q`. -/
def writeReturnRows (P : PostProgram) (q : Nat) : List TableTransition :=
  (tableSupportedSymbols P).map fun a =>
    { state := tableWriteState q
      read := a
      write := a
      next := tableRunState q
      move := Move.left }

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

theorem writeReturnRows_find?_run (P : PostProgram) (q r a : Nat) :
    (writeReturnRows P r).find? (fun e => e.matchesInput (tableRunState q) a) = none := by
  unfold writeReturnRows
  induction tableSupportedSymbols P with
  | nil => rfl
  | cons s rest ih =>
      simp [writeReturnRow_matches_run q r a s, ih]

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

/-- Compile a one-sided Post/TM0 program to the older always-write-and-move table model. -/
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
