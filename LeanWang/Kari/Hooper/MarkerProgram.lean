/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FiniteTM0Program

/-!
# Relocatable programs for chains of marker moves

`MarkerMachine.program` searches for a labelled boundary and then moves it one
cell in the same direction.  Consecutive suffix moves need the two directions
to be independent: after an increment moves the rightmost boundary right, the
machine searches left for the next boundary but moves that boundary right;
positive decrements use the mirror image.

This file supplies that independent-direction primitive and a small linker for
lists of marker moves.  Every primitive owns exactly three source states.  A
list therefore owns one half-open state interval of width three times its
length, and its exact reachability theorem composes guarded moves without any
assumption about cells outside the searched gaps and destinations.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerProgram

open Turing

/-- A finite marker command: find one label in `searchDirection`, then shift
that marker by one cell in the independently chosen `shiftDirection`. -/
structure Move where
  expected : Fin 5
  searchDirection : Turing.Dir
  shiftDirection : Turing.Dir
  deriving DecidableEq

/-- The four-rule local program for an independent-direction marker move. -/
def program (move : Move) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  [ FiniteTM0.Rule.mk MarkerMachine.searchState MarkerMachine.blankSymbol
      MarkerMachine.searchState
      (MarkerMachine.moveAction move.searchDirection)
  , FiniteTM0.Rule.mk MarkerMachine.searchState
      (MarkerMachine.boundarySymbol move.expected)
      MarkerMachine.moveState (.write MarkerMachine.blankSymbol)
  , FiniteTM0.Rule.mk MarkerMachine.moveState MarkerMachine.blankSymbol
      MarkerMachine.verifyState
      (MarkerMachine.moveAction move.shiftDirection)
  , FiniteTM0.Rule.mk MarkerMachine.verifyState MarkerMachine.blankSymbol
      MarkerMachine.doneState
      (.write (MarkerMachine.boundarySymbol move.expected))
  ]

/-- Semantic full-tape machine for one local marker command. -/
def machine (move : Move) :
    Turing.TM0.Machine MarkerMachine.Symbol FiniteTM0.State :=
  FiniteTM0.machine (program move)

/-- The generated primitive has no duplicate transition keys. -/
theorem program_deterministic (move : Move) :
    FiniteTM0.Deterministic (program move) := by
  simp [FiniteTM0.Deterministic, program, FiniteTM0.Rule.mk,
    MarkerMachine.searchState, MarkerMachine.moveState,
    MarkerMachine.verifyState,
    MarkerMachine.blankSymbol_ne_boundarySymbol]

@[simp]
theorem step_search_blank (move : Move) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (machine move) ⟨MarkerMachine.searchState, T⟩ =
      some ⟨MarkerMachine.searchState, T.move move.searchDirection⟩ := by
  change T 0 = MarkerMachine.blankSymbol at hread
  cases move with
  | mk expected searchDirection shiftDirection =>
      cases searchDirection <;>
        simp [FullTM0.step, machine, program, FiniteTM0.machine,
          FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
          MarkerMachine.searchState, MarkerMachine.moveAction,
          FullTM0.Tape.read, hread]

@[simp]
theorem step_search_boundary (move : Move)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.boundarySymbol move.expected) :
    FullTM0.step (machine move) ⟨MarkerMachine.searchState, T⟩ =
      some ⟨MarkerMachine.moveState, T.write MarkerMachine.blankSymbol⟩ := by
  change T 0 = MarkerMachine.boundarySymbol move.expected at hread
  have hne : MarkerMachine.boundarySymbol move.expected ≠
      MarkerMachine.blankSymbol :=
    (MarkerMachine.blankSymbol_ne_boundarySymbol move.expected).symm
  cases move with
  | mk expected searchDirection shiftDirection =>
      cases searchDirection <;>
        simp [FullTM0.step, machine, program, FiniteTM0.machine,
          FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
          MarkerMachine.searchState, MarkerMachine.moveState,
          MarkerMachine.moveAction, FullTM0.Tape.read, hread, hne]

@[simp]
theorem step_move (move : Move) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (machine move) ⟨MarkerMachine.moveState, T⟩ =
      some ⟨MarkerMachine.verifyState, T.move move.shiftDirection⟩ := by
  change T 0 = MarkerMachine.blankSymbol at hread
  cases move with
  | mk expected searchDirection shiftDirection =>
      cases shiftDirection <;>
        simp [FullTM0.step, machine, program, FiniteTM0.machine,
          FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
          MarkerMachine.searchState, MarkerMachine.moveState,
          MarkerMachine.verifyState, MarkerMachine.moveAction,
          FullTM0.Tape.read, hread]

@[simp]
theorem step_verify (move : Move) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (machine move) ⟨MarkerMachine.verifyState, T⟩ =
      some ⟨MarkerMachine.doneState,
        T.write (MarkerMachine.boundarySymbol move.expected)⟩ := by
  change T 0 = MarkerMachine.blankSymbol at hread
  cases move with
  | mk expected searchDirection shiftDirection =>
      cases searchDirection <;> cases shiftDirection <;>
        simp [FullTM0.step, machine, program, FiniteTM0.machine,
          FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
          MarkerMachine.searchState, MarkerMachine.moveState,
          MarkerMachine.verifyState, MarkerMachine.doneState,
          MarkerMachine.moveAction, FullTM0.Tape.read, hread]

/-- One successful semantic step gives full-tape reachability. -/
private theorem reaches_of_step {move : Move}
    {c d : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State}
    (h : FullTM0.step (machine move) c = some d) :
    FullTM0.Reaches (machine move) c d := by
  apply Relation.ReflTransGen.single
  simp [h]

/-- The search phase crosses exactly `distance` blank cells and clears the
expected labelled boundary. -/
theorem search_reaches_clear (move : Move)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol move.expected)
      T move.searchDirection distance) :
    FullTM0.Reaches (machine move)
      ⟨MarkerMachine.searchState, T⟩
      ⟨MarkerMachine.moveState,
        (T.moveN move.searchDirection distance).write
          MarkerMachine.blankSymbol⟩ := by
  induction distance generalizing T with
  | zero =>
      have hread : T.read = MarkerMachine.boundarySymbol move.expected := by
        simpa [SearchGap, FullTM0.Tape.read] using hgap.2
      simpa using reaches_of_step (step_search_boundary move T hread)
  | succ distance ih =>
      have hread : T.read = MarkerMachine.blankSymbol := by
        simpa [FullTM0.Tape.read] using
          hgap.blank (Nat.zero_lt_succ distance)
      have hfirst := reaches_of_step (step_search_blank move T hread)
      have htail : SearchGap (fun a => a = MarkerMachine.blankSymbol)
          (fun a => a = MarkerMachine.boundarySymbol move.expected)
          (T.move move.searchDirection) move.searchDirection distance := by
        simpa [Nat.succ_eq_add_one] using hgap.tail
      have hrest := ih (T.move move.searchDirection) htail
      have hall := hfirst.trans hrest
      simpa [FullTM0.Reaches, StateTransition.Reaches,
        FullTM0.Tape.move_moveN, Nat.succ_eq_add_one] using hall

/-- Head-relative tape after a guarded marker command at a given search
distance. -/
def resultTape (move : Move) (distance : Nat)
    (T : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.Tape MarkerMachine.Symbol :=
  ((((T.moveN move.searchDirection distance).write
      MarkerMachine.blankSymbol).move move.shiftDirection).write
        (MarkerMachine.boundarySymbol move.expected))

/-- The local primitive performs exactly the independent-direction marker
move when the searched gap and destination cell satisfy their guards. -/
theorem move_reaches (move : Move)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol move.expected)
      T move.searchDirection distance)
    (hdestination :
      (((T.moveN move.searchDirection distance).write
          MarkerMachine.blankSymbol).move move.shiftDirection).read =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (machine move)
      ⟨MarkerMachine.searchState, T⟩
      ⟨MarkerMachine.doneState, resultTape move distance T⟩ := by
  have hsearch := search_reaches_clear move T distance hgap
  have hmove := reaches_of_step
    (step_move move
      ((T.moveN move.searchDirection distance).write
        MarkerMachine.blankSymbol) (by simp))
  have hwrite := reaches_of_step
    (step_verify move
      (((T.moveN move.searchDirection distance).write
        MarkerMachine.blankSymbol).move move.shiftDirection)
      hdestination)
  exact hsearch.trans (hmove.trans hwrite)

/-! ## Relocatable commands and list programs -/

/-- Every marker command owns local source states `0`, `1`, and `2`, with
fall-through exit state `3`. -/
def commandWidth : Nat := 3

/-- Relocate one marker command to an arbitrary entry state. -/
def moveTable (offset : FiniteTM0.State) (move : Move) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  FiniteTM0Program.relocate offset (program move)

/-- Exact reachability through one relocated marker command. -/
theorem moveTable_reaches (offset : FiniteTM0.State) (move : Move)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol move.expected)
      T move.searchDirection distance)
    (hdestination :
      (((T.moveN move.searchDirection distance).write
          MarkerMachine.blankSymbol).move move.shiftDirection).read =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (moveTable offset move))
      ⟨offset, T⟩
      ⟨offset + commandWidth, resultTape move distance T⟩ := by
  have h := FiniteTM0Program.reaches_relocate offset (program move)
    (move_reaches move T distance hgap hdestination)
  simpa [moveTable, FiniteTM0Program.liftCfg,
    MarkerMachine.searchState, MarkerMachine.doneState, commandWidth] using h

/-- Compile a list of commands into adjacent three-state blocks. -/
def table (offset : FiniteTM0.State) : List Move →
    FiniteTM0.Table MarkerMachine.AlphabetSize
  | [] => []
  | move :: moves =>
      moveTable offset move ++ table (offset + commandWidth) moves

/-- Width of a compiled marker-command list. -/
def width (moves : List Move) : Nat :=
  commandWidth * moves.length

/-- Exit state of a compiled marker-command list. -/
def exitState (offset : FiniteTM0.State) (moves : List Move) :
    FiniteTM0.State :=
  offset + width moves

@[simp]
theorem exitState_cons (offset : FiniteTM0.State) (move : Move)
    (moves : List Move) :
    exitState offset (move :: moves) =
      exitState (offset + commandWidth) moves := by
  simp [exitState, width, commandWidth, Nat.mul_succ,
    Nat.add_assoc, Nat.add_comm]

/-- The source states owned by one relocated command are exactly inside its
three-state half-open interval. -/
theorem source_mem_moveTable {offset : FiniteTM0.State} {move : Move}
    {state : FiniteTM0.State}
    (hstate : state ∈ FiniteTM0.sourceStates (moveTable offset move)) :
    offset ≤ state ∧ state < offset + commandWidth := by
  simp only [moveTable, FiniteTM0Program.relocate,
    FiniteTM0.sourceStates, List.map_map, List.mem_map] at hstate
  rcases hstate with ⟨rule, hrule, rfl⟩
  simp [program] at hrule
  rcases hrule with rfl | rfl | rfl | rfl <;>
    simp [FiniteTM0Program.relocateRule, FiniteTM0.Rule.mk,
      MarkerMachine.searchState, MarkerMachine.moveState,
      MarkerMachine.verifyState, commandWidth]

/-- Every source state of the list program lies in its allocated half-open
interval. -/
theorem source_mem_table {moves : List Move} {offset state : FiniteTM0.State}
    (hstate : state ∈ FiniteTM0.sourceStates (table offset moves)) :
    offset ≤ state ∧ state < exitState offset moves := by
  induction moves generalizing offset with
  | nil =>
      simp [table, FiniteTM0.sourceStates] at hstate
  | cons move moves ih =>
      simp only [table, FiniteTM0.sourceStates, List.map_append,
        List.mem_append] at hstate
      rcases hstate with hfirst | hrest
      · have hbounds := source_mem_moveTable hfirst
        constructor
        · exact hbounds.1
        · refine Nat.lt_of_lt_of_le hbounds.2 ?_
          rw [exitState_cons]
          exact Nat.le_add_right (offset + commandWidth) (width moves)
      · have hbounds := ih hrest
        constructor
        · exact Nat.le_trans (Nat.le_add_right offset commandWidth) hbounds.1
        · rw [exitState_cons]
          exact hbounds.2

/-- If the left table has no rule at the current state, prefixing it cannot
change a step of the right table. -/
theorem step_append_of_state_not_mem_left
    (first second : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State)
    (hsource : cfg.q ∉ FiniteTM0.sourceStates first) :
    FullTM0.step (FiniteTM0.machine (first ++ second)) cfg =
      FullTM0.step (FiniteTM0.machine second) cfg := by
  have hlookup :
      FiniteTM0.lookupAction first cfg.q (cfg.tape 0) = none := by
    cases h : FiniteTM0.lookupAction first cfg.q (cfg.tape 0) with
    | none => rfl
    | some result =>
        rcases result with ⟨target, action⟩
        exfalso
        apply hsource
        have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some h
        exact List.mem_map.mpr
          ⟨FiniteTM0.Rule.mk cfg.q (cfg.tape 0) target action,
            hrule, rfl⟩
  simp only [FullTM0.step, FiniteTM0.machine, FullTM0.Tape.read_eq]
  rw [FiniteTM0Program.lookupAction_append, hlookup]

/-- A path through a right-hand table remains valid after prefixing a table
whose source states are disjoint from every source state of the right table. -/
theorem reaches_append_right_of_source_disjoint
    (first second : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (hdisjoint : ∀ state,
      state ∈ FiniteTM0.sourceStates second →
      state ∉ FiniteTM0.sourceStates first)
    {start finish :
      FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine second) start finish) :
    FullTM0.Reaches (FiniteTM0.machine (first ++ second)) start finish := by
  apply Relation.ReflTransGen.mono ?_ hreach
  intro current next hstep
  have hright : current.q ∈ FiniteTM0.sourceStates second := by
    by_contra hsource
    have hnone := FiniteTM0.machine_eq_none_of_state_not_mem
      hsource current.tape.read
    have hstepNone :
        FullTM0.step (FiniteTM0.machine second) current = none := by
      unfold FullTM0.step
      rw [hnone]
      rfl
    rw [hstepNone] at hstep
    simp at hstep
  rw [step_append_of_state_not_mem_left first second current
    (hdisjoint current.q hright)]
  exact hstep

/-- A guarded semantic execution of a command list.  The search distance is a
run-time witness and deliberately does not occur in the compiled table. -/
inductive Executes : List Move →
    FullTM0.Tape MarkerMachine.Symbol →
    FullTM0.Tape MarkerMachine.Symbol → Prop
  | nil (T) : Executes [] T T
  | cons (move : Move) (moves : List Move)
      (T U : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
      (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
        (fun a => a = MarkerMachine.boundarySymbol move.expected)
        T move.searchDirection distance)
      (hdestination :
        (((T.moveN move.searchDirection distance).write
            MarkerMachine.blankSymbol).move move.shiftDirection).read =
          MarkerMachine.blankSymbol)
      (hrest : Executes moves (resultTape move distance T) U) :
      Executes (move :: moves) T U

/-- Exact reachability theorem for a compiled list of independently directed
marker moves. -/
theorem executes_reaches (offset : FiniteTM0.State)
    {moves : List Move} {T U : FullTM0.Tape MarkerMachine.Symbol}
    (hexec : Executes moves T U) :
    FullTM0.Reaches (FiniteTM0.machine (table offset moves))
      ⟨offset, T⟩ ⟨exitState offset moves, U⟩ := by
  induction hexec generalizing offset with
  | nil T =>
      simp only [table, exitState, width, List.length_nil, Nat.mul_zero,
        Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | cons move moves T U distance hgap hdestination hrest ih =>
      let first := moveTable offset move
      let rest := table (offset + commandWidth) moves
      have hfirstLocal := moveTable_reaches offset move T distance
        hgap hdestination
      have hfirst : FullTM0.Reaches (FiniteTM0.machine (first ++ rest))
          ⟨offset, T⟩
          ⟨offset + commandWidth, resultTape move distance T⟩ := by
        exact FiniteTM0Program.reaches_append_left first rest hfirstLocal
      have hrestLocal := ih (offset + commandWidth)
      have hseparate : ∀ state,
          state ∈ FiniteTM0.sourceStates rest →
          state ∉ FiniteTM0.sourceStates first := by
        intro state hrestSource hfirstSource
        have hfirstBounds : state < offset + commandWidth :=
          (source_mem_moveTable hfirstSource).2
        have hrestBounds : offset + commandWidth ≤ state := by
          exact (source_mem_table hrestSource).1
        exact (Nat.not_lt_of_ge hrestBounds) hfirstBounds
      have htail : FullTM0.Reaches (FiniteTM0.machine (first ++ rest))
          ⟨offset + commandWidth, resultTape move distance T⟩
          ⟨exitState (offset + commandWidth) moves, U⟩ :=
        reaches_append_right_of_source_disjoint first rest hseparate hrestLocal
      have hall := hfirst.trans htail
      have hExit :
          exitState (offset + commandWidth) moves =
            exitState offset (move :: moves) :=
        (exitState_cons offset move moves).symm
      change FullTM0.Reaches (FiniteTM0.machine (first ++ rest))
        ⟨offset, T⟩ ⟨exitState offset (move :: moves), U⟩
      rw [← hExit]
      exact hall

/-! ## Collision-free suffix schedules -/

/-- Keep the first search direction supplied by the caller, then search in a
fixed between-command direction after each marker shift. -/
def schedule (firstSearch betweenSearch shift : Turing.Dir) :
    List (Fin 5) → List Move
  | [] => []
  | label :: labels =>
      ⟨label, firstSearch, shift⟩ ::
        labels.map fun next => ⟨next, betweenSearch, shift⟩

/-- Right-to-left suffix order for increment: subsequent searches go left,
while every located marker shifts right. -/
def incrementSchedule (firstSearch : Turing.Dir)
    (register : CounterMachine.Register) : List Move :=
  schedule firstSearch .left .right (MarkerShift.incrementOrder register)

/-- Left-to-right suffix order for a positive decrement: subsequent searches
go right, while every located marker shifts left. -/
def decrementSchedule (firstSearch : Turing.Dir)
    (register : CounterMachine.Register) : List Move :=
  schedule firstSearch .right .left (MarkerShift.decrementOrder register)

@[simp]
theorem schedule_expected (firstSearch betweenSearch shift : Turing.Dir)
    (labels : List (Fin 5)) :
    (schedule firstSearch betweenSearch shift labels).map Move.expected =
      labels := by
  cases labels with
  | nil => rfl
  | cons label labels => simp [schedule, Function.comp_def]

end MarkerProgram
end Hooper
end Kari
end LeanWang
