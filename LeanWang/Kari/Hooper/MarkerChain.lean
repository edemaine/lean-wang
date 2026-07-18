/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.MarkerProgram

/-!
# Executable chains of marker moves

`MarkerProgram.moveTable` finishes with the head on the boundary it has just
written.  A following search for a different boundary cannot start there: its
entry state accepts only blank or the boundary it is looking for.  This module
makes the missing inter-command motion explicit.  Every command performs one
guarded marker move and then steps off the written boundary in a specified
direction.  Consequently a later command starts on the adjacent cell, which
may be blank or may already be its target boundary.

This four-state command is the executable chaining primitive needed by the
counter-program compiler and by Hooper's bounded replacement of its search
phase.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerChain

open Turing

/-- One marker move together with the direction in which control leaves the
newly written boundary. -/
structure Command where
  move : MarkerProgram.Move
  depart : Turing.Dir
  deriving DecidableEq

/-- A chained command owns the three source states of the marker move and one
additional source state that steps off the newly written boundary. -/
def commandWidth : Nat := 4

/-- Head-relative tape after performing the marker move and stepping away
from the new boundary. -/
def resultTape (command : Command) (distance : Nat)
    (T : FullTM0.Tape MarkerMachine.Symbol) :
    FullTM0.Tape MarkerMachine.Symbol :=
  (MarkerProgram.resultTape command.move distance T).move command.depart

/-- Compile one marker move followed by its explicit departure step. -/
def commandTable (offset : FiniteTM0.State) (command : Command) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  MarkerProgram.moveTable offset command.move ++
    [FiniteTM0.Rule.mk (offset + MarkerProgram.commandWidth)
      (MarkerMachine.boundarySymbol command.move.expected)
      (offset + commandWidth) (MarkerMachine.moveAction command.depart)]

/-- The four owned source states of a chained command are pairwise distinct. -/
theorem commandTable_deterministic (offset : FiniteTM0.State)
    (command : Command) :
    FiniteTM0.Deterministic (commandTable offset command) := by
  rcases command with ⟨⟨expected, searchDirection, shiftDirection⟩,
    depart⟩
  cases searchDirection <;> cases shiftDirection <;> cases depart <;>
    simp [commandTable, MarkerProgram.moveTable, MarkerProgram.program,
      FiniteTM0Program.relocate, FiniteTM0Program.relocateRule,
      FiniteTM0.Deterministic,
      FiniteTM0.Rule.mk, MarkerProgram.commandWidth, commandWidth,
      MarkerMachine.searchState, MarkerMachine.moveState,
      MarkerMachine.verifyState,
      MarkerMachine.blankSymbol_ne_boundarySymbol]

/-- Exact execution of one command, including the step that makes the next
search executable. -/
theorem command_reaches (offset : FiniteTM0.State) (command : Command)
    (T : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol command.move.expected)
      T command.move.searchDirection distance)
    (hdestination :
      (((T.moveN command.move.searchDirection distance).write
          MarkerMachine.blankSymbol).move command.move.shiftDirection).read =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (commandTable offset command))
      ⟨offset, T⟩ ⟨offset + commandWidth,
        resultTape command distance T⟩ := by
  have hmoveLocal := MarkerProgram.moveTable_reaches offset command.move T
    distance hgap hdestination
  have hmove : FullTM0.Reaches
      (FiniteTM0.machine (commandTable offset command))
      ⟨offset, T⟩
      ⟨offset + MarkerProgram.commandWidth,
        MarkerProgram.resultTape command.move distance T⟩ := by
    exact FiniteTM0Program.reaches_append_left _ _ hmoveLocal
  have hread :
      (MarkerProgram.resultTape command.move distance T).read =
        MarkerMachine.boundarySymbol command.move.expected := by
    simp [MarkerProgram.resultTape]
  have hstep : FullTM0.step
      (FiniteTM0.machine (commandTable offset command))
      ⟨offset + MarkerProgram.commandWidth,
        MarkerProgram.resultTape command.move distance T⟩ =
      some ⟨offset + commandWidth,
        resultTape command distance T⟩ := by
    rcases command with ⟨⟨expected, searchDirection, shiftDirection⟩,
      depart⟩
    cases searchDirection <;> cases shiftDirection <;> cases depart <;>
      simp [FullTM0.step, FiniteTM0.machine, commandTable,
        MarkerProgram.moveTable, MarkerProgram.program,
        FiniteTM0Program.relocate, FiniteTM0Program.relocateRule,
        FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
        MarkerProgram.commandWidth, commandWidth,
        MarkerMachine.searchState, MarkerMachine.moveState,
        MarkerMachine.verifyState, MarkerMachine.moveAction,
        FullTM0.Tape.read_eq, MarkerProgram.resultTape, resultTape]
  exact Relation.ReflTransGen.tail hmove hstep

/-- Compile commands into adjacent four-state intervals. -/
def table (offset : FiniteTM0.State) : List Command →
    FiniteTM0.Table MarkerMachine.AlphabetSize
  | [] => []
  | command :: commands =>
      commandTable offset command ++ table (offset + commandWidth) commands

/-- Total state width of a command chain. -/
def width (commands : List Command) : Nat :=
  commandWidth * commands.length

/-- Fall-through control state of a command chain. -/
def exitState (offset : FiniteTM0.State) (commands : List Command) :
    FiniteTM0.State :=
  offset + width commands

@[simp]
theorem exitState_cons (offset : FiniteTM0.State) (command : Command)
    (commands : List Command) :
    exitState offset (command :: commands) =
      exitState (offset + commandWidth) commands := by
  simp [exitState, width, commandWidth, Nat.mul_succ,
    Nat.add_assoc, Nat.add_comm]

/-- Every source state owned by one command lies in its four-state interval. -/
theorem source_mem_commandTable {offset state : FiniteTM0.State}
    {command : Command}
    (hstate : state ∈ FiniteTM0.sourceStates
      (commandTable offset command)) :
    offset ≤ state ∧ state < offset + commandWidth := by
  simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append, List.map_singleton, List.mem_singleton] at hstate
  rcases hstate with hmove | hdepart
  · have hbounds := MarkerProgram.source_mem_moveTable hmove
    exact ⟨hbounds.1, lt_of_lt_of_le hbounds.2 (by
      simp [MarkerProgram.commandWidth, commandWidth])⟩
  · change state = offset + MarkerProgram.commandWidth at hdepart
    subst state
    simp [MarkerProgram.commandWidth, commandWidth]

/-- Every source state of a command list lies in the list's fresh interval. -/
theorem source_mem_table {commands : List Command}
    {offset state : FiniteTM0.State}
    (hstate : state ∈ FiniteTM0.sourceStates (table offset commands)) :
    offset ≤ state ∧ state < exitState offset commands := by
  induction commands generalizing offset with
  | nil => simp [table, FiniteTM0.sourceStates] at hstate
  | cons command commands ih =>
      simp only [table, FiniteTM0.sourceStates, List.map_append,
        List.mem_append] at hstate
      rcases hstate with hfirst | hrest
      · have hbounds := source_mem_commandTable hfirst
        constructor
        · exact hbounds.1
        · rw [exitState_cons]
          exact lt_of_lt_of_le hbounds.2
            (Nat.le_add_right (offset + commandWidth) (width commands))
      · have hbounds := ih hrest
        constructor
        · exact Nat.le_trans (Nat.le_add_right offset commandWidth)
            hbounds.1
        · rw [exitState_cons]
          exact hbounds.2

/-- The list compiler owns disjoint state intervals, hence its complete rule
table has no duplicate transition keys. -/
theorem table_deterministic (offset : FiniteTM0.State)
    (commands : List Command) :
    FiniteTM0.Deterministic (table offset commands) := by
  induction commands generalizing offset with
  | nil => simp [table, FiniteTM0.Deterministic]
  | cons command commands ih =>
      simp only [table, FiniteTM0.Deterministic, List.map_append]
      apply List.Nodup.append (commandTable_deterministic offset command)
        (ih (offset + commandWidth))
      rw [List.disjoint_iff_ne]
      intro left hleft right hright heq
      have hleftState : left.1 ∈ FiniteTM0.sourceStates
          (commandTable offset command) := by
        rcases List.mem_map.mp hleft with ⟨rule, hrule, hkey⟩
        apply List.mem_map.mpr
        exact ⟨rule, hrule, congrArg Prod.fst hkey⟩
      have hrightState : right.1 ∈ FiniteTM0.sourceStates
          (table (offset + commandWidth) commands) := by
        rcases List.mem_map.mp hright with ⟨rule, hrule, hkey⟩
        apply List.mem_map.mpr
        exact ⟨rule, hrule, congrArg Prod.fst hkey⟩
      have hleftBound : left.1 < offset + commandWidth :=
        (source_mem_commandTable hleftState).2
      have hrightBound : offset + commandWidth ≤ right.1 :=
        (source_mem_table hrightState).1
      apply (Nat.ne_of_lt (lt_of_lt_of_le hleftBound hrightBound))
      exact congrArg Prod.fst heq

/-- Guarded semantic execution of a whole command chain. -/
inductive Executes : List Command →
    FullTM0.Tape MarkerMachine.Symbol →
    FullTM0.Tape MarkerMachine.Symbol → Prop
  | nil (T) : Executes [] T T
  | cons (command : Command) (commands : List Command)
      (T U : FullTM0.Tape MarkerMachine.Symbol) (distance : Nat)
      (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
        (fun a => a = MarkerMachine.boundarySymbol command.move.expected)
        T command.move.searchDirection distance)
      (hdestination :
        (((T.moveN command.move.searchDirection distance).write
            MarkerMachine.blankSymbol).move
              command.move.shiftDirection).read =
          MarkerMachine.blankSymbol)
      (hrest : Executes commands (resultTape command distance T) U) :
      Executes (command :: commands) T U

/-- Exact reachability for an executable command chain. -/
theorem executes_reaches (offset : FiniteTM0.State)
    {commands : List Command}
    {T U : FullTM0.Tape MarkerMachine.Symbol}
    (hexec : Executes commands T U) :
    FullTM0.Reaches (FiniteTM0.machine (table offset commands))
      ⟨offset, T⟩ ⟨exitState offset commands, U⟩ := by
  induction hexec generalizing offset with
  | nil T =>
      exact Relation.ReflTransGen.refl
  | cons command commands T U distance hgap hdestination hrest ih =>
      let first := commandTable offset command
      let rest := table (offset + commandWidth) commands
      have hfirstLocal := command_reaches offset command T distance hgap
        hdestination
      have hfirst : FullTM0.Reaches (FiniteTM0.machine (first ++ rest))
          ⟨offset, T⟩
          ⟨offset + commandWidth, resultTape command distance T⟩ := by
        exact FiniteTM0Program.reaches_append_left first rest hfirstLocal
      have hrestLocal := ih (offset + commandWidth)
      have hseparate : ∀ state,
          state ∈ FiniteTM0.sourceStates rest →
          state ∉ FiniteTM0.sourceStates first := by
        intro state hrestSource hfirstSource
        have hfirstBound : state < offset + commandWidth :=
          (source_mem_commandTable hfirstSource).2
        have hrestLower : offset + commandWidth ≤ state :=
          (source_mem_table hrestSource).1
        exact (Nat.not_lt_of_ge hrestLower) hfirstBound
      have htail : FullTM0.Reaches (FiniteTM0.machine (first ++ rest))
          ⟨offset + commandWidth, resultTape command distance T⟩
          ⟨exitState (offset + commandWidth) commands, U⟩ :=
        MarkerProgram.reaches_append_right_of_source_disjoint first rest
          hseparate hrestLocal
      have hall := hfirst.trans htail
      rw [exitState_cons]
      exact hall

end MarkerChain
end Hooper
end Kari
end LeanWang
