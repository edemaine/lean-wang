/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.FullTM0
import LeanWang.Kari.Hooper.FiniteTM0

/-!
# Finite straight-line paths for TM0 machines

This file compiles a list of guarded actions into consecutive states of an
explicit `FiniteTM0` table.  Each instruction records the symbol that must be
under the head and the action to perform.  Successful execution falls through
from state `offset` to `offset + instructions.length`, with the tape changed by
exactly the listed actions.

In addition to the compiler and its execution theorem, the file supplies the
generic table-linking facts needed to embed a path in a larger finite machine.
They are independent of Hooper's marker alphabet.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace FiniteTM0Path

open Turing

/-- One guarded action in a straight-line path. -/
structure Instruction (numSymbols : Nat) where
  read : FiniteTM0.Symbol numSymbols
  action : FiniteTM0.Action numSymbols
  deriving DecidableEq

namespace Instruction

variable {numSymbols : Nat}

/-- The canonical product code for guarded actions. -/
def equivCode : Instruction numSymbols ≃
    FiniteTM0.Symbol numSymbols × FiniteTM0.Action numSymbols where
  toFun instruction := (instruction.read, instruction.action)
  invFun code := ⟨code.1, code.2⟩
  left_inv instruction := by cases instruction; rfl
  right_inv code := by cases code; rfl

instance : Primcodable (Instruction numSymbols) :=
  Primcodable.ofEquiv
    (FiniteTM0.Symbol numSymbols × FiniteTM0.Action numSymbols) equivCode

end Instruction

variable {numSymbols : Nat}

/-- Execute an explicitly coded action on a full tape. -/
def applyAction (action : FiniteTM0.Action numSymbols)
    (T : FullTM0.Tape (FiniteTM0.Symbol numSymbols)) :
    FullTM0.Tape (FiniteTM0.Symbol numSymbols) :=
  match action with
  | .moveLeft => T.move .left
  | .moveRight => T.move .right
  | .write a => T.write a

@[simp]
theorem applyAction_moveLeft
    (T : FullTM0.Tape (FiniteTM0.Symbol numSymbols)) :
    applyAction .moveLeft T = T.move .left :=
  rfl

@[simp]
theorem applyAction_moveRight
    (T : FullTM0.Tape (FiniteTM0.Symbol numSymbols)) :
    applyAction .moveRight T = T.move .right :=
  rfl

@[simp]
theorem applyAction_write (a : FiniteTM0.Symbol numSymbols)
    (T : FullTM0.Tape (FiniteTM0.Symbol numSymbols)) :
    applyAction (.write a) T = T.write a :=
  rfl

/-- Compile guarded actions into consecutive source states. -/
def table (offset : FiniteTM0.State) : List (Instruction numSymbols) →
    FiniteTM0.Table numSymbols
  | [] => []
  | instruction :: instructions =>
      FiniteTM0.Rule.mk offset instruction.read (offset + 1)
        instruction.action :: table (offset + 1) instructions

/-- Fold step used to expose the compiler as a primitive-recursive function. -/
def foldStep
    (accumulator : FiniteTM0.State × FiniteTM0.Table numSymbols)
    (instruction : Instruction numSymbols) :
    FiniteTM0.State × FiniteTM0.Table numSymbols :=
  (accumulator.1 + 1,
    accumulator.2 ++
      [FiniteTM0.Rule.mk accumulator.1 instruction.read
        (accumulator.1 + 1) instruction.action])

/-- The accumulating compiler agrees with the structural compiler, even when
started after an arbitrary table prefix. -/
theorem foldl_foldStep (instructions : List (Instruction numSymbols))
    (nextState : FiniteTM0.State) (rulesSoFar : FiniteTM0.Table numSymbols) :
    (instructions.foldl foldStep (nextState, rulesSoFar)).2 =
      rulesSoFar ++ table nextState instructions := by
  induction instructions generalizing nextState rulesSoFar with
  | nil => simp [table]
  | cons instruction instructions ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [foldStep, table, List.append_assoc]

/-- One accumulating compiler step is primitive recursive. -/
theorem foldStep_primrec :
    Primrec fun input :
        (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
          Instruction numSymbols =>
      foldStep input.1 input.2 := by
  have hcode : Primrec
      (Instruction.equivCode : Instruction numSymbols →
        FiniteTM0.Symbol numSymbols × FiniteTM0.Action numSymbols) :=
    Primrec.of_equiv
  have hsource : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hprefix : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hread : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols => input.2.read :=
    Primrec.fst.comp (hcode.comp Primrec.snd)
  have haction : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols => input.2.action :=
    Primrec.snd.comp (hcode.comp Primrec.snd)
  have htarget : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols => input.1.1 + 1 :=
    Primrec.nat_add.comp hsource (Primrec.const 1)
  have hrule : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols =>
      FiniteTM0.Rule.mk input.1.1 input.2.read
        (input.1.1 + 1) input.2.action :=
    Primrec.pair (Primrec.pair hsource hread)
      (Primrec.pair htarget haction)
  have hsingleton : Primrec fun input :
      (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
        Instruction numSymbols =>
      [FiniteTM0.Rule.mk input.1.1 input.2.read
        (input.1.1 + 1) input.2.action] :=
    Primrec.list_cons.comp hrule (Primrec.const [])
  exact Primrec.pair htarget
    (Primrec.list_append.comp hprefix hsingleton)

/-- Straight-line table compilation is primitive recursive. -/
theorem table_primrec :
    Primrec fun input :
        FiniteTM0.State × List (Instruction numSymbols) =>
      table input.1 input.2 := by
  have hstep : Primrec₂ fun _input :
      FiniteTM0.State × List (Instruction numSymbols) =>
      fun pair :
          (FiniteTM0.State × FiniteTM0.Table numSymbols) ×
            Instruction numSymbols =>
        foldStep pair.1 pair.2 :=
    (Primrec.to₂ foldStep_primrec).comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  have hfold : Primrec fun input :
      FiniteTM0.State × List (Instruction numSymbols) =>
      input.2.foldl foldStep (input.1, []) :=
    Primrec.list_foldl Primrec.snd
      (Primrec.pair Primrec.fst (Primrec.const [])) hstep
  exact (Primrec.snd.comp hfold).of_eq fun input => by
    simpa using foldl_foldStep input.2 input.1 []

/-- Computability corollary for straight-line table compilation. -/
theorem table_computable :
    Computable fun input :
        FiniteTM0.State × List (Instruction numSymbols) =>
      table input.1 input.2 :=
  table_primrec.to_comp

/-- The number of source states owned by a straight-line path. -/
def width (instructions : List (Instruction numSymbols)) : Nat :=
  instructions.length

/-- The fall-through state immediately after a straight-line path. -/
def exitState (offset : FiniteTM0.State)
    (instructions : List (Instruction numSymbols)) : FiniteTM0.State :=
  offset + width instructions

@[simp]
theorem exitState_nil (offset : FiniteTM0.State) :
    exitState offset ([] : List (Instruction numSymbols)) = offset := by
  simp [exitState, width]

@[simp]
theorem exitState_cons (offset : FiniteTM0.State)
    (instruction : Instruction numSymbols)
    (instructions : List (Instruction numSymbols)) :
    exitState offset (instruction :: instructions) =
      exitState (offset + 1) instructions := by
  simp [exitState, width, Nat.add_assoc, Nat.add_comm]

/-! ## Source-state intervals and deterministic compilation -/

/-- Every compiled source state lies in the path's half-open state interval. -/
theorem source_mem_table {instructions : List (Instruction numSymbols)}
    {offset state : FiniteTM0.State}
    (hstate : state ∈ FiniteTM0.sourceStates (table offset instructions)) :
    offset ≤ state ∧ state < exitState offset instructions := by
  induction instructions generalizing offset with
  | nil => simp [table, FiniteTM0.sourceStates] at hstate
  | cons instruction instructions ih =>
      simp only [table, FiniteTM0.sourceStates, List.map_cons,
        List.mem_cons] at hstate
      rcases hstate with hfirst | hrest
      · change state = offset at hfirst
        subst state
        constructor
        · exact Nat.le_refl offset
        · rw [exitState_cons]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self offset)
            (Nat.le_add_right (offset + 1) (width instructions))
      · have hbounds := ih hrest
        constructor
        · exact Nat.le_trans (Nat.le_add_right offset 1) hbounds.1
        · rw [exitState_cons]
          exact hbounds.2

/-- Paths whose state intervals are ordered do not share source states. -/
theorem sourceStates_disjoint_of_before
    {first second : List (Instruction numSymbols)}
    {firstOffset secondOffset : FiniteTM0.State}
    (hbefore : exitState firstOffset first ≤ secondOffset) :
    List.Disjoint
      (FiniteTM0.sourceStates (table firstOffset first))
      (FiniteTM0.sourceStates (table secondOffset second)) := by
  rw [List.disjoint_iff_ne]
  intro left hleft right hright heq
  have hleftBounds := source_mem_table hleft
  have hrightBounds := source_mem_table hright
  subst right
  exact (Nat.not_lt_of_ge (Nat.le_trans hbefore hrightBounds.1))
    hleftBounds.2

/-- The compiler generates no duplicate transition keys. -/
theorem table_deterministic (offset : FiniteTM0.State)
    (instructions : List (Instruction numSymbols)) :
    FiniteTM0.Deterministic (table offset instructions) := by
  induction instructions generalizing offset with
  | nil => simp [table, FiniteTM0.Deterministic]
  | cons instruction instructions ih =>
      simp only [table, FiniteTM0.Deterministic, List.map_cons,
        List.nodup_cons]
      constructor
      · intro hkey
        have hstate : offset ∈ FiniteTM0.sourceStates
            (table (offset + 1) instructions) := by
          rcases List.mem_map.mp hkey with ⟨rule, hrule, heq⟩
          apply List.mem_map.mpr
          exact ⟨rule, hrule, congrArg Prod.fst heq⟩
        have hlower : offset + 1 ≤ offset :=
          (source_mem_table hstate).1
        rw [Nat.add_one] at hlower
        exact Nat.not_succ_le_self offset hlower
      · exact ih (offset + 1)

/-! ## Generic linking of finite tables -/

/-- Association-list lookup in an append first consults the left table. -/
theorem lookupAction_append (first second : FiniteTM0.Table numSymbols)
    (q : FiniteTM0.State) (a : FiniteTM0.Symbol numSymbols) :
    FiniteTM0.lookupAction (first ++ second) q a =
      match FiniteTM0.lookupAction first q a with
      | some result => some result
      | none => FiniteTM0.lookupAction second q a := by
  induction first with
  | nil => rfl
  | cons rule first ih =>
      rcases rule with ⟨key, result⟩
      by_cases hkey : (q, a) = key
      · simp [FiniteTM0.lookupAction, hkey]
      · simp [FiniteTM0.lookupAction, hkey, ih]

section Semantics

/-- Appending a suffix preserves every step defined by the left table. -/
theorem step_append_left
    (first second : FiniteTM0.Table numSymbols)
    {cfg next : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hstep : FullTM0.step (FiniteTM0.machine first) cfg = some next) :
    FullTM0.step (FiniteTM0.machine (first ++ second)) cfg = some next := by
  simp only [FullTM0.step, FiniteTM0.machine, FullTM0.Tape.read_eq] at hstep ⊢
  rw [lookupAction_append]
  cases hlookup : FiniteTM0.lookupAction first cfg.q (cfg.tape 0) with
  | none => simp [hlookup] at hstep
  | some result => simpa [hlookup] using hstep

/-- Prefixing a table with no rule at the current state preserves the right
table's step. -/
theorem step_append_of_state_not_mem_left
    (first second : FiniteTM0.Table numSymbols)
    (cfg : FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State)
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
  rw [lookupAction_append, hlookup]

/-- Every finite path through the left table survives appending a suffix. -/
theorem reaches_append_left
    (first second : FiniteTM0.Table numSymbols)
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine first) start finish) :
    FullTM0.Reaches (FiniteTM0.machine (first ++ second)) start finish := by
  apply Relation.ReflTransGen.mono ?_ hreach
  intro current next hstep
  exact step_append_left first second hstep

/-- Every finite path through the right table survives a source-disjoint
prefix. -/
theorem reaches_append_right_of_source_disjoint
    (first second : FiniteTM0.Table numSymbols)
    (hdisjoint : List.Disjoint (FiniteTM0.sourceStates first)
      (FiniteTM0.sourceStates second))
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
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
    (fun hleft => hdisjoint hleft hright)]
  exact hstep

/-- Every finite path through the right table survives a prefix whose source
states are absent from the right table's source set. -/
theorem reaches_append_right_of_source_separate
    (first second : FiniteTM0.Table numSymbols)
    (hseparate : ∀ state,
      state ∈ FiniteTM0.sourceStates second →
      state ∉ FiniteTM0.sourceStates first)
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine second) start finish) :
    FullTM0.Reaches (FiniteTM0.machine (first ++ second)) start finish := by
  apply reaches_append_right_of_source_disjoint first second
  · rw [List.disjoint_left]
    intro state hfirst hsecond
    exact hseparate state hsecond hfirst
  · exact hreach

/-! ## Exact guarded execution -/

/-- The exact tape-level meaning of a guarded instruction list. -/
inductive Executes : List (Instruction numSymbols) →
    FullTM0.Tape (FiniteTM0.Symbol numSymbols) →
    FullTM0.Tape (FiniteTM0.Symbol numSymbols) → Prop
  | nil (T) : Executes [] T T
  | cons (instruction : Instruction numSymbols)
      (instructions : List (Instruction numSymbols))
      (T U : FullTM0.Tape (FiniteTM0.Symbol numSymbols))
      (hread : T.read = instruction.read)
      (hrest : Executes instructions (applyAction instruction.action T) U) :
      Executes (instruction :: instructions) T U

/-- Exact execution determines its final tape. -/
theorem Executes.deterministic
    {instructions : List (Instruction numSymbols)}
    {T U V : FullTM0.Tape (FiniteTM0.Symbol numSymbols)}
    (hU : Executes instructions T U) (hV : Executes instructions T V) :
    U = V := by
  induction hU generalizing V with
  | nil T =>
      cases hV
      rfl
  | cons instruction instructions T U hread hrest ih =>
      cases hV with
      | cons _ _ _ V _ hrestV => exact ih hrestV

/-- The first compiled rule performs exactly its explicit tape action. -/
theorem step_cons (offset : FiniteTM0.State)
    (instruction : Instruction numSymbols)
    (instructions : List (Instruction numSymbols))
    (T : FullTM0.Tape (FiniteTM0.Symbol numSymbols))
    (hread : T.read = instruction.read) :
    FullTM0.step
        (FiniteTM0.machine (table offset (instruction :: instructions)))
        ⟨offset, T⟩ =
      some ⟨offset + 1, applyAction instruction.action T⟩ := by
  rcases instruction with ⟨read, action⟩
  change T 0 = read at hread
  cases action <;>
    simp [FullTM0.step, FiniteTM0.machine, table,
      FiniteTM0.lookupAction, FiniteTM0.Rule.mk, FullTM0.Tape.read_eq,
      applyAction, hread]

/-- Every guarded tape execution is a path through the compiled finite table. -/
theorem executes_reaches (offset : FiniteTM0.State)
    {instructions : List (Instruction numSymbols)}
    {T U : FullTM0.Tape (FiniteTM0.Symbol numSymbols)}
    (hexec : Executes instructions T U) :
    FullTM0.Reaches (FiniteTM0.machine (table offset instructions))
      ⟨offset, T⟩ ⟨exitState offset instructions, U⟩ := by
  induction hexec generalizing offset with
  | nil T =>
      exact Relation.ReflTransGen.refl
  | cons instruction instructions T U hread hrest ih =>
      let first : FiniteTM0.Table numSymbols :=
        table offset [instruction]
      let rest : FiniteTM0.Table numSymbols :=
        table (offset + 1) instructions
      have hfirst : FullTM0.Reaches
          (FiniteTM0.machine (first ++ rest))
          ⟨offset, T⟩
          ⟨offset + 1, applyAction instruction.action T⟩ := by
        apply Relation.ReflTransGen.single
        simpa [first, rest, table] using
          step_cons offset instruction instructions T hread
      have hrestLocal := ih (offset + 1)
      have hseparate : List.Disjoint
          (FiniteTM0.sourceStates first)
          (FiniteTM0.sourceStates rest) := by
        apply sourceStates_disjoint_of_before
        simp [exitState, width]
      have htail : FullTM0.Reaches
          (FiniteTM0.machine (first ++ rest))
          ⟨offset + 1, applyAction instruction.action T⟩
          ⟨exitState (offset + 1) instructions, U⟩ :=
        reaches_append_right_of_source_disjoint first rest hseparate
          hrestLocal
      have hall := hfirst.trans htail
      rw [exitState_cons]
      change FullTM0.Reaches (FiniteTM0.machine (first ++ rest))
        ⟨offset, T⟩
        ⟨exitState (offset + 1) instructions, U⟩
      exact hall

/-- The same guarded execution remains valid after appending any table. -/
theorem executes_reaches_append (offset : FiniteTM0.State)
    {instructions : List (Instruction numSymbols)}
    {T U : FullTM0.Tape (FiniteTM0.Symbol numSymbols)}
    (suffix : FiniteTM0.Table numSymbols)
    (hexec : Executes instructions T U) :
    FullTM0.Reaches
      (FiniteTM0.machine (table offset instructions ++ suffix))
      ⟨offset, T⟩ ⟨exitState offset instructions, U⟩ :=
  reaches_append_left _ _ (executes_reaches offset hexec)

end Semantics

end FiniteTM0Path
end Hooper
end Kari
end LeanWang
