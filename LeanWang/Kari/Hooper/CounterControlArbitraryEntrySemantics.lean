/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Arbitrary-entry semantics of the shared canonical initializer

An arbitrary natural-number state owned by the initializer is either its
shared tag dispatcher or a precise position in one tag-specific guarded
path.  The path is straight-line: every successful internal transition moves
to a larger initializer state, and its only exit is the oriented canonical
logical state selected by that tag.  A malformed tape simply disables the
unique guarded rule and halts.

Starting in the middle of a private path does *not* imply a canonical tape:
the skipped prefix may contain the boundary writes that establish the frame.
The honest arbitrary-entry endpoint proved here is therefore a canonical
logical control state whose scanned symbol is boundary `4`.  Later logical
validation is responsible for rejecting or nesting around a malformed core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlArbitraryEntrySemantics

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlArbitraryEntry
open CanonicalInitializerProgram

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Exact initializer phases -/

/-- A source of the shared initializer is either its dispatcher or an exact
position in one tag block.  The last block position is the preserving exit
rule; all earlier positions are guarded path instructions. -/
inductive InitializerPhase (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.State → Prop
  | dispatch : InitializerPhase base c (controllerCoreEntry base c)
  | path (tag : Fin numTags) (position : Fin (tagBlockWidth c)) :
      InitializerPhase base c
        (pathOffset (controllerCoreEntry base c) c tag + position.val)

/-- Every source state of the concrete initializer has an exact phase. -/
theorem initializerPhase_of_source
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates (initializerTable base c)) :
    InitializerPhase base c state := by
  simp only [initializerTable, CanonicalInitializerProgram.table,
    FiniteTM0.sourceStates, List.map_append, List.mem_append] at hsource
  rcases hsource with hdispatch | hblocks
  · have hstate : state = controllerCoreEntry base c := by
      simp only [dispatchTable, List.map_map, List.mem_map,
        FiniteTM0.Rule.mk, Function.comp_apply] at hdispatch
      rcases hdispatch with ⟨tag, _htag, hstate⟩
      exact hstate.symm
    subst state
    exact .dispatch
  · have hflat : state ∈
        (List.finRange numTags).flatMap fun tag =>
          FiniteTM0.sourceStates
            (tagBlock (controllerCoreEntry base c) c
              (initializerGrowth tag) tag (initializerExitFor base c tag)) := by
      simpa only [FiniteTM0.sourceStates, List.map_flatMap] using hblocks
    rcases List.mem_flatMap.mp hflat with ⟨tag, _htag, htagSource⟩
    rcases source_mem_tagBlock htagSource with ⟨hlower, hupper⟩
    have hposition :
        state - pathOffset (controllerCoreEntry base c) c tag <
          tagBlockWidth c := by
      exact (Nat.sub_lt_iff_lt_add' hlower).2 hupper
    let position : Fin (tagBlockWidth c) :=
      ⟨state - pathOffset (controllerCoreEntry base c) c tag, hposition⟩
    have hstate : state =
        pathOffset (controllerCoreEntry base c) c tag + position.val := by
      dsimp [position]
      exact (Nat.add_sub_of_le hlower).symm
    rw [hstate]
    exact .path tag position

/-! ## Structural witnesses for generated rules -/

/-- Every rule of a compiled straight-line path comes from one exact list
position. -/
theorem pathTable_rule_witness {numSymbols offset}
    {instructions : List (FiniteTM0Path.Instruction numSymbols)}
    {tableRule : FiniteTM0.Rule numSymbols}
    (hrule : tableRule ∈ FiniteTM0Path.table offset instructions) :
    ∃ before instruction after,
      instructions = before ++ instruction :: after ∧
      tableRule = FiniteTM0.Rule.mk (offset + before.length)
        instruction.read (offset + before.length + 1) instruction.action := by
  induction instructions generalizing offset with
  | nil => simp [FiniteTM0Path.table] at hrule
  | cons first rest ih =>
      simp only [FiniteTM0Path.table, List.mem_cons] at hrule
      rcases hrule with hfirst | hrest
      · refine ⟨[], first, rest, by simp, ?_⟩
        simpa using hfirst
      · rcases ih hrest with ⟨before, instruction, after, hlist, htable⟩
        refine ⟨first :: before, instruction, after, ?_, ?_⟩
        · simp [hlist]
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htable

/-- Every initializer rule is a dispatcher rule, an exact guarded path
instruction, or one tag block's final preserving exit. -/
theorem initializerRule_witness
    (base : Nat) (c : Nat.Partrec.Code)
    {tableRule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : tableRule ∈ initializerTable base c) :
    (∃ tag : Fin numTags,
        tableRule = FiniteTM0.Rule.mk (controllerCoreEntry base c)
          (tagSymbol tag)
          (pathOffset (controllerCoreEntry base c) c tag)
          (.write blankSymbol)) ∨
      (∃ (tag : Fin numTags)
          (before : List (FiniteTM0Path.Instruction (AlphabetSize numTags)))
          (instruction : FiniteTM0Path.Instruction (AlphabetSize numTags))
          (after : List (FiniteTM0Path.Instruction (AlphabetSize numTags))),
        instructions c (initializerGrowth tag) tag =
          before ++ instruction :: after ∧
        tableRule = FiniteTM0.Rule.mk
          (pathOffset (controllerCoreEntry base c) c tag + before.length)
          instruction.read
          (pathOffset (controllerCoreEntry base c) c tag + before.length + 1)
          instruction.action) ∨
      ∃ tag : Fin numTags,
        tableRule = FiniteTM0.Rule.mk
          (pathExit (controllerCoreEntry base c) c tag)
          (boundarySymbol 4) (initializerExitFor base c tag)
          (.write (boundarySymbol 4)) := by
  simp only [initializerTable, CanonicalInitializerProgram.table,
    List.mem_append] at hrule
  rcases hrule with hdispatch | hblocks
  · left
    simp only [dispatchTable, List.mem_map] at hdispatch
    rcases hdispatch with ⟨tag, _htag, htable⟩
    exact ⟨tag, htable.symm⟩
  · right
    rcases List.mem_flatMap.mp hblocks with ⟨tag, _htag, htag⟩
    simp only [tagBlock, List.mem_append, List.mem_singleton] at htag
    rcases htag with hpath | hexit
    · left
      rcases pathTable_rule_witness hpath with
        ⟨before, instruction, after, hlist, htable⟩
      exact ⟨tag, before, instruction, after, hlist, htable⟩
    · right
      exact ⟨tag, hexit⟩

/-- The end of every tag block lies at or before the first fresh initializer
state. -/
theorem tagBlockEnd_le_initializerEnd
    (base : Nat) (c : Nat.Partrec.Code) (tag : Fin numTags) :
    pathOffset (controllerCoreEntry base c) c tag + tagBlockWidth c ≤
      initializerEnd base c := by
  have hmul := Nat.mul_le_mul_right (tagBlockWidth c)
    (Nat.succ_le_of_lt tag.isLt)
  simpa [pathOffset, initializerEnd, CanonicalInitializerProgram.exitState,
    Nat.succ_mul, Nat.add_assoc] using
    Nat.add_le_add_left hmul (controllerCoreEntry base c + 1)

/-- A generated initializer rule either advances strictly inside the finite
initializer interval, or is exactly one tag block's final preserving exit. -/
theorem initializerRule_advances_or_isExit
    (base : Nat) (c : Nat.Partrec.Code)
    {tableRule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : tableRule ∈ initializerTable base c) :
    (tableRule.1.1 < tableRule.2.1 ∧
        tableRule.2.1 < initializerEnd base c) ∨
      ∃ tag : Fin numTags,
        tableRule = FiniteTM0.Rule.mk
          (pathExit (controllerCoreEntry base c) c tag)
          (boundarySymbol 4) (initializerExitFor base c tag)
          (.write (boundarySymbol 4)) := by
  rcases initializerRule_witness base c hrule with
    ⟨tag, rfl⟩ | ⟨tag, before, instruction, after, hlist, rfl⟩ |
      ⟨tag, rfl⟩
  · left
    constructor
    · exact Nat.lt_of_lt_of_le
        (Nat.lt_succ_self (controllerCoreEntry base c))
        (Nat.le_add_right (controllerCoreEntry base c + 1)
          (tag.val * tagBlockWidth c))
    · have hend := tagBlockEnd_le_initializerEnd base c tag
      have hwidth : 0 < tagBlockWidth c := by
        simp [tagBlockWidth, pathWidth]
      exact (Nat.lt_add_of_pos_right hwidth).trans_le hend
  · left
    constructor
    · exact Nat.lt_succ_self _
    · have hbefore : before.length < pathWidth c := by
        have hlength := congrArg List.length hlist
        simp only [instructions_length, List.length_append,
          List.length_cons] at hlength
        omega
      have hend := tagBlockEnd_le_initializerEnd base c tag
      have hnext_le :
          pathOffset (controllerCoreEntry base c) c tag + before.length + 1 ≤
            pathOffset (controllerCoreEntry base c) c tag + pathWidth c := by
        simpa [Nat.add_assoc] using Nat.add_le_add_left
          (Nat.succ_le_of_lt hbefore)
          (pathOffset (controllerCoreEntry base c) c tag)
      have hexit_lt_blockEnd :
          pathOffset (controllerCoreEntry base c) c tag + pathWidth c <
            pathOffset (controllerCoreEntry base c) c tag + tagBlockWidth c := by
        simp [tagBlockWidth]
      exact (hnext_le.trans_lt hexit_lt_blockEnd).trans_le hend
  · right
    exact ⟨tag, rfl⟩

/-- A generated initializer rule either advances strictly inside the finite
initializer interval, or exits to the tag-selected canonical logical state. -/
theorem initializerRule_advances_or_exits
    (base : Nat) (c : Nat.Partrec.Code)
    {tableRule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : tableRule ∈ initializerTable base c) :
    (tableRule.1.1 < tableRule.2.1 ∧
        tableRule.2.1 < initializerEnd base c) ∨
      ∃ tag : Fin numTags,
        tableRule.2.1 = canonicalEntry base c (initializerGrowth tag) := by
  rcases initializerRule_advances_or_isExit base c hrule with
    hinternal | ⟨tag, htable⟩
  · exact Or.inl hinternal
  · right
    refine ⟨tag, ?_⟩
    rw [htable]
    exact initializerExitFor_eq base c tag

/-! ## Initializer steps inside the complete machine -/

/-- Numeric separation forces every complete-table rule whose source is owned
by the initializer to come from the initializer table itself. -/
theorem tableRule_mem_initializer_of_source
    (base : Nat) (c : Nat.Partrec.Code)
    {tableRule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : tableRule ∈ CounterControlPlan.table base c)
    (hsource : tableRule.1.1 ∈
      FiniteTM0.sourceStates (initializerTable base c)) :
    tableRule ∈ initializerTable base c := by
  simp only [CounterControlPlan.table, BoundedMarkerProgram.table, coreTable,
    List.mem_append] at hrule
  rcases hrule with hcontroller | hinitializer | hdirect
  · have hcontrollerSource : tableRule.1.1 ∈
        FiniteTM0.sourceStates
          (BoundedMarkerProgram.controllerTable base
            (CanonicalInitializer.radius c) (commands base c)) :=
      List.mem_map.mpr ⟨tableRule, hcontroller, rfl⟩
    have hc := controller_lt_coreEntry base c hcontrollerSource
    have hi := (initializer_bounds base c hsource).1
    exact False.elim ((Nat.not_lt_of_ge hi) hc)
  · exact hinitializer
  · have hdirectSource : tableRule.1.1 ∈
        FiniteTM0.sourceStates (directTable base c) :=
      List.mem_map.mpr ⟨tableRule, hdirect, rfl⟩
    have hi := (initializer_bounds base c hsource).2
    have hd := initializerEnd_le_direct base c hdirectSource
    exact False.elim ((Nat.not_lt_of_ge hd) hi)

/-- At an initializer source, one complete-machine step either is absent,
which halts immediately, advances strictly within the initializer interval,
or is the preserving boundary-`4` exit to canonical logical control. -/
theorem initializer_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (state : FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : state ∈ FiniteTM0.sourceStates (initializerTable base c)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨state, T⟩ ∨
      ∃ next : FullTM0.Cfg (Symbol numTags) FiniteTM0.State,
        FullTM0.step (CounterControlNestingBridge.machine base c)
            ⟨state, T⟩ = some next ∧
          ((state < next.q ∧ next.q < initializerEnd base c) ∨
            ∃ tag : Fin numTags,
              next.q = canonicalEntry base c (initializerGrowth tag) ∧
                next.tape.read = boundarySymbol 4) := by
  classical
  cases hlookup : FiniteTM0.lookupAction (CounterControlPlan.table base c)
      state T.read with
  | none =>
      left
      refine ⟨⟨state, T⟩, Relation.ReflTransGen.refl, ?_⟩
      change FullTM0.step
        (FiniteTM0.machine (CounterControlPlan.table base c)) ⟨state, T⟩ = none
      simp only [FullTM0.step, FiniteTM0.machine_apply]
      rw [hlookup]
      rfl
  | some result =>
      right
      rcases result with ⟨target, action⟩
      have htable : FiniteTM0.Rule.mk state T.read target action ∈
          CounterControlPlan.table base c :=
        FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      have hinitializer : FiniteTM0.Rule.mk state T.read target action ∈
          initializerTable base c := by
        apply tableRule_mem_initializer_of_source base c htable
        simpa using hsource
      rcases initializerRule_advances_or_isExit base c hinitializer with
        hinternal | ⟨tag, hexit⟩
      · let next : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
          ⟨target, FiniteTM0Path.applyAction action T⟩
        refine ⟨next, ?_, Or.inl ?_⟩
        · change FullTM0.step
            (FiniteTM0.machine (CounterControlPlan.table base c))
              ⟨state, T⟩ = some next
          simp only [FullTM0.step, FiniteTM0.machine_apply]
          rw [hlookup]
          cases action <;> rfl
        · simpa [next, FiniteTM0.Rule.mk] using hinternal
      · have htarget : target = initializerExitFor base c tag := by
          simpa [FiniteTM0.Rule.mk] using
            congrArg (fun rule => rule.2.1) hexit
        have haction : action = .write (boundarySymbol 4) := by
          simpa [FiniteTM0.Rule.mk] using
            congrArg (fun rule => rule.2.2) hexit
        rw [htarget, haction] at hlookup
        let next : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
          ⟨initializerExitFor base c tag, T.write (boundarySymbol 4)⟩
        refine ⟨next, ?_, Or.inr ⟨tag, ?_, ?_⟩⟩
        · change FullTM0.step
            (FiniteTM0.machine (CounterControlPlan.table base c))
              ⟨state, T⟩ = some next
          simp only [FullTM0.step, FiniteTM0.machine_apply]
          rw [hlookup]
          rfl
        · exact initializerExitFor_eq base c tag
        · exact FullTM0.Tape.read_write (boundarySymbol 4) T

/-! ## Finite arbitrary-entry normalization -/

/-- Every arbitrary configuration whose state is owned by the shared
initializer either reaches a terminal configuration, or finitely exits at
the tag-selected canonical logical state while scanning boundary `4`.

No assertion is made about the rest of the tape: entry in the middle of a
private initializer path may have skipped any prefix of the frame-building
writes. -/
theorem initializer_normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (hsource : cfg.q ∈ FiniteTM0.sourceStates (initializerTable base c)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) cfg ∨
      ∃ (tag : Fin numTags) (U : FullTM0.Tape (Symbol numTags)),
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) cfg
            ⟨canonicalEntry base c (initializerGrowth tag), U⟩ ∧
          U.read = boundarySymbol 4 := by
  classical
  generalize hmeasure : initializerEnd base c - cfg.q = distance
  induction distance using Nat.strong_induction_on generalizing cfg with
  | h distance ih =>
      rcases initializer_step_or_haltsFrom base c cfg.q cfg.tape hsource with
        hhalts | ⟨next, hstep, hprogress⟩
      · exact Or.inl hhalts
      · have hone : FullTM0.Reaches
            (CounterControlNestingBridge.machine base c) cfg next :=
          Relation.ReflTransGen.single hstep
        rcases hprogress with hinternal | ⟨tag, hstate, hboundary⟩
        · rcases hinternal with ⟨hadvance, hnextUpper⟩
          by_cases hnextSource : next.q ∈
              FiniteTM0.sourceStates (initializerTable base c)
          · have hsmaller : initializerEnd base c - next.q < distance := by
              rw [← hmeasure]
              exact Nat.sub_lt_sub_left
                (hadvance.trans hnextUpper) hadvance
            rcases ih (initializerEnd base c - next.q) hsmaller next
                hnextSource rfl with htailHalts | ⟨tag, U, htail, hread⟩
            · exact Or.inl
                (FullTM0.HaltsFrom.of_reaches hone htailHalts)
            · exact Or.inr ⟨tag, U, hone.trans htail, hread⟩
          · have hnotFull : next.q ∉ FiniteTM0.sourceStates
                (CounterControlPlan.table base c) := by
              intro hfull
              cases sourceRegion_of_mem base c hfull with
              | controller hcontroller =>
                  have hc := controller_lt_coreEntry base c hcontroller
                  have hi := (initializer_bounds base c hsource).1
                  exact (Nat.not_lt_of_ge (hi.trans hadvance.le)) hc
              | initializer hinitializer =>
                  exact hnextSource hinitializer
              | direct hdirect =>
                  have hd := initializerEnd_le_direct base c hdirect
                  exact (Nat.not_lt_of_ge hd) hnextUpper
            have hnextHalts : FullTM0.HaltsFrom
                (FiniteTM0.machine (CounterControlPlan.table base c)) next :=
              FiniteTM0Halting.haltsFrom_of_state_not_mem
                (CounterControlPlan.table base c) next hnotFull
            exact Or.inl (FullTM0.HaltsFrom.of_reaches hone hnextHalts)
        · rcases next with ⟨nextState, nextTape⟩
          change nextState =
            canonicalEntry base c (initializerGrowth tag) at hstate
          change nextTape.read = boundarySymbol 4 at hboundary
          subst nextState
          exact Or.inr ⟨tag, nextTape, hone, hboundary⟩

/-- In particular, an immortal arbitrary initializer entry must leave the
initializer after finitely many steps at canonical logical control, scanning
boundary `4`. -/
theorem initializer_reaches_canonical_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (hsource : cfg.q ∈ FiniteTM0.sourceStates (initializerTable base c))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cfg) :
    ∃ (tag : Fin numTags) (U : FullTM0.Tape (Symbol numTags)),
      FullTM0.Reaches (CounterControlNestingBridge.machine base c) cfg
          ⟨canonicalEntry base c (initializerGrowth tag), U⟩ ∧
        U.read = boundarySymbol 4 := by
  rcases initializer_normalizes_arbitrary_entry base c cfg hsource with
    hhalts | hexit
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c) cfg).mp himmortal hhalts)
  · exact hexit

end

end CounterControlArbitraryEntrySemantics
end Hooper
end Kari
end LeanWang
