/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Arbitrary entries into a compiled controller block

The private bounded controller is a finite straight-line device even when it
is entered in the middle.  Its scan states advance to `foundState` or
`launchState`; its unwind states advance back to the command's search entry.
This file first records the exact scan/unwind position of every private
source and proves that the selected command block has exactly the same
one-step semantics inside the complete counter controller.

These facts are deliberately independent of any well-formed-frame
assumption.  In particular, an arbitrary private entry may halt on the first
unexpected symbol; it cannot manufacture a canonical tape invariant.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlControllerEntrySemantics

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlArbitraryEntry

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

@[simp] private theorem tape_write_read {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) : T.write T.read = T := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.read, FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

/-! ## Exact private-controller positions -/

/-- A private command source is either an exact bounded-scan position or an
exact position in the finite unwind path. -/
theorem private_source_scan_or_unwind {numTags radius offset}
    {command : Command numTags} {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates
      (privateControllerTable radius offset command)) :
    (∃ progress ≤ NestingMachine.bound radius,
        state = offset + progress) ∨
      ∃ progress ≤ radius,
        state = offset + NestingMachine.localUnwindState radius + progress := by
  simp only [privateControllerTable, sourceStates_relocate,
    List.mem_map] at hsource
  rcases hsource with ⟨localState, hlocal, rfl⟩
  simp only [nativeLocalTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hlocal
  rcases hlocal with hscan | hunwind
  · left
    have hb := source_mem_nativeScanTableAux
      (target := command.target) (direction := command.searchDirection)
      (success := NestingMachine.localSuccessState radius)
      (launch := NestingMachine.localLaunchState radius)
      (state := 0) (remaining := NestingMachine.bound radius) hscan
    exact ⟨localState, by simpa using hb.2, rfl⟩
  · right
    have hunwind' : localState ∈ FiniteTM0.sourceStates
        (NestingMachine.unwindTable radius command.searchDirection) := by
      rw [← sourceStates_liftTable (numTags := numTags)]
      exact hunwind
    have hb := NestingMachine.source_mem_unwindTableAux
      (by simpa [NestingMachine.unwindTable] using hunwind')
    refine ⟨localState - NestingMachine.localUnwindState radius, ?_, ?_⟩
    · omega
    · have heq : NestingMachine.localUnwindState radius +
      (localState - NestingMachine.localUnwindState radius) =
            localState := Nat.add_sub_of_le hb.1
      calc
        offset + localState = offset +
            (NestingMachine.localUnwindState radius +
              (localState - NestingMachine.localUnwindState radius)) :=
          congrArg (offset + ·) heq.symm
        _ = offset + NestingMachine.localUnwindState radius +
            (localState - NestingMachine.localUnwindState radius) := by
          rw [Nat.add_assoc]

/-! ## Isolating one selected command block -/

private theorem lookupAction_eq_none_of_state_not_mem {numSymbols : Nat}
    (rules : FiniteTM0.Table numSymbols) (state : FiniteTM0.State)
    (symbol : FiniteTM0.Symbol numSymbols)
    (hstate : state ∉ FiniteTM0.sourceStates rules) :
    FiniteTM0.lookupAction rules state symbol = none := by
  cases hlookup : FiniteTM0.lookupAction rules state symbol with
  | none => rfl
  | some result =>
      exfalso
      apply hstate
      rcases result with ⟨target, action⟩
      have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      exact List.mem_map.mpr
        ⟨FiniteTM0.Rule.mk state symbol target action, hrule, rfl⟩

/-- The base of a selected command family is no larger than the selected
block's own offset. -/
theorem commandAt_base_le_commandOffset {numTags radius base commandOffset}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands) :
    base ≤ commandOffset := by
  induction hat with
  | head => exact Nat.le_refl _
  | tail offset commandOffset first command commands hat ih =>
      exact (Nat.le_add_right offset (blockWidth radius)).trans ih

/-- Within a command family, lookup at a source of the selected block is
exactly lookup in that block.  The statement remains true when the selected
rule is disabled, because all command-state intervals are disjoint. -/
theorem lookupAction_commandTables_of_at {numTags radius sharedCore base
    commandOffset} {command : Command numTags}
    {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (state : FiniteTM0.State) (symbol : Symbol numTags)
    (hsource : state ∈ FiniteTM0.sourceStates
      (commandTable radius commandOffset sharedCore command)) :
    FiniteTM0.lookupAction
        (commandTables radius sharedCore base commands) state symbol =
      FiniteTM0.lookupAction
        (commandTable radius commandOffset sharedCore command) state symbol := by
  induction hat with
  | head offset command commands =>
      rw [commandTables, FiniteTM0Program.lookupAction_append]
      cases hselected : FiniteTM0.lookupAction
          (commandTable radius offset sharedCore command) state symbol with
      | some result => rfl
      | none =>
          apply lookupAction_eq_none_of_state_not_mem
          intro hrest
          have hselectedBounds := source_mem_commandTable hsource
          have hrestBounds := source_mem_commandTables hrest
          exact (Nat.not_le_of_gt hselectedBounds.2) hrestBounds.1
  | tail offset commandOffset first command commands hat ih =>
      rw [commandTables, FiniteTM0Program.lookupAction_append]
      have hfirstNone : FiniteTM0.lookupAction
          (commandTable radius offset sharedCore first) state symbol = none := by
        apply lookupAction_eq_none_of_state_not_mem
        intro hfirst
        have hfirstBounds := source_mem_commandTable hfirst
        have hselectedBounds := source_mem_commandTable hsource
        have hselectedLower : offset + blockWidth radius ≤ state := by
          exact ((commandAt_base_le_commandOffset hat).trans
            hselectedBounds.1)
        exact (Nat.not_le_of_gt hfirstBounds.2) hselectedLower
      rw [hfirstNone]
      exact ih hsource

/-- A source of the selected block is a source of the complete command
family containing that block. -/
theorem source_mem_commandTables_of_at {numTags radius sharedCore base
    commandOffset} {command : Command numTags}
    {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates
      (commandTable radius commandOffset sharedCore command)) :
    state ∈ FiniteTM0.sourceStates
      (commandTables radius sharedCore base commands) := by
  induction hat with
  | head =>
      simp only [commandTables, FiniteTM0.sourceStates, List.map_append,
        List.mem_append]
      exact Or.inl hsource
  | tail offset commandOffset first command commands hat ih =>
      simp only [commandTables, FiniteTM0.sourceStates, List.map_append,
        List.mem_append]
      exact Or.inr (ih hsource)

/-- Lookup at a selected command source is unchanged by appending the two
directional return dispatchers. -/
theorem lookupAction_controllerTable_of_at {numTags radius base commandOffset}
    {command : Command numTags} {commands : List (Command numTags)}
    (hat : CommandAt radius base commandOffset command commands)
    (state : FiniteTM0.State) (symbol : Symbol numTags)
    (hsource : state ∈ FiniteTM0.sourceStates
      (commandTable radius commandOffset
        (coreEntry base radius commands) command)) :
    FiniteTM0.lookupAction (controllerTable base radius commands)
        state symbol =
      FiniteTM0.lookupAction
        (commandTable radius commandOffset
          (coreEntry base radius commands) command) state symbol := by
  rw [controllerTable, FiniteTM0Program.lookupAction_append]
  rw [lookupAction_commandTables_of_at hat state symbol hsource]
  cases hselected : FiniteTM0.lookupAction
      (commandTable radius commandOffset
        (coreEntry base radius commands) command) state symbol with
  | some result => rfl
  | none =>
      apply lookupAction_eq_none_of_state_not_mem
      intro hreturn
      rcases source_mem_returnTable hreturn with ⟨direction, hstate⟩
      have hcommands : state ∈ FiniteTM0.sourceStates
          (commandTables radius (coreEntry base radius commands)
            base commands) := source_mem_commandTables_of_at hat hsource
      have hbounds := source_mem_commandTables hcommands
      rw [hstate] at hbounds
      cases direction <;>
        simp only [returnState, BoundedMarkerProgram.commandOffset] at hbounds <;>
        omega

/-- At a selected compiled counter command, the complete table has exactly
the selected block's lookup.  This includes disabled reads: neither another
command, a return dispatcher, nor the initializer/direct core can capture
the same state. -/
theorem lookupAction_table_of_commandAt
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (state : FiniteTM0.State) (symbol : Symbol numTags)
    (hsource : state ∈ FiniteTM0.sourceStates
      (commandTable (CanonicalInitializer.radius c) commandOffset
        (controllerCoreEntry base c) command)) :
    FiniteTM0.lookupAction (CounterControlPlan.table base c) state symbol =
      FiniteTM0.lookupAction
        (commandTable (CanonicalInitializer.radius c) commandOffset
          (controllerCoreEntry base c) command) state symbol := by
  have hcoreEq : controllerCoreEntry base c =
      coreEntry base (CanonicalInitializer.radius c) (commands base c) :=
    (controllerCoreEntry_eq base c).symm
  rw [hcoreEq] at hsource ⊢
  simp only [CounterControlPlan.table, BoundedMarkerProgram.table, coreTable,
    FiniteTM0Program.lookupAction_append]
  rw [lookupAction_controllerTable_of_at hat state symbol hsource]
  cases hselected : FiniteTM0.lookupAction
      (commandTable (CanonicalInitializer.radius c) commandOffset
        (coreEntry base (CanonicalInitializer.radius c) (commands base c))
        command) state symbol with
  | some result => rfl
  | none =>
      have hcommands : state ∈ FiniteTM0.sourceStates
          (commandTables (CanonicalInitializer.radius c)
            (coreEntry base (CanonicalInitializer.radius c)
              (commands base c)) base (commands base c)) :=
        source_mem_commandTables_of_at hat hsource
      have hcontroller : state ∈ FiniteTM0.sourceStates
          (controllerTable base (CanonicalInitializer.radius c)
            (commands base c)) := by
        simp only [controllerTable, FiniteTM0.sourceStates, List.map_append,
          List.mem_append]
        exact Or.inl hcommands
      have hlt : state < controllerCoreEntry base c :=
        controller_lt_coreEntry base c hcontroller
      have hinitializerNot : state ∉
          FiniteTM0.sourceStates (initializerTable base c) := by
        intro hinitializer
        have hlower := (initializer_bounds base c hinitializer).1
        exact (Nat.not_lt_of_ge hlower) hlt
      have hdirectNot : state ∉
          FiniteTM0.sourceStates (directTable base c) := by
        intro hdirect
        have hdirectLower := initializerEnd_le_direct base c hdirect
        have hentryEnd : controllerCoreEntry base c ≤ initializerEnd base c := by
          simp [initializerEnd, CanonicalInitializerProgram.exitState]
          omega
        exact (Nat.not_lt_of_ge (hentryEnd.trans hdirectLower)) hlt
      have hinitializerNone := lookupAction_eq_none_of_state_not_mem
        (initializerTable base c) state symbol hinitializerNot
      have hdirectNone := lookupAction_eq_none_of_state_not_mem
        (directTable base c) state symbol hdirectNot
      rw [hinitializerNone, hdirectNone]

/-- One-step semantics of a selected command block are therefore identical
inside the complete counter machine. -/
theorem step_table_of_commandAt
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (hsource : cfg.q ∈ FiniteTM0.sourceStates
      (commandTable (CanonicalInitializer.radius c) commandOffset
        (controllerCoreEntry base c) command)) :
    FullTM0.step (CounterControlNestingBridge.machine base c) cfg =
      FullTM0.step
        (FiniteTM0.machine
          (commandTable (CanonicalInitializer.radius c) commandOffset
            (controllerCoreEntry base c) command)) cfg := by
  change FullTM0.step
      (FiniteTM0.machine (CounterControlPlan.table base c)) cfg = _
  simp only [FullTM0.step, FiniteTM0.machine_apply]
  rw [lookupAction_table_of_commandAt base c hat cfg.q cfg.tape.read hsource]

/-! ## Disabled private reads -/

/-- A target-rule family has no lookup exactly when its recognition
predicate fails at that symbol. -/
theorem lookupAction_targetRules_of_not_matches {numTags : Nat}
    (state success : FiniteTM0.State) (target : Target numTags)
    (symbol : Symbol numTags) (hnot : ¬ target.Matches symbol) :
    FiniteTM0.lookupAction (targetRules state success target)
        state symbol = none := by
  apply FiniteTM0.lookupAction_eq_none_of_key_not_mem
  cases target with
  | boundary label =>
      simp only [targetRules, List.map_cons, List.map_nil,
        List.mem_singleton, FiniteTM0.Rule.mk]
      intro heq
      apply hnot
      change symbol = boundarySymbol label
      simpa using congrArg Prod.snd heq
  | anyTag =>
      simp only [targetRules, List.map_map, List.mem_map,
        FiniteTM0.Rule.mk, Function.comp_apply]
      rintro ⟨tag, _htag, heq⟩
      apply hnot
      exact ⟨tag, by simpa using (congrArg Prod.snd heq).symm⟩

/-- At an exact scan position, a symbol which is neither the target nor
blank disables the whole finite scan table. -/
theorem lookup_nativeScanTableAux_other_at {numTags : Nat}
    (target : Target numTags) (direction : Turing.Dir)
    (success launch state remaining i : Nat) (symbol : Symbol numTags)
    (hi : i ≤ remaining) (hnot : ¬ target.Matches symbol)
    (hnonblank : symbol ≠ blankSymbol) :
    FiniteTM0.lookupAction
        (nativeScanTableAux target direction success launch remaining state)
        (state + i) symbol = none := by
  induction i generalizing remaining state with
  | zero =>
      simp only [Nat.add_zero]
      cases remaining with
      | zero =>
          simp only [nativeScanTableAux,
            FiniteTM0Program.lookupAction_append]
          rw [lookupAction_targetRules_of_not_matches _ _ _ _ hnot]
          simp [FiniteTM0.lookupAction, FiniteTM0.Rule.mk, hnonblank]
      | succ remaining =>
          simp only [nativeScanTableAux,
            FiniteTM0Program.lookupAction_append]
          rw [lookupAction_targetRules_of_not_matches _ _ _ _ hnot]
          have hblankKey :
              (state, symbol) ≠ (state, (blankSymbol : Symbol numTags)) := by
            intro heq
            exact hnonblank (congrArg Prod.snd heq)
          rw [FiniteTM0.lookupAction_cons_ne hblankKey]
          apply lookupAction_eq_none_of_state_not_mem
          intro htail
          have hb := source_mem_nativeScanTableAux htail
          omega
  | succ i ih =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          simp only [nativeScanTableAux,
            FiniteTM0Program.lookupAction_append]
          have hstateNe : state + (i + 1) ≠ state := by omega
          rw [lookupAction_targetRules_state_ne target hstateNe symbol]
          have hblankKey :
              (state + (i + 1), symbol) ≠
                (state, (blankSymbol : Symbol numTags)) := by
            intro heq
            exact hstateNe (congrArg Prod.fst heq)
          rw [FiniteTM0.lookupAction_cons_ne hblankKey]
          have htail := ih (state := state + 1) (remaining := remaining)
            (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Specialized disabled-read equation for the native bounded scan. -/
theorem lookup_nativeScanTable_other_at {numTags : Nat}
    (radius : Nat) (target : Target numTags) (direction : Turing.Dir)
    (progress : Nat) (hprogress : progress ≤ NestingMachine.bound radius)
    (symbol : Symbol numTags) (hnot : ¬ target.Matches symbol)
    (hnonblank : symbol ≠ blankSymbol) :
    FiniteTM0.lookupAction (nativeScanTable radius target direction)
        progress symbol = none := by
  simpa [nativeScanTable] using
    lookup_nativeScanTableAux_other_at target direction
      (NestingMachine.localSuccessState radius)
      (NestingMachine.localLaunchState radius) 0
      (NestingMachine.bound radius) progress symbol hprogress hnot hnonblank

/-! ## Scan positions in the complete machine -/

/-- Every advertised scan position really is a private-controller source. -/
theorem private_scan_position_source {numTags : Nat}
    (radius offset : Nat) (command : Command numTags) (progress : Nat)
    (hprogress : progress ≤ NestingMachine.bound radius) :
    offset + progress ∈ FiniteTM0.sourceStates
      (privateControllerTable radius offset command) := by
  have hlocal : progress ∈ FiniteTM0.sourceStates
      (nativeLocalTable radius command.target command.searchDirection) := by
    simp only [nativeLocalTable, FiniteTM0.sourceStates, List.map_append,
      List.mem_append]
    left
    by_cases hlt : progress < NestingMachine.bound radius
    · have hlookup := lookup_nativeScanTableAux_blank_at command.target
        command.searchDirection (NestingMachine.localSuccessState radius)
        (NestingMachine.localLaunchState radius) 0
        (NestingMachine.bound radius) progress hlt
      simp only [Nat.zero_add] at hlookup
      have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      exact List.mem_map.mpr ⟨_, hrule, rfl⟩
    · have heq : progress = NestingMachine.bound radius := by omega
      subst progress
      have hlookup := lookup_nativeScanTableAux_launch_at command.target
        command.searchDirection (NestingMachine.localSuccessState radius)
        (NestingMachine.localLaunchState radius) 0
        (NestingMachine.bound radius)
      simp only [Nat.zero_add] at hlookup
      have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      exact List.mem_map.mpr ⟨_, hrule, rfl⟩
  simp only [privateControllerTable, sourceStates_relocate, List.mem_map]
  exact ⟨progress, hlocal, rfl⟩

/-- Lookup in a relocated private controller at a scan position is just the
native scan lookup, with its result state relocated. -/
theorem lookupAction_privateController_scan {numTags : Nat}
    (radius offset : Nat) (command : Command numTags) (progress : Nat)
    (hprogress : progress ≤ NestingMachine.bound radius)
    (symbol : Symbol numTags) :
    FiniteTM0.lookupAction (privateControllerTable radius offset command)
        (offset + progress) symbol =
      (FiniteTM0.lookupAction
        (nativeScanTable radius command.target command.searchDirection)
        progress symbol).map (FiniteTM0Program.relocateResult offset) := by
  rw [privateControllerTable, FiniteTM0Program.lookupAction_relocate]
  simp only [nativeLocalTable, FiniteTM0Program.lookupAction_append]
  cases hscan : FiniteTM0.lookupAction
      (nativeScanTable radius command.target command.searchDirection)
      progress symbol with
  | some result => rfl
  | none =>
      simp only [Option.map_none]
      have hunwindNone : FiniteTM0.lookupAction
          (liftTable (numTags := numTags)
            (NestingMachine.unwindTable radius command.searchDirection))
          progress symbol = none := by
        apply lookupAction_eq_none_of_state_not_mem
        rw [sourceStates_liftTable]
        intro hunwind
        have hb := NestingMachine.source_mem_unwindTableAux
          (by simpa [NestingMachine.unwindTable] using hunwind)
        simp [NestingMachine.localUnwindState] at hb
        omega
      rw [hunwindNone]
      rfl

/-- At a private source, the continuation prefix cannot intercept lookup. -/
theorem lookupAction_commandTable_of_private {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (state : FiniteTM0.State) (symbol : Symbol numTags)
    (hprivate : state ∈ FiniteTM0.sourceStates
      (privateControllerTable radius offset command)) :
    FiniteTM0.lookupAction (commandTable radius offset sharedCore command)
        state symbol =
      FiniteTM0.lookupAction (privateControllerTable radius offset command)
        state symbol := by
  rw [commandTable, FiniteTM0Program.lookupAction_append]
  have hnone : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore command) state symbol = none :=
    lookupAction_eq_none_of_state_not_mem _ _ _
      (private_continuation_source_disjoint radius offset sharedCore command
        state hprivate)
  rw [hnone]

/-- Exact one-step classification of an arbitrary bounded-scan position in
the complete counter controller.  The only nonterminal possibilities are a
target handoff, a one-cell blank advance, or the final launch handoff. -/
theorem scan_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress : Nat)
    (hprogress : progress ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨commandOffset + progress, T⟩ ∨
      (command.target.Matches T.read ∧
        FullTM0.step (CounterControlNestingBridge.machine base c)
            ⟨commandOffset + progress, T⟩ =
          some ⟨foundState (CanonicalInitializer.radius c) commandOffset,
            T⟩) ∨
      (T.read = blankSymbol ∧
        ((progress < NestingMachine.bound (CanonicalInitializer.radius c) ∧
            FullTM0.step (CounterControlNestingBridge.machine base c)
                ⟨commandOffset + progress, T⟩ =
              some ⟨commandOffset + progress + 1,
                T.move command.searchDirection⟩) ∨
          (progress = NestingMachine.bound
              (CanonicalInitializer.radius c) ∧
            FullTM0.step (CounterControlNestingBridge.machine base c)
                ⟨commandOffset + progress, T⟩ =
              some ⟨launchState (CanonicalInitializer.radius c)
                commandOffset, T⟩))) := by
  let radius := CanonicalInitializer.radius c
  change progress ≤ NestingMachine.bound radius at hprogress
  have hprivate := private_scan_position_source radius commandOffset command
    progress hprogress
  have hcommand : commandOffset + progress ∈ FiniteTM0.sourceStates
      (commandTable radius commandOffset (controllerCoreEntry base c)
        command) := by
    simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
      List.mem_append]
    exact Or.inr hprivate
  have hfullLookup := lookupAction_table_of_commandAt base c hat
    (commandOffset + progress) T.read hcommand
  rw [lookupAction_commandTable_of_private radius commandOffset
    (controllerCoreEntry base c) command _ _ hprivate] at hfullLookup
  rw [lookupAction_privateController_scan radius commandOffset command
    progress hprogress T.read] at hfullLookup
  by_cases hmatch : command.target.Matches T.read
  · right
    left
    refine ⟨hmatch, ?_⟩
    have hscan := lookup_nativeScanTableAux_target_at command.target
      command.searchDirection (NestingMachine.localSuccessState radius)
      (NestingMachine.localLaunchState radius) 0
      (NestingMachine.bound radius) progress T.read hmatch hprogress
    simp only [Nat.zero_add] at hscan
    change FiniteTM0.lookupAction
      (nativeScanTable radius command.target command.searchDirection)
      progress T.read = _ at hscan
    rw [hscan] at hfullLookup
    change FullTM0.step (FiniteTM0.machine (CounterControlPlan.table base c))
      _ = _
    simp only [FullTM0.step, FiniteTM0.machine_apply]
    rw [hfullLookup]
    simp [FiniteTM0Program.relocateResult, foundState,
      NestingMachine.localSuccessState, radius]
    change T.write T.read = T
    exact tape_write_read T
  · by_cases hblank : T.read = blankSymbol
    · right
      right
      refine ⟨hblank, ?_⟩
      by_cases hlt : progress < NestingMachine.bound radius
      · left
        refine ⟨by simpa [radius] using hlt, ?_⟩
        have hscan := lookup_nativeScanTableAux_blank_at command.target
          command.searchDirection (NestingMachine.localSuccessState radius)
          (NestingMachine.localLaunchState radius) 0
          (NestingMachine.bound radius) progress hlt
        simp only [Nat.zero_add] at hscan
        change FiniteTM0.lookupAction
          (nativeScanTable radius command.target command.searchDirection)
          progress blankSymbol = _ at hscan
        rw [hblank, hscan] at hfullLookup
        change FullTM0.step
          (FiniteTM0.machine (CounterControlPlan.table base c)) _ = _
        simp only [FullTM0.step, FiniteTM0.machine_apply]
        rw [hblank, hfullLookup]
        cases command.searchDirection
        · simp only [Option.map_some, FiniteTM0Program.relocateResult,
            liftAction, MarkerMachine.moveAction,
            FiniteTM0.Action.toStmt_moveLeft]
          simp [Nat.add_assoc]
        · simp only [Option.map_some, FiniteTM0Program.relocateResult,
            liftAction, MarkerMachine.moveAction,
            FiniteTM0.Action.toStmt_moveRight]
          simp [Nat.add_assoc]
      · right
        have heq : progress = NestingMachine.bound radius := by omega
        refine ⟨by simpa [radius] using heq, ?_⟩
        have hscan := lookup_nativeScanTableAux_launch_at command.target
          command.searchDirection (NestingMachine.localSuccessState radius)
          (NestingMachine.localLaunchState radius) 0
          (NestingMachine.bound radius)
        simp only [Nat.zero_add] at hscan
        change FiniteTM0.lookupAction
          (nativeScanTable radius command.target command.searchDirection)
          (NestingMachine.bound radius) blankSymbol = _ at hscan
        rw [hblank, heq, hscan] at hfullLookup
        change FullTM0.step
          (FiniteTM0.machine (CounterControlPlan.table base c)) _ = _
        simp only [FullTM0.step, FiniteTM0.machine_apply]
        rw [heq, hblank, hfullLookup]
        simp [FiniteTM0Program.relocateResult, launchState,
          NestingMachine.localLaunchState]
        constructor
        · rfl
        · rw [← hblank]
          exact tape_write_read T
    · left
      have hscan := lookup_nativeScanTable_other_at radius command.target
        command.searchDirection progress hprogress T.read hmatch hblank
      rw [hscan] at hfullLookup
      simp only [Option.map_none] at hfullLookup
      refine ⟨⟨commandOffset + progress, T⟩,
        Relation.ReflTransGen.refl, ?_⟩
      change FullTM0.step
        (FiniteTM0.machine (CounterControlPlan.table base c)) _ = none
      simp only [FullTM0.step, FiniteTM0.machine_apply]
      rw [hfullLookup]
      rfl

/-- Every arbitrary entry into a private scan prefix finitely reaches its
`foundState`/`launchState` handoff or makes the complete controller halt.
No tape-shape invariant is assumed or concluded. -/
theorem scan_normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress : Nat)
    (hprogress : progress ≤
      NestingMachine.bound (CanonicalInitializer.radius c))
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨commandOffset + progress, T⟩ ∨
      (∃ U : FullTM0.Tape (Symbol numTags),
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨commandOffset + progress, T⟩
          ⟨foundState (CanonicalInitializer.radius c) commandOffset, U⟩) ∨
      ∃ U : FullTM0.Tape (Symbol numTags),
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨commandOffset + progress, T⟩
          ⟨launchState (CanonicalInitializer.radius c) commandOffset, U⟩ := by
  let bound := NestingMachine.bound (CanonicalInitializer.radius c)
  generalize hremaining : bound - progress = remaining
  induction remaining using Nat.strong_induction_on generalizing progress T with
  | h remaining ih =>
      rcases scan_step_or_haltsFrom base c hat progress hprogress T with
        hhalts | ⟨_hmatch, hfoundStep⟩ |
          ⟨_hblank, ⟨hlt, hadvanceStep⟩ | ⟨heq, hlaunchStep⟩⟩
      · exact Or.inl hhalts
      · right
        left
        exact ⟨T, Relation.ReflTransGen.single hfoundStep⟩
      · have hnextProgress : progress + 1 ≤ bound := by
          simpa [bound] using (Nat.succ_le_iff.mpr hlt)
        have hsmaller : bound - (progress + 1) < remaining := by
          rw [← hremaining]
          omega
        have hone : FullTM0.Reaches
            (CounterControlNestingBridge.machine base c)
            ⟨commandOffset + progress, T⟩
            ⟨commandOffset + (progress + 1),
              T.move command.searchDirection⟩ := by
          apply Relation.ReflTransGen.single
          simpa [Nat.add_assoc] using hadvanceStep
        rcases ih (bound - (progress + 1)) hsmaller (progress + 1)
            (by simpa [bound] using hnextProgress)
            (T.move command.searchDirection) rfl with
          htailHalts | ⟨U, hfound⟩ | ⟨U, hlaunch⟩
        · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone htailHalts)
        · exact Or.inr (Or.inl ⟨U, hone.trans hfound⟩)
        · exact Or.inr (Or.inr ⟨U, hone.trans hlaunch⟩)
      · right
        right
        exact ⟨T, Relation.ReflTransGen.single hlaunchStep⟩

end

end CounterControlControllerEntrySemantics
end Hooper
end Kari
end LeanWang
