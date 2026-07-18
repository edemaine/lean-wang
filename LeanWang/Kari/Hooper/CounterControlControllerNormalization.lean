/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlControllerEntrySemantics
import LeanWang.Kari.Hooper.BoundedMarkerContinuation

/-!
# Finite normalization of arbitrary controller entries

This file completes the state-local part of Hooper's arbitrary-entry
argument.  No framed-tape hypothesis is used: private unwind positions,
continuation positions, and return dispatchers either halt or reach a genuine
compiler handoff after finitely many steps.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlControllerNormalization

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlArbitraryEntry
open CounterControlControllerEntrySemantics

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem lookup_none_of_state_not_mem {numSymbols : Nat}
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

@[simp] private theorem tape_write_read {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) : T.write T.read = T := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.read, FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

/-! ## Arbitrary private-unwind entries -/

private theorem unwindTableAux_rule_read_blank
    (direction : Turing.Dir) (search state remaining : Nat)
    {rule : FiniteTM0.Rule MarkerMachine.AlphabetSize}
    (hrule : rule ∈
      NestingMachine.unwindTableAux direction search remaining state) :
    rule.1.2 = MarkerMachine.blankSymbol := by
  induction remaining generalizing state with
  | zero =>
      simp only [NestingMachine.unwindTableAux, List.mem_singleton] at hrule
      subst rule
      rfl
  | succ remaining ih =>
      simp only [NestingMachine.unwindTableAux, List.mem_cons] at hrule
      rcases hrule with hfirst | hrest
      · subst rule
        rfl
      · exact ih (state + 1) hrest

private theorem lookup_liftUnwind_nonblank {numTags : Nat}
    (radius : Nat) (direction : Turing.Dir) (state : FiniteTM0.State)
    (symbol : Symbol numTags) (hnonblank : symbol ≠ blankSymbol) :
    FiniteTM0.lookupAction
        (liftTable (numTags := numTags)
          (NestingMachine.unwindTable radius direction))
        state symbol = none := by
  apply FiniteTM0.lookupAction_eq_none_of_key_not_mem
  simp only [liftTable, List.map_map, List.mem_map, liftRule,
    FiniteTM0.Rule.mk, Function.comp_apply]
  rintro ⟨rule, hrule, heq⟩
  apply hnonblank
  have hread := unwindTableAux_rule_read_blank direction 0
    (NestingMachine.localUnwindState radius) radius
    (by simpa [NestingMachine.unwindTable] using hrule)
  have hsymbol := congrArg Prod.snd heq
  simpa [hread, blankSymbol_eq_baseSymbol] using hsymbol.symm

/-- Every exact unwind position is a source of the relocated private block. -/
theorem private_unwind_position_source {numTags : Nat}
    (radius offset : Nat) (command : Command numTags) (progress : Nat)
    (hprogress : progress ≤ radius) :
    offset + NestingMachine.localUnwindState radius + progress ∈
      FiniteTM0.sourceStates
        (privateControllerTable radius offset command) := by
  have hunwind : NestingMachine.localUnwindState radius + progress ∈
      FiniteTM0.sourceStates
        (NestingMachine.unwindTable radius command.searchDirection) := by
    by_cases hlt : progress < radius
    · have hlookup := NestingMachine.lookup_unwindTableAux_move_at
        command.searchDirection 0 (NestingMachine.localUnwindState radius)
        radius progress hlt
      have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      exact List.mem_map.mpr ⟨_, hrule, rfl⟩
    · have heq : progress = radius := by omega
      subst progress
      have hlookup := NestingMachine.lookup_unwindTableAux_finish_at
        command.searchDirection 0 (NestingMachine.localUnwindState radius)
        radius
      have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      exact List.mem_map.mpr ⟨_, hrule, rfl⟩
  have hlocal : NestingMachine.localUnwindState radius + progress ∈
      FiniteTM0.sourceStates
        (nativeLocalTable radius command.target command.searchDirection) := by
    simp only [nativeLocalTable, FiniteTM0.sourceStates, List.map_append,
      List.mem_append]
    right
    change NestingMachine.localUnwindState radius + progress ∈
      FiniteTM0.sourceStates
        (liftTable (NestingMachine.unwindTable radius command.searchDirection))
    rw [sourceStates_liftTable]
    exact hunwind
  simp only [privateControllerTable, sourceStates_relocate, List.mem_map]
  refine ⟨NestingMachine.localUnwindState radius + progress,
    hlocal, ?_⟩
  omega

/-- Lookup at an exact private unwind position is lookup in the lifted
finite unwind table, with the result state relocated. -/
theorem lookupAction_privateController_unwind {numTags : Nat}
    (radius offset : Nat) (command : Command numTags) (progress : Nat)
    (_hprogress : progress ≤ radius) (symbol : Symbol numTags) :
    FiniteTM0.lookupAction (privateControllerTable radius offset command)
        (offset + NestingMachine.localUnwindState radius + progress) symbol =
      (FiniteTM0.lookupAction
        (liftTable (numTags := numTags)
          (NestingMachine.unwindTable radius command.searchDirection))
        (NestingMachine.localUnwindState radius + progress) symbol).map
          (FiniteTM0Program.relocateResult offset) := by
  rw [show offset + NestingMachine.localUnwindState radius + progress =
      offset + (NestingMachine.localUnwindState radius + progress) by omega]
  rw [privateControllerTable, FiniteTM0Program.lookupAction_relocate]
  simp only [nativeLocalTable, FiniteTM0Program.lookupAction_append]
  have hscanNone : FiniteTM0.lookupAction
      (nativeScanTable radius command.target command.searchDirection)
      (NestingMachine.localUnwindState radius + progress) symbol = none := by
    apply lookup_none_of_state_not_mem
    intro hscan
    have hb := source_mem_nativeScanTableAux
      (by simpa [nativeScanTable] using hscan)
    simp [NestingMachine.localUnwindState] at hb
    omega
  rw [hscanNone]

/-- One unwind step either halts on a nonblank symbol, advances one cell back
through the fixed path, or returns to this command's bounded-search entry. -/
theorem unwind_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress : Nat)
    (hprogress : progress ≤ CanonicalInitializer.radius c)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨commandOffset + NestingMachine.localUnwindState
          (CanonicalInitializer.radius c) + progress, T⟩ ∨
      (T.read = blankSymbol ∧
        ((progress < CanonicalInitializer.radius c ∧
            FullTM0.step (CounterControlNestingBridge.machine base c)
              ⟨commandOffset + NestingMachine.localUnwindState
                  (CanonicalInitializer.radius c) + progress, T⟩ =
                some ⟨commandOffset + NestingMachine.localUnwindState
                    (CanonicalInitializer.radius c) + progress + 1,
                  T.move (NestingMachine.opposite command.searchDirection)⟩) ∨
          (progress = CanonicalInitializer.radius c ∧
            FullTM0.step (CounterControlNestingBridge.machine base c)
              ⟨commandOffset + NestingMachine.localUnwindState
                  (CanonicalInitializer.radius c) + progress, T⟩ =
                some ⟨entryState (CanonicalInitializer.radius c)
                  commandOffset, T⟩))) := by
  let radius := CanonicalInitializer.radius c
  change progress ≤ radius at hprogress
  have hprivate := private_unwind_position_source radius commandOffset command
    progress hprogress
  have hcommand : commandOffset + NestingMachine.localUnwindState radius +
      progress ∈ FiniteTM0.sourceStates
        (commandTable radius commandOffset (controllerCoreEntry base c)
          command) := by
    simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
      List.mem_append]
    exact Or.inr hprivate
  have hfullLookup := lookupAction_table_of_commandAt base c hat
    (commandOffset + NestingMachine.localUnwindState radius + progress)
    T.read hcommand
  rw [lookupAction_commandTable_of_private radius commandOffset
    (controllerCoreEntry base c) command _ _ hprivate] at hfullLookup
  rw [lookupAction_privateController_unwind radius commandOffset command
    progress hprogress T.read] at hfullLookup
  by_cases hblank : T.read = blankSymbol
  · right
    refine ⟨hblank, ?_⟩
    rw [hblank, blankSymbol_eq_baseSymbol,
      lookupAction_liftTable] at hfullLookup
    by_cases hlt : progress < radius
    · left
      refine ⟨by simpa [radius] using hlt, ?_⟩
      have hunwind := NestingMachine.lookup_unwindTableAux_move_at
        command.searchDirection 0 (NestingMachine.localUnwindState radius)
        radius progress hlt
      change FiniteTM0.lookupAction
        (NestingMachine.unwindTable radius command.searchDirection)
        (NestingMachine.localUnwindState radius + progress)
        MarkerMachine.blankSymbol = _ at hunwind
      rw [hunwind] at hfullLookup
      change FullTM0.step
        (FiniteTM0.machine (CounterControlPlan.table base c)) _ = _
      simp only [FullTM0.step, FiniteTM0.machine_apply]
      rw [show T.read = baseSymbol MarkerMachine.blankSymbol by
          rw [hblank, blankSymbol_eq_baseSymbol], hfullLookup]
      cases command.searchDirection <;>
        simp [liftResult, FiniteTM0Program.relocateResult, liftAction,
          MarkerMachine.moveAction, NestingMachine.opposite,
          Nat.add_assoc, radius]
    · right
      have heq : progress = radius := by omega
      refine ⟨by simpa [radius] using heq, ?_⟩
      have hunwind := NestingMachine.lookup_unwindTableAux_finish_at
        command.searchDirection 0 (NestingMachine.localUnwindState radius)
        radius
      change FiniteTM0.lookupAction
        (NestingMachine.unwindTable radius command.searchDirection)
        (NestingMachine.localUnwindState radius + radius)
        MarkerMachine.blankSymbol = _ at hunwind
      rw [heq, hunwind] at hfullLookup
      change FullTM0.step
        (FiniteTM0.machine (CounterControlPlan.table base c)) _ = _
      simp only [FullTM0.step, FiniteTM0.machine_apply]
      rw [heq, show T.read = baseSymbol MarkerMachine.blankSymbol by
          rw [hblank, blankSymbol_eq_baseSymbol], hfullLookup]
      simp [liftResult, FiniteTM0Program.relocateResult,
        liftAction, entryState]
      rw [← blankSymbol_eq_baseSymbol, ← hblank]
      exact tape_write_read T
  · left
    have hnone := lookup_liftUnwind_nonblank radius command.searchDirection
      (NestingMachine.localUnwindState radius + progress) T.read hblank
    rw [hnone] at hfullLookup
    simp only [Option.map_none] at hfullLookup
    refine ⟨_, Relation.ReflTransGen.refl, ?_⟩
    change FullTM0.step
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ = none
    simp only [FullTM0.step, FiniteTM0.machine_apply]
    rw [hfullLookup]
    rfl

/-- An arbitrary private unwind entry finitely returns to the command's
search entry or halts. -/
theorem unwind_normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (progress : Nat) (hprogress : progress ≤ CanonicalInitializer.radius c)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨commandOffset + NestingMachine.localUnwindState
          (CanonicalInitializer.radius c) + progress, T⟩ ∨
      ∃ U : FullTM0.Tape (Symbol numTags),
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨commandOffset + NestingMachine.localUnwindState
            (CanonicalInitializer.radius c) + progress, T⟩
          ⟨entryState (CanonicalInitializer.radius c) commandOffset, U⟩ := by
  let radius := CanonicalInitializer.radius c
  generalize hremaining : radius - progress = remaining
  induction remaining using Nat.strong_induction_on generalizing progress T with
  | h remaining ih =>
      rcases unwind_step_or_haltsFrom base c hat progress hprogress T with
        hhalts | ⟨_hblank, ⟨hlt, hstep⟩ | ⟨heq, hstep⟩⟩
      · exact Or.inl hhalts
      · have hnext : progress + 1 ≤ radius := by
          simpa [radius] using (Nat.succ_le_iff.mpr hlt)
        have hsmaller : radius - (progress + 1) < remaining := by
          rw [← hremaining]
          omega
        have hone : FullTM0.Reaches
            (CounterControlNestingBridge.machine base c)
            ⟨commandOffset + NestingMachine.localUnwindState radius +
                progress, T⟩
            ⟨commandOffset + NestingMachine.localUnwindState radius +
                (progress + 1),
              T.move (NestingMachine.opposite command.searchDirection)⟩ := by
          apply Relation.ReflTransGen.single
          simpa [Nat.add_assoc] using hstep
        rcases ih (radius - (progress + 1)) hsmaller (progress + 1)
            (by simpa [radius] using hnext)
            (T.move (NestingMachine.opposite command.searchDirection)) rfl with
          htail | ⟨U, hreach⟩
        · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone htail)
        · exact Or.inr ⟨U, hone.trans hreach⟩
      · exact Or.inr ⟨T, Relation.ReflTransGen.single hstep⟩

/-! ## Arbitrary continuation entries -/

/-- At a continuation source, the disjoint private controller cannot
intercept a disabled continuation lookup. -/
theorem lookupAction_commandTable_of_continuation {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    (state : FiniteTM0.State) (symbol : Symbol numTags)
    (hcontinuation : state ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command)) :
    FiniteTM0.lookupAction (commandTable radius offset sharedCore command)
        state symbol =
      FiniteTM0.lookupAction
        (continuationTable radius offset sharedCore command) state symbol := by
  rw [commandTable, FiniteTM0Program.lookupAction_append]
  cases hlookup : FiniteTM0.lookupAction
      (continuationTable radius offset sharedCore command) state symbol with
  | some result => rfl
  | none =>
      have hprivateNone : FiniteTM0.lookupAction
          (privateControllerTable radius offset command) state symbol = none :=
        lookup_none_of_state_not_mem _ _ _ (by
          intro hprivate
          exact private_continuation_source_disjoint radius offset sharedCore
            command state hprivate hcontinuation)
      rw [hprivateNone]

/-- Genuine macro handoffs of one command continuation.  The tape is left
unconstrained: arbitrary entry may have skipped any earlier continuation
actions. -/
inductive ContinuationExit {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    FiniteTM0.State → Prop
  | core : ContinuationExit radius offset sharedCore command sharedCore
  | entry : ContinuationExit radius offset sharedCore command
      (entryState radius offset)
  | success : ContinuationExit radius offset sharedCore command
      command.successState
  | collision (move : MarkerProgram.Move) (success : FiniteTM0.State)
      (returnTag : Fin numTags) (departure : Option Turing.Dir)
      (collision : FiniteTM0.State)
      (hcommand : command = .markerShift move success returnTag departure
        (some collision)) :
      ContinuationExit radius offset sharedCore command collision

/-- Every continuation rule either reaches a declared macro handoff or
advances strictly to another source of the same finite continuation table. -/
theorem continuationRule_exits_or_advances {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags)
    {rule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : rule ∈ continuationTable radius offset sharedCore command) :
    ContinuationExit radius offset sharedCore command rule.2.1 ∨
      (rule.1.1 < rule.2.1 ∧
        rule.2.1 ∈ FiniteTM0.sourceStates
          (continuationTable radius offset sharedCore command)) := by
  have hedge : (rule.1.1, rule.2.1) ∈
      (continuationTable radius offset sharedCore command).map
        (fun tableRule => (tableRule.1.1, tableRule.2.1)) :=
    List.mem_map.mpr ⟨rule, hrule, rfl⟩
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve =>
          simp [continuationTable, targetRules] at hedge
          rcases hedge with hcore | hsuccess | hentry
          · rw [hcore.2]
            exact Or.inl .core
          · rw [hsuccess.2]
            exact Or.inl .success
          · rw [hentry.2]
            exact Or.inl .entry
      | erase departure =>
          cases departure with
          | none =>
              simp [continuationTable] at hedge
              rcases hedge with hcore | hsuccess | hentry
              · rw [hcore.2]
                exact Or.inl .core
              · rw [hsuccess.2]
                exact Or.inl .success
              · rw [hentry.2]
                exact Or.inl .entry
          | some departure =>
              simp [continuationTable] at hedge
              rcases hedge with hcore | hinternal | hsuccess | hentry
              · rw [hcore.2]
                exact Or.inl .core
              · rcases hinternal with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simpa [foundState, departState, clearState,
                    NestingMachine.localSuccessState,
                    NestingMachine.localWidth, NestingMachine.bound, two_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.lt_add_of_pos_right
                      (n := offset + (radius + 1 + 1))
                      (k := radius + 5) (by positivity))
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rw [hsuccess.2]
                exact Or.inl .success
              · rw [hentry.2]
                exact Or.inl .entry
  | tagNavigation direction success returnTag =>
      simp [continuationTable, targetRules] at hedge
      rcases hedge with hcore | hsuccess | hentry
      · rw [hcore.2]
        exact Or.inl .core
      · rcases hsuccess with ⟨_, _, htarget⟩
        rw [← htarget]
        exact Or.inl .success
      · rw [hentry.2]
        exact Or.inl .entry
  | markerShift move success returnTag departure collisionState =>
      cases departure with
      | none =>
          cases collisionState with
          | none =>
              simp [continuationTable] at hedge
              rcases hedge with hcore | hclear | hverify | hsuccess | hentry
              · rw [hcore.2]
                exact Or.inl .core
              · rcases hclear with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simpa [foundState, clearState,
                    NestingMachine.localSuccessState,
                    NestingMachine.localWidth, NestingMachine.bound, two_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.lt_add_of_pos_right
                      (n := offset + 2) (k := radius + 3) (by positivity))
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hverify with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simp [clearState, verifyState]
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rw [hsuccess.2]
                exact Or.inl .success
              · rw [hentry.2]
                exact Or.inl .entry
          | some collision =>
              simp [continuationTable, collisionRules] at hedge
              rcases hedge with hcore | hclear | hverify | hsuccess |
                  hcollision | hentry
              · rw [hcore.2]
                exact Or.inl .core
              · rcases hclear with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simpa [foundState, clearState,
                    NestingMachine.localSuccessState,
                    NestingMachine.localWidth, NestingMachine.bound, two_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.lt_add_of_pos_right
                      (n := offset + 2) (k := radius + 3) (by positivity))
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hverify with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simp [clearState, verifyState]
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rw [hsuccess.2]
                exact Or.inl .success
              · rcases hcollision with ⟨_, _, htarget⟩
                rw [← htarget]
                exact Or.inl (.collision move success returnTag none collision rfl)
              · rw [hentry.2]
                exact Or.inl .entry
      | some departure =>
          cases collisionState with
          | none =>
              simp [continuationTable] at hedge
              rcases hedge with hcore | hclear | hverify | hdepart |
                  hsuccess | hentry
              · rw [hcore.2]
                exact Or.inl .core
              · rcases hclear with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simpa [foundState, clearState,
                    NestingMachine.localSuccessState,
                    NestingMachine.localWidth, NestingMachine.bound, two_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.lt_add_of_pos_right
                      (n := offset + 2) (k := radius + 3) (by positivity))
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hverify with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simp [clearState, verifyState]
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hdepart with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simp [verifyState, departState]
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rw [hsuccess.2]
                exact Or.inl .success
              · rw [hentry.2]
                exact Or.inl .entry
          | some collision =>
              simp [continuationTable, collisionRules] at hedge
              rcases hedge with hcore | hclear | hverify | hdepart |
                  hcollision | hsuccess | hentry
              · rw [hcore.2]
                exact Or.inl .core
              · rcases hclear with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simpa [foundState, clearState,
                    NestingMachine.localSuccessState,
                    NestingMachine.localWidth, NestingMachine.bound, two_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.lt_add_of_pos_right
                      (n := offset + 2) (k := radius + 3) (by positivity))
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hverify with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simp [clearState, verifyState]
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hdepart with ⟨hsource, htarget⟩
                rw [hsource, htarget]
                right
                constructor
                · simp [verifyState, departState]
                · simp [FiniteTM0.sourceStates, continuationTable]
              · rcases hcollision with ⟨_, _, htarget⟩
                rw [← htarget]
                exact Or.inl
                  (.collision move success returnTag (some departure)
                    collision rfl)
              · rw [hsuccess.2]
                exact Or.inl .success
              · rw [hentry.2]
                exact Or.inl .entry

/-- One complete-machine step from a continuation source either is absent,
reaches a declared macro handoff, or advances strictly within the same
finite continuation table. -/
theorem continuation_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset state : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : state ∈ FiniteTM0.sourceStates
      (continuationTable (CanonicalInitializer.radius c) commandOffset
        (controllerCoreEntry base c) command)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨state, T⟩ ∨
      ∃ next : FullTM0.Cfg (Symbol numTags) FiniteTM0.State,
        FullTM0.step (CounterControlNestingBridge.machine base c)
            ⟨state, T⟩ = some next ∧
          (ContinuationExit (CanonicalInitializer.radius c) commandOffset
              (controllerCoreEntry base c) command next.q ∨
            (state < next.q ∧
              next.q ∈ FiniteTM0.sourceStates
                (continuationTable (CanonicalInitializer.radius c)
                  commandOffset (controllerCoreEntry base c) command))) := by
  let radius := CanonicalInitializer.radius c
  have hcommand : state ∈ FiniteTM0.sourceStates
      (commandTable radius commandOffset (controllerCoreEntry base c)
        command) := by
    simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
      List.mem_append]
    exact Or.inl hsource
  have hfullEq := lookupAction_table_of_commandAt base c hat state T.read
    (by simpa [radius] using hcommand)
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
      have hcommandLookup : FiniteTM0.lookupAction
          (commandTable radius commandOffset (controllerCoreEntry base c)
            command) state T.read = some (target, action) := by
        rw [← hfullEq]
        exact hlookup
      have hcontinuationLookup : FiniteTM0.lookupAction
          (continuationTable radius commandOffset
            (controllerCoreEntry base c) command) state T.read =
            some (target, action) := by
        rw [← lookupAction_commandTable_of_continuation radius
          commandOffset (controllerCoreEntry base c) command state T.read
          (by simpa [radius] using hsource)]
        exact hcommandLookup
      have hrule : FiniteTM0.Rule.mk state T.read target action ∈
          continuationTable radius commandOffset
            (controllerCoreEntry base c) command :=
        FiniteTM0.rule_mem_of_lookupAction_eq_some hcontinuationLookup
      have hclass := continuationRule_exits_or_advances radius commandOffset
        (controllerCoreEntry base c) command hrule
      let next : FullTM0.Cfg (Symbol numTags) FiniteTM0.State :=
        ⟨target, FiniteTM0Path.applyAction action T⟩
      refine ⟨next, ?_, ?_⟩
      · change FullTM0.step
          (FiniteTM0.machine (CounterControlPlan.table base c))
            ⟨state, T⟩ = some next
        simp only [FullTM0.step, FiniteTM0.machine_apply]
        rw [hlookup]
        cases action <;> rfl
      · simpa [next, FiniteTM0.Rule.mk, radius] using hclass

/-- An arbitrary entry at any of the six reserved continuation states
finitely reaches a genuine compiler handoff or halts. -/
theorem continuation_normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code) {commandOffset state : Nat}
    {command : Command numTags}
    (hat : CommandAt (CanonicalInitializer.radius c) base commandOffset
      command (commands base c))
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : state ∈ FiniteTM0.sourceStates
      (continuationTable (CanonicalInitializer.radius c) commandOffset
        (controllerCoreEntry base c) command)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨state, T⟩ ∨
      ∃ finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            ⟨state, T⟩ finish ∧
          ContinuationExit (CanonicalInitializer.radius c) commandOffset
            (controllerCoreEntry base c) command finish.q := by
  let radius := CanonicalInitializer.radius c
  generalize hmeasure : commandOffset + blockWidth radius - state = distance
  induction distance using Nat.strong_induction_on generalizing state T with
  | h distance ih =>
      rcases continuation_step_or_haltsFrom base c hat T hsource with
        hhalts | ⟨next, hstep, hexit | ⟨hadvance, hnextSource⟩⟩
      · exact Or.inl hhalts
      · exact Or.inr
          ⟨next, Relation.ReflTransGen.single hstep, hexit⟩
      · have hone : FullTM0.Reaches
            (CounterControlNestingBridge.machine base c) ⟨state, T⟩ next :=
          Relation.ReflTransGen.single hstep
        have hnextUpper : next.q < commandOffset + blockWidth radius :=
          (source_mem_continuationTable_bounds
            (by simpa [radius] using hnextSource)).2
        have hsmaller : commandOffset + blockWidth radius - next.q <
            distance := by
          rw [← hmeasure]
          exact Nat.sub_lt_sub_left (hadvance.trans hnextUpper) hadvance
        rcases ih (commandOffset + blockWidth radius - next.q) hsmaller
            (state := next.q) next.tape
            (by simpa [radius] using hnextSource) rfl with
          htail | ⟨finish, hreach, hexit⟩
        · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone htail)
        · exact Or.inr ⟨finish, hone.trans hreach, hexit⟩

/-! ## Arbitrary return-dispatcher entries -/

/-- A list decomposition canonically determines the selected command's
block offset. -/
theorem commandAt_append {numTags : Nat} (radius base : Nat)
    (before : List (Command numTags)) (command : Command numTags)
    (after : List (Command numTags)) :
    CommandAt radius base (base + before.length * blockWidth radius)
      command (before ++ command :: after) := by
  induction before generalizing base with
  | nil =>
      simpa using CommandAt.head (radius := radius) base command after
  | cons first before ih =>
      apply CommandAt.tail
      simpa [Nat.succ_mul, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
        using ih (base := base + blockWidth radius)

/-- The failed-search launch handoff is always a continuation source. -/
theorem launchState_mem_continuationTable {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    launchState radius offset ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command) := by
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve => simp [continuationTable, FiniteTM0.sourceStates]
      | erase departure =>
          cases departure <;>
            simp [continuationTable, FiniteTM0.sourceStates]
  | tagNavigation direction success returnTag =>
      simp [continuationTable, FiniteTM0.sourceStates]
  | markerShift move success returnTag departure collision =>
      cases departure <;> cases collision <;>
        simp [continuationTable, FiniteTM0.sourceStates]

/-- The successful bounded-search handoff is always a continuation source.
For tag navigation, the command's own return tag witnesses that the tag
alphabet is nonempty. -/
theorem foundState_mem_continuationTable {numTags : Nat}
    (radius offset sharedCore : Nat) (command : Command numTags) :
    foundState radius offset ∈ FiniteTM0.sourceStates
      (continuationTable radius offset sharedCore command) := by
  cases command with
  | boundaryNavigation expected direction success returnTag action =>
      cases action with
      | preserve =>
          simp [continuationTable, targetRules, FiniteTM0.sourceStates]
      | erase departure =>
          cases departure <;>
            simp [continuationTable, FiniteTM0.sourceStates]
  | tagNavigation direction success returnTag =>
      simp [continuationTable, targetRules, FiniteTM0.sourceStates]
      exact Or.inr (Or.inl ⟨returnTag⟩)
  | markerShift move success returnTag departure collision =>
      cases departure <;> cases collision <;>
        simp [continuationTable, FiniteTM0.sourceStates]

/-- An arbitrary return-dispatcher entry either halts on an unrecognized
symbol, or clears a recognized command tag and finitely reaches that
command's honest bounded-search entry. -/
theorem return_normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩ ∨
      ∃ before command after U,
        commands base c = before ++ command :: after ∧
          command.searchDirection = direction ∧
          FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            ⟨controllerReturn base c direction, T⟩
            ⟨entryState (CanonicalInitializer.radius c)
                (base + before.length *
                  blockWidth (CanonicalInitializer.radius c)), U⟩ := by
  rcases return_step_or_haltsFrom base c direction T with
    hhalts | ⟨before, command, after, hlist, hdirection, _hread, hstep⟩
  · exact Or.inl hhalts
  · let radius := CanonicalInitializer.radius c
    let commandOffset := base + before.length * blockWidth radius
    have hat : CommandAt radius base commandOffset command
        (commands base c) := by
      rw [hlist]
      exact commandAt_append radius base before command after
    have hone : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩
        ⟨resumeState radius commandOffset, T.write blankSymbol⟩ := by
      apply Relation.ReflTransGen.single
      simpa [radius, commandOffset] using hstep
    have hresume : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resumeState radius commandOffset, T.write blankSymbol⟩
        ⟨entryState radius commandOffset,
          (T.write blankSymbol).move command.searchDirection⟩ := by
      change FullTM0.Reaches
        (BoundedMarkerProgram.machine base radius (commands base c)
          (coreTable base c)) _ _
      exact machine_resume_reaches (coreTable base c) hat
        (T.write blankSymbol) (FullTM0.Tape.read_write blankSymbol T)
    right
    refine ⟨before, command, after,
      (T.write blankSymbol).move command.searchDirection,
      hlist, hdirection, ?_⟩
    simpa [FullTM0.Reaches, StateTransition.Reaches, radius, commandOffset]
      using hone.trans hresume

/-! ## Complete controller normalization -/

/-- Honest exits from the finite controller region, retaining the selected
command decomposition needed by later compiler-resolution proofs. -/
def ControllerExit (base : Nat) (c : Nat.Partrec.Code)
    (state : FiniteTM0.State) : Prop :=
  ∃ before command after,
    commands base c = before ++ command :: after ∧
      ContinuationExit (CanonicalInitializer.radius c)
        (base + before.length *
          blockWidth (CanonicalInitializer.radius c))
        (controllerCoreEntry base c) command state

/-- Structural classification of a controller exit.  In the non-core cases
the exact selected command block is retained as a `CommandAt` witness. -/
theorem ControllerExit.state_cases
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hexit : ControllerExit base c state) :
    state = controllerCoreEntry base c ∨
      ∃ commandOffset command,
        CommandAt (CanonicalInitializer.radius c) base commandOffset command
            (commands base c) ∧
          (state = entryState (CanonicalInitializer.radius c) commandOffset ∨
            state = command.successState ∨
            ∃ move success returnTag departure collision,
              command = .markerShift move success returnTag departure
                (some collision) ∧
              state = collision) := by
  rcases hexit with ⟨before, command, after, hlist, hcontinuation⟩
  let radius := CanonicalInitializer.radius c
  let commandOffset := base + before.length * blockWidth radius
  have hat : CommandAt radius base commandOffset command
      (commands base c) := by
    rw [hlist]
    exact commandAt_append radius base before command after
  cases hcontinuation with
  | core => exact Or.inl rfl
  | entry =>
      exact Or.inr ⟨commandOffset, command, hat, Or.inl (by
        simp [radius, commandOffset])⟩
  | success =>
      exact Or.inr ⟨commandOffset, command, hat, Or.inr (Or.inl rfl)⟩
  | collision => aesop

private theorem controllerExit_of_continuation
    (base : Nat) (c : Nat.Partrec.Code) (before after)
    (command : Command numTags) (state : FiniteTM0.State)
    (hlist : commands base c = before ++ command :: after)
    (hexit : ContinuationExit (CanonicalInitializer.radius c)
      (base + before.length * blockWidth (CanonicalInitializer.radius c))
      (controllerCoreEntry base c) command state) :
    ControllerExit base c state := by
  exact ⟨before, command, after, hlist, hexit⟩

/-- Every arbitrary source configuration owned by the finite controller
either reaches a terminal configuration, or finitely reaches a genuine
command/compiler handoff.  No frame or tape-shape property is asserted. -/
theorem controller_normalizes_arbitrary_entry
    (base : Nat) (c : Nat.Partrec.Code) (state : FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : state ∈ FiniteTM0.sourceStates
      (BoundedMarkerProgram.controllerTable base
        (CanonicalInitializer.radius c) (commands base c))) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨state, T⟩ ∨
      ∃ finish : FullTM0.Cfg (Symbol numTags) FiniteTM0.State,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            ⟨state, T⟩ finish ∧
          ControllerExit base c finish.q := by
  rcases controller_source_command_or_return base c hsource with
    ⟨before, command, after, hlist, hcommandSource⟩ |
      ⟨direction, hreturn⟩
  · let radius := CanonicalInitializer.radius c
    let commandOffset := base + before.length * blockWidth radius
    have hat : CommandAt radius base commandOffset command
        (commands base c) := by
      rw [hlist]
      exact commandAt_append radius base before command after
    rw [commandTable] at hcommandSource
    change state ∈
      (continuationTable radius commandOffset (controllerCoreEntry base c)
          command ++ privateControllerTable radius commandOffset command).map
        (fun rule => rule.1.1) at hcommandSource
    rw [List.map_append, List.mem_append] at hcommandSource
    rcases hcommandSource with hcontinuation | hprivate
    · rcases continuation_normalizes_arbitrary_entry base c hat T
          hcontinuation with
        hhalts | ⟨finish, hreach, hexit⟩
      · exact Or.inl hhalts
      · right
        refine ⟨finish, hreach, ?_⟩
        apply controllerExit_of_continuation base c before after command
        · exact hlist
        · simpa [radius, commandOffset] using hexit
    · rcases private_source_scan_or_unwind hprivate with
        ⟨progress, hprogress, hstate⟩ |
          ⟨progress, hprogress, hstate⟩
      · subst state
        rcases scan_normalizes_arbitrary_entry base c hat progress
            (by simpa [radius] using hprogress) T with
          hhalts | ⟨U, hfound⟩ | ⟨U, hlaunch⟩
        · exact Or.inl hhalts
        · have hfoundSource : foundState radius commandOffset ∈
              FiniteTM0.sourceStates
                (continuationTable radius commandOffset
                  (controllerCoreEntry base c) command) :=
            foundState_mem_continuationTable radius commandOffset
              (controllerCoreEntry base c) command
          rcases continuation_normalizes_arbitrary_entry base c hat U
              (by simpa [radius] using hfoundSource) with
            htail | ⟨finish, hreach, hexit⟩
          · exact Or.inl
              (FullTM0.HaltsFrom.of_reaches hfound htail)
          · right
            refine ⟨finish, hfound.trans hreach, ?_⟩
            apply controllerExit_of_continuation base c before after command
            · exact hlist
            · simpa [radius, commandOffset] using hexit
        · have hlaunchSource : launchState radius commandOffset ∈
              FiniteTM0.sourceStates
                (continuationTable radius commandOffset
                  (controllerCoreEntry base c) command) :=
            launchState_mem_continuationTable radius commandOffset
              (controllerCoreEntry base c) command
          rcases continuation_normalizes_arbitrary_entry base c hat U
              (by simpa [radius] using hlaunchSource) with
            htail | ⟨finish, hreach, hexit⟩
          · exact Or.inl
              (FullTM0.HaltsFrom.of_reaches hlaunch htail)
          · right
            refine ⟨finish, hlaunch.trans hreach, ?_⟩
            apply controllerExit_of_continuation base c before after command
            · exact hlist
            · simpa [radius, commandOffset] using hexit
      · subst state
        rcases unwind_normalizes_arbitrary_entry base c hat progress
            (by simpa [radius] using hprogress) T with
          hhalts | ⟨U, hreach⟩
        · exact Or.inl hhalts
        · right
          refine ⟨⟨entryState radius commandOffset, U⟩, ?_, ?_⟩
          · simpa [radius, commandOffset] using hreach
          · apply controllerExit_of_continuation base c before after command
            · exact hlist
            · simpa [radius, commandOffset] using
                (ContinuationExit.entry (radius := radius)
                  (offset := commandOffset)
                  (sharedCore := controllerCoreEntry base c)
                  (command := command))
  · subst state
    rcases return_normalizes_arbitrary_entry base c direction T with
      hhalts | ⟨before, command, after, U, hlist, _hdirection, hreach⟩
    · exact Or.inl hhalts
    · right
      refine ⟨⟨entryState (CanonicalInitializer.radius c)
          (base + before.length *
            blockWidth (CanonicalInitializer.radius c)), U⟩,
        hreach, ?_⟩
      apply controllerExit_of_continuation base c before after command
      · exact hlist
      · exact .entry

end

end CounterControlControllerNormalization
end Hooper
end Kari
end LeanWang
