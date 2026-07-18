/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDirectSemantics
import LeanWang.Kari.Hooper.CounterControlNestingBridge
import LeanWang.Kari.Hooper.FiniteTM0Halting

/-!
# Classifying arbitrary entries into the compiled counter controller

The mortality direction of Hooper's construction starts from an arbitrary
control state and an arbitrary bi-infinite tape.  Before using any tape-shape
invariant, one can reduce the possible control states to the three disjoint
tables assembled by the compiler:

* a private bounded-command block or directional return dispatcher;
* the shared canonical initializer;
* the direct one-cell counter glue.

Every other natural-number state is terminal immediately.  This file records
that classification, its numeric separation, and the consequence for every
state visited by a hypothetical immortal orbit.  Later local normalization
lemmas can therefore work component by component.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlArbitraryEntry

open Turing
open BoundedMarkerProgram CounterControlPlan

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The three top-level source regions of the complete generated table. -/
inductive SourceRegion (base : Nat) (c : Nat.Partrec.Code)
    (state : FiniteTM0.State) : Prop
  | controller
      (hsource : state ∈ FiniteTM0.sourceStates
        (BoundedMarkerProgram.controllerTable base
          (CanonicalInitializer.radius c) (commands base c)))
  | initializer
      (hsource : state ∈ FiniteTM0.sourceStates
        (initializerTable base c))
  | direct
      (hsource : state ∈ FiniteTM0.sourceStates (directTable base c))

/-- Membership in the source list of the complete table gives one of the
three compiler regions. -/
theorem sourceRegion_of_mem
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈
      FiniteTM0.sourceStates (CounterControlPlan.table base c)) :
    SourceRegion base c state := by
  simp only [CounterControlPlan.table, BoundedMarkerProgram.table, coreTable,
    FiniteTM0.sourceStates, List.map_append, List.mem_append] at hsource
  rcases hsource with hcontroller | hinitializer | hdirect
  · exact .controller hcontroller
  · exact .initializer hinitializer
  · exact .direct hdirect

/-- Every classified region is a source state of the complete table. -/
theorem mem_of_sourceRegion
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hregion : SourceRegion base c state) :
    state ∈ FiniteTM0.sourceStates (CounterControlPlan.table base c) := by
  cases hregion with
  | controller hsource =>
      simp only [CounterControlPlan.table, BoundedMarkerProgram.table,
        coreTable, FiniteTM0.sourceStates, List.map_append,
        List.mem_append]
      exact Or.inl hsource
  | initializer hsource =>
      simp only [CounterControlPlan.table, BoundedMarkerProgram.table,
        coreTable, FiniteTM0.sourceStates, List.map_append,
        List.mem_append]
      exact Or.inr (Or.inl hsource)
  | direct hsource =>
      simp only [CounterControlPlan.table, BoundedMarkerProgram.table,
        coreTable, FiniteTM0.sourceStates, List.map_append,
        List.mem_append]
      exact Or.inr (Or.inr hsource)

theorem sourceRegion_iff_mem
    (base : Nat) (c : Nat.Partrec.Code) (state : FiniteTM0.State) :
    SourceRegion base c state ↔
      state ∈ FiniteTM0.sourceStates (CounterControlPlan.table base c) :=
  ⟨mem_of_sourceRegion base c, sourceRegion_of_mem base c⟩

/-! ## Refining bounded-command sources -/

/-- A source in the concatenated command family belongs to one concrete
command block, with its exact list prefix determining the relocated offset. -/
theorem commandTables_source_witness {numTags radius sharedCore offset source}
    {commandList : List (Command numTags)}
    (hsource : source ∈ FiniteTM0.sourceStates
      (commandTables radius sharedCore offset commandList)) :
    ∃ before command after,
      commandList = before ++ command :: after ∧
      source ∈ FiniteTM0.sourceStates
        (commandTable radius
          (offset + before.length * blockWidth radius)
          sharedCore command) := by
  induction commandList generalizing offset with
  | nil =>
      simp [commandTables, FiniteTM0.sourceStates] at hsource
  | cons first rest ih =>
      rw [commandTables] at hsource
      change source ∈
        (commandTable radius offset sharedCore first ++
          commandTables radius sharedCore (offset + blockWidth radius)
            rest).map (fun rule => rule.1.1) at hsource
      rw [List.map_append, List.mem_append] at hsource
      rcases hsource with hfirst | hrest
      · refine ⟨[], first, rest, by simp, ?_⟩
        simpa only [List.length_nil, Nat.zero_mul, Nat.add_zero,
          FiniteTM0.sourceStates] using hfirst
      · rcases ih hrest with ⟨before, command, after, hlist, hlocal⟩
        refine ⟨first :: before, command, after, ?_, ?_⟩
        · simp [hlist]
        · simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hlocal

/-- Inside one concrete command block, a source is either in the relocated
bounded scan/unwind controller, or is one of the six reserved continuation
states. -/
theorem command_source_private_or_continuation {numTags radius offset
    sharedCore source} {command : Command numTags}
    (hsource : source ∈ FiniteTM0.sourceStates
      (commandTable radius offset sharedCore command)) :
    source ∈ FiniteTM0.sourceStates
        (privateControllerTable radius offset command) ∨
      source = launchState radius offset ∨
      source = foundState radius offset ∨
      source = clearState radius offset ∨
      source = verifyState radius offset ∨
      source = departState radius offset ∨
      source = resumeState radius offset := by
  simp only [commandTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hsource
  rcases hsource with hcontinuation | hprivate
  · right
    exact source_mem_continuationTable_exact hcontinuation
  · exact Or.inl hprivate

/-- A source in the bounded-controller component belongs either to one exact
relocated command block or to one of the two directional return dispatchers. -/
theorem controller_source_command_or_return
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates
      (BoundedMarkerProgram.controllerTable base
        (CanonicalInitializer.radius c) (commands base c))) :
    (∃ before command after,
        commands base c = before ++ command :: after ∧
        state ∈ FiniteTM0.sourceStates
          (commandTable (CanonicalInitializer.radius c)
            (base + before.length *
              blockWidth (CanonicalInitializer.radius c))
            (controllerCoreEntry base c) command)) ∨
      ∃ direction, state = controllerReturn base c direction := by
  rw [controllerTable] at hsource
  change state ∈
    (commandTables (CanonicalInitializer.radius c)
          (coreEntry base (CanonicalInitializer.radius c) (commands base c))
          base (commands base c) ++
      returnTable (CanonicalInitializer.radius c)
          (returnState base (CanonicalInitializer.radius c) (commands base c))
          base (commands base c)).map (fun rule => rule.1.1) at hsource
  rw [List.map_append, List.mem_append] at hsource
  rcases hsource with hcommands | hreturn
  · left
    have hwitness := commandTables_source_witness hcommands
    simpa [controllerCoreEntry_eq base c] using hwitness
  · right
    rcases source_mem_returnTable hreturn with ⟨direction, hstate⟩
    refine ⟨direction, ?_⟩
    calc
      state = returnState base (CanonicalInitializer.radius c)
          (commands base c) direction := hstate
      _ = controllerReturn base c direction :=
        controllerReturn_eq base c direction

/-- Every rule in a directional return table comes from one exact command
and its list-prefix offset. -/
theorem returnTable_rule_witness {numTags radius sharedReturn offset}
    {commandList : List (Command numTags)}
    {tableRule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : tableRule ∈
      returnTable radius sharedReturn offset commandList) :
    ∃ before command after,
      commandList = before ++ command :: after ∧
      tableRule =
        FiniteTM0.Rule.mk (sharedReturn command.searchDirection)
          (tagSymbol command.returnTag)
          (resumeState radius
            (offset + before.length * blockWidth radius))
          (.write blankSymbol) := by
  induction commandList generalizing offset with
  | nil => simp [returnTable] at hrule
  | cons first rest ih =>
      simp only [returnTable, List.mem_cons] at hrule
      rcases hrule with hfirst | hrest
      · refine ⟨[], first, rest, by simp, ?_⟩
        simpa using hfirst
      · rcases ih hrest with ⟨before, command, after, hlist, htable⟩
        refine ⟨first :: before, command, after, ?_, ?_⟩
        · simp [hlist]
        · simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using htable

/-- The two concrete return-state addresses are distinct. -/
theorem controllerReturn_injective (base : Nat) (c : Nat.Partrec.Code) :
    Function.Injective (controllerReturn base c) := by
  intro first second hstate
  cases first <;> cases second <;>
    simp [controllerReturn, BoundedMarkerProgram.commandOffset] at hstate ⊢

/-- A complete-table rule whose source is a directional return dispatcher is
necessarily the return rule of a command searching in that same direction. -/
theorem table_rule_at_controllerReturn
    (base : Nat) (c : Nat.Partrec.Code) (direction : Turing.Dir)
    {tableRule : FiniteTM0.Rule (AlphabetSize numTags)}
    (hrule : tableRule ∈ CounterControlPlan.table base c)
    (hsource : tableRule.1.1 = controllerReturn base c direction) :
    ∃ before command after,
      commands base c = before ++ command :: after ∧
      command.searchDirection = direction ∧
      tableRule =
        FiniteTM0.Rule.mk (controllerReturn base c direction)
          (tagSymbol command.returnTag)
          (resumeState (CanonicalInitializer.radius c)
            (base + before.length *
              blockWidth (CanonicalInitializer.radius c)))
          (.write blankSymbol) := by
  simp only [CounterControlPlan.table, BoundedMarkerProgram.table,
    coreTable, controllerTable, List.mem_append] at hrule
  rcases hrule with (hcommands | hreturn) | (hinitializer | hdirect)
  · have hcommandSource : tableRule.1.1 ∈ FiniteTM0.sourceStates
        (commandTables (CanonicalInitializer.radius c)
          (coreEntry base (CanonicalInitializer.radius c) (commands base c))
          base (commands base c)) :=
      List.mem_map.mpr ⟨tableRule, hcommands, rfl⟩
    have hbounds := source_mem_commandTables hcommandSource
    rw [hsource] at hbounds
    cases direction <;>
      simp [controllerReturn, BoundedMarkerProgram.commandOffset] at hbounds
  · have hreturnStateEq :
        returnState base (CanonicalInitializer.radius c) (commands base c) =
          controllerReturn base c := by
      funext growth
      exact controllerReturn_eq base c growth
    have hreturn' : tableRule ∈
        returnTable (CanonicalInitializer.radius c) (controllerReturn base c)
          base (commands base c) := by
      simpa only [hreturnStateEq] using hreturn
    rcases returnTable_rule_witness hreturn' with
      ⟨before, command, after, hlist, htable⟩
    have hdirection : command.searchDirection = direction := by
      apply controllerReturn_injective base c
      have := congrArg (fun rule => rule.1.1) htable
      symm
      simpa [hsource] using this
    refine ⟨before, command, after, hlist, hdirection, ?_⟩
    simpa [hdirection] using htable
  · have hi := CanonicalInitializerProgram.source_mem_table
        (List.mem_map.mpr ⟨tableRule, hinitializer, rfl⟩)
    have hreturnLt : controllerReturn base c direction <
        controllerCoreEntry base c := by
      rw [← controllerReturn_eq base c direction,
        ← controllerCoreEntry_eq base c]
      exact returnState_lt_coreEntry base (CanonicalInitializer.radius c)
        (commands base c) direction
    rw [hsource] at hi
    exact False.elim ((Nat.not_lt_of_ge hi.1) hreturnLt)
  · have hd := CounterControlDeterministic.source_mem_directTable
        (List.mem_map.mpr ⟨tableRule, hdirect, rfl⟩)
    have hreturnLt : controllerReturn base c direction <
        controllerCoreEntry base c := by
      rw [← controllerReturn_eq base c direction,
        ← controllerCoreEntry_eq base c]
      exact returnState_lt_coreEntry base (CanonicalInitializer.radius c)
        (commands base c) direction
    have hentryEnd : controllerCoreEntry base c ≤ initializerEnd base c := by
      simp [initializerEnd, CanonicalInitializerProgram.exitState]
      omega
    rw [hsource] at hd
    exact False.elim
      ((Nat.not_lt_of_ge (hentryEnd.trans hd)) hreturnLt)

/-- Local semantic normalization at either directional return dispatcher.
An enabled transition uniquely identifies a command with the matching search
direction and enters its relocated resume state; otherwise the arbitrary
configuration is terminal immediately. -/
theorem return_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩ ∨
      ∃ before command after,
        commands base c = before ++ command :: after ∧
        command.searchDirection = direction ∧
        T.read = tagSymbol command.returnTag ∧
        FullTM0.step (CounterControlNestingBridge.machine base c)
            ⟨controllerReturn base c direction, T⟩ =
          some ⟨resumeState (CanonicalInitializer.radius c)
              (base + before.length *
                blockWidth (CanonicalInitializer.radius c)),
            T.write blankSymbol⟩ := by
  classical
  cases hlookup : FiniteTM0.lookupAction (CounterControlPlan.table base c)
      (controllerReturn base c direction) T.read with
  | none =>
      left
      refine ⟨⟨controllerReturn base c direction, T⟩,
        Relation.ReflTransGen.refl, ?_⟩
      have hmachine : CounterControlNestingBridge.machine base c
          (controllerReturn base c direction) T.read = none := by
        simp only [CounterControlNestingBridge.machine,
          BoundedMarkerProgram.machine, FiniteTM0.machine]
        change FiniteTM0.lookupAction
          (BoundedMarkerProgram.table base (CanonicalInitializer.radius c)
            (commands base c) (coreTable base c))
          (controllerReturn base c direction) T.read = none at hlookup
        rw [hlookup]
        rfl
      unfold FullTM0.step
      rw [hmachine]
      rfl
  | some result =>
      right
      rcases result with ⟨target, action⟩
      have htableMem :
          FiniteTM0.Rule.mk (controllerReturn base c direction) T.read
              target action ∈ CounterControlPlan.table base c :=
        FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      rcases table_rule_at_controllerReturn base c direction htableMem rfl with
        ⟨before, command, after, hlist, hdirection, htableEq⟩
      have hread : T.read = tagSymbol command.returnTag := by
        exact congrArg (fun rule => rule.1.2) htableEq
      have hknownMem :
          FiniteTM0.Rule.mk (controllerReturn base c direction)
              (tagSymbol command.returnTag)
              (resumeState (CanonicalInitializer.radius c)
                (base + before.length *
                  blockWidth (CanonicalInitializer.radius c)))
              (.write blankSymbol) ∈ CounterControlPlan.table base c := by
        rw [← htableEq]
        exact htableMem
      have hknownLookup : FiniteTM0.lookupAction
          (CounterControlPlan.table base c)
          (controllerReturn base c direction) (tagSymbol command.returnTag) =
        some (resumeState (CanonicalInitializer.radius c)
            (base + before.length *
              blockWidth (CanonicalInitializer.radius c)),
          .write blankSymbol) :=
        (FiniteTM0.lookupAction_eq_some_iff_of_deterministic
          (CounterControlDeterministic.table_deterministic base c)).2 hknownMem
      refine ⟨before, command, after, hlist, hdirection, hread, ?_⟩
      change FullTM0.step (FiniteTM0.machine (CounterControlPlan.table base c))
          ⟨controllerReturn base c direction, T⟩ = _
      simp only [FullTM0.step, FiniteTM0.machine_apply]
      rw [hread, hknownLookup]
      rfl

/-! ## Numeric separation of the regions -/

/-- Controller sources lie strictly before the shared initializer entry. -/
theorem controller_lt_coreEntry
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates
      (BoundedMarkerProgram.controllerTable base
        (CanonicalInitializer.radius c) (commands base c))) :
    state < controllerCoreEntry base c := by
  simpa [controllerCoreEntry_eq base c] using
    (BoundedMarkerProgram.source_mem_controllerTable hsource)

/-- Initializer sources occupy their advertised half-open interval. -/
theorem initializer_bounds
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈
      FiniteTM0.sourceStates (initializerTable base c)) :
    controllerCoreEntry base c ≤ state ∧ state < initializerEnd base c := by
  exact CanonicalInitializerProgram.source_mem_table hsource

/-- Direct-glue sources begin only after the entire initializer. -/
theorem initializerEnd_le_direct
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates (directTable base c)) :
    initializerEnd base c ≤ state := by
  exact CounterControlDeterministic.source_mem_directTable hsource

/-- A direct-region source is the resolved source reference of an actual
generated one-cell rule.  This exposes the finite symbolic object that the
next normalization layer must analyze. -/
theorem direct_source_witness
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates (directTable base c)) :
    ∃ rule ∈ rawDirectRules, state = resolve base c rule.source := by
  simp only [directTable, FiniteTM0.sourceStates, List.map_flatMap,
    List.mem_flatMap] at hsource
  rcases hsource with ⟨rule, hrule, hlocal⟩
  refine ⟨rule, hrule, ?_⟩
  simp only [directRuleTable, List.map_map, List.mem_map,
    FiniteTM0.Rule.mk, Function.comp_apply] at hlocal
  rcases hlocal with ⟨symbol, _hsymbol, heq⟩
  exact heq.symm

/-- Direct glue can only be entered at a logical counter state or at one of
the finitely generated internal direct addresses; it never aliases a bounded
search entry or a directional return dispatcher. -/
theorem direct_source_logical_or_internal
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates (directTable base c)) :
    (∃ growth counterState,
        state = logicalState base c growth counterState) ∨
      ∃ address, state = directState base c address := by
  rcases direct_source_witness base c hsource with ⟨rule, hrule, hstate⟩
  have hcounter :=
    CounterControlDeterministic.rawDirectRules_counter_sources rule hrule
  cases hreference : rule.source with
  | logical growth counterState =>
      left
      exact ⟨growth, counterState, by simpa [hreference, resolve] using hstate⟩
  | direct address =>
      right
      exact ⟨address, by simpa [hreference, resolve] using hstate⟩
  | search address => simp [hreference,
      CounterControlDeterministic.IsCounterSource] at hcounter
  | sharedReturn direction => simp [hreference,
      CounterControlDeterministic.IsCounterSource] at hcounter

/-- The source reference of every generated direct rule satisfies the
compiler's allocation bounds. -/
theorem rawDirectRule_source_wellFormed
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules) :
    CounterControlDeterministic.WellFormedSource rule.source := by
  have hsymbols : ∃ symbol, symbol ∈ symbolsForRead rule.read := by
    cases rule.read with
    | blank => exact ⟨blankSymbol, by simp [symbolsForRead]⟩
    | boundary label =>
        exact ⟨boundarySymbol label, by simp [symbolsForRead]⟩
    | nonblank =>
        exact ⟨boundarySymbol ⟨0, by decide⟩, by
          simp [symbolsForRead, nonblankSymbols]⟩
  rcases hsymbols with ⟨symbol, hsymbol⟩
  have hkey : (rule.source, symbol) ∈
      CounterControlDeterministic.rawDirectControlKeys :=
    CounterControlDeterministic.mem_rawDirectControlKeys rule hrule symbol
      hsymbol
  exact CounterControlDeterministic.rawDirectControlKeys_wellFormed hkey

/-- Refined direct-region classification with the bounds that make the two
forms genuine allocated counter states. -/
theorem direct_source_logical_or_internal_bounded
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hsource : state ∈ FiniteTM0.sourceStates (directTable base c)) :
    (∃ growth counterState,
        counterState < logicalSpan ∧
          state = logicalState base c growth counterState) ∨
      ∃ address,
        address.counterState < logicalSpan ∧
          address.slot < directStride ∧
          state = directState base c address := by
  rcases direct_source_witness base c hsource with ⟨rule, hrule, hstate⟩
  have hwell := rawDirectRule_source_wellFormed rule hrule
  cases hreference : rule.source with
  | logical growth counterState =>
      left
      refine ⟨growth, counterState, ?_, ?_⟩
      · simpa [hreference,
          CounterControlDeterministic.WellFormedSource] using hwell
      · simpa [hreference, resolve] using hstate
  | direct address =>
      right
      have hbounds : address.counterState < logicalSpan ∧
          address.slot < directStride := by
        simpa [hreference,
          CounterControlDeterministic.WellFormedSource] using hwell
      refine ⟨address, ?_, ?_, ?_⟩
      · exact hbounds.1
      · exact hbounds.2
      · simpa [hreference, resolve] using hstate
  | search address => simp [hreference,
      CounterControlDeterministic.WellFormedSource] at hwell
  | sharedReturn direction => simp [hreference,
      CounterControlDeterministic.WellFormedSource] at hwell

/-- At a direct-glue source, an arbitrary scanned symbol either enables one
exact generated symbolic rule, or the complete machine halts immediately.
This is the local semantic normalization theorem for the direct region. -/
theorem direct_step_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code) (state : FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hsource : state ∈ FiniteTM0.sourceStates (directTable base c)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
        ⟨state, T⟩ ∨
      ∃ rule ∈ rawDirectRules,
        state = resolve base c rule.source ∧
        rule.read.Matches T.read ∧
        FullTM0.step (CounterControlNestingBridge.machine base c)
            ⟨state, T⟩ =
          some ⟨resolve base c rule.target,
            T.move (orient rule.growth rule.direction)⟩ := by
  classical
  by_cases henabled : ∃ rule ∈ rawDirectRules,
      state = resolve base c rule.source ∧ rule.read.Matches T.read
  · right
    rcases henabled with ⟨rule, hrule, hstate, hmatch⟩
    refine ⟨rule, hrule, hstate, hmatch, ?_⟩
    have hstep := CounterControlDirectSemantics.step_directRule
      base c rule hrule T hmatch
    simpa [hstate, CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table] using hstep
  · left
    have hkey : (state, T.read) ∉
        (CounterControlPlan.table base c).map Prod.fst := by
      intro hkey
      rcases List.mem_map.mp hkey with ⟨tableRule, htableRule, hreadKey⟩
      have htableSource : tableRule.1.1 = state :=
        congrArg Prod.fst hreadKey
      simp only [CounterControlPlan.table, BoundedMarkerProgram.table,
        coreTable, List.mem_append] at htableRule
      rcases htableRule with hcontroller | hinitializer | hdirect
      · have hcontrollerSource : state ∈ FiniteTM0.sourceStates
            (BoundedMarkerProgram.controllerTable base
              (CanonicalInitializer.radius c) (commands base c)) := by
          exact List.mem_map.mpr
            ⟨tableRule, hcontroller, htableSource⟩
        have hc := controller_lt_coreEntry base c hcontrollerSource
        have hd := initializerEnd_le_direct base c hsource
        have hentryEnd : controllerCoreEntry base c ≤
            initializerEnd base c := by
          simp [initializerEnd, CanonicalInitializerProgram.exitState]
          omega
        exact (Nat.not_lt_of_ge (hentryEnd.trans hd)) hc
      · have hinitializerSource : state ∈ FiniteTM0.sourceStates
            (initializerTable base c) := by
          exact List.mem_map.mpr
            ⟨tableRule, hinitializer, htableSource⟩
        have hi := (initializer_bounds base c hinitializerSource).2
        have hd := initializerEnd_le_direct base c hsource
        exact (Nat.not_lt_of_ge hd) hi
      · simp only [directTable, List.mem_flatMap] at hdirect
        rcases hdirect with ⟨rule, hrule, hconcrete⟩
        simp only [directRuleTable, List.mem_map] at hconcrete
        rcases hconcrete with ⟨symbol, hsymbol, htableEq⟩
        have hconcreteKey :
            (resolve base c rule.source, symbol) = tableRule.1 :=
          congrArg Prod.fst htableEq
        have hkeyEq : (resolve base c rule.source, symbol) =
            (state, T.read) := hconcreteKey.trans hreadKey
        apply henabled
        refine ⟨rule, hrule, ?_, ?_⟩
        · exact (congrArg Prod.fst hkeyEq).symm
        · apply (RawRead.mem_symbolsForRead_iff rule.read T.read).1
          have hsymbolEq : symbol = T.read := congrArg Prod.snd hkeyEq
          rw [← hsymbolEq]
          exact hsymbol
    have hlookup : FiniteTM0.lookupAction
        (CounterControlPlan.table base c) state T.read = none :=
      FiniteTM0.lookupAction_eq_none_of_key_not_mem hkey
    refine ⟨⟨state, T⟩, Relation.ReflTransGen.refl, ?_⟩
    have hmachine : CounterControlNestingBridge.machine base c
        state T.read = none := by
      simp only [CounterControlNestingBridge.machine,
        BoundedMarkerProgram.machine, FiniteTM0.machine]
      change FiniteTM0.lookupAction
          (BoundedMarkerProgram.table base (CanonicalInitializer.radius c)
            (commands base c) (coreTable base c)) state T.read = none
        at hlookup
      rw [hlookup]
      rfl
    unfold FullTM0.step
    rw [hmachine]
    rfl

/-- The compiler's three source-region constructors are pairwise disjoint.
This is useful when a later local semantic argument identifies a numeric
state and must recover its unique owner. -/
theorem sourceRegion_exclusive
    (base : Nat) (c : Nat.Partrec.Code) {state : FiniteTM0.State}
    (hfirst hsecond : SourceRegion base c state) :
    hfirst = hsecond := by
  cases hfirst with
  | controller hcontroller =>
      cases hsecond with
      | controller hcontroller' => rfl
      | initializer hinitializer =>
          have hc := controller_lt_coreEntry base c hcontroller
          have hi := (initializer_bounds base c hinitializer).1
          exact False.elim ((Nat.not_lt_of_ge hi) hc)
      | direct hdirect =>
          have hc := controller_lt_coreEntry base c hcontroller
          have hd := initializerEnd_le_direct base c hdirect
          have hentryEnd : controllerCoreEntry base c ≤ initializerEnd base c := by
            simp [initializerEnd, CanonicalInitializerProgram.exitState]
            omega
          exact False.elim
            ((Nat.not_lt_of_ge (hentryEnd.trans hd)) hc)
  | initializer hinitializer =>
      cases hsecond with
      | controller hcontroller =>
          have hi := (initializer_bounds base c hinitializer).1
          have hc := controller_lt_coreEntry base c hcontroller
          exact False.elim ((Nat.not_lt_of_ge hi) hc)
      | initializer hinitializer' => rfl
      | direct hdirect =>
          have hi := (initializer_bounds base c hinitializer).2
          have hd := initializerEnd_le_direct base c hdirect
          exact False.elim ((Nat.not_lt_of_ge hd) hi)
  | direct hdirect =>
      cases hsecond with
      | controller hcontroller =>
          have hc := controller_lt_coreEntry base c hcontroller
          have hd := initializerEnd_le_direct base c hdirect
          have hentryEnd : controllerCoreEntry base c ≤ initializerEnd base c := by
            simp [initializerEnd, CanonicalInitializerProgram.exitState]
            omega
          exact False.elim
            ((Nat.not_lt_of_ge (hentryEnd.trans hd)) hc)
      | initializer hinitializer =>
          have hi := (initializer_bounds base c hinitializer).2
          have hd := initializerEnd_le_direct base c hdirect
          exact False.elim ((Nat.not_lt_of_ge hd) hi)
      | direct hdirect' => rfl

/-! ## Arbitrary configurations and immortal orbits -/

/-- An arbitrary full-tape configuration is either in one of the three
generated source regions or halts immediately. -/
theorem sourceRegion_or_haltsFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) :
    SourceRegion base c cfg.q ∨
      FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) cfg := by
  rcases FiniteTM0Halting.state_mem_or_haltsFrom
      (CounterControlPlan.table base c) cfg with hsource | hhalts
  · exact Or.inl (sourceRegion_of_mem base c hsource)
  · exact Or.inr (by
      simpa [CounterControlNestingBridge.machine,
        BoundedMarkerProgram.machine, CounterControlPlan.table] using hhalts)

/-- The initial state of any hypothetical immortal arbitrary configuration
belongs to one of the three generated regions. -/
theorem sourceRegion_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cfg) :
    SourceRegion base c cfg.q := by
  apply sourceRegion_of_mem base c
  apply FiniteTM0Halting.state_mem_of_immortalFrom
    (CounterControlPlan.table base c) cfg
  simpa [CounterControlNestingBridge.machine,
    BoundedMarkerProgram.machine, CounterControlPlan.table] using himmortal

/-- Every configuration reached from a hypothetical immortal arbitrary entry
is still owned by one of the three compiler regions. -/
theorem reachable_sourceRegion_of_immortalFrom
    (base : Nat) (c : Nat.Partrec.Code)
    {start current : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start current) :
    SourceRegion base c current.q := by
  have himmortal' : FullTM0.ImmortalFrom
      (FiniteTM0.machine (CounterControlPlan.table base c)) start := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table] using himmortal
  have hreach' : FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) start current := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table] using hreach
  exact sourceRegion_of_mem base c
    (FiniteTM0Halting.reachable_state_mem_of_immortalFrom
      (CounterControlPlan.table base c) himmortal' hreach')

end

end CounterControlArbitraryEntry
end Hooper
end Kari
end LeanWang
