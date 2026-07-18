/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlArbitraryMortality

/-!
# Eliminating arbitrary command-continuation handoffs

The finite controller may hand an arbitrary entry to the declared success or
collision state of a generated bounded command.  This file inverts that
command back to the symbolic counter-control plan and follows the resulting
logical, search, direct, or shared-return continuation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlCommandContinuationMortality

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The symbolic success reference retained before command compilation. -/
def rawSuccessRef : RawCommand → ControlRef
  | .boundaryNavigation _ _ _ success _ => success
  | .tagNavigation _ _ success => success
  | .markerShift _ _ _ _ success _ _ => success

/-- The optional symbolic collision reference retained before command
compilation. -/
def rawCollisionRef : RawCommand → Option ControlRef
  | .boundaryNavigation .. => none
  | .tagNavigation .. => none
  | .markerShift _ _ _ _ _ _ collision => collision

/-- Every honest continuation reference is either a bounded logical state,
a symbolic search, a bounded internal direct address, or one of the two
shared return dispatchers.  A symbolic search is later split according to
whether its address occurs in the generated command list; a missing address
numerically aliases the first return dispatcher and is normalized there. -/
def HonestRef (reference : ControlRef) : Prop :=
  (∃ growth state, state < logicalSpan ∧
    reference = .logical growth state) ∨
  (∃ address, reference = .search address) ∨
  (∃ address, address.counterState < logicalSpan ∧
    address.slot < directStride ∧ reference = .direct address) ∨
  ∃ growth, reference = .sharedReturn growth

/-- Local form of `HonestRef`, before a generated counter rule is embedded
in the two global oriented lists. -/
private def LocalHonestRef (growth : Turing.Dir)
    (programRule : CounterMachine.Rule) (reference : ControlRef) : Prop :=
  (∃ state, state ∈ ruleStates programRule ∧
    reference = .logical growth state) ∨
  (∃ address, reference = .search address) ∨
  (∃ address, address.counterState ∈ ruleStates programRule ∧
    address.slot < directStride ∧ reference = .direct address) ∨
  reference = .sharedReturn growth

set_option maxHeartbeats 500000 in
-- The fixed compiler expansion has 16 instruction/orientation cases.
private theorem successRef_local_honest
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (raw : RawCommand) (hraw : raw ∈ commandsForRule growth programRule) :
    LocalHonestRef growth programRule (rawSuccessRef raw) := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register target =>
      cases growth <;> cases register <;>
        simp_all [commandsForRule, validationCommands, routeCommandsAux,
          incrementCommands, incrementShiftCommands,
          incrementShiftCommandsAux, cleanupCommands,
          MarkerValidation.sweep, MarkerShift.incrementOrder,
          AnchoredCounterGeometry.routeFromIncrement,
          LocalHonestRef, rawSuccessRef, bodyEntry, directRef, searchRef,
          instructionTargets, ruleStates, directStride] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, validationDirectBase] at * <;> aesop
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp_all [commandsForRule, validationCommands, routeCommandsAux,
          decrementCommands, decrementShiftCommands,
          decrementShiftCommandsAux, MarkerValidation.sweep,
          MarkerShift.decrementOrder,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero,
          LocalHonestRef, rawSuccessRef, bodyEntry, directRef, searchRef,
          instructionTargets, ruleStates, directStride] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, validationDirectBase, zeroDirectBase] at * <;>
        aesop

private theorem honest_of_local
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (hprogram : programRule ∈ GlobalSourceProgram.program)
    (reference : ControlRef)
    (hlocal : LocalHonestRef growth programRule reference) :
    HonestRef reference := by
  rcases hlocal with
    ⟨state, hstate, href⟩ | ⟨address, href⟩ |
      ⟨address, hstate, hslot, href⟩ | href
  · left
    refine ⟨growth, state, ?_, href⟩
    apply state_lt_logicalSpan
    simp only [programStates, List.mem_flatMap]
    exact ⟨programRule, hprogram, hstate⟩
  · right
    left
    exact ⟨address, href⟩
  · right
    right
    left
    refine ⟨address, ?_, hslot, href⟩
    apply state_lt_logicalSpan
    simp only [programStates, List.mem_flatMap]
    exact ⟨programRule, hprogram, hstate⟩
  · right
    right
    right
    exact ⟨growth, href⟩

private theorem successRef_honest_for
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (hprogram : programRule ∈ GlobalSourceProgram.program)
    (raw : RawCommand)
    (hraw : raw ∈ commandsForRule growth programRule) :
    HonestRef (rawSuccessRef raw) :=
  honest_of_local growth programRule hprogram (rawSuccessRef raw)
    (successRef_local_honest growth programRule raw hraw)

/-- The success reference of every generated raw command is honest. -/
theorem successRef_honest (raw : RawCommand)
    (hraw : raw ∈ rawCommands) : HonestRef (rawSuccessRef raw) := by
  simp only [rawCommands, rawCommandsFor, List.mem_append,
    List.mem_flatMap] at hraw
  rcases hraw with ⟨programRule, hprogram, hcommand⟩ |
      ⟨programRule, hprogram, hcommand⟩
  · exact successRef_honest_for .right programRule hprogram raw hcommand
  · exact successRef_honest_for .left programRule hprogram raw hcommand

set_option maxHeartbeats 500000 in
-- As above, discharge the finite collision-reference table generated for all
-- oriented source instructions.
private theorem collisionRef_local_honest
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (raw : RawCommand) (hraw : raw ∈ commandsForRule growth programRule)
    (reference : ControlRef)
    (hcollision : rawCollisionRef raw = some reference) :
    LocalHonestRef growth programRule reference := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register target =>
      cases growth <;> cases register <;>
        simp_all [commandsForRule, validationCommands, routeCommandsAux,
          incrementCommands, incrementShiftCommands,
          incrementShiftCommandsAux, cleanupCommands,
          MarkerValidation.sweep, MarkerShift.incrementOrder,
          AnchoredCounterGeometry.routeFromIncrement,
          LocalHonestRef, rawCollisionRef, bodyEntry, directRef, searchRef,
          instructionTargets, ruleStates, directStride] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, validationDirectBase] at * <;> aesop
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp_all [commandsForRule, validationCommands, routeCommandsAux,
          decrementCommands, decrementShiftCommands,
          decrementShiftCommandsAux, MarkerValidation.sweep,
          MarkerShift.decrementOrder,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero,
          LocalHonestRef, rawCollisionRef, bodyEntry, directRef, searchRef,
          instructionTargets, ruleStates, directStride] <;> aesop

/-- Every populated collision reference of a generated command is honest. -/
theorem collisionRef_honest (raw : RawCommand)
    (hraw : raw ∈ rawCommands) (reference : ControlRef)
    (hcollision : rawCollisionRef raw = some reference) :
    HonestRef reference := by
  simp only [rawCommands, rawCommandsFor, List.mem_append,
    List.mem_flatMap] at hraw
  rcases hraw with ⟨programRule, hprogram, hcommand⟩ |
      ⟨programRule, hprogram, hcommand⟩
  · exact honest_of_local .right programRule hprogram reference
      (collisionRef_local_honest .right programRule raw hcommand reference
        hcollision)
  · exact honest_of_local .left programRule hprogram reference
      (collisionRef_local_honest .left programRule raw hcommand reference
        hcollision)

/-- Compilation resolves exactly the raw symbolic success reference. -/
theorem compileRawCommand_successState (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c raw hraw).successState =
      resolve base c (rawSuccessRef raw) := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  cases raw <;> rfl

/-- A populated compiled collision exit comes from one populated symbolic
collision reference. -/
theorem exists_collisionRef_of_compileRawCommand_eq_markerShift
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (move : MarkerProgram.Move) (success collision : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (heq : CounterControlCommandAt.compileRawCommand base c raw hraw =
      .markerShift move success returnTag departure (some collision)) :
    ∃ reference, rawCollisionRef raw = some reference ∧
      collision = resolve base c reference := by
  rw [CounterControlCommandAt.compileRawCommand_spec] at heq
  cases raw with
  | boundaryNavigation => simp [CounterControlCommandAt.compileRawAtTag] at heq
  | tagNavigation => simp [CounterControlCommandAt.compileRawAtTag] at heq
  | markerShift address expected search shift rawSuccess rawDeparture
      rawCollision =>
      cases rawCollision with
      | none => simp [CounterControlCommandAt.compileRawAtTag] at heq
      | some reference =>
          refine ⟨reference, rfl, ?_⟩
          have hop := congrArg (fun command => match command with
              | .markerShift _ _ _ _ collision => collision
              | _ => none) heq
          change some (resolve base c reference) = some collision at hop
          exact (Option.some.inj hop).symm

set_option maxHeartbeats 500000 in
-- The target table is another finite expansion over the same 16 oriented
-- instruction cases.
private theorem directTarget_local_honest
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (rule : RawDirectRule)
    (hrule : rule ∈ directRulesForRule growth programRule) :
    LocalHonestRef growth programRule rule.target := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register target =>
      cases growth <;> cases register <;>
        simp_all [directRulesForRule, validationRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, incrementRules,
          AnchoredCounterGeometry.routeFromIncrement,
          MarkerValidation.sweep, LocalHonestRef, directRef, searchRef,
          instructionTargets, ruleStates, directStride] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, validationDirectBase] at * <;> aesop
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp_all [directRulesForRule, validationRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, decrementRules,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero,
          AnchoredCounterGeometry.registerGap,
          MarkerSchedule.decrementStartBoundary,
          MarkerValidation.sweep, LocalHonestRef, directRef, searchRef,
          instructionTargets, ruleStates, directStride] <;>
        norm_num [bodyDirectBase, testDirectSlot, branchDirectSlot,
          finishDirectSlot, validationDirectBase, zeroDirectBase] at * <;>
        aesop

/-- Every generated direct-rule target is an honest bounded continuation. -/
theorem directTarget_honest (rule : RawDirectRule)
    (hrule : rule ∈ rawDirectRules) : HonestRef rule.target := by
  simp only [rawDirectRules, rawDirectRulesFor, List.mem_append,
    List.mem_flatMap] at hrule
  rcases hrule with ⟨programRule, hprogram, hlocal⟩ |
      ⟨programRule, hprogram, hlocal⟩
  · exact honest_of_local .right programRule hprogram rule.target
      (directTarget_local_honest .right programRule rule hlocal)
  · exact honest_of_local .left programRule hprogram rule.target
      (directTarget_local_honest .left programRule rule hlocal)

/-! ## Semantic endpoints -/

/-- The desired tape-level endpoint: either bounded logical control or the
entry state of an actually generated raw search. -/
inductive Frontier (base : Nat) (c : Nat.Partrec.Code) :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State → Prop where
  | logical (growth : Turing.Dir) (state : Nat)
      (hstate : state < logicalSpan)
      (T : FullTM0.Tape (Symbol numTags)) :
      Frontier base c ⟨logicalState base c growth state, T⟩
  | search (raw : RawCommand) (hraw : raw ∈ rawCommands)
      (T : FullTM0.Tape (Symbol numTags)) :
      Frontier base c ⟨searchState base c raw.address, T⟩

/-- An immortal arbitrary entry at a shared return dispatcher recognizes a
real tag, resumes that exact generated command, and reaches its search
entry. -/
theorem reaches_frontier_of_immortal_return
    (base : Nat) (c : Nat.Partrec.Code) (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨controllerReturn base c direction, T⟩ finish ∧
        Frontier base c finish := by
  rcases CounterControlControllerNormalization.return_normalizes_arbitrary_entry
      base c direction T with
    hhalts | ⟨before, command, after, U, hlist, _hdirection, hreach⟩
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c direction, T⟩).mp himmortal hhalts)
  · have hat : CommandAt (CanonicalInitializer.radius c) base
        (base + before.length *
          blockWidth (CanonicalInitializer.radius c))
        command (commands base c) := by
      rw [hlist]
      exact CounterControlControllerNormalization.commandAt_append
        (CanonicalInitializer.radius c) base before command after
    rcases CounterControlCommandAtConverse.exists_raw_of_commandAt
        base c hat with ⟨raw, hraw, _hcommand, hoffset⟩
    refine ⟨⟨searchState base c raw.address, U⟩, ?_, .search raw hraw U⟩
    simpa [entryState, hoffset] using hreach

/-- A symbolic search address either names a generated command directly or,
if absent from the generated address list, its executable `findIdx` encoding
is exactly the first shared return dispatcher and normalizes there. -/
theorem reaches_frontier_of_immortal_searchRef
    (base : Nat) (c : Nat.Partrec.Code) (address : SearchAddress)
    (T : FullTM0.Tape (Symbol numTags))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨searchState base c address, T⟩) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨searchState base c address, T⟩ finish ∧
        Frontier base c finish := by
  classical
  by_cases haddress : address ∈ rawCommands.map RawCommand.address
  · rcases List.mem_map.mp haddress with ⟨raw, hraw, hrawAddress⟩
    refine ⟨⟨searchState base c address, T⟩,
      Relation.ReflTransGen.refl, ?_⟩
    simpa [hrawAddress] using Frontier.search (base := base) (c := c)
      raw hraw T
  · have hindex : searchIndex address = numTags := by
      unfold searchIndex numTags
      calc
        (rawCommands.map RawCommand.address).findIdx
              (fun candidate => candidate == address) =
            (rawCommands.map RawCommand.address).length := by
          apply List.findIdx_eq_length.mpr
          intro candidate hcandidate
          have hne : candidate ≠ address := by
            intro heq
            exact haddress (heq ▸ hcandidate)
          simp [hne]
        _ = rawCommands.length := by simp
    have hreturn : searchState base c address =
        controllerReturn base c .left := by
      simp [searchState, controllerReturn, hindex]
    have himmortalReturn : FullTM0.ImmortalFrom
        (CounterControlNestingBridge.machine base c)
        ⟨controllerReturn base c .left, T⟩ := by
      simpa [hreturn] using himmortal
    rcases reaches_frontier_of_immortal_return base c .left T
        himmortalReturn with ⟨finish, hreach, hfrontier⟩
    exact ⟨finish, by simpa [hreturn] using hreach, hfrontier⟩

/-- Honest references after all internal direct bridges have been crossed. -/
def SurfaceRef (reference : ControlRef) : Prop :=
  (∃ growth state, state < logicalSpan ∧
    reference = .logical growth state) ∨
  (∃ address, reference = .search address) ∨
  ∃ growth, reference = .sharedReturn growth

/-- A concrete configuration whose state resolves a surface reference. -/
def SurfaceCfg (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State) : Prop :=
  ∃ reference, cfg.q = resolve base c reference ∧ SurfaceRef reference

/-- Starting at any generated direct source, at most two enabled direct
steps reach bounded logical control or a symbolic search; a disabled step
halts.  The stronger target bounds come from `directTarget_honest`. -/
theorem directSource_reaches_surface_or_halts
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (hsource : cfg.q ∈ FiniteTM0.sourceStates (directTable base c)) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c) cfg ∨
      ∃ finish,
        FullTM0.Reaches (CounterControlNestingBridge.machine base c)
            cfg finish ∧
          SurfaceCfg base c finish := by
  rcases CounterControlArbitraryEntry.direct_step_or_haltsFrom
      base c cfg.q cfg.tape hsource with
    hhalts | ⟨rule, hrule, hstate, _hmatch, hstep⟩
  · exact Or.inl hhalts
  · have hone : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) cfg
        ⟨resolve base c rule.target,
          cfg.tape.move (orient rule.growth rule.direction)⟩ := by
      apply Relation.ReflTransGen.single
      simpa using hstep
    have hhonest := directTarget_honest rule hrule
    rcases CounterControlDirectNormalization.target_logical_search_or_bridge
        rule hrule with
      ⟨growth, state, htarget⟩ | ⟨address, htarget⟩ |
        ⟨growth, state, htarget⟩ | ⟨growth, state, htarget⟩
    · have hbound : state < logicalSpan := by
        simpa [HonestRef, htarget] using hhonest
      right
      refine ⟨_, hone, ?_⟩
      refine ⟨.logical growth state, ?_, ?_⟩
      · simp [htarget]
      · exact Or.inl ⟨growth, state, hbound, rfl⟩
    · right
      refine ⟨_, hone, ?_⟩
      refine ⟨.search address, ?_, ?_⟩
      · simp [htarget]
      · exact Or.inr (Or.inl ⟨address, rfl⟩)
    · have hnextSource : resolve base c rule.target ∈
          FiniteTM0.sourceStates (directTable base c) := by
        rw [htarget]
        simp only [directRef, resolve]
        rcases CounterControlDirectNormalization.bridge_target_is_source
            rule hrule growth state (bodyDirectBase + 1) (Or.inl rfl)
            htarget with ⟨next, hnext, hsourceNext⟩
        have hsourceNext' : next.source =
            directRef growth state (bodyDirectBase + 1) :=
          hsourceNext.trans htarget
        simp only [directTable, FiniteTM0.sourceStates, List.map_flatMap,
          List.mem_flatMap]
        refine ⟨next, hnext, ?_⟩
        simp only [directRuleTable, List.map_map, List.mem_map,
          FiniteTM0.Rule.mk, Function.comp_apply]
        rcases next.read with _ | label | _
        · refine ⟨blankSymbol, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext', resolve, directRef]
        · refine ⟨boundarySymbol label, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext', resolve, directRef]
        · refine ⟨boundarySymbol ⟨0, by decide⟩, by
              simp [symbolsForRead, nonblankSymbols], ?_⟩
          simpa [hsourceNext', resolve, directRef]
      rcases CounterControlArbitraryEntry.direct_step_or_haltsFrom
          base c _ _ hnextSource with
        hhalts | ⟨next, hnext, hnextState, _hnextMatch, hnextStep⟩
      · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone hhalts)
      · have htargetWell :=
          CounterControlDirectNormalization.bridge_target_wellFormed
            rule hrule growth state (bodyDirectBase + 1) (Or.inl rfl)
            htarget
        have htargetCounter :
            CounterControlDeterministic.IsCounterSource rule.target := by
          simp [htarget, directRef,
            CounterControlDeterministic.IsCounterSource]
        have hnextCounter :
            CounterControlDeterministic.IsCounterSource next.source :=
          CounterControlDeterministic.rawDirectRules_counter_sources
            next hnext
        have hoffset : CounterControlDeterministic.sourceOffset rule.target =
            CounterControlDeterministic.sourceOffset next.source := by
          apply Nat.add_left_cancel
          calc
            rightLogicalBase base c +
                  CounterControlDeterministic.sourceOffset rule.target =
                resolve base c rule.target :=
              (CounterControlDeterministic.resolve_eq_add_sourceOffset
                base c htargetCounter).symm
            _ = resolve base c next.source := hnextState
            _ = rightLogicalBase base c +
                  CounterControlDeterministic.sourceOffset next.source :=
              CounterControlDeterministic.resolve_eq_add_sourceOffset
                base c hnextCounter
        have heq : rule.target = next.source :=
          CounterControlDeterministic.sourceOffset_injective_on
            htargetWell
            (CounterControlArbitraryEntry.rawDirectRule_source_wellFormed
              next hnext) hoffset
        have hbridge : next.source =
            directRef growth state (bodyDirectBase + 1) := by
          rw [← heq, htarget]
        rcases CounterControlDirectNormalization.bridge_source_targets_search
            next hnext growth state (Or.inl hbridge) with
          ⟨address, htargetNext⟩
        right
        refine ⟨_, hone.trans (Relation.ReflTransGen.single hnextStep), ?_⟩
        refine ⟨.search address, ?_, ?_⟩
        · simp [htargetNext]
        · exact Or.inr (Or.inl ⟨address, rfl⟩)
    · have hnextSource : resolve base c rule.target ∈
          FiniteTM0.sourceStates (directTable base c) := by
        rcases CounterControlDirectNormalization.bridge_target_is_source
            rule hrule growth state branchDirectSlot (Or.inr rfl)
            htarget with ⟨next, hnext, hsourceNext⟩
        simp only [directTable, FiniteTM0.sourceStates, List.map_flatMap,
          List.mem_flatMap]
        refine ⟨next, hnext, ?_⟩
        simp only [directRuleTable, List.map_map, List.mem_map,
          FiniteTM0.Rule.mk, Function.comp_apply]
        rcases next.read with _ | label | _
        · refine ⟨blankSymbol, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext]
        · refine ⟨boundarySymbol label, by simp [symbolsForRead], ?_⟩
          simpa [hsourceNext]
        · refine ⟨boundarySymbol ⟨0, by decide⟩, by
              simp [symbolsForRead, nonblankSymbols], ?_⟩
          simpa [hsourceNext]
      rcases CounterControlArbitraryEntry.direct_step_or_haltsFrom
          base c _ _ hnextSource with
        hhalts | ⟨next, hnext, hnextState, _hnextMatch, hnextStep⟩
      · exact Or.inl (FullTM0.HaltsFrom.of_reaches hone hhalts)
      · have htargetWell :=
          CounterControlDirectNormalization.bridge_target_wellFormed
            rule hrule growth state branchDirectSlot (Or.inr rfl) htarget
        have htargetCounter :
            CounterControlDeterministic.IsCounterSource rule.target := by
          simp [htarget, directRef,
            CounterControlDeterministic.IsCounterSource]
        have hnextCounter :
            CounterControlDeterministic.IsCounterSource next.source :=
          CounterControlDeterministic.rawDirectRules_counter_sources
            next hnext
        have hoffset : CounterControlDeterministic.sourceOffset rule.target =
            CounterControlDeterministic.sourceOffset next.source := by
          apply Nat.add_left_cancel
          calc
            rightLogicalBase base c +
                  CounterControlDeterministic.sourceOffset rule.target =
                resolve base c rule.target :=
              (CounterControlDeterministic.resolve_eq_add_sourceOffset
                base c htargetCounter).symm
            _ = resolve base c next.source := hnextState
            _ = rightLogicalBase base c +
                  CounterControlDeterministic.sourceOffset next.source :=
              CounterControlDeterministic.resolve_eq_add_sourceOffset
                base c hnextCounter
        have heq : rule.target = next.source :=
          CounterControlDeterministic.sourceOffset_injective_on
            htargetWell
            (CounterControlArbitraryEntry.rawDirectRule_source_wellFormed
              next hnext) hoffset
        have hbridge : next.source =
            directRef growth state branchDirectSlot := by
          rw [← heq, htarget]
        rcases CounterControlDirectNormalization.bridge_source_targets_search
            next hnext growth state (Or.inr hbridge) with
          ⟨address, htargetNext⟩
        right
        refine ⟨_, hone.trans (Relation.ReflTransGen.single hnextStep), ?_⟩
        refine ⟨.search address, ?_, ?_⟩
        · simp [htargetNext]
        · exact Or.inr (Or.inl ⟨address, rfl⟩)

/-- Every immortal surface configuration reaches the final bounded
logical/generated-search frontier. -/
theorem reaches_frontier_of_immortal_surfaceCfg
    (base : Nat) (c : Nat.Partrec.Code)
    (cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cfg)
    (hsurface : SurfaceCfg base c cfg) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          cfg finish ∧
        Frontier base c finish := by
  rcases cfg with ⟨q, T⟩
  rcases hsurface with ⟨reference, hq,
    ⟨growth, state, hstate, href⟩ |
      ⟨address, href⟩ | ⟨growth, href⟩⟩
  · subst reference
    simp only [resolve] at hq
    subst q
    exact ⟨_, Relation.ReflTransGen.refl,
      .logical growth state hstate T⟩
  · subst reference
    simp only [resolve] at hq
    subst q
    exact reaches_frontier_of_immortal_searchRef base c address T himmortal
  · subst reference
    simp only [resolve] at hq
    subst q
    exact reaches_frontier_of_immortal_return base c growth T himmortal

/-- Resolving any honest symbolic continuation on an immortal orbit reaches
bounded logical control or a generated search entry. -/
theorem reaches_frontier_of_immortal_honestRef
    (base : Nat) (c : Nat.Partrec.Code) (reference : ControlRef)
    (T : FullTM0.Tape (Symbol numTags))
    (hreference : HonestRef reference)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
        ⟨resolve base c reference, T⟩) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          ⟨resolve base c reference, T⟩ finish ∧
        Frontier base c finish := by
  rcases hreference with
    ⟨growth, state, hstate, href⟩ | ⟨address, href⟩ |
      ⟨address, hcounterState, hslot, href⟩ | ⟨growth, href⟩
  · apply reaches_frontier_of_immortal_surfaceCfg base c _ himmortal
    exact ⟨reference, rfl,
      Or.inl ⟨growth, state, hstate, href⟩⟩
  · apply reaches_frontier_of_immortal_surfaceCfg base c _ himmortal
    exact ⟨reference, rfl,
      Or.inr (Or.inl ⟨address, href⟩)⟩
  · subst reference
    have hlower : initializerEnd base c ≤
        directState base c address := by
      rcases address with ⟨growth, counterState, slot⟩
      cases growth <;>
        simp [directState, directBase, rightDirectBase, leftDirectBase,
          leftLogicalBase, rightLogicalBase] <;> omega
    have hdirect : directState base c address ∈
        FiniteTM0.sourceStates (directTable base c) := by
      cases CounterControlArbitraryEntry.sourceRegion_of_immortalFrom
          base c ⟨directState base c address, T⟩ himmortal with
      | controller hsource =>
          have hupper : directState base c address <
              controllerCoreEntry base c :=
            CounterControlArbitraryEntry.controller_lt_coreEntry
              base c hsource
          have hcore : controllerCoreEntry base c < initializerEnd base c := by
            simp [initializerEnd, CanonicalInitializerProgram.exitState]
            omega
          omega
      | initializer hsource =>
          have hupper : directState base c address < initializerEnd base c :=
            (CounterControlArbitraryEntry.initializer_bounds
              base c hsource).2
          omega
      | direct hsource => exact hsource
    rcases directSource_reaches_surface_or_halts base c
        ⟨directState base c address, T⟩ hdirect with
      hhalts | ⟨finish, hreach, hsurface⟩
    · exact False.elim
        ((FullTM0.HaltsFrom.immortalFrom_iff_not
          (CounterControlNestingBridge.machine base c)
          ⟨directState base c address, T⟩).mp himmortal hhalts)
    · have himmortalFinish : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c) finish := by
        rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
        intro hhalts
        exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)
      rcases reaches_frontier_of_immortal_surfaceCfg base c finish
          himmortalFinish hsurface with ⟨final, htail, hfrontier⟩
      exact ⟨final, hreach.trans htail, hfrontier⟩
  · apply reaches_frontier_of_immortal_surfaceCfg base c _ himmortal
    exact ⟨reference, rfl,
      Or.inr (Or.inr ⟨growth, href⟩)⟩

/-- A command success or collision handoff on an immortal concrete orbit
reaches bounded logical control or an actually generated search entry. -/
theorem reaches_frontier_of_commandContinuationHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    {start cfg : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start cfg)
    (hhandoff :
      CounterControlArbitraryMortality.CommandContinuationHandoff
        base c cfg) :
    ∃ finish,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          start finish ∧
        Frontier base c finish := by
  have himmortalCfg : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) cfg := by
    rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
    intro hhalts
    exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)
  rcases hhandoff with
    ⟨_commandOffset, command, hat, hsuccess | hcollision⟩
  · rcases CounterControlCommandAtConverse.exists_raw_of_commandAt
        base c hat with ⟨raw, hraw, hcommand, _hoffset⟩
    rcases cfg with ⟨q, T⟩
    have hq : q = resolve base c (rawSuccessRef raw) := by
      calc
        q = command.successState := hsuccess
        _ = (CounterControlCommandAt.compileRawCommand
              base c raw hraw).successState := by rw [hcommand]
        _ = resolve base c (rawSuccessRef raw) :=
          compileRawCommand_successState base c raw hraw
    subst q
    rcases reaches_frontier_of_immortal_honestRef base c
        (rawSuccessRef raw) T (successRef_honest raw hraw)
        himmortalCfg with ⟨finish, htail, hfrontier⟩
    exact ⟨finish, hreach.trans htail, hfrontier⟩
  · rcases hcollision with
      ⟨move, success, returnTag, departure, collision,
        hmarkerShift, hcollisionState⟩
    rcases CounterControlCommandAtConverse.exists_raw_of_commandAt
        base c hat with ⟨raw, hraw, hcommand, _hoffset⟩
    have hcompiled :
        CounterControlCommandAt.compileRawCommand base c raw hraw =
          .markerShift move success returnTag departure
            (some collision) :=
      hcommand.symm.trans hmarkerShift
    rcases exists_collisionRef_of_compileRawCommand_eq_markerShift
        base c raw hraw move success collision returnTag departure
        hcompiled with
      ⟨reference, hcollisionRef, hcollisionResolve⟩
    rcases cfg with ⟨q, T⟩
    have hq : q = resolve base c reference :=
      hcollisionState.trans hcollisionResolve
    subst q
    rcases reaches_frontier_of_immortal_honestRef base c reference T
        (collisionRef_honest raw hraw reference hcollisionRef)
        himmortalCfg with ⟨finish, htail, hfrontier⟩
    exact ⟨finish, hreach.trans htail, hfrontier⟩

end


end CounterControlCommandContinuationMortality
end Hooper
end Kari
end LeanWang
