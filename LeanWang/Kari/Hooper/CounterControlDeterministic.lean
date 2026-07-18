/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPlan

/-!
# Determinism of the compiled counter controller

The counter plan is a fixed finite symbolic program, while its numeric state
addresses depend on the input code.  This file separates those two facts.  A
structural certificate checks the symbolic direct-rule keys instruction by
instruction; the remaining proofs show that code-dependent allocation is an
injective translation of those keys into fresh numeric intervals.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlDeterministic

open Turing
open BoundedMarkerProgram CounterControlPlan

noncomputable section

/-! ## Symbolic source offsets -/

/-- Offset of a logical or direct counter state from the first right-logical
state.  Search and shared-return references are not counter-core sources and
are assigned an irrelevant default. -/
def sourceOffset : ControlRef → Nat
  | .logical .right state => state
  | .logical .left state => logicalSpan + directSpan + state
  | .direct ⟨.right, state, slot⟩ =>
      logicalSpan + state * directStride + slot
  | .direct ⟨.left, state, slot⟩ =>
      2 * logicalSpan + directSpan + state * directStride + slot
  | .search _ => 0
  | .sharedReturn _ => 0

/-- Exactly the two reference forms permitted as sources of direct glue
rules. -/
def IsCounterSource : ControlRef → Prop
  | .logical _ _ => True
  | .direct _ => True
  | .search _ => False
  | .sharedReturn _ => False

instance (reference : ControlRef) : Decidable (IsCounterSource reference) := by
  cases reference <;> simp only [IsCounterSource] <;> infer_instance

/-- Numeric allocation is translation by the first right-logical state. -/
theorem resolve_eq_add_sourceOffset (base : Nat) (c : Nat.Partrec.Code)
    {reference : ControlRef} (hsource : IsCounterSource reference) :
    resolve base c reference =
      rightLogicalBase base c + sourceOffset reference := by
  cases reference with
  | logical growth state =>
      cases growth <;>
        simp [resolve, logicalState, logicalBase,
          rightLogicalBase, leftLogicalBase, rightDirectBase,
          sourceOffset, Nat.add_assoc]
  | direct address =>
      rcases address with ⟨growth, state, slot⟩
      cases growth <;>
        simp [resolve, directState, directBase,
          rightDirectBase, leftDirectBase, leftLogicalBase, sourceOffset,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
        omega
  | search address => simp [IsCounterSource] at hsource
  | sharedReturn _ => simp [IsCounterSource] at hsource

/-! ## Fixed direct-rule keys -/

/-- Symbolic keys emitted by one direct rule before numeric state
translation. -/
def rawDirectRuleKeys (rule : RawDirectRule) :
    List (Nat × Symbol numTags) :=
  (symbolsForRead rule.read).map fun symbol =>
    (sourceOffset rule.source, symbol)

/-- All symbolic direct-rule keys of the fixed two-orientation plan. -/
def rawDirectKeys : List (Nat × Symbol numTags) :=
  rawDirectRules.flatMap rawDirectRuleKeys

/-- Direct keys before numeric state allocation. -/
def rawDirectControlRuleKeys (rule : RawDirectRule) :
    List (ControlRef × Symbol numTags) :=
  (symbolsForRead rule.read).map fun symbol => (rule.source, symbol)

def rawDirectControlKeysForRule (growth : Turing.Dir)
    (programRule : CounterMachine.Rule) :
    List (ControlRef × Symbol numTags) :=
  (directRulesForRule growth programRule).flatMap rawDirectControlRuleKeys

/-- A counter-core reference belongs to one oriented source-state block. -/
def Owns (growth : Turing.Dir) (source : Nat) : ControlRef → Prop
  | .logical referenceGrowth referenceSource =>
      referenceGrowth = growth ∧ referenceSource = source
  | .direct address =>
      address.growth = growth ∧ address.counterState = source
  | .search _ => False
  | .sharedReturn _ => False

/-- Within one counter instruction, every direct transition key is unique. -/
theorem rawDirectControlKeysForRule_nodup (growth : Turing.Dir)
    (programRule : CounterMachine.Rule) :
    (rawDirectControlKeysForRule growth programRule).Nodup := by
  have hnonblank (reference : ControlRef) :
      ((nonblankSymbols numTags).map fun symbol =>
        (reference, symbol)).Nodup :=
    (BoundedMarkerProgram.nonblankSymbols_nodup numTags).map fun _ _ heq =>
      congrArg Prod.snd heq
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register next =>
      cases growth <;> cases register <;>
        simp [rawDirectControlKeysForRule, rawDirectControlRuleKeys,
          directRulesForRule, validationRules, incrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeFromIncrement, directRef,
          symbolsForRead, validationDirectBase, bodyDirectBase,
          testDirectSlot] <;>
        exact hnonblank _
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp [rawDirectControlKeysForRule, rawDirectControlRuleKeys,
          directRulesForRule, validationRules, decrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero, directRef,
          symbolsForRead, validationDirectBase, bodyDirectBase,
          testDirectSlot, branchDirectSlot, finishDirectSlot,
          zeroDirectBase, MarkerSchedule.decrementStartBoundary,
          AnchoredCounterGeometry.registerGap] <;>
        exact blankSymbol_ne_boundarySymbol _

theorem rawDirectControlKeysForRule_owns (growth : Turing.Dir)
    (programRule : CounterMachine.Rule) :
    ∀ key ∈ rawDirectControlKeysForRule growth programRule,
      Owns growth programRule.1 key.1 := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register next =>
      cases growth <;> cases register <;>
        simp [rawDirectControlKeysForRule, rawDirectControlRuleKeys,
          directRulesForRule, validationRules, incrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeFromIncrement, directRef,
          symbolsForRead, Owns]
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp [rawDirectControlKeysForRule, rawDirectControlRuleKeys,
          directRulesForRule, validationRules, decrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero, directRef,
          symbolsForRead, Owns]

theorem rawDirectControlKeysForRule_disjoint_of_source_ne
    (growth : Turing.Dir) {first second : CounterMachine.Rule}
    (hne : first.1 ≠ second.1) :
    List.Disjoint (rawDirectControlKeysForRule growth first)
      (rawDirectControlKeysForRule growth second) := by
  rw [List.disjoint_iff_ne]
  intro firstKey hfirst secondKey hsecond heq
  have hfirstOwns := rawDirectControlKeysForRule_owns growth first
    firstKey hfirst
  have hsecondOwns := rawDirectControlKeysForRule_owns growth second
    secondKey hsecond
  subst secondKey
  apply hne
  rcases firstKey with ⟨reference, symbol⟩
  cases reference <;> simp_all [Owns]

/-- Direct keys for one physical orientation. -/
def rawDirectControlKeysFor (growth : Turing.Dir) :
    List (ControlRef × Symbol numTags) :=
  GlobalSourceProgram.program.flatMap
    (rawDirectControlKeysForRule growth)

theorem rawDirectControlKeysFor_nodup (growth : Turing.Dir) :
    (rawDirectControlKeysFor growth).Nodup := by
  rw [rawDirectControlKeysFor, List.nodup_flatMap]
  constructor
  · intro rule _
    exact rawDirectControlKeysForRule_nodup growth rule
  · have hsources := GlobalSourceProgram.program_deterministic
    change (GlobalSourceProgram.program.map Prod.fst).Nodup at hsources
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hsources
    exact hsources.imp fun hne =>
      rawDirectControlKeysForRule_disjoint_of_source_ne growth hne

theorem rawDirectControlKeys_orientations_disjoint :
    List.Disjoint (rawDirectControlKeysFor .right)
      (rawDirectControlKeysFor .left) := by
  rw [List.disjoint_iff_ne]
  intro rightKey hright leftKey hleft heq
  simp only [rawDirectControlKeysFor, List.mem_flatMap] at hright hleft
  rcases hright with ⟨rightRule, -, hright⟩
  rcases hleft with ⟨leftRule, -, hleft⟩
  have hrightOwns := rawDirectControlKeysForRule_owns .right rightRule
    rightKey hright
  have hleftOwns := rawDirectControlKeysForRule_owns .left leftRule
    leftKey hleft
  subst leftKey
  rcases rightKey with ⟨reference, symbol⟩
  cases reference <;> simp_all [Owns]

/-- Every symbolic source/symbol key in both oriented copies is unique. -/
def rawDirectControlKeys : List (ControlRef × Symbol numTags) :=
  rawDirectControlKeysFor .right ++ rawDirectControlKeysFor .left

theorem rawDirectControlKeys_nodup : rawDirectControlKeys.Nodup := by
  exact List.Nodup.append
    (rawDirectControlKeysFor_nodup .right)
    (rawDirectControlKeysFor_nodup .left)
    rawDirectControlKeys_orientations_disjoint

/-- Range invariant under which the numeric source-offset encoding is
injective. -/
def WellFormedSource : ControlRef → Prop
  | .logical _ source => source < logicalSpan
  | .direct address =>
      address.counterState < logicalSpan ∧ address.slot < directStride
  | .search _ => False
  | .sharedReturn _ => False

/-- The local part of `WellFormedSource`, independent of the source state of
the counter instruction that owns the reference. -/
def SlotBound : ControlRef → Prop
  | .logical _ _ => True
  | .direct address => address.slot < directStride
  | .search _ => False
  | .sharedReturn _ => False

theorem rawDirectControlKeysForRule_slotBound (growth : Turing.Dir)
    (programRule : CounterMachine.Rule) :
    ∀ key ∈ rawDirectControlKeysForRule growth programRule,
      SlotBound key.1 := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register next =>
      cases growth <;> cases register <;>
        simp [rawDirectControlKeysForRule, rawDirectControlRuleKeys,
          directRulesForRule, validationRules, incrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeFromIncrement, directRef,
          symbolsForRead, SlotBound, directStride] <;>
        norm_num [validationDirectBase, bodyDirectBase, testDirectSlot]
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp [rawDirectControlKeysForRule, rawDirectControlRuleKeys,
          directRulesForRule, validationRules, decrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero, directRef,
          symbolsForRead, SlotBound, directStride] <;>
        norm_num [validationDirectBase, bodyDirectBase, testDirectSlot,
          branchDirectSlot, finishDirectSlot, zeroDirectBase]

theorem rawDirectControlKeysForRule_wellFormed (growth : Turing.Dir)
    (programRule : CounterMachine.Rule)
    (hsource : programRule.1 < logicalSpan) :
    ∀ key ∈ rawDirectControlKeysForRule growth programRule,
      WellFormedSource key.1 := by
  intro key hkey
  have howns := rawDirectControlKeysForRule_owns growth programRule key hkey
  have hslot := rawDirectControlKeysForRule_slotBound growth programRule key hkey
  rcases programRule with ⟨source, instruction⟩
  rcases key with ⟨reference, symbol⟩
  cases reference <;>
    simp_all [Owns, SlotBound, WellFormedSource]

theorem rawDirectControlKeys_wellFormed {key : ControlRef × Symbol numTags}
    (hkey : key ∈ rawDirectControlKeys) : WellFormedSource key.1 := by
  simp only [rawDirectControlKeys, List.mem_append,
    rawDirectControlKeysFor, List.mem_flatMap] at hkey
  rcases hkey with ⟨programRule, hprogram, hkey⟩ |
      ⟨programRule, hprogram, hkey⟩
  · apply rawDirectControlKeysForRule_wellFormed .right programRule
      (state_lt_logicalSpan
        (source_mem_programStates programRule hprogram)) key hkey
  · apply rawDirectControlKeysForRule_wellFormed .left programRule
      (state_lt_logicalSpan
        (source_mem_programStates programRule hprogram)) key hkey

private theorem packed_lt_directSpan {source slot : Nat}
    (hsource : source < logicalSpan) (hslot : slot < directStride) :
    source * directStride + slot < directSpan := by
  unfold directSpan directStride at *
  omega

private theorem packed_injective {firstSource firstSlot secondSource secondSlot : Nat}
    (hfirstSlot : firstSlot < directStride)
    (hsecondSlot : secondSlot < directStride)
    (heq : firstSource * directStride + firstSlot =
      secondSource * directStride + secondSlot) :
    firstSource = secondSource ∧ firstSlot = secondSlot := by
  unfold directStride at *
  omega

private theorem logical_direct_sourceOffset_ne (logicalGrowth directGrowth : Turing.Dir)
    {logicalSource directSource slot : Nat}
    (hlogical : logicalSource < logicalSpan)
    (hdirect : directSource < logicalSpan) (hslot : slot < directStride) :
    sourceOffset (.logical logicalGrowth logicalSource) ≠
      sourceOffset (.direct ⟨directGrowth, directSource, slot⟩) := by
  have hpacked := packed_lt_directSpan hdirect hslot
  have hlogicalRightUpper :
      sourceOffset (.logical .right logicalSource) < logicalSpan := by
    simpa [sourceOffset] using hlogical
  have hlogicalLeftLower :
      logicalSpan + directSpan ≤
        sourceOffset (.logical .left logicalSource) := by
    simp [sourceOffset]
  have hlogicalLeftUpper :
      sourceOffset (.logical .left logicalSource) <
        2 * logicalSpan + directSpan := by
    simp only [sourceOffset]
    omega
  have hdirectRightLower :
      logicalSpan ≤ sourceOffset
        (.direct ⟨.right, directSource, slot⟩) := by
    simpa [sourceOffset, Nat.add_assoc] using
      Nat.le_add_right logicalSpan (directSource * directStride + slot)
  have hdirectRightUpper :
      sourceOffset (.direct ⟨.right, directSource, slot⟩) <
        logicalSpan + directSpan := by
    simpa [sourceOffset, Nat.add_assoc] using
      Nat.add_lt_add_left hpacked logicalSpan
  have hdirectLeftLower :
      2 * logicalSpan + directSpan ≤ sourceOffset
        (.direct ⟨.left, directSource, slot⟩) := by
    simpa [sourceOffset, Nat.add_assoc] using
      Nat.le_add_right (2 * logicalSpan + directSpan)
        (directSource * directStride + slot)
  cases logicalGrowth <;> cases directGrowth
  · intro heq
    rw [heq] at hlogicalLeftUpper
    exact (Nat.not_lt_of_ge hdirectLeftLower hlogicalLeftUpper)
  · intro heq
    rw [← heq] at hdirectRightUpper
    exact (Nat.not_lt_of_ge hlogicalLeftLower hdirectRightUpper)
  · intro heq
    rw [heq] at hlogicalRightUpper
    exact (Nat.not_lt_of_ge
      (Nat.le_trans (by omega) hdirectLeftLower) hlogicalRightUpper)
  · intro heq
    rw [heq] at hlogicalRightUpper
    exact (Nat.not_lt_of_ge hdirectRightLower hlogicalRightUpper)

/-- The four half-open state regions make the symbolic source encoding
injective on every generated logical/direct source. -/
theorem sourceOffset_injective_on {first second : ControlRef}
    (hfirst : WellFormedSource first) (hsecond : WellFormedSource second)
    (heq : sourceOffset first = sourceOffset second) : first = second := by
  cases first with
  | logical firstGrowth firstSource =>
      change firstSource < logicalSpan at hfirst
      cases second with
      | logical secondGrowth secondSource =>
          change secondSource < logicalSpan at hsecond
          cases firstGrowth <;> cases secondGrowth
          · have hsource : firstSource = secondSource := by
              simp [sourceOffset] at heq
              omega
            subst secondSource
            rfl
          · have hlower : logicalSpan ≤ secondSource := by
              simp [sourceOffset] at heq
              rw [← heq]
              omega
            exact (Nat.not_le_of_gt hsecond hlower).elim
          · have hlower : logicalSpan ≤ firstSource := by
              simp [sourceOffset] at heq
              rw [heq]
              omega
            exact (Nat.not_le_of_gt hfirst hlower).elim
          · have hsource : firstSource = secondSource := by
              simpa [sourceOffset] using heq
            subst secondSource
            rfl
      | direct secondAddress =>
          rcases secondAddress with ⟨secondGrowth, secondSource, secondSlot⟩
          change secondSource < logicalSpan ∧ secondSlot < directStride at hsecond
          rcases hsecond with ⟨hsecondSource, hsecondSlot⟩
          exact (logical_direct_sourceOffset_ne firstGrowth secondGrowth
            hfirst hsecondSource hsecondSlot heq).elim
      | search _ => simp [WellFormedSource] at hsecond
      | sharedReturn _ => simp [WellFormedSource] at hsecond
  | direct firstAddress =>
      rcases firstAddress with ⟨firstGrowth, firstSource, firstSlot⟩
      change firstSource < logicalSpan ∧ firstSlot < directStride at hfirst
      rcases hfirst with ⟨hfirstSource, hfirstSlot⟩
      cases second with
      | logical secondGrowth secondSource =>
          change secondSource < logicalSpan at hsecond
          exact (logical_direct_sourceOffset_ne secondGrowth firstGrowth
            hsecond hfirstSource hfirstSlot heq.symm).elim
      | direct secondAddress =>
          rcases secondAddress with ⟨secondGrowth, secondSource, secondSlot⟩
          change secondSource < logicalSpan ∧ secondSlot < directStride at hsecond
          rcases hsecond with ⟨hsecondSource, hsecondSlot⟩
          have hfirstPacked := packed_lt_directSpan hfirstSource hfirstSlot
          have hsecondPacked := packed_lt_directSpan
            hsecondSource hsecondSlot
          unfold directSpan directStride at hfirstPacked hsecondPacked
          cases firstGrowth <;> cases secondGrowth
          · have hpacked : firstSource * directStride + firstSlot =
                secondSource * directStride + secondSlot := by
              simpa [sourceOffset, Nat.add_assoc] using heq
            rcases packed_injective hfirstSlot hsecondSlot hpacked with
              ⟨rfl, rfl⟩
            rfl
          · simp [sourceOffset, directSpan, directStride] at heq ⊢
            omega
          · simp [sourceOffset, directSpan, directStride] at heq ⊢
            omega
          · have hpacked : firstSource * directStride + firstSlot =
                secondSource * directStride + secondSlot := by
              simpa [sourceOffset, Nat.add_assoc] using heq
            rcases packed_injective hfirstSlot hsecondSlot hpacked with
              ⟨rfl, rfl⟩
            rfl
      | search _ => simp [WellFormedSource] at hsecond
      | sharedReturn _ => simp [WellFormedSource] at hsecond
  | search _ => simp [WellFormedSource] at hfirst
  | sharedReturn _ => simp [WellFormedSource] at hfirst

/-- The fixed plan never uses a search or shared-return state as a direct-rule
source. -/
private theorem directRulesForRule_counter_sources
    (growth : Turing.Dir) (programRule : CounterMachine.Rule) :
    ∀ rule ∈ directRulesForRule growth programRule,
      IsCounterSource rule.source := by
  rcases programRule with ⟨source, instruction⟩
  cases instruction with
  | increment register next =>
      cases growth <;> cases register <;>
        simp [directRulesForRule, validationRules, incrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeFromIncrement, directRef,
          IsCounterSource]
  | decrement register ifZero ifPositive =>
      cases growth <;> cases register <;>
        simp [directRulesForRule, validationRules, decrementRules,
          routeEntryRules, routeContinuationRules,
          routeContinuationRulesFrom, MarkerValidation.sweep,
          AnchoredCounterGeometry.routeToDecrementStart,
          AnchoredCounterGeometry.routeFromZero, directRef,
          IsCounterSource]

theorem rawDirectRules_counter_sources :
    ∀ rule ∈ rawDirectRules, IsCounterSource rule.source := by
  intro rule hrule
  rcases (mem_rawDirectRules_iff rule).1 hrule with
    ⟨growth, programRule, _hprogram, hlocal⟩
  exact directRulesForRule_counter_sources growth programRule rule hlocal

/-- Every concrete read symbol of a generated local direct rule contributes
its source key to the corresponding oriented controller fragment. -/
theorem mem_rawDirectControlKeysForRule
    (growth : Turing.Dir) (programRule : CounterMachine.Rule)
    (rule : RawDirectRule)
    (hlocal : rule ∈ directRulesForRule growth programRule)
    (symbol : Symbol numTags) (hsymbol : symbol ∈ symbolsForRead rule.read) :
    (rule.source, symbol) ∈ rawDirectControlKeysForRule growth programRule := by
  simp only [rawDirectControlKeysForRule, List.mem_flatMap]
  refine ⟨rule, hlocal, ?_⟩
  simpa [rawDirectControlRuleKeys] using hsymbol

/-- Every concrete read symbol of a globally generated direct rule contributes
its source key to the complete controller table. -/
theorem mem_rawDirectControlKeys
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (symbol : Symbol numTags) (hsymbol : symbol ∈ symbolsForRead rule.read) :
    (rule.source, symbol) ∈ rawDirectControlKeys := by
  rcases (mem_rawDirectRules_iff rule).1 hrule with
    ⟨growth, programRule, hprogram, hlocal⟩
  have hkey := mem_rawDirectControlKeysForRule growth programRule rule hlocal
    symbol hsymbol
  simp only [rawDirectControlKeys, rawDirectControlKeysFor,
    List.mem_append, List.mem_flatMap]
  cases growth with
  | right => exact Or.inl ⟨programRule, hprogram, hkey⟩
  | left => exact Or.inr ⟨programRule, hprogram, hkey⟩

/-- Numeric symbolic keys are exactly the source-offset image of the
unallocated control-reference keys. -/
theorem rawDirectKeys_eq : rawDirectKeys =
    rawDirectControlKeys.map fun key => (sourceOffset key.1, key.2) := by
  have keysForRules (rules : List RawDirectRule) :
      rules.flatMap rawDirectRuleKeys =
        (rules.flatMap rawDirectControlRuleKeys).map fun key =>
          (sourceOffset key.1, key.2) := by
    induction rules with
    | nil => rfl
    | cons rule rules ih =>
        simp [rawDirectRuleKeys, rawDirectControlRuleKeys, ih,
          Function.comp_def, List.map_append]
  have controlKeysFor (growth : Turing.Dir) :
      rawDirectControlKeysFor growth =
        (rawDirectRulesFor growth).flatMap rawDirectControlRuleKeys := by
    unfold rawDirectControlKeysFor rawDirectRulesFor
    rw [List.flatMap_assoc]
    rfl
  rw [rawDirectKeys, rawDirectRules, List.flatMap_append,
    rawDirectControlKeys, List.map_append, controlKeysFor .right,
    controlKeysFor .left, keysForRules, keysForRules]

/-- The expanded fixed direct-rule keys have no duplicates, including the
intentional multi-symbol branches. -/
theorem rawDirectKeys_nodup : rawDirectKeys.Nodup := by
  rw [rawDirectKeys_eq]
  apply rawDirectControlKeys_nodup.map_on
  intro first hfirst second hsecond heq
  have hreference := sourceOffset_injective_on
      (rawDirectControlKeys_wellFormed hfirst)
      (rawDirectControlKeys_wellFormed hsecond)
      (congrArg Prod.fst heq)
  have hsymbol : first.2 = second.2 :=
    congrArg (fun key : Nat × Symbol numTags => key.2) heq
  rcases first with ⟨firstReference, firstSymbol⟩
  rcases second with ⟨secondReference, secondSymbol⟩
  simp only at hreference hsymbol
  subst secondReference
  subst secondSymbol
  rfl

private theorem translated_direct_keys (base : Nat)
    (c : Nat.Partrec.Code) (rules : List RawDirectRule)
    (hsources : ∀ rule ∈ rules, IsCounterSource rule.source) :
    ((rules.flatMap (directRuleTable base c)).map Prod.fst) =
      (rules.flatMap rawDirectRuleKeys).map fun key =>
        (rightLogicalBase base c + key.1, key.2) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      have hhead : IsCounterSource rule.source :=
        hsources rule (by simp)
      have htail : ∀ next ∈ rules, IsCounterSource next.source := by
        intro next hnext
        exact hsources next (by simp [hnext])
      have hresolve := resolve_eq_add_sourceOffset base c hhead
      simp [directRuleTable, rawDirectRuleKeys, hresolve, ih htail,
        List.map_append]

/-- The actual direct-table key list is the injective numeric translation of
the fixed symbolic key list. -/
theorem directTable_keys (base : Nat) (c : Nat.Partrec.Code) :
    ((directTable base c).map Prod.fst) =
      rawDirectKeys.map fun key =>
        (rightLogicalBase base c + key.1, key.2) := by
  exact translated_direct_keys base c rawDirectRules
    rawDirectRules_counter_sources

/-- The direct glue table is deterministic for every code-dependent state
allocation. -/
theorem directTable_deterministic (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Deterministic (directTable base c) := by
  rw [FiniteTM0.Deterministic, directTable_keys]
  apply rawDirectKeys_nodup.map
  intro first second heq
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.fst heq)
  · simpa using congrArg Prod.snd heq

/-! ## Freshness and complete-table determinism -/

private theorem key_source_mem {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols} {key : FiniteTM0.Key numSymbols}
    (hkey : key ∈ rules.map Prod.fst) :
    key.1 ∈ FiniteTM0.sourceStates rules := by
  rcases List.mem_map.mp hkey with ⟨rule, hrule, hkey⟩
  exact List.mem_map.mpr ⟨rule, hrule, congrArg Prod.fst hkey⟩

private theorem deterministic_append_of_source_disjoint {numSymbols : Nat}
    {first second : FiniteTM0.Table numSymbols}
    (hfirst : FiniteTM0.Deterministic first)
    (hsecond : FiniteTM0.Deterministic second)
    (hdisjoint : List.Disjoint (FiniteTM0.sourceStates first)
      (FiniteTM0.sourceStates second)) :
    FiniteTM0.Deterministic (first ++ second) := by
  simp only [FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append hfirst hsecond
  rw [List.disjoint_iff_ne]
  intro firstKey hfirstKey secondKey hsecondKey heq
  exact (List.disjoint_iff_ne.mp hdisjoint)
    firstKey.1 (key_source_mem hfirstKey)
    secondKey.1 (key_source_mem hsecondKey)
    (congrArg Prod.fst heq)

/-- Every direct-rule source is at or after the first right-logical state. -/
theorem source_mem_directTable {base source : Nat}
    {c : Nat.Partrec.Code}
    (hsource : source ∈ FiniteTM0.sourceStates (directTable base c)) :
    rightLogicalBase base c ≤ source := by
  rcases List.mem_map.mp hsource with ⟨rule, hrule, hsourceEq⟩
  have hkey : rule.1 ∈ (directTable base c).map Prod.fst :=
    List.mem_map.mpr ⟨rule, hrule, rfl⟩
  rw [directTable_keys] at hkey
  rcases List.mem_map.mp hkey with ⟨key, _hkey, htranslated⟩
  have hfirst : rightLogicalBase base c + key.1 = rule.1.1 :=
    congrArg Prod.fst htranslated
  change rule.1.1 = source at hsourceEq
  calc
    rightLogicalBase base c ≤ rightLogicalBase base c + key.1 :=
      Nat.le_add_right _ _
    _ = rule.1.1 := hfirst
    _ = source := hsourceEq

/-- Every source of the initializer/direct shared core is fresh with respect
to the bounded controller. -/
theorem source_mem_coreTable {base source : Nat} {c : Nat.Partrec.Code}
    (hsource : source ∈ FiniteTM0.sourceStates (coreTable base c)) :
    controllerCoreEntry base c ≤ source := by
  simp only [coreTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hsource
  rcases hsource with hinitializer | hdirect
  · exact (CanonicalInitializerProgram.source_mem_table hinitializer).1
  · have hlower := source_mem_directTable hdirect
    have hentry : controllerCoreEntry base c ≤ rightLogicalBase base c := by
      simp [rightLogicalBase, initializerEnd,
        CanonicalInitializerProgram.exitState]
      omega
    exact hentry.trans hlower

/-- Initializer sources lie strictly before every direct-rule source. -/
theorem initializer_direct_source_disjoint (base : Nat)
    (c : Nat.Partrec.Code) :
    List.Disjoint
      (FiniteTM0.sourceStates (initializerTable base c))
      (FiniteTM0.sourceStates (directTable base c)) := by
  rw [List.disjoint_iff_ne]
  intro initializerSource hinitializer directSource hdirect heq
  have hi := CanonicalInitializerProgram.source_mem_table hinitializer
  have hd := source_mem_directTable hdirect
  apply Nat.ne_of_lt (hi.2.trans_le hd)
  exact heq

/-- The complete shared canonical core is deterministic. -/
theorem coreTable_deterministic (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Deterministic (coreTable base c) := by
  exact deterministic_append_of_source_disjoint
    (CanonicalInitializerProgram.table_deterministic
      (controllerCoreEntry base c) c numTags initializerGrowth
      (initializerExitFor base c))
    (directTable_deterministic base c)
    (initializer_direct_source_disjoint base c)

/-- The final code-dependent finite table has unique transition keys. -/
theorem table_deterministic (base : Nat) (c : Nat.Partrec.Code) :
    FiniteTM0.Deterministic (table base c) := by
  apply BoundedMarkerProgram.table_deterministic
  · exact commands_returnTags_nodup base c
  · exact coreTable_deterministic base c
  · intro source hsource
    rw [controllerCoreEntry_eq base c]
    exact source_mem_coreTable hsource

end

end CounterControlDeterministic
end Hooper
end Kari
end LeanWang
