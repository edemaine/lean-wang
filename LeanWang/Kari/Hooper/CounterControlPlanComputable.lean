/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgramComputable
import LeanWang.Kari.Hooper.CanonicalInitializerProgramComputable
import LeanWang.Kari.Hooper.CounterControlPlan

/-!
# Uniform effectiveness of the compiled counter controller

The symbolic counter program is fixed, but its concrete state allocation and
canonical initializer depend on the source code.  This file proves that the
complete finite table produced by `CounterControlPlan` varies primitive
recursively with that code.  Together with the semantic compiler theorems,
this is the effectiveness input needed by the final many-one reduction.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPlan

open Turing
open BoundedMarkerProgram

noncomputable section

/-! ## Concrete state allocation -/

private theorem controllerBlockEnd_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code =>
      BoundedMarkerProgram.commandOffset base
        (CanonicalInitializer.radius c) numTags := by
  exact BoundedMarkerProgram.commandOffset_primrec.comp
    (Primrec.pair (Primrec.const base)
      (Primrec.pair CanonicalInitializer.radius_primrec
        (Primrec.const numTags)))

theorem controllerReturn_primrec (base : Nat) (growth : Turing.Dir) :
    Primrec fun c : Nat.Partrec.Code => controllerReturn base c growth := by
  cases growth
  · exact controllerBlockEnd_primrec base
  · exact Primrec.succ.comp (controllerBlockEnd_primrec base)

theorem controllerCoreEntry_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => controllerCoreEntry base c := by
  exact Primrec.nat_add.comp (controllerBlockEnd_primrec base)
    (Primrec.const 2)

theorem initializerEnd_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => initializerEnd base c := by
  exact CanonicalInitializerProgram.exitState_primrec numTags
    (controllerCoreEntry_primrec base)

theorem rightLogicalBase_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => rightLogicalBase base c :=
  initializerEnd_primrec base

theorem rightDirectBase_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => rightDirectBase base c := by
  exact Primrec.nat_add.comp (rightLogicalBase_primrec base)
    (Primrec.const logicalSpan)

theorem leftLogicalBase_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => leftLogicalBase base c := by
  exact Primrec.nat_add.comp (rightDirectBase_primrec base)
    (Primrec.const directSpan)

theorem leftDirectBase_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => leftDirectBase base c := by
  exact Primrec.nat_add.comp (leftLogicalBase_primrec base)
    (Primrec.const logicalSpan)

theorem logicalBase_primrec (base : Nat) (growth : Turing.Dir) :
    Primrec fun c : Nat.Partrec.Code => logicalBase base c growth := by
  cases growth
  · exact leftLogicalBase_primrec base
  · exact rightLogicalBase_primrec base

theorem directBase_primrec (base : Nat) (growth : Turing.Dir) :
    Primrec fun c : Nat.Partrec.Code => directBase base c growth := by
  cases growth
  · exact leftDirectBase_primrec base
  · exact rightDirectBase_primrec base

theorem logicalState_primrec_of (base : Nat) (growth : Turing.Dir)
    {state : Nat.Partrec.Code → Nat} (hstate : Primrec state) :
    Primrec fun c => logicalState base c growth (state c) := by
  exact Primrec.nat_add.comp (logicalBase_primrec base growth) hstate

theorem logicalState_primrec (base : Nat) (growth : Turing.Dir)
    (state : Nat) :
    Primrec fun c : Nat.Partrec.Code => logicalState base c growth state :=
  logicalState_primrec_of base growth (Primrec.const state)

theorem directState_primrec (base : Nat) (address : DirectAddress) :
    Primrec fun c : Nat.Partrec.Code => directState base c address := by
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (directBase_primrec base address.growth)
      (Primrec.const (address.counterState * directStride)))
    (Primrec.const address.slot)

theorem searchState_primrec (base : Nat) (address : SearchAddress) :
    Primrec fun c : Nat.Partrec.Code => searchState base c address := by
  exact BoundedMarkerProgram.commandOffset_primrec.comp
    (Primrec.pair (Primrec.const base)
      (Primrec.pair CanonicalInitializer.radius_primrec
        (Primrec.const (searchIndex address))))

theorem resolve_primrec (base : Nat) (ref : ControlRef) :
    Primrec fun c : Nat.Partrec.Code => resolve base c ref := by
  cases ref with
  | logical growth state => exact logicalState_primrec base growth state
  | direct address => exact directState_primrec base address
  | search address => exact searchState_primrec base address
  | sharedReturn growth => exact controllerReturn_primrec base growth

/-! ## The varying tagged command list -/

private theorem boundaryCommandCode_primrec (base : Nat)
    (expected : Fin 5) (direction : Turing.Dir) (success : ControlRef)
    (tag : Fin numTags) (action : NavigationAction) :
    Primrec fun c : Nat.Partrec.Code =>
      (Sum.inl (expected, direction, resolve base c success, tag, action) :
        CommandCode numTags) := by
  exact Primrec.sumInl.comp
    (Primrec.pair (Primrec.const expected)
      (Primrec.pair (Primrec.const direction)
        (Primrec.pair (resolve_primrec base success)
          (Primrec.pair (Primrec.const tag) (Primrec.const action)))))

private theorem tagCommandCode_primrec (base : Nat)
    (direction : Turing.Dir) (success : ControlRef) (tag : Fin numTags) :
    Primrec fun c : Nat.Partrec.Code =>
      (Sum.inr (Sum.inl (direction, resolve base c success, tag)) :
        CommandCode numTags) := by
  exact Primrec.sumInr.comp (Primrec.sumInl.comp
    (Primrec.pair (Primrec.const direction)
      (Primrec.pair (resolve_primrec base success) (Primrec.const tag))))

private theorem shiftCommandCode_primrec (base : Nat)
    (move : MarkerProgram.Move) (success : ControlRef) (tag : Fin numTags)
    (departure : Option Turing.Dir) (collision : Option ControlRef) :
    Primrec fun c : Nat.Partrec.Code =>
      (Sum.inr (Sum.inr
        (move, resolve base c success, tag, departure,
          collision.map (resolve base c))) : CommandCode numTags) := by
  have hcollision : Primrec fun c : Nat.Partrec.Code =>
      collision.map (resolve base c) := by
    cases collision with
    | none => exact Primrec.const none
    | some collision =>
        exact Primrec.option_some.comp (resolve_primrec base collision)
  exact Primrec.sumInr.comp (Primrec.sumInr.comp
    (Primrec.pair (Primrec.const move)
      (Primrec.pair (resolve_primrec base success)
        (Primrec.pair (Primrec.const tag)
          (Primrec.pair (Primrec.const departure) hcollision)))))

/-- Every fixed raw command compiles primitive recursively as the source code
changes the concrete state allocation. -/
theorem compileCommand_primrec (base : Nat) (tag : Fin rawCommands.length) :
    Primrec fun c : Nat.Partrec.Code => compileCommand base c tag := by
  unfold compileCommand
  generalize hraw : rawCommands.get tag = raw
  cases raw with
  | boundaryNavigation address expected direction success action =>
      exact BoundedMarkerProgram.command_ofCode_primrec.comp
        (boundaryCommandCode_primrec base expected
          (orient address.growth direction) success tag
          (compileNavigationAction address.growth action))
  | tagNavigation address direction success =>
      exact BoundedMarkerProgram.command_ofCode_primrec.comp
        (tagCommandCode_primrec base (orient address.growth direction)
          success tag)
  | markerShift address expected search shift success departure collision =>
      exact BoundedMarkerProgram.command_ofCode_primrec.comp
        (shiftCommandCode_primrec base
          ⟨expected, orient address.growth search,
            orient address.growth shift⟩ success tag
          (departure.map (orient address.growth)) collision)

/-- The complete fixed enumeration of tagged commands varies primitive
recursively with the source code. -/
theorem commands_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => commands base c := by
  exact Primrec.list_ofFn fun tag => compileCommand_primrec base tag

/-! ## The initializer and direct finite-control glue -/

private theorem canonicalSourceStateCode_primrec :
    Primrec fun c : Nat.Partrec.Code =>
      SourceControl.encodeState (SourceRegisterSemantics.canonical c).state := by
  exact (Primrec.const
    (SourceControl.encodeState (default : SourceMachine.State))).of_eq
      fun c => by
        apply congrArg SourceControl.encodeState
        exact SourceMachine.canonical_q c

private theorem canonicalHeadDigit_primrec :
    Primrec fun c : Nat.Partrec.Code =>
      SourceControl.symbolDigit
        (UniversalTM0Semantic.input c).headI :=
  UniversalTM0Semantic.input_head_nat_primrec SourceControl.symbolDigit

private theorem canonicalControlCode_primrec :
    Primrec fun c : Nat.Partrec.Code =>
      SourceProgram.controlCode (default : SourceMachine.State)
        (UniversalTM0Semantic.input c).headI := by
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp canonicalSourceStateCode_primrec
      (Primrec.const SourceControl.numSymbols)) canonicalHeadDigit_primrec

theorem canonicalEntry_primrec (base : Nat) (growth : Turing.Dir) :
    Primrec fun c : Nat.Partrec.Code => canonicalEntry base c growth := by
  exact (logicalState_primrec_of base growth
    canonicalControlCode_primrec).of_eq fun c => by
      rw [canonicalEntry, GlobalSourceSemantics.canonicalCounterCfg_state]

theorem initializerExitFor_primrec (base : Nat) (tag : Fin numTags) :
    Primrec fun c : Nat.Partrec.Code => initializerExitFor base c tag := by
  exact canonicalEntry_primrec base (initializerGrowth tag)

/-- The complete tag-dispatched canonical initializer varies primitive
recursively with the source code. -/
theorem initializerTable_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => initializerTable base c := by
  exact CanonicalInitializerProgram.table_primrec initializerGrowth
    (fun c tag => initializerExitFor base c tag)
    (controllerCoreEntry_primrec base)
    (fun tag => initializerExitFor_primrec base tag)

private theorem compiledDirectRule_primrec (base : Nat)
    (rule : RawDirectRule) (symbol : Symbol numTags) :
    Primrec fun c : Nat.Partrec.Code =>
      FiniteTM0.Rule.mk (resolve base c rule.source) symbol
        (resolve base c rule.target)
        (liftAction (MarkerMachine.moveAction
          (orient rule.growth rule.direction))) := by
  exact Primrec.pair
    (Primrec.pair (resolve_primrec base rule.source) (Primrec.const symbol))
    (Primrec.pair (resolve_primrec base rule.target)
      (Primrec.const (liftAction (numTags := numTags)
        (MarkerMachine.moveAction (orient rule.growth rule.direction)))))

private theorem directRuleTableFrom_primrec (base : Nat)
    (rule : RawDirectRule) (symbols : List (Symbol numTags)) :
    Primrec fun c : Nat.Partrec.Code => symbols.map fun symbol =>
      FiniteTM0.Rule.mk (resolve base c rule.source) symbol
        (resolve base c rule.target)
        (liftAction (MarkerMachine.moveAction
          (orient rule.growth rule.direction))) := by
  induction symbols with
  | nil => exact Primrec.const []
  | cons symbol symbols ih =>
      exact Primrec.list_cons.comp
        (compiledDirectRule_primrec base rule symbol) ih

theorem directRuleTable_primrec (base : Nat) (rule : RawDirectRule) :
    Primrec fun c : Nat.Partrec.Code => directRuleTable base c rule := by
  exact directRuleTableFrom_primrec base rule (symbolsForRead rule.read)

private theorem directTableFrom_primrec (base : Nat)
    (rules : List RawDirectRule) :
    Primrec fun c : Nat.Partrec.Code => rules.flatMap fun rule =>
      directRuleTable base c rule := by
  induction rules with
  | nil => exact Primrec.const []
  | cons rule rules ih =>
      exact Primrec.list_append.comp (directRuleTable_primrec base rule) ih

/-- All direct glue rules vary primitive recursively with their allocated
source and target states. -/
theorem directTable_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => directTable base c := by
  exact directTableFrom_primrec base rawDirectRules

theorem coreTable_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => coreTable base c := by
  exact Primrec.list_append.comp (initializerTable_primrec base)
    (directTable_primrec base)

/-! ## Complete finite table -/

/-- The complete two-orientation counter-controller table, including every
bounded search, the tag-selected canonical initializer, and all direct glue,
is primitive recursive in the designated source code. -/
theorem table_primrec (base : Nat) :
    Primrec fun c : Nat.Partrec.Code => CounterControlPlan.table base c := by
  exact BoundedMarkerProgram.table_primrec_of
    (Primrec.const base) CanonicalInitializer.radius_primrec
    (commands_primrec base) (coreTable_primrec base)

/-- Computable form used by the final many-one reduction. -/
theorem table_computable (base : Nat) :
    Computable fun c : Nat.Partrec.Code => CounterControlPlan.table base c :=
  (table_primrec base).to_comp

end

end CounterControlPlan
end Hooper
end Kari
end LeanWang
