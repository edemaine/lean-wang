/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerContinuation
import LeanWang.Kari.Hooper.CounterControlDeterministic

/-!
# One-step semantics of counter-controller glue rules

The symbolic counter plan describes the symbols accepted by a direct rule
using `RawRead`.  This module gives that description its semantic predicate
and connects every generated direct rule to an exact one-step transition of
the complete linked machine.
-/

namespace LeanWang
namespace Kari
namespace Hooper

open Turing
open BoundedMarkerProgram

namespace CounterControlPlan.RawRead

noncomputable section

/-- A symbolic direct-rule read condition accepts a concrete tagged tape
symbol.  `nonblank` includes both boundary markers and return tags. -/
def Matches (read : CounterControlPlan.RawRead)
    (symbol : Symbol CounterControlPlan.numTags) : Prop :=
  match read with
  | .blank => symbol = blankSymbol
  | .boundary label => symbol = boundarySymbol label
  | .nonblank => symbol ≠ blankSymbol

instance (read : CounterControlPlan.RawRead)
    (symbol : Symbol CounterControlPlan.numTags) :
    Decidable (Matches read symbol) := by
  cases read <;> simp only [Matches] <;> infer_instance

/-- `symbolsForRead` enumerates exactly the concrete symbols accepted by a
symbolic read condition. -/
theorem mem_symbolsForRead_iff (read : CounterControlPlan.RawRead)
    (symbol : Symbol CounterControlPlan.numTags) :
    symbol ∈ CounterControlPlan.symbolsForRead read ↔
      Matches read symbol := by
  cases read with
  | blank => simp [CounterControlPlan.symbolsForRead, Matches]
  | boundary label => simp [CounterControlPlan.symbolsForRead, Matches]
  | nonblank =>
      simpa [CounterControlPlan.symbolsForRead, Matches] using
        BoundedMarkerContinuation.mem_nonblankSymbols_iff symbol

end

end CounterControlPlan.RawRead

namespace CounterControlDirectSemantics

open CounterControlPlan CounterControlDeterministic

noncomputable section

/-! ## Membership and exact lookup -/

/-- Every concrete instance of a generated symbolic direct rule occurs in
the complete controller table. -/
theorem directRule_mem_table (base : Nat) (c : Nat.Partrec.Code)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (symbol : Symbol numTags) (hmatch : rule.read.Matches symbol) :
    FiniteTM0.Rule.mk (resolve base c rule.source) symbol
        (resolve base c rule.target)
        (liftAction (MarkerMachine.moveAction
          (orient rule.growth rule.direction))) ∈
      CounterControlPlan.table base c := by
  have hsymbol : symbol ∈ symbolsForRead rule.read :=
    (RawRead.mem_symbolsForRead_iff rule.read symbol).2 hmatch
  unfold CounterControlPlan.table BoundedMarkerProgram.table coreTable directTable
  simp only [List.mem_append]
  right
  right
  apply List.mem_flatMap.mpr
  refine ⟨rule, hrule, ?_⟩
  exact List.mem_map.mpr ⟨symbol, hsymbol, rfl⟩

/-- Determinism of the full linked table turns generated-rule membership
into its unique executable lookup result. -/
theorem lookupAction_directRule (base : Nat) (c : Nat.Partrec.Code)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (symbol : Symbol numTags) (hmatch : rule.read.Matches symbol) :
    FiniteTM0.lookupAction (CounterControlPlan.table base c)
        (resolve base c rule.source) symbol =
      some (resolve base c rule.target,
        liftAction (MarkerMachine.moveAction
          (orient rule.growth rule.direction))) := by
  apply (FiniteTM0.lookupAction_eq_some_iff_of_deterministic
    (table_deterministic base c)).2
  exact directRule_mem_table base c rule hrule symbol hmatch

/-! ## Exact one-step execution -/

/-- The semantic transition function of the complete table executes a
generated direct rule as the prescribed physical head move. -/
theorem machine_directRule (base : Nat) (c : Nat.Partrec.Code)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (symbol : Symbol numTags) (hmatch : rule.read.Matches symbol) :
    FiniteTM0.machine (CounterControlPlan.table base c)
        (resolve base c rule.source) symbol =
      some (resolve base c rule.target,
        Turing.TM0.Stmt.move (orient rule.growth rule.direction)) := by
  rw [FiniteTM0.machine_apply,
    lookupAction_directRule base c rule hrule symbol hmatch]
  cases orient rule.growth rule.direction <;> rfl

/-- On a full tape whose scanned symbol satisfies the raw read condition,
the complete linked machine takes exactly one step to the resolved target
state and moves in the rule's physical direction. -/
theorem step_directRule (base : Nat) (c : Nat.Partrec.Code)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : rule.read.Matches T.read) :
    FullTM0.step (FiniteTM0.machine (CounterControlPlan.table base c))
        ⟨resolve base c rule.source, T⟩ =
      some ⟨resolve base c rule.target,
        T.move (orient rule.growth rule.direction)⟩ := by
  simp only [FullTM0.step]
  rw [machine_directRule base c rule hrule T.read hmatch]
  rfl

/-- Reachability form of `step_directRule`, convenient for composing direct
glue transitions with bounded-search executions. -/
theorem reaches_directRule (base : Nat) (c : Nat.Partrec.Code)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : rule.read.Matches T.read) :
    FullTM0.Reaches (FiniteTM0.machine (CounterControlPlan.table base c))
      ⟨resolve base c rule.source, T⟩
      ⟨resolve base c rule.target,
        T.move (orient rule.growth rule.direction)⟩ := by
  apply Relation.ReflTransGen.single
  exact step_directRule base c rule hrule T hmatch

end

end CounterControlDirectSemantics
end Hooper
end Kari
end LeanWang
