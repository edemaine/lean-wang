/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Finite-control support facts for Mathlib's `PartrecToTM2` evaluator.

The eventual `TM2TableCompiler` needs finite state data for the TM2 evaluator.
Mathlib already provides the finite reachable-label set
`Turing.PartrecToTM2.codeSupp`; this file packages the exact support facts
needed for the evaluator configuration used by the reduction.
-/

noncomputable section

namespace LeanWang

namespace PartrecToTM2Support

open Turing
open Turing.PartrecToTM2

/-- The evaluator label used by `PartrecToTM2.init tc [0]`. -/
def startLabel (tc : ToPartrec.Code) : Λ' :=
  trNormal tc Cont'.halt

/-- Finite set of TM2 labels reachable from the evaluator start label. -/
def labels (tc : ToPartrec.Code) : Finset Λ' :=
  codeSupp tc Cont'.halt

/-- The four stack names used by Mathlib's `PartrecToTM2` evaluator. -/
def stackNames : List K' :=
  [K'.main, K'.rev, K'.aux, K'.stack]

theorem mem_stackNames (k : K') : k ∈ stackNames := by
  cases k <;> simp [stackNames]

/-- The finite stack alphabet used by Mathlib's `PartrecToTM2` evaluator. -/
def stackAlphabet : Finset Γ' :=
  Finset.univ

theorem mem_stackAlphabet (a : Γ') : a ∈ stackAlphabet := by
  simp [stackAlphabet]

theorem startLabel_mem_labels (tc : ToPartrec.Code) :
    startLabel tc ∈ labels tc :=
  codeSupp_self tc Cont'.halt (trStmts₁_self _)

theorem init_label_mem_labels (tc : ToPartrec.Code) :
    (init tc [0]).l ∈ Finset.insertNone (labels tc) := by
  exact Finset.some_mem_insertNone.2 (startLabel_mem_labels tc)

/--
Mathlib's support theorem specialized to the evaluator label set.

The `Inhabited` instance is deliberately local: `TM2.Supports` stores the start
label as `default`, and for the reduction this default is `startLabel tc`.
-/
theorem tr_supports_labels (tc : ToPartrec.Code) :
    @TM2.Supports _ _ _ _ ⟨startLabel tc⟩ tr (labels tc) := by
  change @TM2.Supports _ _ _ _ ⟨trNormal tc Cont'.halt⟩ tr (codeSupp tc Cont'.halt)
  exact tr_supports tc Cont'.halt

/--
Finite set of TM2 statement substates needed to execute all evaluator labels in
`labels tc`.
-/
def statements (tc : ToPartrec.Code) : Finset (Option Stmt') :=
  by
    classical
    exact TM2.stmts tr (labels tc)

theorem label_statement_mem {tc : ToPartrec.Code} {q : Λ'}
    (hq : q ∈ labels tc) :
    some (tr q) ∈ statements tc := by
  classical
  exact Finset.some_mem_insertNone.2
    (Finset.mem_biUnion.2 ⟨q, hq, TM2.stmts₁_self⟩)

theorem statement_supports {tc : ToPartrec.Code} {stmt : Stmt'}
    (hstmt : some stmt ∈ statements tc) :
    TM2.SupportsStmt (labels tc) stmt := by
  classical
  letI : Inhabited Λ' := ⟨startLabel tc⟩
  exact TM2.stmts_supportsStmt (tr_supports_labels tc) hstmt

theorem labels_step_closed {tc : ToPartrec.Code}
    {cfg cfg' : Cfg'}
    (hstep : cfg' ∈ TM2.step tr cfg)
    (hcfg : cfg.l ∈ Finset.insertNone (labels tc)) :
    cfg'.l ∈ Finset.insertNone (labels tc) := by
  letI : Inhabited Λ' := ⟨startLabel tc⟩
  exact TM2.step_supports tr (tr_supports_labels tc) hstep hcfg

theorem labels_reaches_closed {tc : ToPartrec.Code}
    {cfg cfg' : Cfg'}
    (hreach : TM2.Reaches tr cfg cfg')
    (hcfg : cfg.l ∈ Finset.insertNone (labels tc)) :
    cfg'.l ∈ Finset.insertNone (labels tc) := by
  induction hreach with
  | refl =>
      exact hcfg
  | tail _ hstep ih =>
      exact labels_step_closed hstep ih

theorem init_reaches_label_mem {tc : ToPartrec.Code}
    {cfg : Cfg'}
    (hreach : TM2.Reaches tr (init tc [0]) cfg) :
    cfg.l ∈ Finset.insertNone (labels tc) :=
  labels_reaches_closed hreach (init_label_mem_labels tc)

end PartrecToTM2Support

end LeanWang

end
