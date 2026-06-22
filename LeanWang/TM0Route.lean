/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PartrecToTM2Support
import Mathlib.Data.Nat.Pairing

/-!
The Mathlib TM0 route for the machine side of the reduction.

Mathlib already translates TM2 machines to TM1 machines and TM1 machines to TM0
machines. The `PartrecToTM2` evaluator, however, starts from a code-dependent
TM2 label rather than the default label used by `TM2.eval`. This file packages a
code-specific relabeling where that evaluator label is the default start label,
so the standard Mathlib translation theorems apply.
-/

noncomputable section

namespace LeanWang

namespace TM0Route

open Turing
open Turing.PartrecToTM2

/-- Relabel the target labels of a TM2 statement. -/
def relabelTM2Stmt {K : Type u} {Γ : K → Type v} {Λ : Type w} {Λ' : Type x}
    {σ : Type y} (f : Λ → Λ') :
    Turing.TM2.Stmt Γ Λ σ → Turing.TM2.Stmt Γ Λ' σ
  | Turing.TM2.Stmt.push k g q => Turing.TM2.Stmt.push k g (relabelTM2Stmt f q)
  | Turing.TM2.Stmt.peek k g q => Turing.TM2.Stmt.peek k g (relabelTM2Stmt f q)
  | Turing.TM2.Stmt.pop k g q => Turing.TM2.Stmt.pop k g (relabelTM2Stmt f q)
  | Turing.TM2.Stmt.load g q => Turing.TM2.Stmt.load g (relabelTM2Stmt f q)
  | Turing.TM2.Stmt.branch g q₁ q₂ =>
      Turing.TM2.Stmt.branch g (relabelTM2Stmt f q₁) (relabelTM2Stmt f q₂)
  | Turing.TM2.Stmt.goto g => Turing.TM2.Stmt.goto fun s => f (g s)
  | Turing.TM2.Stmt.halt => Turing.TM2.Stmt.halt

theorem relabelTM2Stmt_supportsStmt {K : Type u} {Γ : K → Type v}
    {Λ : Type w} {Λ' : Type x} {σ : Type y} {S : Finset Λ} {S' : Finset Λ'}
    (f : Λ → Λ') (hf : ∀ q, q ∈ S → f q ∈ S') :
    ∀ q : Turing.TM2.Stmt Γ Λ σ,
      Turing.TM2.SupportsStmt S q →
        Turing.TM2.SupportsStmt S' (relabelTM2Stmt f q) := by
  intro q
  induction q with
  | push k g q IH =>
      exact fun h => IH h
  | peek k g q IH =>
      exact fun h => IH h
  | pop k g q IH =>
      exact fun h => IH h
  | load g q IH =>
      exact fun h => IH h
  | branch g q₁ q₂ IH₁ IH₂ =>
      exact fun h => ⟨IH₁ h.1, IH₂ h.2⟩
  | goto g =>
      exact fun h v => hf (g v) (h v)
  | halt =>
      exact fun _ => trivial

/-- Relabel a TM2 configuration. -/
def relabelTM2Cfg {K : Type u} {Γ : K → Type v} {Λ : Type w} {Λ' : Type x}
    {σ : Type y} (f : Λ → Λ') :
    Turing.TM2.Cfg Γ Λ σ → Turing.TM2.Cfg Γ Λ' σ :=
  fun c => { l := c.l.map f, var := c.var, stk := c.stk }

theorem relabelTM2Cfg_stepAux {K : Type u} {Γ : K → Type v} {Λ : Type w}
    {Λ' : Type x} {σ : Type y} [DecidableEq K] (f : Λ → Λ')
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    relabelTM2Cfg f (Turing.TM2.stepAux q v S) =
      Turing.TM2.stepAux (relabelTM2Stmt f q) v S := by
  induction q generalizing v S with
  | push k g q IH =>
      simp [relabelTM2Stmt, Turing.TM2.stepAux, IH]
  | peek k g q IH =>
      simp [relabelTM2Stmt, Turing.TM2.stepAux, IH]
  | pop k g q IH =>
      simp [relabelTM2Stmt, Turing.TM2.stepAux, IH]
  | load g q IH =>
      simp [relabelTM2Stmt, Turing.TM2.stepAux, IH]
  | branch g q₁ q₂ IH₁ IH₂ =>
      by_cases h : g v = true
      · simp [relabelTM2Stmt, Turing.TM2.stepAux, h, IH₁]
      · simp [relabelTM2Stmt, Turing.TM2.stepAux, h, IH₂]
  | goto g =>
      rfl
  | halt =>
      rfl

/-- The `PartrecToTM2` stack names. -/
abbrev PartrecStack : Type :=
  Turing.PartrecToTM2.K'

/-- The `PartrecToTM2` stack alphabet, viewed as a constant family. -/
abbrev PartrecStackSymbol (_k : PartrecStack) : Type :=
  Turing.PartrecToTM2.Γ'

/-- The `PartrecToTM2` local state type. -/
abbrev PartrecVar : Type :=
  Option Turing.PartrecToTM2.Γ'

/-- Mathlib's `PartrecToTM2` evaluator at the local constant stack-alphabet type. -/
def partrecTM2 :
    Turing.PartrecToTM2.Λ' →
      Turing.TM2.Stmt PartrecStackSymbol Turing.PartrecToTM2.Λ' PartrecVar :=
  Turing.PartrecToTM2.tr

/--
Code-specific wrapper for evaluator labels.

The wrapper lets us choose a code-dependent `Inhabited` instance, so
`TM2.init` starts at the evaluator label for this particular code.
-/
structure StartedLabel (tc : Turing.ToPartrec.Code) where
  val : Turing.PartrecToTM2.Λ'

namespace StartedLabel

def wrap (tc : Turing.ToPartrec.Code) (q : Turing.PartrecToTM2.Λ') : StartedLabel tc :=
  ⟨q⟩

theorem wrap_injective (tc : Turing.ToPartrec.Code) :
    Function.Injective (wrap tc) := by
  intro q r h
  cases h
  rfl

instance (tc : Turing.ToPartrec.Code) : Inhabited (StartedLabel tc) :=
  ⟨wrap tc (PartrecToTM2Support.startLabel tc)⟩

end StartedLabel

/--
The code-dependent TM2 evaluator whose default label is the evaluator start
label for `tc`.
-/
def partrecStartedTM2 (tc : Turing.ToPartrec.Code) :
    StartedLabel tc →
      Turing.TM2.Stmt PartrecStackSymbol (StartedLabel tc) PartrecVar :=
  fun q => relabelTM2Stmt (StartedLabel.wrap tc) (partrecTM2 q.val)

noncomputable def partrecStartedTM2Labels (tc : Turing.ToPartrec.Code) :
    Finset (StartedLabel tc) :=
  (PartrecToTM2Support.labels tc).map
    ⟨StartedLabel.wrap tc, StartedLabel.wrap_injective tc⟩

theorem mem_partrecStartedTM2Labels (tc : Turing.ToPartrec.Code)
    (q : StartedLabel tc) :
    q ∈ partrecStartedTM2Labels tc ↔ q.val ∈ PartrecToTM2Support.labels tc := by
  constructor
  · intro h
    rcases Finset.mem_map.1 h with ⟨r, hr, hq⟩
    cases hq
    exact hr
  · intro h
    refine Finset.mem_map.2 ⟨q.val, h, ?_⟩
    cases q
    rfl

theorem partrecStartedTM2_supports (tc : Turing.ToPartrec.Code) :
    Turing.TM2.Supports (partrecStartedTM2 tc) (partrecStartedTM2Labels tc) := by
  constructor
  · change StartedLabel.wrap tc (PartrecToTM2Support.startLabel tc) ∈
      partrecStartedTM2Labels tc
    exact Finset.mem_map.2
      ⟨PartrecToTM2Support.startLabel tc,
        PartrecToTM2Support.startLabel_mem_labels tc, rfl⟩
  · intro q hq
    exact relabelTM2Stmt_supportsStmt (StartedLabel.wrap tc)
      (fun r hr => (mem_partrecStartedTM2Labels tc (StartedLabel.wrap tc r)).2 hr)
      (partrecTM2 q.val)
      ((PartrecToTM2Support.tr_supports_labels tc).2 q.val
        ((mem_partrecStartedTM2Labels tc q).1 hq))

theorem partrecStartedTM2_step_eq_map (tc : Turing.ToPartrec.Code)
    (c : Turing.TM2.Cfg PartrecStackSymbol Turing.PartrecToTM2.Λ' PartrecVar) :
    Turing.TM2.step (partrecStartedTM2 tc)
        (relabelTM2Cfg (StartedLabel.wrap tc) c) =
      (Turing.TM2.step partrecTM2 c).map
        (relabelTM2Cfg (StartedLabel.wrap tc)) := by
  cases c with
  | mk l var stk =>
    cases l with
    | none =>
        rfl
    | some q =>
        change
          some (Turing.TM2.stepAux (relabelTM2Stmt (StartedLabel.wrap tc) (partrecTM2 q))
            var stk) =
            some (relabelTM2Cfg (StartedLabel.wrap tc)
              (Turing.TM2.stepAux (partrecTM2 q) var stk))
        exact congrArg some
          ((relabelTM2Cfg_stepAux (StartedLabel.wrap tc) (partrecTM2 q) var stk).symm)

/--
The relabeled started machine refines the original `PartrecToTM2` machine
step-for-step.
-/
theorem partrecStartedTM2_respects (tc : Turing.ToPartrec.Code) :
    StateTransition.Respects
      (Turing.TM2.step partrecTM2)
      (Turing.TM2.step (partrecStartedTM2 tc))
      (fun c₁ c₂ =>
        relabelTM2Cfg (StartedLabel.wrap tc) c₁ = c₂) := by
  intro a₁ a₂ hrel
  subst a₂
  cases hstep : Turing.TM2.step partrecTM2 a₁ with
  | none =>
      simp [partrecStartedTM2_step_eq_map, hstep]
  | some b₁ =>
      refine ⟨relabelTM2Cfg (StartedLabel.wrap tc) b₁, rfl, ?_⟩
      exact Relation.TransGen.single (by simp [partrecStartedTM2_step_eq_map, hstep])

/-- The unary input stack for evaluating a code at input `0`. -/
def partrecStartedTM2Input : List (PartrecStackSymbol Turing.PartrecToTM2.K'.main) :=
  Turing.PartrecToTM2.trList [0]

/-- Mathlib's `PartrecToTM2` initial evaluator configuration at the local aliases. -/
def partrecInit (tc : Turing.ToPartrec.Code) :
    Turing.TM2.Cfg PartrecStackSymbol Turing.PartrecToTM2.Λ' PartrecVar :=
  Turing.PartrecToTM2.init tc [0]

theorem partrecStartedTM2_init_relabel (tc : Turing.ToPartrec.Code) :
    relabelTM2Cfg (StartedLabel.wrap tc) (partrecInit tc) =
      Turing.TM2.init Turing.PartrecToTM2.K'.main partrecStartedTM2Input := by
  change
    (Turing.TM2.Cfg.mk
      (some (StartedLabel.wrap tc (PartrecToTM2Support.startLabel tc)))
      (none : PartrecVar)
      (Turing.PartrecToTM2.K'.elim (Turing.PartrecToTM2.trList [0]) [] [] []) :
        Turing.TM2.Cfg PartrecStackSymbol (StartedLabel tc) PartrecVar) =
    Turing.TM2.Cfg.mk
      (some (default : StartedLabel tc))
      (default : PartrecVar)
      (Function.update (fun _ : Turing.PartrecToTM2.K' => [])
        Turing.PartrecToTM2.K'.main partrecStartedTM2Input)
  rw [Turing.TM2.Cfg.mk.injEq]
  constructor
  · rfl
  constructor
  · rfl
  · funext k
    cases k <;> simp [partrecStartedTM2Input]

theorem part_dom_map_iff {α β : Type} (f : α → β) (p : Part α) :
    (f <$> p).Dom ↔ p.Dom := by
  rw [Part.map_eq_map]
  rfl

/--
The code-specific started TM2 evaluator has the same halting domain as the
original `PartrecToTM2.init` evaluator configuration.
-/
theorem partrecStartedTM2_eval_dom_iff_partrec (tc : Turing.ToPartrec.Code) :
    (Turing.TM2.eval (partrecStartedTM2 tc)
      Turing.PartrecToTM2.K'.main partrecStartedTM2Input).Dom ↔
      (StateTransition.eval
        (Turing.TM2.step partrecTM2)
        (partrecInit tc)).Dom := by
  unfold Turing.TM2.eval
  exact (part_dom_map_iff
      (fun c : Turing.TM2.Cfg PartrecStackSymbol (StartedLabel tc) PartrecVar =>
        c.stk Turing.PartrecToTM2.K'.main)
      (StateTransition.eval
        (Turing.TM2.step (partrecStartedTM2 tc))
        (Turing.TM2.init Turing.PartrecToTM2.K'.main partrecStartedTM2Input))).trans
    (StateTransition.tr_eval_dom
      (partrecStartedTM2_respects tc)
      (partrecStartedTM2_init_relabel tc))

/-- The TM1 machine obtained from the code-specific started TM2 evaluator. -/
def partrecStartedTM1Machine (tc : Turing.ToPartrec.Code) :=
  Turing.TM2to1.tr (partrecStartedTM2 tc)

noncomputable def partrecStartedTM1Labels (tc : Turing.ToPartrec.Code) :=
  Turing.TM2to1.trSupp (partrecStartedTM2 tc) (partrecStartedTM2Labels tc)

theorem partrecStartedTM1_supports (tc : Turing.ToPartrec.Code) :
    Turing.TM1.Supports (partrecStartedTM1Machine tc)
      (partrecStartedTM1Labels tc) := by
  exact Turing.TM2to1.tr_supports
    (M := partrecStartedTM2 tc)
    (S := partrecStartedTM2Labels tc)
    (partrecStartedTM2_supports tc)

/-- The TM1/TM0 input list obtained from the started TM2 input stack. -/
def partrecStartedTM0Input :
    List (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :=
  Turing.TM2to1.trInit (Γ := PartrecStackSymbol)
    Turing.PartrecToTM2.K'.main partrecStartedTM2Input

/-- The TM0 machine obtained by composing Mathlib's TM2-to-TM1 and TM1-to-TM0 reductions. -/
def partrecStartedTM0Machine (tc : Turing.ToPartrec.Code) :=
  Turing.TM1to0.tr (partrecStartedTM1Machine tc)

noncomputable def partrecStartedTM0Labels (tc : Turing.ToPartrec.Code) :=
  Turing.TM1to0.trStmts (partrecStartedTM1Machine tc)
    (partrecStartedTM1Labels tc)

noncomputable def partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code) :
    List (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  (partrecStartedTM0Labels tc).toList

theorem mem_partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :
    q ∈ partrecStartedTM0LabelList tc ↔ q ∈ partrecStartedTM0Labels tc := by
  simp [partrecStartedTM0LabelList]

/--
Finite support list for translated TM0 states, with the start/default state
forced to position `0`.
-/
noncomputable def partrecStartedTM0LabelSupportList (tc : Turing.ToPartrec.Code) :
    List (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  default :: partrecStartedTM0LabelList tc

theorem partrecStartedTM0_default_mem_labelSupportList (tc : Turing.ToPartrec.Code) :
    (default : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) ∈
      partrecStartedTM0LabelSupportList tc := by
  simp [partrecStartedTM0LabelSupportList]

theorem mem_partrecStartedTM0LabelSupportList_of_mem_labels
    {tc : Turing.ToPartrec.Code} {q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)}
    (hq : q ∈ partrecStartedTM0Labels tc) :
    q ∈ partrecStartedTM0LabelSupportList tc := by
  simp [partrecStartedTM0LabelSupportList, mem_partrecStartedTM0LabelList, hq]

/-- Numeric state list for the finite one-sided TM0 program extracted from `TM0Route`. -/
noncomputable def partrecStartedTM0States (tc : Turing.ToPartrec.Code) : List Nat :=
  List.range (partrecStartedTM0LabelSupportList tc).length

/-- Numeric start state corresponding to the default translated TM0 label. -/
def partrecStartedTM0Start : Nat :=
  0

theorem partrecStartedTM0Start_mem_states (tc : Turing.ToPartrec.Code) :
    partrecStartedTM0Start ∈ partrecStartedTM0States tc := by
  simp [partrecStartedTM0Start, partrecStartedTM0States, partrecStartedTM0LabelSupportList]

theorem partrecStartedTM0LabelSupportList_get_zero (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM0LabelSupportList tc)[0]? =
      some (default : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) := by
  simp [partrecStartedTM0LabelSupportList]

/-- Choose an index for a state known to occur in the finite support list. -/
noncomputable def partrecStartedTM0StateIndexOfMem (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) :
    Fin (partrecStartedTM0LabelSupportList tc).length :=
  Classical.choose (List.get_of_mem hq)

theorem partrecStartedTM0StateIndexOfMem_get (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) :
    (partrecStartedTM0LabelSupportList tc).get
      (partrecStartedTM0StateIndexOfMem tc q hq) = q :=
  Classical.choose_spec (List.get_of_mem hq)

/-- Numeric code for a supported translated TM0 state. -/
noncomputable def partrecStartedTM0StateCodeOfMem (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) : Nat :=
  (partrecStartedTM0StateIndexOfMem tc q hq).val

theorem partrecStartedTM0StateCodeOfMem_mem_states (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) :
    partrecStartedTM0StateCodeOfMem tc q hq ∈ partrecStartedTM0States tc := by
  unfold partrecStartedTM0StateCodeOfMem partrecStartedTM0States
  exact List.mem_range.2 (partrecStartedTM0StateIndexOfMem tc q hq).isLt

theorem partrecStartedTM0StateCodeOfMem_get? (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) :
    (partrecStartedTM0LabelSupportList tc)[partrecStartedTM0StateCodeOfMem tc q hq]? =
      some q := by
  unfold partrecStartedTM0StateCodeOfMem
  rw [List.getElem?_eq_getElem (partrecStartedTM0StateIndexOfMem tc q hq).isLt]
  exact congrArg some (partrecStartedTM0StateIndexOfMem_get tc q hq)

/-- The finite cell values that can occur in one stack coordinate of the TM2-to-TM1 alphabet. -/
def partrecStartedTM0CellValues : List (Option Turing.PartrecToTM2.Γ') :=
  none :: (PartrecToTM2Support.stackAlphabetList.map some)

theorem mem_partrecStartedTM0CellValues (a : Option Turing.PartrecToTM2.Γ') :
    a ∈ partrecStartedTM0CellValues := by
  cases a with
  | none =>
      simp [partrecStartedTM0CellValues]
  | some a =>
      simp [partrecStartedTM0CellValues, PartrecToTM2Support.mem_stackAlphabetList a]

/-- Build the four-stack vector component of the TM2-to-TM1 alphabet. -/
def partrecStartedTM0StackVector
    (main rev aux stack : Option Turing.PartrecToTM2.Γ') :
    ∀ k : PartrecStack, Option (PartrecStackSymbol k)
  | Turing.PartrecToTM2.K'.main => main
  | Turing.PartrecToTM2.K'.rev => rev
  | Turing.PartrecToTM2.K'.aux => aux
  | Turing.PartrecToTM2.K'.stack => stack

theorem partrecStartedTM0StackVector_ext
    (v : ∀ k : PartrecStack, Option (PartrecStackSymbol k)) :
    partrecStartedTM0StackVector
      (v Turing.PartrecToTM2.K'.main)
      (v Turing.PartrecToTM2.K'.rev)
      (v Turing.PartrecToTM2.K'.aux)
      (v Turing.PartrecToTM2.K'.stack) = v := by
  funext k
  cases k <;> rfl

def partrecStartedTM0StackVectorToTuple
    (v : ∀ k : PartrecStack, Option (PartrecStackSymbol k)) :
    Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
      Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' :=
  (v Turing.PartrecToTM2.K'.main, v Turing.PartrecToTM2.K'.rev,
    v Turing.PartrecToTM2.K'.aux, v Turing.PartrecToTM2.K'.stack)

def partrecStartedTM0StackVectorOfTuple
    (p : Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
      Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ') :
    ∀ k : PartrecStack, Option (PartrecStackSymbol k) :=
  partrecStartedTM0StackVector p.1 p.2.1 p.2.2.1 p.2.2.2

def partrecStartedTM0StackVectorEquivTuple :
    (∀ k : PartrecStack, Option (PartrecStackSymbol k)) ≃
      Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
        Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' where
  toFun := partrecStartedTM0StackVectorToTuple
  invFun := partrecStartedTM0StackVectorOfTuple
  left_inv := by
    intro v
    exact partrecStartedTM0StackVector_ext v
  right_inv := by
    intro p
    rcases p with ⟨main, rev, aux, stack⟩
    rfl

instance instPrimcodablePartrecStartedTM0StackVector :
    Primcodable (∀ k : PartrecStack, Option (PartrecStackSymbol k)) :=
  Primcodable.ofEquiv
    (Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
      Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ')
    partrecStartedTM0StackVectorEquivTuple

instance instPrimcodablePartrecStartedTM0Symbol :
    Primcodable (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :=
  inferInstanceAs (Primcodable
    (Bool × (∀ k : PartrecStack, Option (PartrecStackSymbol k))))

/-- Explicit finite list of all stack-vector components of the TM2-to-TM1 alphabet. -/
def partrecStartedTM0StackVectors :
    List (∀ k : PartrecStack, Option (PartrecStackSymbol k)) :=
  partrecStartedTM0CellValues.flatMap fun main =>
    partrecStartedTM0CellValues.flatMap fun rev =>
      partrecStartedTM0CellValues.flatMap fun aux =>
        partrecStartedTM0CellValues.map fun stack =>
          partrecStartedTM0StackVector main rev aux stack

theorem mem_partrecStartedTM0StackVectors
    (v : ∀ k : PartrecStack, Option (PartrecStackSymbol k)) :
    v ∈ partrecStartedTM0StackVectors := by
  rw [← partrecStartedTM0StackVector_ext v]
  unfold partrecStartedTM0StackVectors
  simp only [List.mem_flatMap, List.mem_map]
  exact
    ⟨v Turing.PartrecToTM2.K'.main,
      mem_partrecStartedTM0CellValues _,
      v Turing.PartrecToTM2.K'.rev,
      mem_partrecStartedTM0CellValues _,
      v Turing.PartrecToTM2.K'.aux,
      mem_partrecStartedTM0CellValues _,
      v Turing.PartrecToTM2.K'.stack,
      mem_partrecStartedTM0CellValues _,
      rfl⟩

/-- Explicit finite list of all symbols in the TM0 machine produced by `TM0Route`. -/
def partrecStartedTM0SymbolList :
    List (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :=
  [false, true].flatMap fun bottom =>
    partrecStartedTM0StackVectors.map fun cells =>
      (bottom, cells)

theorem mem_partrecStartedTM0SymbolList
    (a : Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :
    a ∈ partrecStartedTM0SymbolList := by
  rcases a with ⟨bottom, cells⟩
  cases bottom <;>
    simp [partrecStartedTM0SymbolList, mem_partrecStartedTM0StackVectors]

theorem partrecStartedTM0Input_symbols (a : Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
    (_ha : a ∈ partrecStartedTM0Input) :
    a ∈ partrecStartedTM0SymbolList :=
  mem_partrecStartedTM0SymbolList a

/-- Numeric code for the four-stack vector component of a translated TM0 tape symbol. -/
def partrecStartedTM0StackVectorCode
    (v : ∀ k : PartrecStack, Option (PartrecStackSymbol k)) : Nat :=
  Nat.pair
    (PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.main))
    (Nat.pair
      (PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.rev))
      (Nat.pair
        (PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.aux))
        (PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.stack))))

theorem partrecStartedTM0StackVectorCode_injective :
    Function.Injective partrecStartedTM0StackVectorCode := by
  intro v w h
  unfold partrecStartedTM0StackVectorCode at h
  have hmain :
      PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.main) =
        PartrecToTM2Support.tapeSymbolCode (w Turing.PartrecToTM2.K'.main) :=
    (Nat.pair_eq_pair.mp h).1
  have htail := (Nat.pair_eq_pair.mp h).2
  have hrev :
      PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.rev) =
        PartrecToTM2Support.tapeSymbolCode (w Turing.PartrecToTM2.K'.rev) :=
    (Nat.pair_eq_pair.mp htail).1
  have htail' := (Nat.pair_eq_pair.mp htail).2
  have haux :
      PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.aux) =
        PartrecToTM2Support.tapeSymbolCode (w Turing.PartrecToTM2.K'.aux) :=
    (Nat.pair_eq_pair.mp htail').1
  have hstack :
      PartrecToTM2Support.tapeSymbolCode (v Turing.PartrecToTM2.K'.stack) =
        PartrecToTM2Support.tapeSymbolCode (w Turing.PartrecToTM2.K'.stack) :=
    (Nat.pair_eq_pair.mp htail').2
  funext k
  cases k
  · exact PartrecToTM2Support.tapeSymbolCode_injective hmain
  · exact PartrecToTM2Support.tapeSymbolCode_injective hrev
  · exact PartrecToTM2Support.tapeSymbolCode_injective haux
  · exact PartrecToTM2Support.tapeSymbolCode_injective hstack

theorem partrecStartedTM0StackVectorCode_primrec :
    Primrec partrecStartedTM0StackVectorCode := by
  classical
  exact Primrec.dom_finite partrecStartedTM0StackVectorCode

/-- Numeric code for a translated TM0 tape symbol. -/
def partrecStartedTM0SymbolCode
    (a : Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) : Nat :=
  Nat.pair (if a.1 then 1 else 0) (partrecStartedTM0StackVectorCode a.2)

theorem partrecStartedTM0SymbolCode_injective :
    Function.Injective partrecStartedTM0SymbolCode := by
  intro a b h
  rcases a with ⟨ba, va⟩
  rcases b with ⟨bb, vb⟩
  unfold partrecStartedTM0SymbolCode at h
  have hpair := Nat.pair_eq_pair.mp h
  have hbool : ba = bb := by
    cases ba <;> cases bb <;> simp at hpair ⊢
  have hvec : va = vb :=
    partrecStartedTM0StackVectorCode_injective hpair.2
  cases hbool
  cases hvec
  rfl

theorem partrecStartedTM0SymbolCode_primrec :
    Primrec partrecStartedTM0SymbolCode := by
  classical
  exact Primrec.dom_finite partrecStartedTM0SymbolCode

/-- Numeric alphabet for the translated TM0 route, suitable for `FiniteTM0Program`. -/
def partrecStartedTM0Symbols : List Nat :=
  partrecStartedTM0SymbolList.map partrecStartedTM0SymbolCode

theorem partrecStartedTM0SymbolCode_mem_symbols
    (a : Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :
    partrecStartedTM0SymbolCode a ∈ partrecStartedTM0Symbols :=
  List.mem_map_of_mem (f := partrecStartedTM0SymbolCode) (mem_partrecStartedTM0SymbolList a)

/-- Numeric code of the translated TM0 blank symbol. -/
def partrecStartedTM0Blank : Nat :=
  partrecStartedTM0SymbolCode default

theorem partrecStartedTM0Blank_mem_symbols :
    partrecStartedTM0Blank ∈ partrecStartedTM0Symbols := by
  unfold partrecStartedTM0Blank
  exact partrecStartedTM0SymbolCode_mem_symbols default

theorem partrecStartedTM0_supports (tc : Turing.ToPartrec.Code) :
    Turing.TM0.Supports (partrecStartedTM0Machine tc)
      (partrecStartedTM0Labels tc : Set _) := by
  exact Turing.TM1to0.tr_supports
    (M := partrecStartedTM1Machine tc)
    (S := partrecStartedTM1Labels tc)
    (partrecStartedTM1_supports tc)

/--
Correctness of the composed Mathlib TM0 route for the code-specific started
TM2 evaluator.
-/
theorem partrecStartedTM0_eval_dom_iff_tm2 (tc : Turing.ToPartrec.Code) :
    (Turing.TM0.eval (partrecStartedTM0Machine tc) partrecStartedTM0Input).Dom ↔
      (Turing.TM2.eval (partrecStartedTM2 tc)
        Turing.PartrecToTM2.K'.main partrecStartedTM2Input).Dom := by
  unfold partrecStartedTM0Machine partrecStartedTM1Machine partrecStartedTM0Input
  rw [Turing.TM1to0.tr_eval]
  exact Turing.TM2to1.tr_eval_dom
    (M := partrecStartedTM2 tc) Turing.PartrecToTM2.K'.main partrecStartedTM2Input

end TM0Route

end LeanWang
