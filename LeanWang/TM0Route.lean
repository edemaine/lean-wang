/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PartrecToTM2SupportList
import LeanWang.ToPartrecEncoding
import Mathlib.Data.Nat.Pairing

/-!
The Mathlib TM0 route for the machine side of the reduction.

Mathlib already translates TM2 machines to TM1 machines and TM1 machines to TM0
machines. The `PartrecToTM2` evaluator, however, starts from a code-dependent
TM2 label rather than the default label used by `TM2.eval`. This file packages a
code-specific relabeling where that evaluator label is the default start label,
so the standard Mathlib translation theorems apply.
-/

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

theorem relabelTM2Stmt_id {K : Type u} {Γ : K → Type v} {Λ : Type w} {σ : Type y} :
    ∀ stmt : Turing.TM2.Stmt Γ Λ σ, relabelTM2Stmt id stmt = stmt
  | Turing.TM2.Stmt.push k g q => by simp [relabelTM2Stmt, relabelTM2Stmt_id q]
  | Turing.TM2.Stmt.peek k g q => by simp [relabelTM2Stmt, relabelTM2Stmt_id q]
  | Turing.TM2.Stmt.pop k g q => by simp [relabelTM2Stmt, relabelTM2Stmt_id q]
  | Turing.TM2.Stmt.load g q => by simp [relabelTM2Stmt, relabelTM2Stmt_id q]
  | Turing.TM2.Stmt.branch g q₁ q₂ => by
      simp [relabelTM2Stmt, relabelTM2Stmt_id q₁, relabelTM2Stmt_id q₂]
  | Turing.TM2.Stmt.goto g => by
      simp [relabelTM2Stmt]
  | Turing.TM2.Stmt.halt => by
      simp [relabelTM2Stmt]

theorem relabelTM2Stmt_comp {K : Type u} {Γ : K → Type v}
    {Λ : Type w} {Λ' : Type x} {Λ'' : Type z} {σ : Type y}
    (f : Λ → Λ') (g : Λ' → Λ'') :
    ∀ stmt : Turing.TM2.Stmt Γ Λ σ,
      relabelTM2Stmt g (relabelTM2Stmt f stmt) = relabelTM2Stmt (g ∘ f) stmt
  | Turing.TM2.Stmt.push k h q => by simp [relabelTM2Stmt, relabelTM2Stmt_comp f g q]
  | Turing.TM2.Stmt.peek k h q => by simp [relabelTM2Stmt, relabelTM2Stmt_comp f g q]
  | Turing.TM2.Stmt.pop k h q => by simp [relabelTM2Stmt, relabelTM2Stmt_comp f g q]
  | Turing.TM2.Stmt.load h q => by simp [relabelTM2Stmt, relabelTM2Stmt_comp f g q]
  | Turing.TM2.Stmt.branch h q₁ q₂ => by
      simp [relabelTM2Stmt, relabelTM2Stmt_comp f g q₁, relabelTM2Stmt_comp f g q₂]
  | Turing.TM2.Stmt.goto h => by
      simp [relabelTM2Stmt]
  | Turing.TM2.Stmt.halt => by
      simp [relabelTM2Stmt]

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

/-- Explicit finite list of possible `PartrecToTM2` local variable values. -/
def partrecVarList : List PartrecVar :=
  none :: (PartrecToTM2Support.stackAlphabetList.map some)

theorem mem_partrecVarList (v : PartrecVar) :
    v ∈ partrecVarList := by
  cases v with
  | none =>
      simp [partrecVarList]
  | some a =>
      simp [partrecVarList, PartrecToTM2Support.mem_stackAlphabetList a]

/-- Finite encoding of functions out of `Bool`. -/
def boolFunctionEquivPair (β : Type*) :
    (Bool → β) ≃ β × β where
  toFun f := (f false, f true)
  invFun p
    | false => p.1
    | true => p.2
  left_inv := by
    intro f
    funext b
    cases b <;> rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b⟩
    rfl

instance instPrimcodableBoolFunction (β : Type*) [Primcodable β] :
    Primcodable (Bool → β) :=
  Primcodable.ofEquiv (β × β) (boolFunctionEquivPair β)

theorem boolFunctionEquivPair_primrec (β : Type*) [Primcodable β] :
    Primrec (boolFunctionEquivPair β) := by
  simpa [instPrimcodableBoolFunction] using
    (Primrec.of_equiv (α := β × β) (e := boolFunctionEquivPair β))

theorem boolFunction_app_primrec (β : Type*) [Primcodable β] :
    Primrec₂ (fun f : Bool → β => fun b : Bool => f b) := by
  apply Primrec₂.mk
  let pair : (Bool → β) × Bool → β × β := fun p => boolFunctionEquivPair β p.1
  have hpair : Primrec pair := (boolFunctionEquivPair_primrec β).comp Primrec.fst
  have hfalse : Primrec (fun p : (Bool → β) × Bool => (pair p).1) :=
    Primrec.fst.comp hpair
  have htrue : Primrec (fun p : (Bool → β) × Bool => (pair p).2) :=
    Primrec.snd.comp hpair
  exact (Primrec.cond (Primrec.snd : Primrec (fun p : (Bool → β) × Bool => p.2))
    htrue hfalse).of_eq fun p => by
      rcases p with ⟨f, b⟩
      cases b <;> rfl

/-- Finite encoding of functions out of the evaluator local variable. -/
def partrecVarFunctionEquivTuple (β : Type*) :
    (PartrecVar → β) ≃ β × β × β × β × β where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance instPrimcodablePartrecVarFunction (β : Type*) [Primcodable β] :
    Primcodable (PartrecVar → β) :=
  Primcodable.ofEquiv (β × β × β × β × β)
    (partrecVarFunctionEquivTuple β)

theorem partrecVarFunctionEquivTuple_primrec (β : Type*) [Primcodable β] :
    Primrec (partrecVarFunctionEquivTuple β) := by
  simpa [instPrimcodablePartrecVarFunction] using
    (Primrec.of_equiv (α := β × β × β × β × β)
      (e := partrecVarFunctionEquivTuple β))

theorem partrecVarFunction_app_primrec (β : Type*) [Primcodable β] :
    Primrec₂ (fun f : PartrecVar → β => fun v : PartrecVar => f v) := by
  apply Primrec₂.mk
  let tuple : (PartrecVar → β) × PartrecVar → β × β × β × β × β :=
    fun p => partrecVarFunctionEquivTuple β p.1
  have htuple : Primrec tuple :=
    (partrecVarFunctionEquivTuple_primrec β).comp Primrec.fst
  have hnone : Primrec (fun p : (PartrecVar → β) × PartrecVar =>
      (tuple p).1) :=
    Primrec.fst.comp htuple
  have hsome : Primrec₂ (fun p : (PartrecVar → β) × PartrecVar =>
      fun a : Γ' =>
        match a with
        | Γ'.consₗ => (tuple p).2.1
        | Γ'.cons => (tuple p).2.2.1
        | Γ'.bit0 => (tuple p).2.2.2.1
        | Γ'.bit1 => (tuple p).2.2.2.2) := by
    apply Primrec₂.mk
    let tuple' : ((PartrecVar → β) × PartrecVar) × Γ' → β × β × β × β × β :=
      fun p => tuple p.1
    let sym : ((PartrecVar → β) × PartrecVar) × Γ' → Γ' := fun p => p.2
    have htuple' : Primrec tuple' := htuple.comp Primrec.fst
    have hsym : Primrec sym := Primrec.snd
    have hconsₗ : PrimrecPred (fun p : ((PartrecVar → β) × PartrecVar) × Γ' =>
        sym p = Γ'.consₗ) :=
      Primrec.eq.comp hsym (Primrec.const Γ'.consₗ)
    have hcons : PrimrecPred (fun p : ((PartrecVar → β) × PartrecVar) × Γ' =>
        sym p = Γ'.cons) :=
      Primrec.eq.comp hsym (Primrec.const Γ'.cons)
    have hbit0 : PrimrecPred (fun p : ((PartrecVar → β) × PartrecVar) × Γ' =>
        sym p = Γ'.bit0) :=
      Primrec.eq.comp hsym (Primrec.const Γ'.bit0)
    exact (Primrec.ite hconsₗ (Primrec.fst.comp (Primrec.snd.comp htuple'))
      (Primrec.ite hcons (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp htuple')))
        (Primrec.ite hbit0
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp htuple'))))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp htuple'))))))).of_eq fun p => by
        rcases p with ⟨p, a⟩
        cases a <;> rfl
  exact (Primrec.option_casesOn Primrec.snd hnone hsome).of_eq fun p => by
    rcases p with ⟨f, v⟩
    cases v with
    | none => rfl
    | some a => cases a <;> rfl

/-- Finite symbol-valued actions on the evaluator local variable. -/
def partrecVarToSymbolEquivTuple :
    (PartrecVar → Turing.PartrecToTM2.Γ') ≃
      Turing.PartrecToTM2.Γ' × Turing.PartrecToTM2.Γ' × Turing.PartrecToTM2.Γ' ×
        Turing.PartrecToTM2.Γ' × Turing.PartrecToTM2.Γ' where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance instPrimcodablePartrecVarToSymbol :
    Primcodable (PartrecVar → Turing.PartrecToTM2.Γ') :=
  Primcodable.ofEquiv
    (Turing.PartrecToTM2.Γ' × Turing.PartrecToTM2.Γ' × Turing.PartrecToTM2.Γ' ×
      Turing.PartrecToTM2.Γ' × Turing.PartrecToTM2.Γ')
    partrecVarToSymbolEquivTuple

/-- Finite Boolean tests on the evaluator local variable. -/
def partrecVarPredicateEquivTuple :
    (PartrecVar → Bool) ≃ Bool × Bool × Bool × Bool × Bool where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance instPrimcodablePartrecVarPredicate :
    Primcodable (PartrecVar → Bool) :=
  Primcodable.ofEquiv (Bool × Bool × Bool × Bool × Bool)
    partrecVarPredicateEquivTuple

/-- Finite label-valued jumps on the evaluator local variable. -/
def partrecVarToLabelEquivTuple :
    (PartrecVar → Turing.PartrecToTM2.Λ') ≃
      Turing.PartrecToTM2.Λ' × Turing.PartrecToTM2.Λ' × Turing.PartrecToTM2.Λ' ×
        Turing.PartrecToTM2.Λ' × Turing.PartrecToTM2.Λ' where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance instPrimcodablePartrecVarToLabel :
    Primcodable (PartrecVar → Turing.PartrecToTM2.Λ') :=
  Primcodable.ofEquiv
    (Turing.PartrecToTM2.Λ' × Turing.PartrecToTM2.Λ' × Turing.PartrecToTM2.Λ' ×
      Turing.PartrecToTM2.Λ' × Turing.PartrecToTM2.Λ')
    partrecVarToLabelEquivTuple

/-- Finite binary local-store actions used by `peek`/`pop`. -/
def partrecVarBinaryActionEquivTuple :
    (PartrecVar → PartrecVar → PartrecVar) ≃
      (PartrecVar → PartrecVar) × (PartrecVar → PartrecVar) ×
        (PartrecVar → PartrecVar) × (PartrecVar → PartrecVar) ×
          (PartrecVar → PartrecVar) where
  toFun f := (f none, f (some Γ'.consₗ), f (some Γ'.cons),
    f (some Γ'.bit0), f (some Γ'.bit1))
  invFun t
    | none => t.1
    | some Γ'.consₗ => t.2.1
    | some Γ'.cons => t.2.2.1
    | some Γ'.bit0 => t.2.2.2.1
    | some Γ'.bit1 => t.2.2.2.2
  left_inv := by
    intro f
    funext s a
    cases s with
    | none => rfl
    | some x => cases x <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance instPrimcodablePartrecVarBinaryAction :
    Primcodable (PartrecVar → PartrecVar → PartrecVar) :=
  Primcodable.ofEquiv
    ((PartrecVar → PartrecVar) × (PartrecVar → PartrecVar) ×
      (PartrecVar → PartrecVar) × (PartrecVar → PartrecVar) ×
        (PartrecVar → PartrecVar))
    partrecVarBinaryActionEquivTuple

/-- Finite encoding of the concrete stack actions used by the TM2-to-TM1 route. -/
def partrecStActEquivSum (k : PartrecStack) :
    Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar k ≃
      (PartrecVar → Turing.PartrecToTM2.Γ') ⊕
        ((PartrecVar → PartrecVar → PartrecVar) ⊕
          (PartrecVar → PartrecVar → PartrecVar)) where
  toFun
    | Turing.TM2to1.StAct.push f => Sum.inl f
    | Turing.TM2to1.StAct.peek f => Sum.inr (Sum.inl f)
    | Turing.TM2to1.StAct.pop f => Sum.inr (Sum.inr f)
  invFun
    | Sum.inl f => Turing.TM2to1.StAct.push (k := k) f
    | Sum.inr (Sum.inl f) => Turing.TM2to1.StAct.peek (k := k) f
    | Sum.inr (Sum.inr f) => Turing.TM2to1.StAct.pop (k := k) f
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro a
    cases a with
    | inl f => rfl
    | inr b =>
        cases b <;> rfl

instance instPrimcodablePartrecStAct (k : PartrecStack) :
    Primcodable (Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar k) :=
  Primcodable.ofEquiv
    ((PartrecVar → Turing.PartrecToTM2.Γ') ⊕
      ((PartrecVar → PartrecVar → PartrecVar) ⊕
        (PartrecVar → PartrecVar → PartrecVar)))
    (partrecStActEquivSum k)

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

def equivVal (tc : Turing.ToPartrec.Code) :
    StartedLabel tc ≃ Turing.PartrecToTM2.Λ' where
  toFun := StartedLabel.val
  invFun := wrap tc
  left_inv := by
    intro q
    cases q
    rfl
  right_inv := by
    intro q
    rfl

@[simp]
theorem wrap_val (tc : Turing.ToPartrec.Code) (q : Turing.PartrecToTM2.Λ') :
    (wrap tc q).val = q :=
  rfl

theorem wrap_injective (tc : Turing.ToPartrec.Code) :
    Function.Injective (wrap tc) := by
  intro q r h
  cases h
  rfl

instance (tc : Turing.ToPartrec.Code) : Inhabited (StartedLabel tc) :=
  ⟨wrap tc (PartrecToTM2Support.startLabel tc)⟩

instance (tc : Turing.ToPartrec.Code) : DecidableEq (StartedLabel tc) := by
  intro q r
  exact decidable_of_iff (q.val = r.val) (by
    constructor
    · intro h
      cases q
      cases r
      cases h
      rfl
    · intro h
      exact congrArg StartedLabel.val h)

instance instPrimcodable (tc : Turing.ToPartrec.Code) : Primcodable (StartedLabel tc) :=
  Primcodable.ofEquiv Turing.PartrecToTM2.Λ' (equivVal tc)

end StartedLabel

instance instDecidableEqPartrecStartedTM0Symbol :
    DecidableEq (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :=
  inferInstanceAs (DecidableEq (Bool × (∀ k : PartrecStack, Option (PartrecStackSymbol k))))

instance instDecidableEqPartrecStAct {k : PartrecStack} :
    DecidableEq (Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar k) := fun a b => by
  cases a <;> cases b
  case push.push f g =>
    exact decidable_of_iff' (f = g) (by simp)
  case peek.peek f g =>
    exact decidable_of_iff' (f = g) (by simp)
  case pop.pop f g =>
    exact decidable_of_iff' (f = g) (by simp)
  all_goals exact .isFalse (by intro h; cases h)

def decEqPartrecStartedTM2Stmt (tc : Turing.ToPartrec.Code) :
    (a b : Turing.TM2.Stmt PartrecStackSymbol (StartedLabel tc) PartrecVar) →
      Decidable (a = b)
  | Turing.TM2.Stmt.push k f q, b =>
      match b with
      | Turing.TM2.Stmt.push k' f' q' =>
          if hk : k = k' then by
            subst k'
            letI : Decidable (q = q') := decEqPartrecStartedTM2Stmt tc q q'
            exact decidable_of_iff' (f = f' ∧ q = q') (by simp)
          else
            .isFalse (by intro h; cases h; exact hk rfl)
      | Turing.TM2.Stmt.peek .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.pop .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM2.Stmt.peek k f q, b =>
      match b with
      | Turing.TM2.Stmt.push .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.peek k' f' q' =>
          if hk : k = k' then by
            subst k'
            letI : Decidable (q = q') := decEqPartrecStartedTM2Stmt tc q q'
            exact decidable_of_iff' (f = f' ∧ q = q') (by simp)
          else
            .isFalse (by intro h; cases h; exact hk rfl)
      | Turing.TM2.Stmt.pop .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM2.Stmt.pop k f q, b =>
      match b with
      | Turing.TM2.Stmt.push .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.peek .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.pop k' f' q' =>
          if hk : k = k' then by
            subst k'
            letI : Decidable (q = q') := decEqPartrecStartedTM2Stmt tc q q'
            exact decidable_of_iff' (f = f' ∧ q = q') (by simp)
          else
            .isFalse (by intro h; cases h; exact hk rfl)
      | Turing.TM2.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM2.Stmt.load f q, b =>
      match b with
      | Turing.TM2.Stmt.push .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.peek .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.pop .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.load f' q' => by
          letI : Decidable (q = q') := decEqPartrecStartedTM2Stmt tc q q'
          exact decidable_of_iff' (f = f' ∧ q = q') (by simp)
      | Turing.TM2.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM2.Stmt.branch f q1 q2, b =>
      match b with
      | Turing.TM2.Stmt.push .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.peek .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.pop .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.branch f' q1' q2' => by
          letI : Decidable (q1 = q1') := decEqPartrecStartedTM2Stmt tc q1 q1'
          letI : Decidable (q2 = q2') := decEqPartrecStartedTM2Stmt tc q2 q2'
          exact decidable_of_iff' (f = f' ∧ q1 = q1' ∧ q2 = q2') (by simp)
      | Turing.TM2.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM2.Stmt.goto f, b =>
      match b with
      | Turing.TM2.Stmt.push .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.peek .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.pop .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.goto f' => decidable_of_iff' (f = f') (by simp)
      | Turing.TM2.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM2.Stmt.halt, b =>
      match b with
      | Turing.TM2.Stmt.push .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.peek .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.pop .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM2.Stmt.halt => .isTrue rfl

instance instDecidableEqPartrecStartedTM2Stmt (tc : Turing.ToPartrec.Code) :
    DecidableEq (Turing.TM2.Stmt PartrecStackSymbol (StartedLabel tc) PartrecVar) :=
  decEqPartrecStartedTM2Stmt tc

/--
One preorder node of a concrete started `PartrecToTM2` statement.

Recursive statement values will be encoded as valid preorder lists of these
nodes. The payload domains are all finite and already have concrete
`Primcodable` instances.
-/
inductive PartrecStartedTM2StmtNode (tc : Turing.ToPartrec.Code) where
  | push : PartrecStack → (PartrecVar → Turing.PartrecToTM2.Γ') →
      PartrecStartedTM2StmtNode tc
  | peek : PartrecStack → (PartrecVar → PartrecVar → PartrecVar) →
      PartrecStartedTM2StmtNode tc
  | pop : PartrecStack → (PartrecVar → PartrecVar → PartrecVar) →
      PartrecStartedTM2StmtNode tc
  | load : (PartrecVar → PartrecVar) → PartrecStartedTM2StmtNode tc
  | branch : (PartrecVar → Bool) → PartrecStartedTM2StmtNode tc
  | goto : (PartrecVar → StartedLabel tc) → PartrecStartedTM2StmtNode tc
  | halt : PartrecStartedTM2StmtNode tc

namespace PartrecStartedTM2StmtNode

abbrev PushCode : Type :=
  PartrecStack × (PartrecVar → Turing.PartrecToTM2.Γ')

abbrev UpdateCode : Type :=
  PartrecStack × (PartrecVar → PartrecVar → PartrecVar)

abbrev LoadCode : Type :=
  PartrecVar → PartrecVar

abbrev BranchCode : Type :=
  PartrecVar → Bool

abbrev GotoCode (tc : Turing.ToPartrec.Code) : Type :=
  PartrecVar → StartedLabel tc

abbrev GotoHaltCode (tc : Turing.ToPartrec.Code) : Type :=
  GotoCode tc ⊕ PUnit

abbrev BranchTailCode (tc : Turing.ToPartrec.Code) : Type :=
  BranchCode ⊕ GotoHaltCode tc

abbrev LoadTailCode (tc : Turing.ToPartrec.Code) : Type :=
  LoadCode ⊕ BranchTailCode tc

abbrev PopTailCode (tc : Turing.ToPartrec.Code) : Type :=
  UpdateCode ⊕ LoadTailCode tc

abbrev PeekTailCode (tc : Turing.ToPartrec.Code) : Type :=
  UpdateCode ⊕ PopTailCode tc

abbrev Code (tc : Turing.ToPartrec.Code) : Type :=
  PushCode ⊕ PeekTailCode tc

def toCode {tc : Turing.ToPartrec.Code} :
    PartrecStartedTM2StmtNode tc → Code tc
  | push k f => Sum.inl (k, f)
  | peek k f => Sum.inr (Sum.inl (k, f))
  | pop k f => Sum.inr (Sum.inr (Sum.inl (k, f)))
  | load f => Sum.inr (Sum.inr (Sum.inr (Sum.inl f)))
  | branch f => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl f))))
  | goto f => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl f)))))
  | halt => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))

def ofCode {tc : Turing.ToPartrec.Code} :
    Code tc → PartrecStartedTM2StmtNode tc
  | Sum.inl p => push p.1 p.2
  | Sum.inr (Sum.inl p) => peek p.1 p.2
  | Sum.inr (Sum.inr (Sum.inl p)) => pop p.1 p.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl f))) => load f
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl f)))) => branch f
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl f))))) => goto f
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => halt

def equivCode (tc : Turing.ToPartrec.Code) :
    PartrecStartedTM2StmtNode tc ≃ Code tc where
  toFun := toCode
  invFun := ofCode
  left_inv := by
    intro n
    cases n <;> rfl
  right_inv := by
    intro c
    rcases c with p | c
    · rcases p with ⟨k, f⟩
      rfl
    rcases c with p | c
    · rcases p with ⟨k, f⟩
      rfl
    rcases c with p | c
    · rcases p with ⟨k, f⟩
      rfl
    rcases c with f | c
    · rfl
    rcases c with f | c
    · rfl
    rcases c with f | u
    · rfl
    cases u
    rfl

instance instPrimcodable (tc : Turing.ToPartrec.Code) :
    Primcodable (PartrecStartedTM2StmtNode tc) :=
  Primcodable.ofEquiv (Code tc) (equivCode tc)

/-- Number of recursive child statements required after this preorder node. -/
def arity {tc : Turing.ToPartrec.Code} :
    PartrecStartedTM2StmtNode tc → Nat
  | push .. => 1
  | peek .. => 1
  | pop .. => 1
  | load .. => 1
  | branch .. => 2
  | goto .. => 0
  | halt => 0

def codeArity {tc : Turing.ToPartrec.Code} :
    Code tc → Nat
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => 0

def gotoHaltCodeArity {tc : Turing.ToPartrec.Code} :
    GotoHaltCode tc → Nat
  | Sum.inl _ => 0
  | Sum.inr _ => 0

theorem gotoHaltCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (gotoHaltCodeArity (tc := tc)) :=
  (Primrec.const 0).of_eq fun c => by
    cases c <;> rfl

def branchTailCodeArity {tc : Turing.ToPartrec.Code} :
    BranchTailCode tc → Nat
  | Sum.inl _ => 2
  | Sum.inr c => gotoHaltCodeArity c

theorem branchTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (branchTailCodeArity (tc := tc)) := by
  unfold branchTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : BranchTailCode tc => c))
    (Primrec.const 2).to₂
    ((gotoHaltCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

def loadTailCodeArity {tc : Turing.ToPartrec.Code} :
    LoadTailCode tc → Nat
  | Sum.inl _ => 1
  | Sum.inr c => branchTailCodeArity c

theorem loadTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (loadTailCodeArity (tc := tc)) := by
  unfold loadTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : LoadTailCode tc => c))
    (Primrec.const 1).to₂
    ((branchTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

def popTailCodeArity {tc : Turing.ToPartrec.Code} :
    PopTailCode tc → Nat
  | Sum.inl _ => 1
  | Sum.inr c => loadTailCodeArity c

theorem popTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (popTailCodeArity (tc := tc)) := by
  unfold popTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : PopTailCode tc => c))
    (Primrec.const 1).to₂
    ((loadTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

def peekTailCodeArity {tc : Turing.ToPartrec.Code} :
    PeekTailCode tc → Nat
  | Sum.inl _ => 1
  | Sum.inr c => popTailCodeArity c

theorem peekTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (peekTailCodeArity (tc := tc)) := by
  unfold peekTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : PeekTailCode tc => c))
    (Primrec.const 1).to₂
    ((popTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

theorem codeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (codeArity (tc := tc)) := by
  unfold codeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : Code tc => c))
    (Primrec.const 1).to₂
    ((peekTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      rcases x with p | c
      · rfl
      rcases c with p | c
      · rfl
      rcases c with p | c
      · rfl
      rcases c with f | c
      · rfl
      rcases c with f | c
      · rfl
      rcases c with f | u
      · rfl
      cases u
      rfl

theorem toCode_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (toCode : PartrecStartedTM2StmtNode tc → Code tc) := by
  simpa [equivCode] using
    (Primrec.of_equiv (e := equivCode tc) :
      Primrec (equivCode tc))

theorem arity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (arity (tc := tc)) :=
  ((codeArity_primrec tc).comp (toCode_primrec tc)).of_eq fun n => by
    cases n <;> rfl

def validStep {tc : Turing.ToPartrec.Code}
    (state : Bool × Nat) (node : PartrecStartedTM2StmtNode tc) : Bool × Nat :=
  if state.1 ∧ 0 < state.2 then
    (true, state.2 - 1 + arity node)
  else
    (false, state.2)

theorem validStep_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : (Bool × Nat) × PartrecStartedTM2StmtNode tc =>
      validStep p.1 p.2) := by
  have hstate : Primrec (fun p : (Bool × Nat) × PartrecStartedTM2StmtNode tc =>
      p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hslots : Primrec (fun p : (Bool × Nat) × PartrecStartedTM2StmtNode tc =>
      p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hok : PrimrecPred (fun p : (Bool × Nat) × PartrecStartedTM2StmtNode tc =>
      p.1.1 ∧ 0 < p.1.2) :=
    PrimrecPred.and
      (Primrec.eq.comp hstate (Primrec.const true))
      (Primrec.nat_lt.comp (Primrec.const 0) hslots)
  have hthen : Primrec (fun p : (Bool × Nat) × PartrecStartedTM2StmtNode tc =>
      (true, p.1.2 - 1 + arity p.2)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.nat_add.comp
        (Primrec.nat_sub.comp
          hslots
          (Primrec.const 1))
        ((arity_primrec tc).comp Primrec.snd))
  have helse : Primrec (fun p : (Bool × Nat) × PartrecStartedTM2StmtNode tc =>
      (false, p.1.2)) :=
    Primrec.pair (Primrec.const false) hslots
  exact (Primrec.ite hok hthen helse).of_eq fun p => by
    simp [validStep]

/-- Shape-only validity of a preorder statement encoding. -/
def Valid {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM2StmtNode tc)) : Prop :=
  nodes.foldl validStep (true, 1) = (true, 0)

instance instDecidableValid (tc : Turing.ToPartrec.Code)
    (nodes : List (PartrecStartedTM2StmtNode tc)) :
    Decidable (Valid nodes) :=
  inferInstanceAs (Decidable (nodes.foldl validStep (true, 1) = (true, 0)))

theorem valid_primrecPred (tc : Turing.ToPartrec.Code) :
    PrimrecPred (Valid (tc := tc)) := by
  unfold Valid
  exact Primrec.eq.comp
    (Primrec.list_foldl Primrec.id (Primrec.const (true, 1))
      (((validStep_primrec tc).comp Primrec.snd).to₂))
    (Primrec.const (true, 0))

theorem foldl_validStep_false {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM2StmtNode tc)) (slots : Nat) :
    nodes.foldl validStep (false, slots) = (false, slots) := by
  induction nodes generalizing slots with
  | nil =>
      rfl
  | cons node rest ih =>
      simp [validStep, ih]

theorem foldl_validStep_true_zero {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM2StmtNode tc)) :
    nodes.foldl validStep (true, 0) =
      match nodes with
      | [] => (true, 0)
      | _ :: _ => (false, 0) := by
  cases nodes with
  | nil =>
      rfl
  | cons node rest =>
      simp [validStep, foldl_validStep_false]

theorem foldl_validStep_true_zero_eq_true_zero_iff {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM2StmtNode tc)) :
    nodes.foldl validStep (true, 0) = (true, 0) ↔ nodes = [] := by
  cases nodes with
  | nil =>
      simp
  | cons node rest =>
      simp only [List.foldl_cons]
      rw [show validStep (true, 0) node = (false, 0) by simp [validStep]]
      rw [foldl_validStep_false]
      simp

theorem valid_tail_nil_of_arity_zero {tc : Turing.ToPartrec.Code}
    {node : PartrecStartedTM2StmtNode tc} {rest : List (PartrecStartedTM2StmtNode tc)}
    (harity : arity node = 0)
    (hvalid : (node :: rest).foldl validStep (true, 1) = (true, 0)) :
    rest = [] := by
  have htail : rest.foldl validStep (true, 0) = (true, 0) := by
    simpa [validStep, harity] using hvalid
  exact (foldl_validStep_true_zero_eq_true_zero_iff rest).1 htail

/-- The concrete started TM2 statement type encoded by these preorder nodes. -/
abbrev Stmt (tc : Turing.ToPartrec.Code) : Type :=
  Turing.TM2.Stmt PartrecStackSymbol (StartedLabel tc) PartrecVar

/-- Encode a concrete started TM2 statement as a preorder list of nodes. -/
def ofStmt {tc : Turing.ToPartrec.Code} : Stmt tc → List (PartrecStartedTM2StmtNode tc)
  | Turing.TM2.Stmt.push k f q => push k f :: ofStmt q
  | Turing.TM2.Stmt.peek k f q => peek k f :: ofStmt q
  | Turing.TM2.Stmt.pop k f q => pop k f :: ofStmt q
  | Turing.TM2.Stmt.load f q => load f :: ofStmt q
  | Turing.TM2.Stmt.branch f q₁ q₂ => branch f :: (ofStmt q₁ ++ ofStmt q₂)
  | Turing.TM2.Stmt.goto f => [goto f]
  | Turing.TM2.Stmt.halt => [halt]

theorem ofStmt_length_pos {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    0 < (ofStmt stmt).length := by
  cases stmt <;> simp [ofStmt]

/--
Fuelled parser for preorder-encoded concrete started TM2 statements.

The returned tail is the unconsumed suffix after one complete statement.
-/
def parseWithFuel {tc : Turing.ToPartrec.Code} :
    Nat → List (PartrecStartedTM2StmtNode tc) →
      Option (Stmt tc × List (PartrecStartedTM2StmtNode tc))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, node :: rest =>
      match node with
      | push k f =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM2.Stmt.push k f p.1, p.2)
      | peek k f =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM2.Stmt.peek k f p.1, p.2)
      | pop k f =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM2.Stmt.pop k f p.1, p.2)
      | load f =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM2.Stmt.load f p.1, p.2)
      | branch f =>
          (parseWithFuel fuel rest).bind fun left =>
            (parseWithFuel fuel left.2).map fun right =>
              (Turing.TM2.Stmt.branch f left.1 right.1, right.2)
      | goto f => some (Turing.TM2.Stmt.goto f, rest)
      | halt => some (Turing.TM2.Stmt.halt, rest)

/-- Parse a preorder list using its own length as fuel. -/
def parse? {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM2StmtNode tc)) :
    Option (Stmt tc × List (PartrecStartedTM2StmtNode tc)) :=
  parseWithFuel nodes.length nodes

set_option linter.flexible false in
theorem parseWithFuel_mono {tc : Turing.ToPartrec.Code}
    {fuel fuel' : Nat} (h : fuel ≤ fuel')
    (nodes : List (PartrecStartedTM2StmtNode tc))
    {out : Stmt tc × List (PartrecStartedTM2StmtNode tc)}
    (hparse : parseWithFuel (tc := tc) fuel nodes = some out) :
    parseWithFuel (tc := tc) fuel' nodes = some out := by
  induction fuel generalizing fuel' nodes out with
  | zero =>
      simp [parseWithFuel] at hparse
  | succ fuel ih =>
      cases fuel' with
      | zero =>
          omega
      | succ fuel' =>
          cases nodes with
          | nil =>
              simp [parseWithFuel] at hparse
          | cons node rest =>
              cases node with
              | push k f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | peek k f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | pop k f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | load f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | branch f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hleft : parseWithFuel (tc := tc) fuel rest with _ | left <;>
                    simp [hleft] at hparse
                  rcases hright : parseWithFuel (tc := tc) fuel left.2 with _ | right <;>
                    simp [hright] at hparse
                  rcases right with ⟨q₂, tail⟩
                  simp at hparse
                  subst out
                  have hleft' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := left) (by simpa using hleft)
                  have hright' := ih (Nat.succ_le_succ_iff.1 h) left.2
                    (out := (q₂, tail)) (by simpa using hright)
                  simp [hleft', hright']
              | goto f =>
                  simp [parseWithFuel] at hparse ⊢
                  exact hparse
              | halt =>
                  simp [parseWithFuel] at hparse ⊢
                  exact hparse

set_option linter.flexible false in
theorem parseWithFuel_eq_ofStmt_append {tc : Turing.ToPartrec.Code}
    {fuel : Nat} {nodes : List (PartrecStartedTM2StmtNode tc)}
    {out : Stmt tc × List (PartrecStartedTM2StmtNode tc)}
    (hparse : parseWithFuel (tc := tc) fuel nodes = some out) :
    nodes = ofStmt out.1 ++ out.2 := by
  induction fuel generalizing nodes out with
  | zero =>
      simp [parseWithFuel] at hparse
  | succ fuel ih =>
      cases nodes with
      | nil =>
          simp [parseWithFuel] at hparse
      | cons node rest =>
          cases node with
          | push k f =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | peek k f =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | pop k f =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | load f =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | branch f =>
              simp [parseWithFuel] at hparse
              rcases hleft : parseWithFuel (tc := tc) fuel rest with _ | left <;>
                simp [hleft] at hparse
              rcases hright : parseWithFuel (tc := tc) fuel left.2 with _ | right <;>
                simp [hright] at hparse
              rcases left with ⟨q₁, mid⟩
              rcases right with ⟨q₂, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q₁, mid)) (by simpa using hleft)
              have hmid := ih (nodes := mid) (out := (q₂, tail)) (by simpa using hright)
              simp [ofStmt, hrest, hmid, List.append_assoc]
          | goto f =>
              simp [parseWithFuel] at hparse
              subst out
              simp [ofStmt]
          | halt =>
              simp [parseWithFuel] at hparse
              subst out
              simp [ofStmt]

theorem parse?_eq_some_empty_ofStmt {tc : Turing.ToPartrec.Code}
    {nodes : List (PartrecStartedTM2StmtNode tc)} {stmt : Stmt tc}
    (hparse : parse? (tc := tc) nodes = some (stmt, [])) :
    nodes = ofStmt stmt := by
  have hsound := parseWithFuel_eq_ofStmt_append (tc := tc) hparse
  simpa [parse?] using hsound

set_option linter.flexible false in
theorem parseWithFuel_complete_prefix {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM2StmtNode tc)) (slots final : Nat)
    (hvalid : nodes.foldl validStep (true, slots + 1) = (true, final))
    (hfinal : final ≤ slots) :
    ∃ stmt tail,
      parseWithFuel (tc := tc) nodes.length nodes = some (stmt, tail) ∧
        tail.foldl validStep (true, slots) = (true, final) := by
  induction hlen : nodes.length using Nat.strong_induction_on
      generalizing nodes slots final with
  | _ n ih =>
      subst hlen
      cases nodes with
      | nil =>
          simp at hvalid
          omega
      | cons node rest =>
          cases node with
          | push k f =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM2.Stmt.push k f stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | peek k f =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM2.Stmt.peek k f stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | pop k f =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM2.Stmt.pop k f stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | load f =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM2.Stmt.load f stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | branch f =>
              have hrest :
                  rest.foldl validStep (true, (slots + 1) + 1) = (true, final) := by
                simpa [validStep, arity, Nat.add_assoc] using hvalid
              have hfinalLeft : final ≤ slots + 1 := by omega
              rcases ih rest.length (by simp) rest (slots + 1) final hrest hfinalLeft rfl with
                ⟨left, mid, hleft, hmidValid⟩
              have hrest_eq : rest = ofStmt left ++ mid :=
                parseWithFuel_eq_ofStmt_append (tc := tc) hleft
              have hmid_lt : mid.length < (PartrecStartedTM2StmtNode.branch f :: rest).length := by
                rw [hrest_eq]
                have hpos := ofStmt_length_pos (tc := tc) left
                simp
                omega
              rcases ih mid.length hmid_lt mid slots final hmidValid hfinal rfl with
                ⟨right, tail, hright, htail⟩
              have hmid_le_rest : mid.length ≤ rest.length := by
                rw [hrest_eq]
                simp
              have hrightBig := parseWithFuel_mono
                (tc := tc)
                (fuel := mid.length)
                (fuel' := rest.length)
                hmid_le_rest
                mid
                hright
              refine ⟨Turing.TM2.Stmt.branch f left right, tail, ?_, htail⟩
              simp [parseWithFuel, hleft, hrightBig]
          | goto f =>
              have htail : rest.foldl validStep (true, slots) = (true, final) := by
                simpa [validStep, arity] using hvalid
              refine ⟨Turing.TM2.Stmt.goto f, rest, ?_, htail⟩
              simp [parseWithFuel]
          | halt =>
              have htail : rest.foldl validStep (true, slots) = (true, final) := by
                simpa [validStep, arity] using hvalid
              refine ⟨Turing.TM2.Stmt.halt, rest, ?_, htail⟩
              simp [parseWithFuel]

set_option linter.flexible false in
theorem parseWithFuel_ofStmt_append {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM2StmtNode tc)) :
    parseWithFuel (tc := tc) (ofStmt stmt).length (ofStmt stmt ++ tail) =
      some (stmt, tail) := by
  induction stmt generalizing tail with
  | push k f q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | peek k f q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | pop k f q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | load f q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp [ofStmt, parseWithFuel]
      have hleft :
          parseWithFuel (tc := tc) (ofStmt q₁).length
              (ofStmt q₁ ++ ofStmt q₂ ++ tail) =
            some (q₁, ofStmt q₂ ++ tail) := by
        simpa [List.append_assoc] using ih₁ (ofStmt q₂ ++ tail)
      have hleft' :
          parseWithFuel (tc := tc) (ofStmt q₁).length
              (ofStmt q₁ ++ (ofStmt q₂ ++ tail)) =
            some (q₁, ofStmt q₂ ++ tail) := by
        simpa [List.append_assoc] using hleft
      have hleftBig := parseWithFuel_mono
        (tc := tc)
        (fuel := (ofStmt q₁).length)
        (fuel' := (ofStmt q₁).length + (ofStmt q₂).length)
        (by omega)
        (ofStmt q₁ ++ (ofStmt q₂ ++ tail))
        hleft'
      have hright :
          parseWithFuel (tc := tc) (ofStmt q₂).length
              (ofStmt q₂ ++ tail) =
            some (q₂, tail) := ih₂ tail
      have hrightBig := parseWithFuel_mono
        (tc := tc)
        (fuel := (ofStmt q₂).length)
        (fuel' := (ofStmt q₁).length + (ofStmt q₂).length)
        (by omega)
        (ofStmt q₂ ++ tail)
        hright
      simp [hleftBig, hrightBig]
  | goto f =>
      simp [ofStmt, parseWithFuel]
  | halt =>
      simp [ofStmt, parseWithFuel]

theorem parse?_ofStmt {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    parse? (tc := tc) (ofStmt stmt) = some (stmt, []) := by
  unfold parse?
  simpa using parseWithFuel_ofStmt_append (tc := tc) stmt []

theorem parse?_eq_some_of_valid {tc : Turing.ToPartrec.Code}
    {nodes : List (PartrecStartedTM2StmtNode tc)}
    (hvalid : Valid (tc := tc) nodes) :
    ∃ stmt : Stmt tc, parse? (tc := tc) nodes = some (stmt, []) := by
  rcases parseWithFuel_complete_prefix (tc := tc) nodes 0 0 hvalid (by omega) with
    ⟨stmt, tail, hparse, htail⟩
  have htail_nil : tail = [] :=
    (foldl_validStep_true_zero_eq_true_zero_iff tail).1 htail
  subst tail
  exact ⟨stmt, by simpa [parse?] using hparse⟩

theorem ofStmt_injective {tc : Turing.ToPartrec.Code} :
    Function.Injective (ofStmt (tc := tc)) := by
  intro a b h
  have ha := parse?_ofStmt (tc := tc) a
  rw [h] at ha
  rw [parse?_ofStmt (tc := tc) b] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

set_option linter.flexible false in
theorem ofStmt_foldl_validStep {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (slots : Nat) :
    (ofStmt stmt).foldl validStep (true, slots + 1) = (true, slots) := by
  induction stmt generalizing slots with
  | push k f q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | peek k f q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | pop k f q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | load f q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp [ofStmt, validStep, arity, List.foldl_append]
      rw [ih₁ (slots + 1)]
      exact ih₂ slots
  | goto f =>
      simp [ofStmt, validStep, arity]
  | halt =>
      simp [ofStmt, validStep, arity]

theorem valid_ofStmt {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    Valid (tc := tc) (ofStmt stmt) := by
  unfold Valid
  simpa using ofStmt_foldl_validStep (tc := tc) stmt 0

/-- Valid preorder-list representation of a concrete started TM2 statement. -/
abbrev ValidCode (tc : Turing.ToPartrec.Code) : Type :=
  { nodes : List (PartrecStartedTM2StmtNode tc) // Valid (tc := tc) nodes }

def toValidCode {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) : ValidCode tc :=
  ⟨ofStmt stmt, valid_ofStmt stmt⟩

theorem toValidCode_injective {tc : Turing.ToPartrec.Code} :
    Function.Injective (toValidCode (tc := tc)) := by
  intro a b h
  exact ofStmt_injective (congrArg Subtype.val h)

theorem toValidCode_surjective {tc : Turing.ToPartrec.Code} :
    Function.Surjective (toValidCode (tc := tc)) := by
  intro code
  rcases parse?_eq_some_of_valid (tc := tc) code.2 with ⟨stmt, hparse⟩
  refine ⟨stmt, Subtype.ext ?_⟩
  exact (parse?_eq_some_empty_ofStmt (tc := tc) hparse).symm

noncomputable def stmtEquivValidCode (tc : Turing.ToPartrec.Code) :
    Stmt tc ≃ ValidCode tc :=
  Equiv.ofBijective (toValidCode (tc := tc))
    ⟨toValidCode_injective (tc := tc), toValidCode_surjective (tc := tc)⟩

instance instPrimcodableValidCode (tc : Turing.ToPartrec.Code) :
    Primcodable (ValidCode tc) :=
  Primcodable.subtype (valid_primrecPred tc)

noncomputable instance instPrimcodableStmt (tc : Turing.ToPartrec.Code) :
    Primcodable (Stmt tc) :=
  Primcodable.ofEquiv (ValidCode tc) (stmtEquivValidCode tc)

end PartrecStartedTM2StmtNode

abbrev PartrecTM2Stmt : Type :=
  Turing.TM2.Stmt PartrecStackSymbol Turing.PartrecToTM2.Λ' PartrecVar

abbrev PartrecStartedTM2Stmt (tc : Turing.ToPartrec.Code) : Type :=
  PartrecStartedTM2StmtNode.Stmt tc

noncomputable def partrecTM2StmtEquivStarted (tc : Turing.ToPartrec.Code) :
    PartrecTM2Stmt ≃ PartrecStartedTM2Stmt tc where
  toFun := relabelTM2Stmt (StartedLabel.wrap tc)
  invFun := relabelTM2Stmt (fun q : StartedLabel tc => q.val)
  left_inv := by
    intro stmt
    rw [relabelTM2Stmt_comp]
    have hcomp :
        ((fun q : StartedLabel tc => q.val) ∘ StartedLabel.wrap tc) = id := by
      funext q
      rfl
    rw [hcomp]
    exact relabelTM2Stmt_id stmt
  right_inv := by
    intro stmt
    rw [relabelTM2Stmt_comp]
    have hcomp :
        (StartedLabel.wrap tc ∘ fun q : StartedLabel tc => q.val) = id := by
      funext q
      cases q
      rfl
    rw [hcomp]
    exact relabelTM2Stmt_id stmt

noncomputable instance instPrimcodablePartrecTM2Stmt :
    Primcodable PartrecTM2Stmt :=
  Primcodable.ofEquiv
    (PartrecStartedTM2Stmt (Turing.ToPartrec.Code.zero'))
    (partrecTM2StmtEquivStarted Turing.ToPartrec.Code.zero')

abbrev PartrecStartedTM1Label (tc : Turing.ToPartrec.Code) : Type :=
  Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar

abbrev PartrecStartedTM1GoCode (tc : Turing.ToPartrec.Code) : Type :=
  ((Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
        Turing.PartrecToTM2.K'.main × PartrecStartedTM2Stmt tc) ⊕
    (Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
        Turing.PartrecToTM2.K'.rev × PartrecStartedTM2Stmt tc)) ⊕
  ((Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
        Turing.PartrecToTM2.K'.aux × PartrecStartedTM2Stmt tc) ⊕
    (Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
        Turing.PartrecToTM2.K'.stack × PartrecStartedTM2Stmt tc))

abbrev PartrecStartedTM1LabelCode (tc : Turing.ToPartrec.Code) : Type :=
  StartedLabel tc ⊕ (PartrecStartedTM1GoCode tc ⊕ PartrecStartedTM2Stmt tc)

def partrecStartedTM1LabelEquivCode (tc : Turing.ToPartrec.Code) :
    PartrecStartedTM1Label tc ≃ PartrecStartedTM1LabelCode tc where
  toFun
    | Turing.TM2to1.Λ'.normal q => Sum.inl q
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.main s q =>
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (s, q))))
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.rev s q =>
        Sum.inr (Sum.inl (Sum.inl (Sum.inr (s, q))))
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.aux s q =>
        Sum.inr (Sum.inl (Sum.inr (Sum.inl (s, q))))
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.stack s q =>
        Sum.inr (Sum.inl (Sum.inr (Sum.inr (s, q))))
    | Turing.TM2to1.Λ'.ret q => Sum.inr (Sum.inr q)
  invFun
    | Sum.inl q => Turing.TM2to1.Λ'.normal q
    | Sum.inr (Sum.inl (Sum.inl (Sum.inl (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.main s q
    | Sum.inr (Sum.inl (Sum.inl (Sum.inr (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.rev s q
    | Sum.inr (Sum.inl (Sum.inr (Sum.inl (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.aux s q
    | Sum.inr (Sum.inl (Sum.inr (Sum.inr (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.stack s q
    | Sum.inr (Sum.inr q) => Turing.TM2to1.Λ'.ret q
  left_inv := by
    intro q
    cases q with
    | normal q => rfl
    | go k s q =>
        cases k <;> rfl
    | ret q => rfl
  right_inv := by
    intro code
    rcases code with q | rest
    · rfl
    rcases rest with goCode | stmt
    · rcases goCode with left | right
      · rcases left with p | p <;> rcases p with ⟨s, q⟩ <;> rfl
      · rcases right with p | p <;> rcases p with ⟨s, q⟩ <;> rfl
    · rfl

noncomputable instance instPrimcodablePartrecStartedTM1Label (tc : Turing.ToPartrec.Code) :
    Primcodable (PartrecStartedTM1Label tc) :=
  Primcodable.ofEquiv
    (PartrecStartedTM1LabelCode tc)
    (partrecStartedTM1LabelEquivCode tc)

abbrev PartrecTM1Label : Type :=
  Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol Turing.PartrecToTM2.Λ' PartrecVar

abbrev PartrecTM1LabelCode : Type :=
  Turing.PartrecToTM2.Λ' ⊕
    ((((Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
          Turing.PartrecToTM2.K'.main × PartrecTM2Stmt) ⊕
        (Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
          Turing.PartrecToTM2.K'.rev × PartrecTM2Stmt)) ⊕
      ((Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
          Turing.PartrecToTM2.K'.aux × PartrecTM2Stmt) ⊕
        (Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar
          Turing.PartrecToTM2.K'.stack × PartrecTM2Stmt))) ⊕
      PartrecTM2Stmt)

def partrecTM1LabelEquivCode : PartrecTM1Label ≃ PartrecTM1LabelCode where
  toFun
    | Turing.TM2to1.Λ'.normal q => Sum.inl q
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.main s q =>
        Sum.inr (Sum.inl (Sum.inl (Sum.inl (s, q))))
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.rev s q =>
        Sum.inr (Sum.inl (Sum.inl (Sum.inr (s, q))))
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.aux s q =>
        Sum.inr (Sum.inl (Sum.inr (Sum.inl (s, q))))
    | Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.stack s q =>
        Sum.inr (Sum.inl (Sum.inr (Sum.inr (s, q))))
    | Turing.TM2to1.Λ'.ret q => Sum.inr (Sum.inr q)
  invFun
    | Sum.inl q => Turing.TM2to1.Λ'.normal q
    | Sum.inr (Sum.inl (Sum.inl (Sum.inl (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.main s q
    | Sum.inr (Sum.inl (Sum.inl (Sum.inr (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.rev s q
    | Sum.inr (Sum.inl (Sum.inr (Sum.inl (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.aux s q
    | Sum.inr (Sum.inl (Sum.inr (Sum.inr (s, q)))) =>
        Turing.TM2to1.Λ'.go Turing.PartrecToTM2.K'.stack s q
    | Sum.inr (Sum.inr q) => Turing.TM2to1.Λ'.ret q
  left_inv := by
    intro q
    cases q with
    | normal q => rfl
    | go k s q =>
        cases k <;> rfl
    | ret q => rfl
  right_inv := by
    intro code
    rcases code with q | rest
    · rfl
    rcases rest with goCode | stmt
    · rcases goCode with left | right
      · rcases left with p | p <;> rcases p with ⟨s, q⟩ <;> rfl
      · rcases right with p | p <;> rcases p with ⟨s, q⟩ <;> rfl
    · rfl

noncomputable instance instPrimcodablePartrecTM1Label : Primcodable PartrecTM1Label :=
  Primcodable.ofEquiv PartrecTM1LabelCode partrecTM1LabelEquivCode

def decEqPartrecStartedTM1Label (tc : Turing.ToPartrec.Code) :
    (a b : Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar) →
      Decidable (a = b)
  | Turing.TM2to1.Λ'.normal q, b =>
      match b with
      | Turing.TM2to1.Λ'.normal q' => decidable_of_iff' (q = q') (by simp)
      | Turing.TM2to1.Λ'.go .. => .isFalse (by intro h; cases h)
      | Turing.TM2to1.Λ'.ret .. => .isFalse (by intro h; cases h)
  | Turing.TM2to1.Λ'.go k s q, b =>
      match b with
      | Turing.TM2to1.Λ'.normal .. => .isFalse (by intro h; cases h)
      | Turing.TM2to1.Λ'.go k' s' q' =>
          if hk : k = k' then by
            subst k'
            exact decidable_of_iff' (s = s' ∧ q = q') (by simp)
          else
            .isFalse (by intro h; cases h; exact hk rfl)
      | Turing.TM2to1.Λ'.ret .. => .isFalse (by intro h; cases h)
  | Turing.TM2to1.Λ'.ret q, b =>
      match b with
      | Turing.TM2to1.Λ'.normal .. => .isFalse (by intro h; cases h)
      | Turing.TM2to1.Λ'.go .. => .isFalse (by intro h; cases h)
      | Turing.TM2to1.Λ'.ret q' => decidable_of_iff' (q = q') (by simp)

instance instDecidableEqPartrecStartedTM1Label (tc : Turing.ToPartrec.Code) :
    DecidableEq
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar) :=
  decEqPartrecStartedTM1Label tc

def decEqPartrecStartedTM1Stmt (tc : Turing.ToPartrec.Code) :
    (a b : Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar) → Decidable (a = b)
  | Turing.TM1.Stmt.move d q, b =>
      match b with
      | Turing.TM1.Stmt.move d' q' => by
          letI : Decidable (q = q') := decEqPartrecStartedTM1Stmt tc q q'
          exact decidable_of_iff' (d = d' ∧ q = q') (by simp)
      | Turing.TM1.Stmt.write .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM1.Stmt.write f q, b =>
      match b with
      | Turing.TM1.Stmt.move .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.write f' q' => by
          letI : Decidable (q = q') := decEqPartrecStartedTM1Stmt tc q q'
          exact decidable_of_iff' (f = f' ∧ q = q') (by simp)
      | Turing.TM1.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM1.Stmt.load f q, b =>
      match b with
      | Turing.TM1.Stmt.move .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.write .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.load f' q' => by
          letI : Decidable (q = q') := decEqPartrecStartedTM1Stmt tc q q'
          exact decidable_of_iff' (f = f' ∧ q = q') (by simp)
      | Turing.TM1.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM1.Stmt.branch f q1 q2, b =>
      match b with
      | Turing.TM1.Stmt.move .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.write .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.branch f' q1' q2' => by
          letI : Decidable (q1 = q1') := decEqPartrecStartedTM1Stmt tc q1 q1'
          letI : Decidable (q2 = q2') := decEqPartrecStartedTM1Stmt tc q2 q2'
          exact decidable_of_iff' (f = f' ∧ q1 = q1' ∧ q2 = q2') (by simp)
      | Turing.TM1.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM1.Stmt.goto f, b =>
      match b with
      | Turing.TM1.Stmt.move .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.write .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.goto f' => decidable_of_iff' (f = f') (by simp)
      | Turing.TM1.Stmt.halt => .isFalse (by intro h; cases h)
  | Turing.TM1.Stmt.halt, b =>
      match b with
      | Turing.TM1.Stmt.move .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.write .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.load .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.branch .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.goto .. => .isFalse (by intro h; cases h)
      | Turing.TM1.Stmt.halt => .isTrue rfl

instance instDecidableEqPartrecStartedTM1Stmt (tc : Turing.ToPartrec.Code) :
    DecidableEq
      (Turing.TM1.Stmt
        (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
        (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
        PartrecVar) :=
  decEqPartrecStartedTM1Stmt tc

instance instPrimcodableTM1to0Label {Γ Λ σ : Type}
    [Primcodable (Turing.TM1.Stmt Γ Λ σ)] [Primcodable σ]
    {M : Λ → Turing.TM1.Stmt Γ Λ σ} :
    Primcodable (Turing.TM1to0.Λ' M) := by
  dsimp [Turing.TM1to0.Λ']
  infer_instance

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

/-- Executable list-valued support for the code-specific started TM2 labels. -/
def partrecStartedTM2LabelList (tc : Turing.ToPartrec.Code) : List (StartedLabel tc) :=
  (PartrecToTM2SupportList.labelList tc).map (StartedLabel.wrap tc)

/-- Numeric count of started TM2 labels generated for code `tc`. -/
def partrecStartedTM2LabelCount (tc : Turing.ToPartrec.Code) : Nat :=
  PartrecToTM2SupportList.labelCount tc

theorem partrecStartedTM2LabelList_length (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM2LabelList tc).length = partrecStartedTM2LabelCount tc := by
  simp [partrecStartedTM2LabelList, partrecStartedTM2LabelCount,
    PartrecToTM2SupportList.labelList_length]

theorem mem_partrecStartedTM2LabelList (tc : Turing.ToPartrec.Code)
    (q : StartedLabel tc) :
    q ∈ partrecStartedTM2LabelList tc ↔ q ∈ partrecStartedTM2Labels tc := by
  constructor
  · intro h
    rw [partrecStartedTM2LabelList, List.mem_map] at h
    rcases h with ⟨r, hr, hq⟩
    cases hq
    exact (mem_partrecStartedTM2Labels tc (StartedLabel.wrap tc r)).2
      (PartrecToTM2SupportList.mem_labelList_iff.1 hr)
  · intro h
    refine List.mem_map.2 ⟨q.val, ?_, ?_⟩
    · exact PartrecToTM2SupportList.mem_labelList_iff.2
        ((mem_partrecStartedTM2Labels tc q).1 h)
    · cases q
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

/-- The TM1 machine obtained directly from Mathlib's `PartrecToTM2` evaluator. -/
def partrecTM1Machine :
    PartrecTM1Label →
      Turing.TM1.Stmt (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
        PartrecTM1Label PartrecVar :=
  Turing.TM2to1.tr partrecTM2

def relabelTM2to1Label {Λ Λ' : Type}
    (f : Λ → Λ') :
    Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol Λ PartrecVar →
      Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol Λ' PartrecVar
  | Turing.TM2to1.Λ'.normal q => Turing.TM2to1.Λ'.normal (f q)
  | Turing.TM2to1.Λ'.go k s q =>
      Turing.TM2to1.Λ'.go k s (relabelTM2Stmt f q)
  | Turing.TM2to1.Λ'.ret q =>
      Turing.TM2to1.Λ'.ret (relabelTM2Stmt f q)

def relabelTM1Stmt {Γ Λ Λ' σ : Type}
    (f : Λ → Λ') : Turing.TM1.Stmt Γ Λ σ → Turing.TM1.Stmt Γ Λ' σ
  | Turing.TM1.Stmt.move d q => Turing.TM1.Stmt.move d (relabelTM1Stmt f q)
  | Turing.TM1.Stmt.write g q => Turing.TM1.Stmt.write g (relabelTM1Stmt f q)
  | Turing.TM1.Stmt.load g q => Turing.TM1.Stmt.load g (relabelTM1Stmt f q)
  | Turing.TM1.Stmt.branch p q₁ q₂ =>
      Turing.TM1.Stmt.branch p (relabelTM1Stmt f q₁) (relabelTM1Stmt f q₂)
  | Turing.TM1.Stmt.goto g => Turing.TM1.Stmt.goto fun a s => f (g a s)
  | Turing.TM1.Stmt.halt => Turing.TM1.Stmt.halt

instance instDecidableEqPartrecStartedTM0Label (tc : Turing.ToPartrec.Code) :
    DecidableEq (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) := by
  unfold Turing.TM1to0.Λ'
  infer_instance

noncomputable def partrecStartedTM1Labels (tc : Turing.ToPartrec.Code) :=
  Turing.TM2to1.trSupp (partrecStartedTM2 tc) (partrecStartedTM2Labels tc)

/-- List-valued support states introduced by Mathlib's TM2-to-TM1 translation for one TM2
statement. This mirrors `Turing.TM2to1.trStmts₁` without using `Finset`. -/
def tm2to1StmtSupportList {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    List (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol Λ PartrecVar) :=
  match stmt with
  | Turing.TM2.Stmt.push k f q =>
      [Turing.TM2to1.Λ'.go k (Turing.TM2to1.StAct.push f) q,
        Turing.TM2to1.Λ'.ret q] ++ tm2to1StmtSupportList q
  | Turing.TM2.Stmt.peek k f q =>
      [Turing.TM2to1.Λ'.go k (Turing.TM2to1.StAct.peek f) q,
        Turing.TM2to1.Λ'.ret q] ++ tm2to1StmtSupportList q
  | Turing.TM2.Stmt.pop k f q =>
      [Turing.TM2to1.Λ'.go k (Turing.TM2to1.StAct.pop f) q,
        Turing.TM2to1.Λ'.ret q] ++ tm2to1StmtSupportList q
  | Turing.TM2.Stmt.load _ q => tm2to1StmtSupportList q
  | Turing.TM2.Stmt.branch _ q₁ q₂ =>
      tm2to1StmtSupportList q₁ ++ tm2to1StmtSupportList q₂
  | Turing.TM2.Stmt.goto _ => []
  | Turing.TM2.Stmt.halt => []

/-- Numeric length mirror of `tm2to1StmtSupportList`. -/
def tm2to1StmtSupportLength {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) : Nat :=
  match stmt with
  | Turing.TM2.Stmt.push _ _ q => 2 + tm2to1StmtSupportLength q
  | Turing.TM2.Stmt.peek _ _ q => 2 + tm2to1StmtSupportLength q
  | Turing.TM2.Stmt.pop _ _ q => 2 + tm2to1StmtSupportLength q
  | Turing.TM2.Stmt.load _ q => tm2to1StmtSupportLength q
  | Turing.TM2.Stmt.branch _ q₁ q₂ =>
      tm2to1StmtSupportLength q₁ + tm2to1StmtSupportLength q₂
  | Turing.TM2.Stmt.goto _ => 0
  | Turing.TM2.Stmt.halt => 0

theorem tm2to1StmtSupportList_length {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    (tm2to1StmtSupportList stmt).length = tm2to1StmtSupportLength stmt := by
  induction stmt with
  | push k f stmt IH =>
      simp [tm2to1StmtSupportList, tm2to1StmtSupportLength, IH]
      omega
  | peek k f stmt IH =>
      simp [tm2to1StmtSupportList, tm2to1StmtSupportLength, IH]
      omega
  | pop k f stmt IH =>
      simp [tm2to1StmtSupportList, tm2to1StmtSupportLength, IH]
      omega
  | load f stmt IH =>
      simpa [tm2to1StmtSupportList, tm2to1StmtSupportLength] using IH
  | branch f stmt₁ stmt₂ IH₁ IH₂ =>
      simp [tm2to1StmtSupportList, tm2to1StmtSupportLength, IH₁, IH₂]
  | goto f =>
      simp [tm2to1StmtSupportList, tm2to1StmtSupportLength]
  | halt =>
      simp [tm2to1StmtSupportList, tm2to1StmtSupportLength]

/--
Auxiliary-label count contributed by a `PartrecToTM2` continuation when its
`ret` label is translated through Mathlib's TM2-to-TM1 construction.
-/
def partrecTM2RetSupportLength : Turing.PartrecToTM2.Cont' → Nat
  | Turing.PartrecToTM2.Cont'.fix _ _ => 2
  | _ => 0

/-- Code-level version of `partrecTM2RetSupportLength`.

For a `ret k` label, the label payload is `encodeCont k + 1`; the constructor
bits for non-halt continuations are therefore in `payload - 2`.
-/
def partrecTM2RetSupportLengthCode (payload : Nat) : Nat :=
  if (payload - 2).bodd then
    if ((payload - 2).div2).bodd then 2 else 0
  else 0

theorem partrecTM2RetSupportLengthCode_primrec :
    Primrec partrecTM2RetSupportLengthCode := by
  unfold partrecTM2RetSupportLengthCode
  let hpred : Primrec fun payload : Nat => payload - 2 :=
    Primrec.nat_sub.comp Primrec.id (Primrec.const 2)
  let hbodd : Primrec fun payload : Nat => (payload - 2).bodd :=
    Primrec.nat_bodd.comp hpred
  let hdivBodd : Primrec fun payload : Nat => ((payload - 2).div2).bodd :=
    Primrec.nat_bodd.comp (Primrec.nat_div2.comp hpred)
  exact (Primrec.cond hbodd
    (Primrec.cond hdivBodd (Primrec.const 2) (Primrec.const 0))
    (Primrec.const 0)).of_eq fun payload => by
      cases (payload - 2).bodd <;> cases ((payload - 2).div2).bodd <;> rfl

theorem partrecTM2RetSupportLengthCode_encodeCont
    (k : Turing.PartrecToTM2.Cont') :
    partrecTM2RetSupportLengthCode
        (Turing.PartrecToTM2.Cont'.encodeCont k + 1) =
      partrecTM2RetSupportLength k := by
  cases k <;>
    simp [partrecTM2RetSupportLengthCode, partrecTM2RetSupportLength,
      Turing.PartrecToTM2.Cont'.encodeCont, Nat.bit_val]

/--
Numeric mirror of `tm2to1StmtSupportLength (partrecTM2 q)`, specialized to
Mathlib's concrete `PartrecToTM2` evaluator labels.

This avoids needing a `Primcodable` instance for arbitrary recursive
`TM2.Stmt` values when proving computability of the source reduction: for the
evaluator machine, the TM2-to-TM1 auxiliary-label contribution is determined by
the outer evaluator label constructor.
-/
def partrecTM2SupportLength : Turing.PartrecToTM2.Λ' → Nat
  | Turing.PartrecToTM2.Λ'.move .. => 4
  | Turing.PartrecToTM2.Λ'.push .. => 2
  | Turing.PartrecToTM2.Λ'.read .. => 0
  | Turing.PartrecToTM2.Λ'.clear .. => 2
  | Turing.PartrecToTM2.Λ'.copy .. => 6
  | Turing.PartrecToTM2.Λ'.succ .. => 10
  | Turing.PartrecToTM2.Λ'.pred .. => 8
  | Turing.PartrecToTM2.Λ'.ret k => partrecTM2RetSupportLength k

/-- Code-level version of `partrecTM2SupportLength`. -/
def partrecTM2SupportLengthCode (n : Nat) : Nat :=
  if n % 8 = 1 then 4
  else if n % 8 = 2 then 2
  else if n % 8 = 3 then 6
  else if n % 8 = 4 then 2
  else if n % 8 = 5 then 0
  else if n % 8 = 6 then 10
  else if n % 8 = 7 then 8
  else partrecTM2RetSupportLengthCode (n / 8)

theorem partrecTM2SupportLengthCode_primrec :
    Primrec partrecTM2SupportLengthCode := by
  unfold partrecTM2SupportLengthCode
  let htag : Primrec fun n : Nat => n % 8 :=
    Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  let hret : Primrec fun n : Nat => partrecTM2RetSupportLengthCode (n / 8) :=
    partrecTM2RetSupportLengthCode_primrec.comp
      (Primrec.nat_div.comp Primrec.id (Primrec.const 8))
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) (Primrec.const 4)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) (Primrec.const 2)
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) (Primrec.const 6)
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) (Primrec.const 2)
          (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) (Primrec.const 0)
            (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) (Primrec.const 10)
              (Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) (Primrec.const 8)
                hret))))))

theorem partrecTM2SupportLengthCode_encodeLabel
    (q : Turing.PartrecToTM2.Λ') :
    partrecTM2SupportLengthCode (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      partrecTM2SupportLength q := by
  cases q with
  | move p k₁ k₂ q =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_move]
  | push k f q =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_push]
  | read f =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_read]
  | clear p k q =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_clear]
  | copy q =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_copy]
  | succ q =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_succ]
  | pred q₁ q₂ =>
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_pred]
  | ret k =>
      have hcode :
          Turing.PartrecToTM2.Λ'.encodeLabel
              (Turing.PartrecToTM2.Λ'.ret k) =
            8 * (Turing.PartrecToTM2.Cont'.encodeCont k + 1) + 0 := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_ret]
        omega
      rw [hcode]
      simp [partrecTM2SupportLengthCode, partrecTM2SupportLength,
        partrecTM2RetSupportLengthCode_encodeCont]

theorem partrecTM2SupportLength_primrec :
    Primrec partrecTM2SupportLength := by
  exact (partrecTM2SupportLengthCode_primrec.comp Primrec.encode).of_eq fun q => by
    rw [Turing.PartrecToTM2.Λ'.encodeLabel_eq]
    exact partrecTM2SupportLengthCode_encodeLabel q

theorem partrecTM2SupportLength_labelWeight_primrec :
    Primrec (PartrecToTM2SupportList.labelWeight partrecTM2SupportLength) :=
  PartrecToTM2SupportList.labelWeight_primrec_of_codeSuppWeight'
    (PartrecToTM2SupportList.codeSuppWeight'_primrec_of_code
      partrecTM2SupportLengthCode_primrec partrecTM2SupportLengthCode_encodeLabel)

theorem tm2to1StmtSupportLength_partrecTM2
    (q : Turing.PartrecToTM2.Λ') :
    tm2to1StmtSupportLength (partrecTM2 q) = partrecTM2SupportLength q := by
  cases q with
  | move p k₁ k₂ q =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', Turing.PartrecToTM2.push',
        tm2to1StmtSupportLength]
  | push k f q =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        tm2to1StmtSupportLength]
  | read f =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        tm2to1StmtSupportLength]
  | clear p k q =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', tm2to1StmtSupportLength]
  | copy q =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', Turing.PartrecToTM2.push',
        tm2to1StmtSupportLength]
  | succ q =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', tm2to1StmtSupportLength]
  | pred q₁ q₂ =>
      simp [partrecTM2, partrecTM2SupportLength, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', Turing.PartrecToTM2.peek',
        tm2to1StmtSupportLength]
  | ret k =>
      cases k <;>
        simp [partrecTM2, partrecTM2SupportLength, partrecTM2RetSupportLength,
          Turing.PartrecToTM2.tr, Turing.PartrecToTM2.pop',
          tm2to1StmtSupportLength]

theorem tm2to1StmtSupportLength_relabel {Λ Λ' : Type}
    (f : Λ → Λ') (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    tm2to1StmtSupportLength (relabelTM2Stmt f stmt) =
      tm2to1StmtSupportLength stmt := by
  induction stmt with
  | push k g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength, IH]
  | peek k g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength, IH]
  | pop k g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength, IH]
  | load g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength, IH]
  | branch g stmt₁ stmt₂ IH₁ IH₂ =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength, IH₁, IH₂]
  | goto g =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength]
  | halt =>
      simp [relabelTM2Stmt, tm2to1StmtSupportLength]

theorem tm2to1StmtSupportList_relabel {Λ Λ' : Type}
    (f : Λ → Λ') (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    tm2to1StmtSupportList (relabelTM2Stmt f stmt) =
      (tm2to1StmtSupportList stmt).map (relabelTM2to1Label f) := by
  induction stmt with
  | push k g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList, relabelTM2to1Label, IH]
  | peek k g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList, relabelTM2to1Label, IH]
  | pop k g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList, relabelTM2to1Label, IH]
  | load g stmt IH =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList, IH]
  | branch g stmt₁ stmt₂ IH₁ IH₂ =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList, IH₁, IH₂]
  | goto g =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList]
  | halt =>
      simp [relabelTM2Stmt, tm2to1StmtSupportList]

private theorem list_sum_map_one_add {α : Type} (xs : List α) (f : α → Nat) :
    (xs.map fun x => 1 + f x).sum = xs.length + (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

private theorem list_sum_nat_primrec {α : Type} [Primcodable α]
    {f : α → List Nat} (hf : Primrec f) :
    Primrec fun a => (f a).sum := by
  let step : α → Nat × Nat → Nat := fun _ p => p.1 + p.2
  have hstep : Primrec₂ step := by
    apply Primrec₂.mk
    exact Primrec.nat_add.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec fun a => List.foldl (fun s b => s + b) 0 (f a) := by
    exact (Primrec.list_foldl (h := step) hf (Primrec.const 0) hstep).of_eq fun a => by
      rfl
  exact hfold.of_eq fun a => by
    rw [List.sum_eq_foldl]

theorem mem_tm2to1StmtSupportList_iff {Λ : Type}
    {stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar}
    {q : Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol Λ PartrecVar} :
    q ∈ tm2to1StmtSupportList stmt ↔ q ∈ Turing.TM2to1.trStmts₁ stmt := by
  induction stmt with
  | push k f stmt IH =>
      simp [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁, IH]
  | peek k f stmt IH =>
      simp [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁, IH]
  | pop k f stmt IH =>
      simp [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁, IH]
  | load f stmt IH =>
      simpa [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁] using IH
  | branch f stmt₁ stmt₂ IH₁ IH₂ =>
      simp [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁, IH₁, IH₂]
  | goto f =>
      simp [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁]
  | halt =>
      simp [tm2to1StmtSupportList, Turing.TM2to1.trStmts₁]

/-- List-valued support for the started TM1 machine obtained from the TM2-to-TM1 translation. -/
def partrecTM1LabelList (tc : Turing.ToPartrec.Code) : List PartrecTM1Label :=
  (PartrecToTM2SupportList.labelList tc).flatMap fun q =>
    Turing.TM2to1.Λ'.normal q :: tm2to1StmtSupportList (partrecTM2 q)

def partrecStartedTM1LabelList (tc : Turing.ToPartrec.Code) :
    List (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar) :=
  (partrecStartedTM2LabelList tc).flatMap fun q =>
    Turing.TM2to1.Λ'.normal q :: tm2to1StmtSupportList (partrecStartedTM2 tc q)

theorem partrecStartedTM1LabelList_eq_map (tc : Turing.ToPartrec.Code) :
    partrecStartedTM1LabelList tc =
      (partrecTM1LabelList tc).map (relabelTM2to1Label (StartedLabel.wrap tc)) := by
  unfold partrecStartedTM1LabelList partrecTM1LabelList partrecStartedTM2LabelList
    partrecStartedTM2
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro q hq
  simp [relabelTM2to1Label, tm2to1StmtSupportList_relabel]

/-- Numeric count of started TM1 labels generated by the TM2-to-TM1 translation. -/
def partrecStartedTM1LabelCount (tc : Turing.ToPartrec.Code) : Nat :=
  partrecStartedTM2LabelCount tc +
    ((PartrecToTM2SupportList.labelList tc).map fun q =>
      tm2to1StmtSupportLength (partrecTM2 q)).sum

/--
Statement-free numeric form of `partrecStartedTM1LabelCount`.

The summand is the label-level mirror `partrecTM2SupportLength`, so this is the
form that the eventual primitive-recursion proof should target.
-/
def partrecStartedTM1LabelCountData (tc : Turing.ToPartrec.Code) : Nat :=
  partrecStartedTM2LabelCount tc +
    ((PartrecToTM2SupportList.labelList tc).map partrecTM2SupportLength).sum

/--
Numeric started-TM1 label count phrased through the weighted evaluator-support
mirror instead of an explicit mapped support list.
-/
def partrecStartedTM1LabelCountWeightData (tc : Turing.ToPartrec.Code) : Nat :=
  PartrecToTM2SupportList.labelCount tc +
    PartrecToTM2SupportList.labelWeight partrecTM2SupportLength tc

theorem partrecStartedTM2LabelCount_primrec_of_labelList
    (hlabel : Primrec PartrecToTM2SupportList.labelList) :
    Primrec partrecStartedTM2LabelCount := by
  exact (Primrec.list_length.comp hlabel).of_eq fun tc => by
    rw [partrecStartedTM2LabelCount, ← PartrecToTM2SupportList.labelList_length]

theorem partrecStartedTM1LabelCountWeightData_primrec
    (hcount : Primrec PartrecToTM2SupportList.labelCount)
    (hweight : Primrec (PartrecToTM2SupportList.labelWeight partrecTM2SupportLength)) :
    Primrec partrecStartedTM1LabelCountWeightData := by
  unfold partrecStartedTM1LabelCountWeightData
  exact Primrec.nat_add.comp hcount hweight

theorem partrecStartedTM1LabelCountData_primrec_of_labelList
    (hlabel : Primrec PartrecToTM2SupportList.labelList) :
    Primrec partrecStartedTM1LabelCountData := by
  unfold partrecStartedTM1LabelCountData
  have hcount : Primrec partrecStartedTM2LabelCount :=
    partrecStartedTM2LabelCount_primrec_of_labelList hlabel
  have hmap :
      Primrec fun tc : Turing.ToPartrec.Code =>
        (PartrecToTM2SupportList.labelList tc).map partrecTM2SupportLength := by
    refine Primrec.list_map hlabel ?_
    exact (partrecTM2SupportLength_primrec.comp Primrec.snd).to₂
  have hsum :
      Primrec fun tc : Turing.ToPartrec.Code =>
        ((PartrecToTM2SupportList.labelList tc).map partrecTM2SupportLength).sum :=
    list_sum_nat_primrec hmap
  exact Primrec.nat_add.comp hcount hsum

theorem partrecStartedTM1LabelCount_eq_data (tc : Turing.ToPartrec.Code) :
    partrecStartedTM1LabelCount tc = partrecStartedTM1LabelCountData tc := by
  unfold partrecStartedTM1LabelCount partrecStartedTM1LabelCountData
  apply congrArg (fun n => partrecStartedTM2LabelCount tc + n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _hq
  exact tm2to1StmtSupportLength_partrecTM2 q

theorem partrecStartedTM1LabelCountData_eq_weightData (tc : Turing.ToPartrec.Code) :
    partrecStartedTM1LabelCountData tc =
      partrecStartedTM1LabelCountWeightData tc := by
  unfold partrecStartedTM1LabelCountData partrecStartedTM1LabelCountWeightData
    partrecStartedTM2LabelCount
  rw [← PartrecToTM2SupportList.labelList_length]
  rw [PartrecToTM2SupportList.labelList_weight]

theorem partrecStartedTM1LabelCount_primrec_of_labelWeight
    (hcount : Primrec PartrecToTM2SupportList.labelCount)
    (hweight : Primrec (PartrecToTM2SupportList.labelWeight partrecTM2SupportLength)) :
    Primrec partrecStartedTM1LabelCount :=
  (partrecStartedTM1LabelCountWeightData_primrec hcount hweight).of_eq fun tc => by
    rw [partrecStartedTM1LabelCount_eq_data, partrecStartedTM1LabelCountData_eq_weightData]

theorem partrecStartedTM1LabelCount_primrec_of_supportMirrors
    (hcount : Primrec₂ PartrecToTM2SupportList.codeSuppLength)
    (hweight :
      Primrec₂ (PartrecToTM2SupportList.codeSuppWeight partrecTM2SupportLength)) :
    Primrec partrecStartedTM1LabelCount :=
  partrecStartedTM1LabelCount_primrec_of_labelWeight
    (PartrecToTM2SupportList.labelCount_primrec_of_codeSuppLength hcount)
    (PartrecToTM2SupportList.labelWeight_primrec_of_codeSuppWeight hweight)

theorem partrecStartedTM1LabelCount_primrec_of_labelList
    (hlabel : Primrec PartrecToTM2SupportList.labelList) :
    Primrec partrecStartedTM1LabelCount :=
  (partrecStartedTM1LabelCountData_primrec_of_labelList hlabel).of_eq fun tc =>
    (partrecStartedTM1LabelCount_eq_data tc).symm

theorem partrecStartedTM1LabelList_length (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM1LabelList tc).length = partrecStartedTM1LabelCount tc := by
  let labels := partrecStartedTM2LabelList tc
  have hsum :
      (labels.map fun q => tm2to1StmtSupportLength (partrecStartedTM2 tc q)).sum =
        ((PartrecToTM2SupportList.labelList tc).map fun q =>
          tm2to1StmtSupportLength (partrecTM2 q)).sum := by
    simp only [labels, partrecStartedTM2LabelList, List.map_map, partrecStartedTM2]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q
    simp [StartedLabel.wrap, tm2to1StmtSupportLength_relabel]
  calc
    (partrecStartedTM1LabelList tc).length
        = (labels.flatMap fun q =>
            Turing.TM2to1.Λ'.normal q ::
              tm2to1StmtSupportList (partrecStartedTM2 tc q)).length := by
          rfl
    _ = (labels.map fun q =>
            1 + tm2to1StmtSupportLength (partrecStartedTM2 tc q)).sum := by
          simp [List.length_flatMap, tm2to1StmtSupportList_length]
          omega
    _ = (labels.map fun q => tm2to1StmtSupportLength (partrecStartedTM2 tc q)).sum +
          labels.length := by
          rw [list_sum_map_one_add labels
            (fun q => tm2to1StmtSupportLength (partrecStartedTM2 tc q))]
          rw [Nat.add_comm]
    _ = partrecStartedTM1LabelCount tc := by
          rw [hsum]
          change
            ((PartrecToTM2SupportList.labelList tc).map fun q =>
              tm2to1StmtSupportLength (partrecTM2 q)).sum +
              (partrecStartedTM2LabelList tc).length =
                partrecStartedTM1LabelCount tc
          rw [partrecStartedTM2LabelList_length]
          unfold partrecStartedTM1LabelCount
          rw [Nat.add_comm]

theorem mem_partrecStartedTM1LabelList (tc : Turing.ToPartrec.Code)
    (q : Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar) :
    q ∈ partrecStartedTM1LabelList tc ↔ q ∈ partrecStartedTM1Labels tc := by
  letI : DecidableEq
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar) :=
    Classical.decEq _
  constructor
  · intro h
    unfold partrecStartedTM1LabelList at h
    unfold partrecStartedTM1Labels
    rw [List.mem_flatMap] at h
    rcases h with ⟨r, hr, hq⟩
    have hrlabels : r ∈ partrecStartedTM2Labels tc :=
      (mem_partrecStartedTM2LabelList tc r).1 hr
    simp only [Turing.TM2to1.trSupp, Finset.mem_biUnion]
    refine ⟨r, hrlabels, ?_⟩
    simp only [List.mem_cons] at hq
    rcases hq with hq | hq
    · exact Finset.mem_insert.2 (Or.inl hq)
    · exact Finset.mem_insert.2
        (Or.inr ((mem_tm2to1StmtSupportList_iff).1 hq))
  · intro h
    unfold partrecStartedTM1LabelList partrecStartedTM1Labels at *
    simp only [Turing.TM2to1.trSupp, Finset.mem_biUnion] at h
    rcases h with ⟨r, hr, hq⟩
    refine List.mem_flatMap.2
      ⟨r, (mem_partrecStartedTM2LabelList tc r).2 hr, ?_⟩
    simp only [List.mem_cons]
    rcases Finset.mem_insert.1 hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr ((mem_tm2to1StmtSupportList_iff).2 hq)

/-- List-valued substatement closure for a TM1 statement. This mirrors
`Turing.TM1.stmts₁` without using `Finset`. -/
def tm1StmtSupportList {Γ Λ σ : Type}
    (stmt : Turing.TM1.Stmt Γ Λ σ) : List (Turing.TM1.Stmt Γ Λ σ) :=
  match stmt with
  | Turing.TM1.Stmt.move _ q => stmt :: tm1StmtSupportList q
  | Turing.TM1.Stmt.write _ q => stmt :: tm1StmtSupportList q
  | Turing.TM1.Stmt.load _ q => stmt :: tm1StmtSupportList q
  | Turing.TM1.Stmt.branch _ q₁ q₂ =>
      stmt :: (tm1StmtSupportList q₁ ++ tm1StmtSupportList q₂)
  | Turing.TM1.Stmt.goto _ => [stmt]
  | Turing.TM1.Stmt.halt => [stmt]

/-- Numeric length mirror of `tm1StmtSupportList`. -/
def tm1StmtSupportLength {Γ Λ σ : Type}
    (stmt : Turing.TM1.Stmt Γ Λ σ) : Nat :=
  match stmt with
  | Turing.TM1.Stmt.move _ q => 1 + tm1StmtSupportLength q
  | Turing.TM1.Stmt.write _ q => 1 + tm1StmtSupportLength q
  | Turing.TM1.Stmt.load _ q => 1 + tm1StmtSupportLength q
  | Turing.TM1.Stmt.branch _ q₁ q₂ =>
      1 + (tm1StmtSupportLength q₁ + tm1StmtSupportLength q₂)
  | Turing.TM1.Stmt.goto _ => 1
  | Turing.TM1.Stmt.halt => 1

def tm2to1TrNormalSupportLength {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) : Nat :=
  match stmt with
  | Turing.TM2.Stmt.push .. => 1
  | Turing.TM2.Stmt.peek .. => 1
  | Turing.TM2.Stmt.pop .. => 1
  | Turing.TM2.Stmt.load _ q => 1 + tm2to1TrNormalSupportLength q
  | Turing.TM2.Stmt.branch _ q₁ q₂ =>
      1 + (tm2to1TrNormalSupportLength q₁ + tm2to1TrNormalSupportLength q₂)
  | Turing.TM2.Stmt.goto _ => 1
  | Turing.TM2.Stmt.halt => 1

theorem tm2to1TrNormalSupportLength_eq {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    tm1StmtSupportLength (Turing.TM2to1.trNormal stmt) =
      tm2to1TrNormalSupportLength stmt := by
  induction stmt with
  | push k f stmt IH =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength]
  | peek k f stmt IH =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength]
  | pop k f stmt IH =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength]
  | load f stmt IH =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength, IH]
  | branch f stmt₁ stmt₂ IH₁ IH₂ =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength,
        IH₁, IH₂]
  | goto f =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength]
  | halt =>
      simp [Turing.TM2to1.trNormal, tm1StmtSupportLength, tm2to1TrNormalSupportLength]

/-- Statement-support length of a TM2-to-TM1 `go` label. -/
def tm2to1GoStmtSupportLength {k : PartrecStack}
    (s : Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar k) : Nat :=
  match s with
  | Turing.TM2to1.StAct.push _ => 6
  | Turing.TM2to1.StAct.peek _ => 7
  | Turing.TM2to1.StAct.pop _ => 10

theorem tm2to1GoStmtSupportLength_eq {Λ : Type} {k : PartrecStack}
    (M : Λ → Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar)
    (s : Turing.TM2to1.StAct PartrecStack PartrecStackSymbol PartrecVar k)
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    tm1StmtSupportLength (Turing.TM2to1.tr M (Turing.TM2to1.Λ'.go k s stmt)) =
      tm2to1GoStmtSupportLength s := by
  cases s <;>
    simp [Turing.TM2to1.tr, Turing.TM2to1.trStAct,
      tm1StmtSupportLength, tm2to1GoStmtSupportLength]

/-- Statement-support length of a TM2-to-TM1 `ret` label. -/
def tm2to1RetStmtSupportLength {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) : Nat :=
  3 + tm2to1TrNormalSupportLength stmt

theorem tm2to1RetStmtSupportLength_eq {Λ : Type}
    (M : Λ → Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar)
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    tm1StmtSupportLength (Turing.TM2to1.tr M (Turing.TM2to1.Λ'.ret stmt)) =
      tm2to1RetStmtSupportLength stmt := by
  simp [Turing.TM2to1.tr, tm1StmtSupportLength, tm2to1RetStmtSupportLength,
    tm2to1TrNormalSupportLength_eq]
  omega

/--
Weighted statement-support contribution of the auxiliary `go`/`ret` labels
generated by `Turing.TM2to1.trStmts₁` for one TM2 statement.
-/
def tm2to1AuxStmtSupportWeight {Λ : Type}
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) : Nat :=
  match stmt with
  | Turing.TM2.Stmt.push k f q =>
      tm2to1GoStmtSupportLength (Turing.TM2to1.StAct.push (k := k) f) +
        (tm2to1RetStmtSupportLength q + tm2to1AuxStmtSupportWeight q)
  | Turing.TM2.Stmt.peek k f q =>
      tm2to1GoStmtSupportLength (Turing.TM2to1.StAct.peek (k := k) f) +
        (tm2to1RetStmtSupportLength q + tm2to1AuxStmtSupportWeight q)
  | Turing.TM2.Stmt.pop k f q =>
      tm2to1GoStmtSupportLength (Turing.TM2to1.StAct.pop (k := k) f) +
        (tm2to1RetStmtSupportLength q + tm2to1AuxStmtSupportWeight q)
  | Turing.TM2.Stmt.load _ q => tm2to1AuxStmtSupportWeight q
  | Turing.TM2.Stmt.branch _ q₁ q₂ =>
      tm2to1AuxStmtSupportWeight q₁ + tm2to1AuxStmtSupportWeight q₂
  | Turing.TM2.Stmt.goto _ => 0
  | Turing.TM2.Stmt.halt => 0

theorem tm2to1StmtSupportList_statementWeight {Λ : Type}
    (M : Λ → Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar)
    (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    ((tm2to1StmtSupportList stmt).map fun q =>
      tm1StmtSupportLength (Turing.TM2to1.tr M q)).sum =
        tm2to1AuxStmtSupportWeight stmt := by
  induction stmt with
  | push k f stmt IH =>
      simp [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight,
        tm2to1GoStmtSupportLength_eq, tm2to1RetStmtSupportLength_eq, IH]
  | peek k f stmt IH =>
      simp [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight,
        tm2to1GoStmtSupportLength_eq, tm2to1RetStmtSupportLength_eq, IH]
  | pop k f stmt IH =>
      simp [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight,
        tm2to1GoStmtSupportLength_eq, tm2to1RetStmtSupportLength_eq, IH]
  | load f stmt IH =>
      simpa [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight] using IH
  | branch f stmt₁ stmt₂ IH₁ IH₂ =>
      simp [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight, IH₁, IH₂]
  | goto f =>
      simp [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight]
  | halt =>
      simp [tm2to1StmtSupportList, tm2to1AuxStmtSupportWeight]

/-- Statement-support contribution of one original TM2 label after TM2-to-TM1 translation. -/
def tm2to1LabelStmtSupportWeight {Λ : Type}
    (M : Λ → Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) (q : Λ) : Nat :=
  tm2to1TrNormalSupportLength (M q) + tm2to1AuxStmtSupportWeight (M q)

theorem tm2to1LabelList_statementWeight
    (q : Turing.PartrecToTM2.Λ') :
    ((Turing.TM2to1.Λ'.normal q :: tm2to1StmtSupportList (partrecTM2 q)).map
      fun r => tm1StmtSupportLength (partrecTM1Machine r)).sum =
        tm2to1LabelStmtSupportWeight partrecTM2 q := by
  simp only [List.map_cons, List.sum_cons]
  rw [show tm1StmtSupportLength (partrecTM1Machine (Turing.TM2to1.Λ'.normal q)) =
      tm2to1TrNormalSupportLength (partrecTM2 q) by
    simp [partrecTM1Machine, Turing.TM2to1.tr, tm2to1TrNormalSupportLength_eq]]
  rw [show ((tm2to1StmtSupportList (partrecTM2 q)).map fun r =>
      tm1StmtSupportLength (partrecTM1Machine r)).sum =
        tm2to1AuxStmtSupportWeight (partrecTM2 q) by
    simpa [partrecTM1Machine] using
      tm2to1StmtSupportList_statementWeight partrecTM2 (partrecTM2 q)]
  rfl

private theorem list_sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β)
    (w : β → Nat) :
    ((xs.flatMap f).map w).sum = (xs.map fun x => ((f x).map w).sum).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

/-- Statement-support weight contributed by one original `PartrecToTM2` evaluator label. -/
def partrecTM1LabelStmtSupportWeight (q : Turing.PartrecToTM2.Λ') : Nat :=
  tm2to1LabelStmtSupportWeight partrecTM2 q

/-- Code-level statement-support weight for a `ret` evaluator label payload.

For an encoded `ret k` label, the payload is `encodeCont k + 1`. The halt
continuation has payload `1`; non-halt constructors are distinguished by the
two low constructor bits in `payload - 2`.
-/
def partrecTM1RetStmtSupportWeightCode (payload : Nat) : Nat :=
  if payload = 1 then 2
  else if (payload - 2).bodd then
    if ((payload - 2).div2).bodd then 15 else 1
  else 1

theorem partrecTM1RetStmtSupportWeightCode_primrec :
    Primrec partrecTM1RetStmtSupportWeightCode := by
  unfold partrecTM1RetStmtSupportWeightCode
  let hpred : Primrec fun payload : Nat => payload - 2 :=
    Primrec.nat_sub.comp Primrec.id (Primrec.const 2)
  let hbodd : Primrec fun payload : Nat => (payload - 2).bodd :=
    Primrec.nat_bodd.comp hpred
  let hdivBodd : Primrec fun payload : Nat => ((payload - 2).div2).bodd :=
    Primrec.nat_bodd.comp (Primrec.nat_div2.comp hpred)
  let hrest : Primrec fun payload : Nat =>
      if (payload - 2).bodd then
        if ((payload - 2).div2).bodd then 15 else 1
      else 1 :=
    (Primrec.cond hbodd
      (Primrec.cond hdivBodd (Primrec.const 15) (Primrec.const 1))
      (Primrec.const 1)).of_eq fun payload => by
        cases (payload - 2).bodd <;> cases ((payload - 2).div2).bodd <;> rfl
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 2)
    hrest

theorem partrecTM1RetStmtSupportWeightCode_encodeCont
    (k : Turing.PartrecToTM2.Cont') :
    partrecTM1RetStmtSupportWeightCode
        (Turing.PartrecToTM2.Cont'.encodeCont k + 1) =
      partrecTM1LabelStmtSupportWeight (Turing.PartrecToTM2.Λ'.ret k) := by
  cases k <;>
    simp [partrecTM1RetStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
      tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
      Turing.PartrecToTM2.pop', tm2to1TrNormalSupportLength,
      tm2to1AuxStmtSupportWeight, tm2to1RetStmtSupportLength,
      tm2to1GoStmtSupportLength,
      Turing.PartrecToTM2.Cont'.encodeCont, Nat.bit_val]

/-- Code-level statement-support weight for an evaluator label. -/
def partrecTM1LabelStmtSupportWeightCode (n : Nat) : Nat :=
  if n % 8 = 1 then 27
  else if n % 8 = 2 then 17
  else if n % 8 = 3 then 37
  else if n % 8 = 4 then 13
  else if n % 8 = 5 then 1
  else if n % 8 = 6 then 59
  else if n % 8 = 7 then 52
  else partrecTM1RetStmtSupportWeightCode (n / 8)

theorem partrecTM1LabelStmtSupportWeightCode_primrec :
    Primrec partrecTM1LabelStmtSupportWeightCode := by
  unfold partrecTM1LabelStmtSupportWeightCode
  let htag : Primrec fun n : Nat => n % 8 :=
    Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  let hret : Primrec fun n : Nat => partrecTM1RetStmtSupportWeightCode (n / 8) :=
    partrecTM1RetStmtSupportWeightCode_primrec.comp
      (Primrec.nat_div.comp Primrec.id (Primrec.const 8))
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) (Primrec.const 27)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) (Primrec.const 17)
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) (Primrec.const 37)
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) (Primrec.const 13)
          (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) (Primrec.const 1)
            (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) (Primrec.const 59)
              (Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) (Primrec.const 52)
                hret))))))

theorem partrecTM1LabelStmtSupportWeightCode_encodeLabel
    (q : Turing.PartrecToTM2.Λ') :
    partrecTM1LabelStmtSupportWeightCode (Turing.PartrecToTM2.Λ'.encodeLabel q) =
      partrecTM1LabelStmtSupportWeight q := by
  cases q with
  | move p k₁ k₂ q =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', Turing.PartrecToTM2.push',
        tm2to1TrNormalSupportLength, tm2to1AuxStmtSupportWeight,
        tm2to1RetStmtSupportLength, tm2to1GoStmtSupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_move]
  | push k f q =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        tm2to1TrNormalSupportLength, tm2to1AuxStmtSupportWeight,
        tm2to1RetStmtSupportLength, tm2to1GoStmtSupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_push]
  | read f =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        tm2to1TrNormalSupportLength, tm2to1AuxStmtSupportWeight,
        Turing.PartrecToTM2.Λ'.encodeLabel_read]
  | clear p k q =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', tm2to1TrNormalSupportLength,
        tm2to1AuxStmtSupportWeight, tm2to1RetStmtSupportLength,
        tm2to1GoStmtSupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_clear]
  | copy q =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', Turing.PartrecToTM2.push',
        tm2to1TrNormalSupportLength, tm2to1AuxStmtSupportWeight,
        tm2to1RetStmtSupportLength, tm2to1GoStmtSupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_copy]
  | succ q =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', tm2to1TrNormalSupportLength,
        tm2to1AuxStmtSupportWeight, tm2to1RetStmtSupportLength,
        tm2to1GoStmtSupportLength,
        Turing.PartrecToTM2.Λ'.encodeLabel_succ]
  | pred q₁ q₂ =>
      simp [partrecTM1LabelStmtSupportWeightCode, partrecTM1LabelStmtSupportWeight,
        tm2to1LabelStmtSupportWeight, partrecTM2, Turing.PartrecToTM2.tr,
        Turing.PartrecToTM2.pop', Turing.PartrecToTM2.peek',
        tm2to1TrNormalSupportLength, tm2to1AuxStmtSupportWeight,
        tm2to1GoStmtSupportLength,
        tm2to1RetStmtSupportLength, Turing.PartrecToTM2.Λ'.encodeLabel_pred]
  | ret k =>
      have hcode :
          Turing.PartrecToTM2.Λ'.encodeLabel
              (Turing.PartrecToTM2.Λ'.ret k) =
            8 * (Turing.PartrecToTM2.Cont'.encodeCont k + 1) + 0 := by
        rw [Turing.PartrecToTM2.Λ'.encodeLabel_ret]
        omega
      rw [hcode]
      simp [partrecTM1LabelStmtSupportWeightCode,
        partrecTM1RetStmtSupportWeightCode_encodeCont]

theorem partrecTM1LabelStmtSupportWeight_primrec :
    Primrec partrecTM1LabelStmtSupportWeight := by
  exact (partrecTM1LabelStmtSupportWeightCode_primrec.comp Primrec.encode).of_eq fun q => by
    rw [Turing.PartrecToTM2.Λ'.encodeLabel_eq]
    exact partrecTM1LabelStmtSupportWeightCode_encodeLabel q

theorem partrecTM1LabelStmtSupportWeight_labelWeight_primrec :
    Primrec (PartrecToTM2SupportList.labelWeight partrecTM1LabelStmtSupportWeight) :=
  PartrecToTM2SupportList.labelWeight_primrec_of_codeSuppWeight'
    (PartrecToTM2SupportList.codeSuppWeight'_primrec_of_code
      partrecTM1LabelStmtSupportWeightCode_primrec
      partrecTM1LabelStmtSupportWeightCode_encodeLabel)

theorem tm1StmtSupportList_length {Γ Λ σ : Type}
    (stmt : Turing.TM1.Stmt Γ Λ σ) :
    (tm1StmtSupportList stmt).length = tm1StmtSupportLength stmt := by
  induction stmt with
  | move d stmt IH =>
      simp [tm1StmtSupportList, tm1StmtSupportLength, IH]
      omega
  | write f stmt IH =>
      simp [tm1StmtSupportList, tm1StmtSupportLength, IH]
      omega
  | load f stmt IH =>
      simp [tm1StmtSupportList, tm1StmtSupportLength, IH]
      omega
  | branch f stmt₁ stmt₂ IH₁ IH₂ =>
      simp [tm1StmtSupportList, tm1StmtSupportLength, IH₁, IH₂]
      omega
  | goto f =>
      simp [tm1StmtSupportList, tm1StmtSupportLength]
  | halt =>
      simp [tm1StmtSupportList, tm1StmtSupportLength]

theorem tm1StmtSupportLength_relabel {Γ Λ Λ' σ : Type}
    (f : Λ → Λ') (stmt : Turing.TM1.Stmt Γ Λ σ) :
    tm1StmtSupportLength (relabelTM1Stmt f stmt) =
      tm1StmtSupportLength stmt := by
  induction stmt with
  | move d stmt IH =>
      simp [relabelTM1Stmt, tm1StmtSupportLength, IH]
  | write g stmt IH =>
      simp [relabelTM1Stmt, tm1StmtSupportLength, IH]
  | load g stmt IH =>
      simp [relabelTM1Stmt, tm1StmtSupportLength, IH]
  | branch p stmt₁ stmt₂ IH₁ IH₂ =>
      simp [relabelTM1Stmt, tm1StmtSupportLength, IH₁, IH₂]
  | goto g =>
      simp [relabelTM1Stmt, tm1StmtSupportLength]
  | halt =>
      simp [relabelTM1Stmt, tm1StmtSupportLength]

theorem tm2to1TrNormalStmtSupportLength_relabel {Λ Λ' : Type}
    (f : Λ → Λ') (stmt : Turing.TM2.Stmt PartrecStackSymbol Λ PartrecVar) :
    tm1StmtSupportLength (Turing.TM2to1.trNormal (relabelTM2Stmt f stmt)) =
      tm1StmtSupportLength (Turing.TM2to1.trNormal
        (K := PartrecStack) (Γ := PartrecStackSymbol) stmt) := by
  induction stmt with
  | push k g stmt IH =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength]
  | peek k g stmt IH =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength]
  | pop k g stmt IH =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength]
  | load g stmt IH =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength, IH]
  | branch g stmt₁ stmt₂ IH₁ IH₂ =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength, IH₁, IH₂]
  | goto g =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength]
  | halt =>
      simp [relabelTM2Stmt, Turing.TM2to1.trNormal, tm1StmtSupportLength]

theorem partrecStartedTM1Machine_supportLength_relabel
    (tc : Turing.ToPartrec.Code)
    (q : Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol Turing.PartrecToTM2.Λ' PartrecVar) :
    tm1StmtSupportLength
        (partrecStartedTM1Machine tc
          (relabelTM2to1Label (StartedLabel.wrap tc) q)) =
      tm1StmtSupportLength (partrecTM1Machine q) := by
  cases q with
  | normal q =>
      simp [partrecStartedTM1Machine, partrecTM1Machine, Turing.TM2to1.tr,
        partrecStartedTM2, relabelTM2to1Label,
        tm2to1TrNormalStmtSupportLength_relabel]
  | go k s q =>
      cases s <;>
        simp [partrecStartedTM1Machine, partrecTM1Machine, Turing.TM2to1.tr,
          relabelTM2to1Label, Turing.TM2to1.trStAct,
          tm1StmtSupportLength]
  | ret q =>
      simp [partrecStartedTM1Machine, partrecTM1Machine, Turing.TM2to1.tr,
        relabelTM2to1Label, tm1StmtSupportLength,
        tm2to1TrNormalStmtSupportLength_relabel]

theorem mem_tm1StmtSupportList_iff {Γ Λ σ : Type}
    {stmt q : Turing.TM1.Stmt Γ Λ σ} :
    q ∈ tm1StmtSupportList stmt ↔ q ∈ Turing.TM1.stmts₁ stmt := by
  induction stmt with
  | move d stmt IH =>
      simp [tm1StmtSupportList, Turing.TM1.stmts₁, IH]
  | write f stmt IH =>
      simp [tm1StmtSupportList, Turing.TM1.stmts₁, IH]
  | load f stmt IH =>
      simp [tm1StmtSupportList, Turing.TM1.stmts₁, IH]
  | branch f stmt₁ stmt₂ IH₁ IH₂ =>
      simp [tm1StmtSupportList, Turing.TM1.stmts₁, IH₁, IH₂]
  | goto f =>
      simp [tm1StmtSupportList, Turing.TM1.stmts₁]
  | halt =>
      simp [tm1StmtSupportList, Turing.TM1.stmts₁]

/-- List-valued statement support for a TM1 machine over a finite label list. -/
def tm1StatementSupportList {Γ Λ σ : Type}
    (labels : List Λ) (M : Λ → Turing.TM1.Stmt Γ Λ σ) :
    List (Option (Turing.TM1.Stmt Γ Λ σ)) :=
  none :: labels.flatMap fun q => (tm1StmtSupportList (M q)).map some

/-- Numeric length mirror of `tm1StatementSupportList`. -/
def tm1StatementSupportLength {Γ Λ σ : Type}
    (labels : List Λ) (M : Λ → Turing.TM1.Stmt Γ Λ σ) : Nat :=
  1 + (labels.map fun q => tm1StmtSupportLength (M q)).sum

theorem partrecStartedTM0StatementSupportLength_eq_raw
    (tc : Turing.ToPartrec.Code) :
    tm1StatementSupportLength (partrecStartedTM1LabelList tc)
        (partrecStartedTM1Machine tc) =
      tm1StatementSupportLength (partrecTM1LabelList tc) partrecTM1Machine := by
  unfold tm1StatementSupportLength
  rw [partrecStartedTM1LabelList_eq_map]
  simp only [List.map_map]
  apply congrArg (fun n => 1 + n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _hq
  exact partrecStartedTM1Machine_supportLength_relabel tc q

theorem tm1StatementSupportList_length {Γ Λ σ : Type}
    (labels : List Λ) (M : Λ → Turing.TM1.Stmt Γ Λ σ) :
    (tm1StatementSupportList labels M).length =
      tm1StatementSupportLength labels M := by
  simp [tm1StatementSupportList, tm1StatementSupportLength,
    List.length_flatMap, tm1StmtSupportList_length]
  omega

theorem mem_tm1StatementSupportList_iff {Γ Λ σ : Type}
    {labels : List Λ} {M : Λ → Turing.TM1.Stmt Γ Λ σ} {S : Finset Λ}
    (hlabels : ∀ q : Λ, q ∈ labels ↔ q ∈ S)
    (stmt : Option (Turing.TM1.Stmt Γ Λ σ)) :
    stmt ∈ tm1StatementSupportList labels M ↔ stmt ∈ Turing.TM1.stmts M S := by
  classical
  cases stmt with
  | none =>
      simp [tm1StatementSupportList, Turing.TM1.stmts]
  | some stmt =>
      constructor
      · intro h
        unfold tm1StatementSupportList at h
        simp only [List.mem_cons, Option.some.injEq, List.mem_flatMap, List.mem_map] at h
        rcases h with hnone | ⟨q, hq, stmt', hstmt', hsome⟩
        · cases hnone
        · cases hsome
          rw [Turing.TM1.stmts, Finset.some_mem_insertNone]
          exact Finset.mem_biUnion.2
            ⟨q, (hlabels q).1 hq, (mem_tm1StmtSupportList_iff).1 hstmt'⟩
      · intro h
        rw [Turing.TM1.stmts, Finset.some_mem_insertNone] at h
        rcases Finset.mem_biUnion.1 h with ⟨q, hq, hstmt⟩
        unfold tm1StatementSupportList
        simp only [List.mem_cons, Option.some.injEq, List.mem_flatMap, List.mem_map]
        exact Or.inr
          ⟨q, (hlabels q).2 hq, stmt, (mem_tm1StmtSupportList_iff).2 hstmt, rfl⟩

private def flatMapAt? {α β : Type} (xs : List α) (f : α → List β) :
    Nat → Option β
  | i =>
      match xs with
      | [] => none
      | x :: xs =>
          match (f x)[i]? with
          | some y => some y
          | none => flatMapAt? xs f (i - (f x).length)
termination_by xs.length

private theorem flatMapAt?_eq_getElem? {α β : Type}
    (xs : List α) (f : α → List β) (i : Nat) :
    flatMapAt? xs f i = (xs.flatMap f)[i]? := by
  induction xs generalizing i with
  | nil =>
      simp [flatMapAt?]
  | cons x xs ih =>
      unfold flatMapAt?
      simp only [List.flatMap_cons]
      by_cases h : i < (f x).length
      · rw [List.getElem?_append_left h]
        cases hy : (f x)[i]? with
        | none =>
            rw [List.getElem?_eq_none_iff] at hy
            omega
        | some y =>
            simp
      · have hle : (f x).length ≤ i := le_of_not_gt h
        rw [List.getElem?_append_right hle]
        have hynone : (f x)[i]? = none := by
          rw [List.getElem?_eq_none_iff]
          exact hle
        rw [hynone]
        rw [ih]

def tm1StatementSupportAt? {Γ Λ σ : Type}
    (labels : List Λ) (M : Λ → Turing.TM1.Stmt Γ Λ σ) :
    Nat → Option (Option (Turing.TM1.Stmt Γ Λ σ))
  | 0 => some none
  | i + 1 =>
      flatMapAt? labels (fun q => (tm1StmtSupportList (M q)).map some) i

theorem tm1StatementSupportAt?_eq_getElem? {Γ Λ σ : Type}
    (labels : List Λ) (M : Λ → Turing.TM1.Stmt Γ Λ σ) (i : Nat) :
    tm1StatementSupportAt? labels M i =
      (tm1StatementSupportList labels M)[i]? := by
  cases i with
  | zero =>
      simp [tm1StatementSupportAt?, tm1StatementSupportList]
  | succ i =>
      simp [tm1StatementSupportAt?, tm1StatementSupportList,
        flatMapAt?_eq_getElem?]

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

/-- Tape symbols of the started Mathlib TM0 machine. -/
abbrev PartrecStartedTM0Symbol : Type :=
  Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol

/-- TM1 statements stored inside started Mathlib TM0 labels. -/
abbrev PartrecStartedTM0Stmt (tc : Turing.ToPartrec.Code) : Type :=
  Turing.TM1.Stmt PartrecStartedTM0Symbol (PartrecStartedTM1Label tc) PartrecVar

/-!
The started TM0 route indexes Mathlib `TM1.Stmt` values in translated TM0
labels. These statements have finite function payloads over the concrete source
symbol and local-store alphabets, so we encode recursive statement syntax by
preorder node lists, mirroring `PartrecStartedTM2StmtNode`.
-/

inductive PartrecStartedTM1StmtNode (tc : Turing.ToPartrec.Code) where
  | move : Turing.Dir → PartrecStartedTM1StmtNode tc
  | write : (PartrecStartedTM0Symbol → PartrecVar → PartrecStartedTM0Symbol) →
      PartrecStartedTM1StmtNode tc
  | load : (PartrecStartedTM0Symbol → PartrecVar → PartrecVar) →
      PartrecStartedTM1StmtNode tc
  | branch : (PartrecStartedTM0Symbol → PartrecVar → Bool) →
      PartrecStartedTM1StmtNode tc
  | goto : (PartrecStartedTM0Symbol → PartrecVar → PartrecStartedTM1Label tc) →
      PartrecStartedTM1StmtNode tc
  | halt : PartrecStartedTM1StmtNode tc

namespace PartrecStartedTM1StmtNode

abbrev WriteCode : Type :=
  PartrecStartedTM0Symbol → PartrecVar → PartrecStartedTM0Symbol

abbrev LoadCode : Type :=
  PartrecStartedTM0Symbol → PartrecVar → PartrecVar

abbrev BranchCode : Type :=
  PartrecStartedTM0Symbol → PartrecVar → Bool

abbrev GotoCode (tc : Turing.ToPartrec.Code) : Type :=
  PartrecStartedTM0Symbol → PartrecVar → PartrecStartedTM1Label tc

abbrev GotoHaltCode (tc : Turing.ToPartrec.Code) : Type :=
  GotoCode tc ⊕ PUnit

abbrev BranchTailCode (tc : Turing.ToPartrec.Code) : Type :=
  BranchCode ⊕ GotoHaltCode tc

abbrev LoadTailCode (tc : Turing.ToPartrec.Code) : Type :=
  LoadCode ⊕ BranchTailCode tc

abbrev WriteTailCode (tc : Turing.ToPartrec.Code) : Type :=
  WriteCode ⊕ LoadTailCode tc

def dirToBool : Turing.Dir → Bool
  | Turing.Dir.left => false
  | Turing.Dir.right => true

def dirOfBool : Bool → Turing.Dir
  | false => Turing.Dir.left
  | true => Turing.Dir.right

abbrev Code (tc : Turing.ToPartrec.Code) : Type :=
  (Bool × PUnit) ⊕ WriteTailCode tc

def toCode {tc : Turing.ToPartrec.Code} :
    PartrecStartedTM1StmtNode tc → Code tc
  | move d => Sum.inl (dirToBool d, PUnit.unit)
  | write f => Sum.inr (Sum.inl f)
  | load f => Sum.inr (Sum.inr (Sum.inl f))
  | branch f => Sum.inr (Sum.inr (Sum.inr (Sum.inl f)))
  | goto f => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl f))))
  | halt => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))

def ofCode {tc : Turing.ToPartrec.Code} :
    Code tc → PartrecStartedTM1StmtNode tc
  | Sum.inl p => move (dirOfBool p.1)
  | Sum.inr (Sum.inl f) => write f
  | Sum.inr (Sum.inr (Sum.inl f)) => load f
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl f))) => branch f
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl f)))) => goto f
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => halt

def equivCode (tc : Turing.ToPartrec.Code) :
    PartrecStartedTM1StmtNode tc ≃ Code tc where
  toFun := toCode
  invFun := ofCode
  left_inv := by
    intro n
    cases n with
    | move d =>
        cases d <;> rfl
    | write f => rfl
    | load f => rfl
    | branch f => rfl
    | goto f => rfl
    | halt => rfl
  right_inv := by
    intro c
    rcases c with p | c
    · rcases p with ⟨d, u⟩
      cases u
      cases d <;> rfl
    rcases c with f | c
    · rfl
    rcases c with f | c
    · rfl
    rcases c with f | c
    · rfl
    rcases c with f | u
    · rfl
    cases u
    rfl

/-- Number of recursive child statements required after this preorder node. -/
def arity {tc : Turing.ToPartrec.Code} :
    PartrecStartedTM1StmtNode tc → Nat
  | move .. => 1
  | write .. => 1
  | load .. => 1
  | branch .. => 2
  | goto .. => 0
  | halt => 0

def codeArity {tc : Turing.ToPartrec.Code} :
    Code tc → Nat
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => 0

def gotoHaltCodeArity {tc : Turing.ToPartrec.Code} :
    GotoHaltCode tc → Nat
  | Sum.inl _ => 0
  | Sum.inr _ => 0

def branchTailCodeArity {tc : Turing.ToPartrec.Code} :
    BranchTailCode tc → Nat
  | Sum.inl _ => 2
  | Sum.inr c => gotoHaltCodeArity c

def loadTailCodeArity {tc : Turing.ToPartrec.Code} :
    LoadTailCode tc → Nat
  | Sum.inl _ => 1
  | Sum.inr c => branchTailCodeArity c

def writeTailCodeArity {tc : Turing.ToPartrec.Code} :
    WriteTailCode tc → Nat
  | Sum.inl _ => 1
  | Sum.inr c => loadTailCodeArity c

end PartrecStartedTM1StmtNode

/-- Labels of the started Mathlib TM0 machine obtained through Mathlib's TM1-to-TM0 translation. -/
abbrev PartrecStartedTM0Label (tc : Turing.ToPartrec.Code) : Type :=
  Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)

/-- One transition result of the started Mathlib TM0 machine. -/
abbrev PartrecStartedTM0Step (tc : Turing.ToPartrec.Code) : Type :=
  PartrecStartedTM0Label tc × Turing.TM0.Stmt PartrecStartedTM0Symbol

theorem partrecStartedTM0Machine_none (tc : Turing.ToPartrec.Code)
    (v : PartrecVar) (a : Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :
    partrecStartedTM0Machine tc (none, v) a = none := by
  rfl

theorem partrecStartedTM0Machine_some (tc : Turing.ToPartrec.Code)
    (stmt : PartrecStartedTM0Stmt tc)
    (v : PartrecVar) (a : PartrecStartedTM0Symbol) :
    partrecStartedTM0Machine tc (some stmt, v) a =
      some (Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a stmt v) := by
  rfl

theorem partrecStartedTM0_trAux_move (tc : Turing.ToPartrec.Code)
    (a : PartrecStartedTM0Symbol)
    (d : Turing.Dir)
    (q : PartrecStartedTM0Stmt tc)
    (v : PartrecVar) :
    Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a
      (Turing.TM1.Stmt.move d q) v =
        ((some q, v), Turing.TM0.Stmt.move d) := by
  rfl

theorem partrecStartedTM0_trAux_write (tc : Turing.ToPartrec.Code)
    (a : PartrecStartedTM0Symbol)
    (f : PartrecStartedTM0Symbol → PartrecVar → PartrecStartedTM0Symbol)
    (q : PartrecStartedTM0Stmt tc)
    (v : PartrecVar) :
    Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a
      (Turing.TM1.Stmt.write f q) v =
        ((some q, v), Turing.TM0.Stmt.write (f a v)) := by
  rfl

theorem partrecStartedTM0_trAux_load (tc : Turing.ToPartrec.Code)
    (a : PartrecStartedTM0Symbol)
    (f : PartrecStartedTM0Symbol → PartrecVar → PartrecVar)
    (q : PartrecStartedTM0Stmt tc)
    (v : PartrecVar) :
    Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a
      (Turing.TM1.Stmt.load f q) v =
        Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a q (f a v) := by
  rfl

theorem partrecStartedTM0_trAux_branch (tc : Turing.ToPartrec.Code)
    (a : PartrecStartedTM0Symbol)
    (p : PartrecStartedTM0Symbol → PartrecVar → Bool)
    (q₁ q₂ : PartrecStartedTM0Stmt tc)
    (v : PartrecVar) :
    Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a
      (Turing.TM1.Stmt.branch p q₁ q₂) v =
        if p a v then
          Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a q₁ v
        else
          Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a q₂ v := by
  cases h : p a v <;> simp [Turing.TM1to0.trAux, h]

theorem partrecStartedTM0_trAux_goto (tc : Turing.ToPartrec.Code)
    (a : PartrecStartedTM0Symbol)
    (f : PartrecStartedTM0Symbol → PartrecVar → PartrecStartedTM1Label tc)
    (v : PartrecVar) :
    Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a
      (Turing.TM1.Stmt.goto f) v =
        ((some (partrecStartedTM1Machine tc (f a v)), v), Turing.TM0.Stmt.write a) := by
  rfl

theorem partrecStartedTM0_trAux_halt (tc : Turing.ToPartrec.Code)
    (a : PartrecStartedTM0Symbol)
    (v : PartrecVar) :
    Turing.TM1to0.trAux (partrecStartedTM1Machine tc) a
      (Turing.TM1.Stmt.halt) v =
        ((none, v), Turing.TM0.Stmt.write a) := by
  rfl

noncomputable def partrecStartedTM0Labels (tc : Turing.ToPartrec.Code) :=
  Turing.TM1to0.trStmts (partrecStartedTM1Machine tc)
    (partrecStartedTM1Labels tc)

def partrecStartedTM0StatementList (tc : Turing.ToPartrec.Code) :
    List (Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)) :=
  tm1StatementSupportList (partrecStartedTM1LabelList tc) (partrecStartedTM1Machine tc)

def partrecStartedTM0StatementAt? (tc : Turing.ToPartrec.Code) (i : Nat) :
    Option (Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)) :=
  tm1StatementSupportAt? (partrecStartedTM1LabelList tc)
    (partrecStartedTM1Machine tc) i

theorem partrecStartedTM0StatementAt?_eq_getElem?
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    partrecStartedTM0StatementAt? tc i =
      (partrecStartedTM0StatementList tc)[i]? := by
  unfold partrecStartedTM0StatementAt? partrecStartedTM0StatementList
  exact tm1StatementSupportAt?_eq_getElem?
    (partrecStartedTM1LabelList tc) (partrecStartedTM1Machine tc) i

theorem partrecStartedTM0StatementAt?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (partrecStartedTM0StatementAt? tc) :=
  (Primrec.list_getElem?₁ (partrecStartedTM0StatementList tc)).of_eq fun i =>
    (partrecStartedTM0StatementAt?_eq_getElem? tc i).symm

/-- Numeric count of TM1 statements supporting the translated started TM0 machine. -/
def partrecStartedTM0StatementCount (tc : Turing.ToPartrec.Code) : Nat :=
  tm1StatementSupportLength (partrecTM1LabelList tc) partrecTM1Machine

/--
Statement-count data for the code-independent TM1 machine obtained from the
`PartrecToTM2` evaluator.

This exposes the concrete weighted-list form hidden in
`tm1StatementSupportLength`; later computability proofs can target the label
list and the label-local statement-support weight separately.
-/
def partrecTM1StatementCountData (tc : Turing.ToPartrec.Code) : Nat :=
  1 + ((partrecTM1LabelList tc).map fun q =>
    tm1StmtSupportLength (partrecTM1Machine q)).sum

theorem partrecStartedTM0StatementCount_eq_data (tc : Turing.ToPartrec.Code) :
    partrecStartedTM0StatementCount tc = partrecTM1StatementCountData tc := by
  rfl

theorem partrecStartedTM0StatementCount_primrec_of_tm1LabelList
    (hlabels : Primrec partrecTM1LabelList)
    (hweight : Primrec (fun q : PartrecTM1Label =>
      tm1StmtSupportLength (partrecTM1Machine q))) :
    Primrec partrecStartedTM0StatementCount := by
  have hmap :
      Primrec fun tc : Turing.ToPartrec.Code =>
        (partrecTM1LabelList tc).map fun q =>
          tm1StmtSupportLength (partrecTM1Machine q) := by
    refine Primrec.list_map hlabels ?_
    exact (hweight.comp Primrec.snd).to₂
  have hsum :
      Primrec fun tc : Turing.ToPartrec.Code =>
        ((partrecTM1LabelList tc).map fun q =>
          tm1StmtSupportLength (partrecTM1Machine q)).sum :=
    list_sum_nat_primrec hmap
  exact (Primrec.succ.comp hsum).of_eq fun tc => by
    rw [partrecStartedTM0StatementCount_eq_data]
    simp [partrecTM1StatementCountData, Nat.add_comm]

/--
Statement count for the translated started TM0 machine, phrased as a weighted
sum over the original evaluator-label support.
-/
def partrecStartedTM0StatementCountWeightData (tc : Turing.ToPartrec.Code) : Nat :=
  1 + PartrecToTM2SupportList.labelWeight partrecTM1LabelStmtSupportWeight tc

theorem partrecStartedTM0StatementCount_eq_weightData (tc : Turing.ToPartrec.Code) :
    partrecStartedTM0StatementCount tc =
      partrecStartedTM0StatementCountWeightData tc := by
  rw [partrecStartedTM0StatementCount_eq_data]
  unfold partrecTM1StatementCountData partrecTM1LabelList
    partrecStartedTM0StatementCountWeightData
  apply congrArg (fun n => 1 + n)
  rw [list_sum_map_flatMap]
  rw [← PartrecToTM2SupportList.labelList_weight partrecTM1LabelStmtSupportWeight tc]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _hq
  simpa [partrecTM1LabelStmtSupportWeight] using tm2to1LabelList_statementWeight q

theorem partrecStartedTM0StatementCountWeightData_primrec
    (hweight :
      Primrec (PartrecToTM2SupportList.labelWeight partrecTM1LabelStmtSupportWeight)) :
    Primrec partrecStartedTM0StatementCountWeightData := by
  unfold partrecStartedTM0StatementCountWeightData
  exact Primrec.nat_add.comp (Primrec.const 1) hweight

theorem partrecStartedTM0StatementCount_primrec_of_labelWeight
    (hweight :
      Primrec (PartrecToTM2SupportList.labelWeight partrecTM1LabelStmtSupportWeight)) :
    Primrec partrecStartedTM0StatementCount :=
  (partrecStartedTM0StatementCountWeightData_primrec hweight).of_eq fun tc => by
    rw [partrecStartedTM0StatementCount_eq_weightData]

theorem partrecStartedTM0StatementCount_computable_of_labelWeight
    (hweight :
      Computable (PartrecToTM2SupportList.labelWeight partrecTM1LabelStmtSupportWeight)) :
    Computable partrecStartedTM0StatementCount := by
  have hdata : Computable partrecStartedTM0StatementCountWeightData := by
    unfold partrecStartedTM0StatementCountWeightData
    exact Primrec.nat_add.to_comp.comp (Computable.const 1) hweight
  exact hdata.of_eq fun tc => by
    rw [partrecStartedTM0StatementCount_eq_weightData]

theorem partrecStartedTM0StatementCount_primrec :
    Primrec partrecStartedTM0StatementCount :=
  partrecStartedTM0StatementCount_primrec_of_labelWeight
    partrecTM1LabelStmtSupportWeight_labelWeight_primrec

theorem partrecStartedTM0StatementCount_computable :
    Computable partrecStartedTM0StatementCount :=
  partrecStartedTM0StatementCount_primrec.to_comp

theorem partrecStartedTM0StatementCount_primrec_of_supportWeight
    (hweight :
      Primrec₂ (PartrecToTM2SupportList.codeSuppWeight partrecTM1LabelStmtSupportWeight)) :
    Primrec partrecStartedTM0StatementCount :=
  partrecStartedTM0StatementCount_primrec_of_labelWeight
    (PartrecToTM2SupportList.labelWeight_primrec_of_codeSuppWeight hweight)

theorem partrecStartedTM0StatementCount_computable_of_supportWeight
    (hweight :
      Computable₂ (PartrecToTM2SupportList.codeSuppWeight partrecTM1LabelStmtSupportWeight)) :
    Computable partrecStartedTM0StatementCount :=
  partrecStartedTM0StatementCount_computable_of_labelWeight
    (by
      unfold PartrecToTM2SupportList.labelWeight
      exact hweight.comp Computable.id (Computable.const Turing.PartrecToTM2.Cont'.halt))

theorem partrecStartedTM0StatementList_length (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM0StatementList tc).length =
      partrecStartedTM0StatementCount tc := by
  simp [partrecStartedTM0StatementList, partrecStartedTM0StatementCount,
    tm1StatementSupportList_length, partrecStartedTM0StatementSupportLength_eq_raw]

theorem mem_partrecStartedTM0StatementList (tc : Turing.ToPartrec.Code)
    (stmt : Option (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)) :
    stmt ∈ partrecStartedTM0StatementList tc ↔
      stmt ∈ Turing.TM1.stmts (partrecStartedTM1Machine tc)
        (partrecStartedTM1Labels tc) := by
  unfold partrecStartedTM0StatementList
  exact mem_tm1StatementSupportList_iff (mem_partrecStartedTM1LabelList tc) stmt

def partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code) :
    List (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  (partrecStartedTM0StatementList tc).flatMap fun stmt =>
    partrecVarList.map fun v => (stmt, v)

private def flatMapConstMapAt? {α β : Type} (xs : List α) (ys : List β) :
    Nat → Option (α × β)
  | i =>
      match xs with
      | [] => none
      | x :: xs =>
          match ys[i]? with
          | some y => some (x, y)
          | none => flatMapConstMapAt? xs ys (i - ys.length)
termination_by xs.length

private theorem flatMapConstMapAt?_eq_getElem? {α β : Type}
    (xs : List α) (ys : List β) (i : Nat) :
    flatMapConstMapAt? xs ys i =
      (xs.flatMap fun x => ys.map fun y => (x, y))[i]? := by
  induction xs generalizing i with
  | nil =>
      simp [flatMapConstMapAt?]
  | cons x xs ih =>
      unfold flatMapConstMapAt?
      simp only [List.flatMap_cons]
      by_cases h : i < ys.length
      · have hmaplen : i < (ys.map fun y => (x, y)).length := by
          simpa using h
        rw [List.getElem?_append_left hmaplen]
        rw [List.getElem?_map]
        cases hy : ys[i]? with
        | none =>
            rw [List.getElem?_eq_none_iff] at hy
            omega
        | some y =>
            simp
      · have hmaple : (ys.map fun y => (x, y)).length ≤ i := by
          simpa using le_of_not_gt h
        rw [List.getElem?_append_right hmaple]
        have hynone : ys[i]? = none := by
          rw [List.getElem?_eq_none_iff]
          exact le_of_not_gt h
        rw [hynone]
        rw [ih]
        simp [List.length_map]

private def flatMapConstMapAtByGet? {α β : Type}
    (get : Nat → Option α) (ys : List β) : Nat → Nat → Option (α × β)
  | 0, _i => none
  | fuel + 1, i =>
      match ys[i]? with
      | some y => (get 0).map fun x => (x, y)
      | none => flatMapConstMapAtByGet? (fun j => get (j + 1)) ys fuel (i - ys.length)

private theorem flatMapConstMapAtByGet?_eq_list {α β : Type}
    (xs : List α) (ys : List β) (i : Nat) :
    flatMapConstMapAtByGet? (fun j => xs[j]?) ys xs.length i =
      flatMapConstMapAt? xs ys i := by
  induction xs generalizing i with
  | nil =>
      simp [flatMapConstMapAtByGet?, flatMapConstMapAt?]
  | cons x xs ih =>
      cases hy : ys[i]? with
      | some y =>
          simp [flatMapConstMapAtByGet?, flatMapConstMapAt?, hy]
      | none =>
          simpa [flatMapConstMapAtByGet?, flatMapConstMapAt?, hy] using
            ih (i - ys.length)

private def flatMapConstMapAtByGetFrom? {α β : Type}
    (get : Nat → Option α) (ys : List β) :
    Nat → Nat → Nat → Option (α × β)
  | 0, _k, _i => none
  | fuel + 1, k, i =>
      match ys[i]? with
      | some y => (get k).map fun x => (x, y)
      | none => flatMapConstMapAtByGetFrom? get ys fuel (k + 1) (i - ys.length)

private def flatMapConstMapAtByGetFromStep? {α β : Type}
    (get : Nat → Option α) (ys : List β)
    (s : Option (α × β) × Nat × Nat) :
    Option (α × β) × Nat × Nat :=
  match s.1 with
  | some r => (some r, s.2)
  | none =>
      match ys[s.2.2]? with
      | some y => ((get s.2.1).map fun x => (x, y), s.2.1, s.2.2)
      | none => (none, s.2.1 + 1, s.2.2 - ys.length)

private def flatMapConstMapAtByGetFromIter? {α β : Type}
    (get : Nat → Option α) (ys : List β) (fuel k i : Nat) :
    Option (α × β) :=
  ((flatMapConstMapAtByGetFromStep? get ys)^[fuel] (none, k, i)).1

private theorem flatMapConstMapAtByGetFromStep?_fixed_of_current_some {α β : Type}
    (get : Nat → Option α) (ys : List β) {k i : Nat} {y : β}
    (hy : ys[i]? = some y) :
    flatMapConstMapAtByGetFromStep? get ys
        ((get k).map fun x => (x, y), k, i) =
      ((get k).map fun x => (x, y), k, i) := by
  cases hget : get k <;> simp [flatMapConstMapAtByGetFromStep?, hy, hget]

private theorem flatMapConstMapAtByGetFromIter?_eq {α β : Type}
    (get : Nat → Option α) (ys : List β) (fuel k i : Nat) :
    flatMapConstMapAtByGetFromIter? get ys fuel k i =
      flatMapConstMapAtByGetFrom? get ys fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold flatMapConstMapAtByGetFromIter? flatMapConstMapAtByGetFrom?
      rw [Function.iterate_succ_apply]
      cases hy : ys[i]? with
      | some y =>
          have hstep :
              flatMapConstMapAtByGetFromStep? get ys (none, k, i) =
                ((get k).map fun x => (x, y), k, i) := by
            change
              (match ys[i]? with
              | some y' => ((get k).map fun x => (x, y'), k, i)
              | none => (none, k + 1, i - ys.length)) =
                ((get k).map fun x => (x, y), k, i)
            rw [hy]
          rw [hstep]
          exact congrArg Prod.fst
            (Function.iterate_fixed
              (flatMapConstMapAtByGetFromStep?_fixed_of_current_some get ys hy) fuel)
      | none =>
          simpa [flatMapConstMapAtByGetFromStep?, hy, flatMapConstMapAtByGetFromIter?]
            using ih (k + 1) (i - ys.length)

private theorem flatMapConstMapAtByGetFromStep?_primrec {α β : Type}
    [Primcodable α] [Primcodable β]
    (get : Nat → Option α) (ys : List β) (hget : Primrec get) :
    Primrec (flatMapConstMapAtByGetFromStep? get ys) := by
  let found : Option (α × β) × Nat × Nat → Option (α × β) := fun s => s.1
  let offset : Option (α × β) × Nat × Nat → Nat := fun s => s.2.1
  let index : Option (α × β) × Nat × Nat → Nat := fun s => s.2.2
  have hfound : Primrec found := Primrec.fst
  have hoffset : Primrec offset := Primrec.fst.comp Primrec.snd
  have hindex : Primrec index := Primrec.snd.comp Primrec.snd
  have hnoneStep : Primrec (fun s : Option (α × β) × Nat × Nat =>
      ((none : Option (α × β)), (offset s + 1, index s - ys.length))) := by
    exact Primrec.pair (Primrec.const (none : Option (α × β)))
      (Primrec.pair (Primrec.succ.comp hoffset)
        (Primrec.nat_sub.comp hindex (Primrec.const ys.length)))
  have hsomeBlock :
      Primrec₂ (fun s : Option (α × β) × Nat × Nat => fun y : β =>
        ((get (offset s)).map fun x => (x, y), offset s, index s)) := by
    apply Primrec₂.mk
    let base : (Option (α × β) × Nat × Nat) × β → Option (α × β) × Nat × Nat :=
      fun p => p.1
    let yArg : (Option (α × β) × Nat × Nat) × β → β := fun p => p.2
    have hbase : Primrec base := Primrec.fst
    have hyArg : Primrec yArg := Primrec.snd
    have hoffsetBase : Primrec (fun p : (Option (α × β) × Nat × Nat) × β =>
        offset (base p)) := hoffset.comp hbase
    have hindexBase : Primrec (fun p : (Option (α × β) × Nat × Nat) × β =>
        index (base p)) := hindex.comp hbase
    have hgetBase : Primrec (fun p : (Option (α × β) × Nat × Nat) × β =>
        get (offset (base p))) := hget.comp hoffsetBase
    have hpairWithY :
        Primrec₂ (fun p : (Option (α × β) × Nat × Nat) × β => fun x : α =>
          (x, yArg p)) := by
      apply Primrec₂.mk
      exact Primrec.pair Primrec.snd (hyArg.comp Primrec.fst)
    have hmap : Primrec (fun p : (Option (α × β) × Nat × Nat) × β =>
        (get (offset (base p))).map fun x => (x, yArg p)) :=
      Primrec.option_map hgetBase hpairWithY
    exact Primrec.pair hmap (Primrec.pair hoffsetBase hindexBase)
  have hnone : Primrec (fun s : Option (α × β) × Nat × Nat =>
      match ys[index s]? with
      | some y => ((get (offset s)).map fun x => (x, y), offset s, index s)
      | none => ((none : Option (α × β)), (offset s + 1, index s - ys.length))) := by
    have hlookup : Primrec (fun s : Option (α × β) × Nat × Nat => ys[index s]?) :=
      (Primrec.list_getElem?₁ ys).comp hindex
    exact (Primrec.option_casesOn hlookup hnoneStep hsomeBlock).of_eq fun s => by
      cases ys[index s]? <;> rfl
  have hsomeFound :
      Primrec₂ (fun s : Option (α × β) × Nat × Nat => fun r : α × β =>
        (some r, s.2)) := by
    apply Primrec₂.mk
    exact Primrec.pair (Primrec.option_some.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.option_casesOn hfound hnone hsomeFound).of_eq fun s => by
    rcases s with ⟨r, k, i⟩
    cases r <;> rfl

private theorem flatMapConstMapAtByGetFromIter?_primrec {α β : Type}
    [Primcodable α] [Primcodable β]
    (get : Nat → Option α) (ys : List β) (hget : Primrec get) :
    Primrec (fun p : Nat × Nat × Nat =>
      flatMapConstMapAtByGetFromIter? get ys p.1 p.2.1 p.2.2) := by
  let step := flatMapConstMapAtByGetFromStep? get ys
  let init : Nat × Nat × Nat → Option (α × β) × Nat × Nat :=
    fun p => (none, p.2.1, p.2.2)
  have hstep : Primrec step :=
    flatMapConstMapAtByGetFromStep?_primrec get ys hget
  have hinit : Primrec init := by
    exact Primrec.pair (Primrec.const (none : Option (α × β))) Primrec.snd
  have hiter : Primrec (fun p : Nat × Nat × Nat => (step^[p.1]) (init p)) := by
    exact Primrec.nat_iterate Primrec.fst hinit
      ((hstep.comp Primrec.snd).to₂)
  exact Primrec.fst.comp hiter

private theorem flatMapConstMapAtByGetFrom?_primrec {α β : Type}
    [Primcodable α] [Primcodable β]
    (get : Nat → Option α) (ys : List β) (hget : Primrec get) :
    Primrec (fun p : Nat × Nat × Nat =>
      flatMapConstMapAtByGetFrom? get ys p.1 p.2.1 p.2.2) :=
  (flatMapConstMapAtByGetFromIter?_primrec get ys hget).of_eq fun p =>
    flatMapConstMapAtByGetFromIter?_eq get ys p.1 p.2.1 p.2.2

private theorem flatMapConstMapAtByGetFrom?_eq_byGet {α β : Type}
    (get : Nat → Option α) (ys : List β) (fuel k i : Nat) :
    flatMapConstMapAtByGetFrom? get ys fuel k i =
      flatMapConstMapAtByGet? (fun j => get (k + j)) ys fuel i := by
  induction fuel generalizing k i with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold flatMapConstMapAtByGetFrom? flatMapConstMapAtByGet?
      cases hy : ys[i]? with
      | some y =>
          simp
      | none =>
          rw [ih (k + 1) (i - ys.length)]
          simp [Nat.add_comm, Nat.add_left_comm]

/--
Structural decoder for the flat TM0 label index. The label list is a rectangular
expansion of statement support by the fixed `partrecVarList`; this function
exposes that indexing without unfolding the full flatMap at every use site.
-/
def partrecStartedTM0LabelAt? (tc : Turing.ToPartrec.Code) (i : Nat) :
    Option (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  flatMapConstMapAt? (partrecStartedTM0StatementList tc) partrecVarList i

/--
Statement-decoder-based variant of `partrecStartedTM0LabelAt?`.

This avoids constructing the full statement support list before indexing into
the rectangular variable expansion.
-/
def partrecStartedTM0LabelAtByStatement? (tc : Turing.ToPartrec.Code) (i : Nat) :
    Option (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  flatMapConstMapAtByGet? (partrecStartedTM0StatementAt? tc) partrecVarList
    (partrecStartedTM0StatementCount tc) i

/--
Offset form of `partrecStartedTM0LabelAtByStatement?`, with the statement
getter kept fixed for `tc` and the current statement index exposed as data.
-/
def partrecStartedTM0LabelAtByStatementFrom?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  flatMapConstMapAtByGetFrom? (partrecStartedTM0StatementAt? tc)
    partrecVarList fuel k i

theorem partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2) := by
  have hstmt : Primrec (partrecStartedTM0StatementAt? tc) :=
    partrecStartedTM0StatementAt?_primrec_fixed tc
  unfold partrecStartedTM0LabelAtByStatementFrom?
  change Primrec (fun p : Nat × Nat × Nat =>
    (flatMapConstMapAtByGetFrom? (partrecStartedTM0StatementAt? tc)
        partrecVarList p.1 p.2.1 p.2.2 :
      Option
        (Option
          (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
            (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
            PartrecVar) × PartrecVar)))
  exact flatMapConstMapAtByGetFrom?_primrec
    (partrecStartedTM0StatementAt? tc) partrecVarList hstmt

theorem partrecStartedTM0LabelAtByStatementFrom?_zero_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    partrecStartedTM0LabelAtByStatementFrom? tc
        (partrecStartedTM0StatementCount tc) 0 i =
      partrecStartedTM0LabelAtByStatement? tc i := by
  unfold partrecStartedTM0LabelAtByStatementFrom? partrecStartedTM0LabelAtByStatement?
  change
    (flatMapConstMapAtByGetFrom? (partrecStartedTM0StatementAt? tc)
        partrecVarList (partrecStartedTM0StatementCount tc) 0 i :
      Option
        (Option
          (Turing.TM1.Stmt
            (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
            (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
            PartrecVar) × PartrecVar)) =
      flatMapConstMapAtByGet? (partrecStartedTM0StatementAt? tc)
        partrecVarList (partrecStartedTM0StatementCount tc) i
  simpa using flatMapConstMapAtByGetFrom?_eq_byGet
    (partrecStartedTM0StatementAt? tc) partrecVarList
    (partrecStartedTM0StatementCount tc) 0 i

theorem partrecStartedTM0LabelAtByStatement?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (partrecStartedTM0LabelAtByStatement? tc) := by
  have hfrom := partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hspecial : Primrec (fun i : Nat =>
      partrecStartedTM0LabelAtByStatementFrom? tc
        (partrecStartedTM0StatementCount tc) 0 i) := by
    exact hfrom.comp
      (Primrec.pair (Primrec.const (partrecStartedTM0StatementCount tc))
        (Primrec.pair (Primrec.const 0) Primrec.id))
  exact hspecial.of_eq fun i =>
    partrecStartedTM0LabelAtByStatementFrom?_zero_eq tc i

theorem partrecStartedTM0LabelAtByStatement?_eq_labelAt
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    partrecStartedTM0LabelAtByStatement? tc i =
      partrecStartedTM0LabelAt? tc i := by
  unfold partrecStartedTM0LabelAtByStatement? partrecStartedTM0LabelAt?
  rw [← partrecStartedTM0StatementList_length tc]
  have hget :
      partrecStartedTM0StatementAt? tc =
        fun j => (partrecStartedTM0StatementList tc)[j]? := by
    funext j
    exact partrecStartedTM0StatementAt?_eq_getElem? tc j
  rw [hget]
  exact flatMapConstMapAtByGet?_eq_list
    (partrecStartedTM0StatementList tc) partrecVarList i

theorem partrecStartedTM0LabelAt?_eq_getElem?
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    partrecStartedTM0LabelAt? tc i =
      (partrecStartedTM0LabelList tc)[i]? := by
  unfold partrecStartedTM0LabelAt? partrecStartedTM0LabelList
  exact flatMapConstMapAt?_eq_getElem?
    (partrecStartedTM0StatementList tc) partrecVarList i

theorem partrecStartedTM0LabelAt?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (partrecStartedTM0LabelAt? tc) :=
  (partrecStartedTM0LabelAtByStatement?_primrec_fixed tc).of_eq fun i =>
    partrecStartedTM0LabelAtByStatement?_eq_labelAt tc i

/-- Numeric count of translated TM0 labels before the default start label is added. -/
def partrecStartedTM0LabelCount (tc : Turing.ToPartrec.Code) : Nat :=
  partrecStartedTM0StatementCount tc * partrecVarList.length

theorem partrecStartedTM0LabelCount_primrec_of_statementCount
    (h : Primrec partrecStartedTM0StatementCount) :
    Primrec partrecStartedTM0LabelCount := by
  unfold partrecStartedTM0LabelCount
  exact Primrec.nat_mul.comp h (Primrec.const partrecVarList.length)

theorem partrecStartedTM0LabelCount_primrec :
    Primrec partrecStartedTM0LabelCount :=
  partrecStartedTM0LabelCount_primrec_of_statementCount
    partrecStartedTM0StatementCount_primrec

theorem partrecStartedTM0LabelCount_computable :
    Computable partrecStartedTM0LabelCount :=
  partrecStartedTM0LabelCount_primrec.to_comp

theorem partrecStartedTM0LabelList_length (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM0LabelList tc).length =
      partrecStartedTM0LabelCount tc := by
  unfold partrecStartedTM0LabelList partrecStartedTM0LabelCount
  rw [List.length_flatMap]
  simp only [List.length_map]
  have hconst :
      (List.map (fun _ => partrecVarList.length)
          (partrecStartedTM0StatementList tc)).sum =
        (partrecStartedTM0StatementList tc).length * partrecVarList.length := by
    induction partrecStartedTM0StatementList tc with
    | nil =>
        simp
    | cons stmt stmts ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        rw [Nat.add_mul, one_mul]
        rw [Nat.add_comm]
  rw [hconst, partrecStartedTM0StatementList_length]

theorem mem_partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :
    q ∈ partrecStartedTM0LabelList tc ↔ q ∈ partrecStartedTM0Labels tc := by
  classical
  rcases q with ⟨stmt, v⟩
  unfold partrecStartedTM0LabelList partrecStartedTM0Labels Turing.TM1to0.trStmts
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    rcases h with ⟨stmt', hstmt', hp⟩
    rw [List.mem_map] at hp
    rcases hp with ⟨v', hv', hq⟩
    cases hq
    change (stmt, v) ∈
      (Turing.TM1.stmts (partrecStartedTM1Machine tc) (partrecStartedTM1Labels tc) ×ˢ
        (Finset.univ : Finset PartrecVar))
    rw [Finset.mem_product]
    exact ⟨(mem_partrecStartedTM0StatementList tc stmt).1 hstmt', Finset.mem_univ v⟩
  · intro h
    change (stmt, v) ∈
      (Turing.TM1.stmts (partrecStartedTM1Machine tc) (partrecStartedTM1Labels tc) ×ˢ
        (Finset.univ : Finset PartrecVar)) at h
    rw [Finset.mem_product] at h
    exact List.mem_flatMap.2
      ⟨stmt, (mem_partrecStartedTM0StatementList tc stmt).2 h.1,
        List.mem_map.2 ⟨v, mem_partrecVarList v, rfl⟩⟩

/--
Finite support list for translated TM0 states, with the start/default state
forced to position `0`.
-/
def partrecStartedTM0LabelSupportList (tc : Turing.ToPartrec.Code) :
    List (Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) :=
  default :: partrecStartedTM0LabelList tc

/-- Numeric count of translated TM0 labels including the default start label. -/
def partrecStartedTM0LabelSupportCount (tc : Turing.ToPartrec.Code) : Nat :=
  1 + partrecStartedTM0LabelCount tc

theorem partrecStartedTM0LabelSupportCount_primrec_of_statementCount
    (h : Primrec partrecStartedTM0StatementCount) :
    Primrec partrecStartedTM0LabelSupportCount := by
  unfold partrecStartedTM0LabelSupportCount
  exact (Primrec.succ.comp
    (partrecStartedTM0LabelCount_primrec_of_statementCount h)).of_eq fun tc => by
      simp [Nat.succ_eq_add_one, Nat.add_comm]

theorem partrecStartedTM0LabelSupportCount_primrec :
    Primrec partrecStartedTM0LabelSupportCount :=
  partrecStartedTM0LabelSupportCount_primrec_of_statementCount
    partrecStartedTM0StatementCount_primrec

theorem partrecStartedTM0LabelSupportCount_computable :
    Computable partrecStartedTM0LabelSupportCount :=
  partrecStartedTM0LabelSupportCount_primrec.to_comp

theorem partrecStartedTM0LabelSupportList_length (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM0LabelSupportList tc).length =
      partrecStartedTM0LabelSupportCount tc := by
  simp [partrecStartedTM0LabelSupportList, partrecStartedTM0LabelSupportCount,
    partrecStartedTM0LabelList_length]
  omega

theorem partrecStartedTM0_default_mem_labelSupportList (tc : Turing.ToPartrec.Code) :
    (default : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) ∈
      partrecStartedTM0LabelSupportList tc := by
  simp [partrecStartedTM0LabelSupportList]

theorem mem_partrecStartedTM0LabelSupportList_of_mem_labels
    {tc : Turing.ToPartrec.Code} {q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)}
    (hq : q ∈ partrecStartedTM0Labels tc) :
    q ∈ partrecStartedTM0LabelSupportList tc := by
  simp [partrecStartedTM0LabelSupportList, mem_partrecStartedTM0LabelList, hq]

/-- Number of numeric states in the finite one-sided TM0 program extracted from `TM0Route`. -/
def partrecStartedTM0StateCount (tc : Turing.ToPartrec.Code) : Nat :=
  partrecStartedTM0LabelSupportCount tc

theorem partrecStartedTM0StateCount_primrec_of_statementCount
    (h : Primrec partrecStartedTM0StatementCount) :
    Primrec partrecStartedTM0StateCount := by
  unfold partrecStartedTM0StateCount
  exact partrecStartedTM0LabelSupportCount_primrec_of_statementCount h

theorem partrecStartedTM0StateCount_primrec_of_supportWeight
    (hweight :
      Primrec₂ (PartrecToTM2SupportList.codeSuppWeight partrecTM1LabelStmtSupportWeight)) :
    Primrec partrecStartedTM0StateCount :=
  partrecStartedTM0StateCount_primrec_of_statementCount
    (partrecStartedTM0StatementCount_primrec_of_supportWeight hweight)

theorem partrecStartedTM0StateCount_primrec :
    Primrec partrecStartedTM0StateCount :=
  partrecStartedTM0StateCount_primrec_of_statementCount
    partrecStartedTM0StatementCount_primrec

theorem partrecStartedTM0StateCount_computable_of_statementCount
    (h : Computable partrecStartedTM0StatementCount) :
    Computable partrecStartedTM0StateCount := by
  unfold partrecStartedTM0StateCount partrecStartedTM0LabelSupportCount
    partrecStartedTM0LabelCount
  have hmul :
      Computable fun tc : Turing.ToPartrec.Code =>
        partrecStartedTM0StatementCount tc * partrecVarList.length :=
    Primrec.nat_mul.to_comp.comp h (Computable.const partrecVarList.length)
  exact Primrec.nat_add.to_comp.comp (Computable.const 1) hmul

theorem partrecStartedTM0StateCount_computable_of_supportWeight
    (hweight :
      Computable₂ (PartrecToTM2SupportList.codeSuppWeight partrecTM1LabelStmtSupportWeight)) :
    Computable partrecStartedTM0StateCount :=
  partrecStartedTM0StateCount_computable_of_statementCount
    (partrecStartedTM0StatementCount_computable_of_supportWeight hweight)

theorem partrecStartedTM0StateCount_computable :
    Computable partrecStartedTM0StateCount :=
  partrecStartedTM0StateCount_primrec.to_comp

theorem partrecStartedTM0LabelSupportList_length_eq_stateCount
    (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM0LabelSupportList tc).length =
      partrecStartedTM0StateCount tc := by
  rw [partrecStartedTM0LabelSupportList_length, partrecStartedTM0StateCount]

/-- Numeric state list for the finite one-sided TM0 program extracted from `TM0Route`. -/
def partrecStartedTM0States (tc : Turing.ToPartrec.Code) : List Nat :=
  List.range (partrecStartedTM0StateCount tc)

theorem partrecStartedTM0States_primrec :
    Primrec partrecStartedTM0States := by
  unfold partrecStartedTM0States
  exact Primrec.list_range.comp partrecStartedTM0StateCount_primrec

theorem partrecStartedTM0States_computable :
    Computable partrecStartedTM0States :=
  partrecStartedTM0States_primrec.to_comp

/-- Numeric start state corresponding to the default translated TM0 label. -/
def partrecStartedTM0Start : Nat :=
  0

theorem partrecStartedTM0Start_mem_states (tc : Turing.ToPartrec.Code) :
    partrecStartedTM0Start ∈ partrecStartedTM0States tc := by
  simp [partrecStartedTM0Start, partrecStartedTM0States, partrecStartedTM0StateCount,
    partrecStartedTM0LabelSupportCount]

theorem partrecStartedTM0LabelSupportList_get_zero (tc : Turing.ToPartrec.Code) :
    (partrecStartedTM0LabelSupportList tc)[0]? =
      some (default : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc)) := by
  simp [partrecStartedTM0LabelSupportList]

/-- Numeric code for a supported translated TM0 state. -/
def partrecStartedTM0StateCodeOfMem (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (_hq : q ∈ partrecStartedTM0LabelSupportList tc) : Nat :=
  (partrecStartedTM0LabelSupportList tc).idxOf q

theorem partrecStartedTM0StateCodeOfMem_mem_states (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) :
    partrecStartedTM0StateCodeOfMem tc q hq ∈ partrecStartedTM0States tc := by
  unfold partrecStartedTM0StateCodeOfMem partrecStartedTM0States
  exact List.mem_range.2 (by
    rw [← partrecStartedTM0LabelSupportList_length_eq_stateCount]
    exact List.idxOf_lt_length_iff.2 hq)

theorem partrecStartedTM0StateCodeOfMem_get? (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (partrecStartedTM1Machine tc))
    (hq : q ∈ partrecStartedTM0LabelSupportList tc) :
    (partrecStartedTM0LabelSupportList tc)[partrecStartedTM0StateCodeOfMem tc q hq]? =
      some q := by
  unfold partrecStartedTM0StateCodeOfMem
  exact List.getElem?_idxOf hq

/-- The finite cell values that can occur in one stack coordinate of the TM2-to-TM1 alphabet. -/
def partrecStartedTM0CellValues : List (Option Turing.PartrecToTM2.Γ') :=
  partrecVarList

theorem mem_partrecStartedTM0CellValues (a : Option Turing.PartrecToTM2.Γ') :
    a ∈ partrecStartedTM0CellValues := by
  cases a with
  | none =>
      simp [partrecStartedTM0CellValues, partrecVarList]
  | some a =>
      simp [partrecStartedTM0CellValues, partrecVarList,
        PartrecToTM2Support.mem_stackAlphabetList a]

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

theorem partrecStartedTM0StackVectorToTuple_primrec :
    Primrec partrecStartedTM0StackVectorToTuple := by
  change Primrec partrecStartedTM0StackVectorEquivTuple
  simpa [instPrimcodablePartrecStartedTM0StackVector] using
    (Primrec.of_equiv
      (α := Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
        Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ')
      (e := partrecStartedTM0StackVectorEquivTuple))

theorem partrecStartedTM0StackVector_main_primrec :
    Primrec (fun v : ∀ k : PartrecStack, Option (PartrecStackSymbol k) =>
      v Turing.PartrecToTM2.K'.main) :=
  Primrec.fst.comp partrecStartedTM0StackVectorToTuple_primrec

theorem partrecStartedTM0StackVector_rev_primrec :
    Primrec (fun v : ∀ k : PartrecStack, Option (PartrecStackSymbol k) =>
      v Turing.PartrecToTM2.K'.rev) :=
  (Primrec.fst.comp (Primrec.snd.comp partrecStartedTM0StackVectorToTuple_primrec))

theorem partrecStartedTM0StackVector_aux_primrec :
    Primrec (fun v : ∀ k : PartrecStack, Option (PartrecStackSymbol k) =>
      v Turing.PartrecToTM2.K'.aux) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    partrecStartedTM0StackVectorToTuple_primrec)))

theorem partrecStartedTM0StackVector_stack_primrec :
    Primrec (fun v : ∀ k : PartrecStack, Option (PartrecStackSymbol k) =>
      v Turing.PartrecToTM2.K'.stack) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    partrecStartedTM0StackVectorToTuple_primrec)))

instance instPrimcodablePartrecStartedTM0Symbol :
    Primcodable (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol) :=
  inferInstanceAs (Primcodable
    (Bool × (∀ k : PartrecStack, Option (PartrecStackSymbol k))))

/--
Finite encoding of functions out of the concrete TM2-to-TM1 tape alphabet.

The source symbol is a bottom marker together with four stack-cell coordinates,
so a function out of it is the same data as a curried function over those five
finite coordinates.
-/
def partrecStartedTM0SymbolFunctionEquiv
    (β : Type*) :
    (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ≃
      (Bool → PartrecVar → PartrecVar → PartrecVar → PartrecVar → β) where
  toFun f bottom main rev aux stack :=
    f (bottom, partrecStartedTM0StackVector main rev aux stack)
  invFun f a :=
    f a.1
      (a.2 Turing.PartrecToTM2.K'.main)
      (a.2 Turing.PartrecToTM2.K'.rev)
      (a.2 Turing.PartrecToTM2.K'.aux)
      (a.2 Turing.PartrecToTM2.K'.stack)
  left_inv := by
    intro f
    funext a
    rcases a with ⟨bottom, cells⟩
    simp [partrecStartedTM0StackVector_ext cells]
  right_inv := by
    intro f
    funext bottom main rev aux stack
    rfl

instance instPrimcodablePartrecStartedTM0SymbolFunction
    (β : Type*) [Primcodable β] :
    Primcodable (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) :=
  Primcodable.ofEquiv
    (Bool → PartrecVar → PartrecVar → PartrecVar → PartrecVar → β)
    (partrecStartedTM0SymbolFunctionEquiv β)

theorem partrecStartedTM0SymbolFunctionEquiv_primrec
    (β : Type*) [Primcodable β] :
    Primrec (partrecStartedTM0SymbolFunctionEquiv β) := by
  simpa [instPrimcodablePartrecStartedTM0SymbolFunction] using
    (Primrec.of_equiv
      (α := Bool → PartrecVar → PartrecVar → PartrecVar → PartrecVar → β)
      (e := partrecStartedTM0SymbolFunctionEquiv β))

theorem partrecStartedTM0SymbolFunction_app_primrec
    (β : Type*) [Primcodable β] :
    Primrec₂ (fun f : Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β =>
      fun a => f a) := by
  apply Primrec₂.mk
  let curried :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol →
        Bool → PartrecVar → PartrecVar → PartrecVar → PartrecVar → β :=
    fun p => partrecStartedTM0SymbolFunctionEquiv β p.1
  have hcurried : Primrec curried :=
    (partrecStartedTM0SymbolFunctionEquiv_primrec β).comp Primrec.fst
  have hbottom : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcells : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hmain : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        p.2.2 Turing.PartrecToTM2.K'.main) :=
    partrecStartedTM0StackVector_main_primrec.comp hcells
  have hrev : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        p.2.2 Turing.PartrecToTM2.K'.rev) :=
    partrecStartedTM0StackVector_rev_primrec.comp hcells
  have haux : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        p.2.2 Turing.PartrecToTM2.K'.aux) :=
    partrecStartedTM0StackVector_aux_primrec.comp hcells
  have hstack : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        p.2.2 Turing.PartrecToTM2.K'.stack) :=
    partrecStartedTM0StackVector_stack_primrec.comp hcells
  have h₀ : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        (curried p) p.2.1) :=
    (boolFunction_app_primrec
      (PartrecVar → PartrecVar → PartrecVar → PartrecVar → β)).comp hcurried hbottom
  have h₁ : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        (curried p) p.2.1 (p.2.2 Turing.PartrecToTM2.K'.main)) :=
    (partrecVarFunction_app_primrec
      (PartrecVar → PartrecVar → PartrecVar → β)).comp h₀ hmain
  have h₂ : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        (curried p) p.2.1 (p.2.2 Turing.PartrecToTM2.K'.main)
          (p.2.2 Turing.PartrecToTM2.K'.rev)) :=
    (partrecVarFunction_app_primrec
      (PartrecVar → PartrecVar → β)).comp h₁ hrev
  have h₃ : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol =>
        (curried p) p.2.1 (p.2.2 Turing.PartrecToTM2.K'.main)
          (p.2.2 Turing.PartrecToTM2.K'.rev)
          (p.2.2 Turing.PartrecToTM2.K'.aux)) :=
    (partrecVarFunction_app_primrec (PartrecVar → β)).comp h₂ haux
  exact ((partrecVarFunction_app_primrec β).comp h₃ hstack).of_eq fun p => by
    rcases p with ⟨f, bottom, cells⟩
    simp [curried, partrecStartedTM0SymbolFunctionEquiv,
      partrecStartedTM0StackVector_ext cells]

theorem partrecStartedTM0SymbolPartrecVarFunction_app_primrec
    (β : Type*) [Primcodable β] :
    Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → PartrecVar → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol × PartrecVar =>
        p.1 p.2.1 p.2.2) := by
  have hsymbol : Primrec (fun p :
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol → PartrecVar → β) ×
          Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol × PartrecVar =>
        p.1 p.2.1) :=
    (partrecStartedTM0SymbolFunction_app_primrec (PartrecVar → β)).comp
      Primrec.fst (Primrec.fst.comp Primrec.snd)
  exact (partrecVarFunction_app_primrec β).comp hsymbol (Primrec.snd.comp Primrec.snd)

namespace PartrecStartedTM1StmtNode

noncomputable instance instPrimcodable (tc : Turing.ToPartrec.Code) :
    Primcodable (PartrecStartedTM1StmtNode tc) :=
  Primcodable.ofEquiv (Code tc) (equivCode tc)

theorem gotoHaltCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (gotoHaltCodeArity (tc := tc)) :=
  (Primrec.const 0).of_eq fun c => by
    cases c <;> rfl

theorem branchTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (branchTailCodeArity (tc := tc)) := by
  unfold branchTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : BranchTailCode tc => c))
    (Primrec.const 2).to₂
    ((gotoHaltCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

theorem loadTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (loadTailCodeArity (tc := tc)) := by
  unfold loadTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : LoadTailCode tc => c))
    (Primrec.const 1).to₂
    ((branchTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

theorem writeTailCodeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (writeTailCodeArity (tc := tc)) := by
  unfold writeTailCodeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : WriteTailCode tc => c))
    (Primrec.const 1).to₂
    ((loadTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      cases x <;> rfl

theorem codeArity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (codeArity (tc := tc)) := by
  unfold codeArity
  exact (Primrec.sumCasesOn
    (Primrec.id : Primrec (fun c : Code tc => c))
    (Primrec.const 1).to₂
    ((writeTailCodeArity_primrec tc).comp₂ Primrec₂.right)).of_eq fun x => by
      rcases x with p | c
      · rfl
      rcases c with f | c
      · rfl
      rcases c with f | c
      · rfl
      rcases c with f | c
      · rfl
      rcases c with f | u
      · rfl
      cases u
      rfl

theorem toCode_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (toCode : PartrecStartedTM1StmtNode tc → Code tc) := by
  simpa [equivCode] using
    (Primrec.of_equiv (e := equivCode tc) :
      Primrec (equivCode tc))

theorem arity_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (arity (tc := tc)) :=
  ((codeArity_primrec tc).comp (toCode_primrec tc)).of_eq fun n => by
    cases n with
    | move d => cases d <;> rfl
    | write f => rfl
    | load f => rfl
    | branch f => rfl
    | goto f => rfl
    | halt => rfl

def validStep {tc : Turing.ToPartrec.Code}
    (state : Bool × Nat) (node : PartrecStartedTM1StmtNode tc) : Bool × Nat :=
  if state.1 ∧ 0 < state.2 then
    (true, state.2 - 1 + arity node)
  else
    (false, state.2)

theorem validStep_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : (Bool × Nat) × PartrecStartedTM1StmtNode tc =>
      validStep p.1 p.2) := by
  have hstate : Primrec (fun p : (Bool × Nat) × PartrecStartedTM1StmtNode tc =>
      p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hslots : Primrec (fun p : (Bool × Nat) × PartrecStartedTM1StmtNode tc =>
      p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hok : PrimrecPred (fun p : (Bool × Nat) × PartrecStartedTM1StmtNode tc =>
      p.1.1 ∧ 0 < p.1.2) :=
    PrimrecPred.and
      (Primrec.eq.comp hstate (Primrec.const true))
      (Primrec.nat_lt.comp (Primrec.const 0) hslots)
  have hthen : Primrec (fun p : (Bool × Nat) × PartrecStartedTM1StmtNode tc =>
      (true, p.1.2 - 1 + arity p.2)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.nat_add.comp
        (Primrec.nat_sub.comp
          hslots
          (Primrec.const 1))
        ((arity_primrec tc).comp Primrec.snd))
  have helse : Primrec (fun p : (Bool × Nat) × PartrecStartedTM1StmtNode tc =>
      (false, p.1.2)) :=
    Primrec.pair (Primrec.const false) hslots
  exact (Primrec.ite hok hthen helse).of_eq fun p => by
    simp [validStep]

/-- Shape-only validity of a preorder statement encoding. -/
def Valid {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) : Prop :=
  nodes.foldl validStep (true, 1) = (true, 0)

instance instDecidableValid (tc : Turing.ToPartrec.Code)
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    Decidable (Valid nodes) :=
  inferInstanceAs (Decidable (nodes.foldl validStep (true, 1) = (true, 0)))

theorem valid_primrecPred (tc : Turing.ToPartrec.Code) :
    PrimrecPred (Valid (tc := tc)) := by
  unfold Valid
  exact Primrec.eq.comp
    (Primrec.list_foldl Primrec.id (Primrec.const (true, 1))
      (((validStep_primrec tc).comp Primrec.snd).to₂))
    (Primrec.const (true, 0))

theorem foldl_validStep_false {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) (slots : Nat) :
    nodes.foldl validStep (false, slots) = (false, slots) := by
  induction nodes generalizing slots with
  | nil =>
      rfl
  | cons node rest ih =>
      simp [validStep, ih]

theorem foldl_validStep_true_zero {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    nodes.foldl validStep (true, 0) =
      match nodes with
      | [] => (true, 0)
      | _ :: _ => (false, 0) := by
  cases nodes with
  | nil =>
      rfl
  | cons node rest =>
      simp [validStep, foldl_validStep_false]

theorem foldl_validStep_true_zero_eq_true_zero_iff {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    nodes.foldl validStep (true, 0) = (true, 0) ↔ nodes = [] := by
  cases nodes with
  | nil =>
      simp
  | cons node rest =>
      simp only [List.foldl_cons]
      rw [show validStep (true, 0) node = (false, 0) by simp [validStep]]
      rw [foldl_validStep_false]
      simp

theorem valid_tail_nil_of_arity_zero {tc : Turing.ToPartrec.Code}
    {node : PartrecStartedTM1StmtNode tc} {rest : List (PartrecStartedTM1StmtNode tc)}
    (harity : arity node = 0)
    (hvalid : (node :: rest).foldl validStep (true, 1) = (true, 0)) :
    rest = [] := by
  have htail : rest.foldl validStep (true, 0) = (true, 0) := by
    simpa [validStep, harity] using hvalid
  exact (foldl_validStep_true_zero_eq_true_zero_iff rest).1 htail

/-- The concrete started TM1 statement type encoded by these preorder nodes. -/
abbrev Stmt (tc : Turing.ToPartrec.Code) : Type :=
  PartrecStartedTM0Stmt tc

/-- Encode a concrete started TM1 statement as a preorder list of nodes. -/
def ofStmt {tc : Turing.ToPartrec.Code} : Stmt tc → List (PartrecStartedTM1StmtNode tc)
  | Turing.TM1.Stmt.move d q => move d :: ofStmt q
  | Turing.TM1.Stmt.write f q => write f :: ofStmt q
  | Turing.TM1.Stmt.load f q => load f :: ofStmt q
  | Turing.TM1.Stmt.branch f q₁ q₂ => branch f :: (ofStmt q₁ ++ ofStmt q₂)
  | Turing.TM1.Stmt.goto f => [goto f]
  | Turing.TM1.Stmt.halt => [halt]

theorem ofStmt_length_pos {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    0 < (ofStmt stmt).length := by
  cases stmt <;> simp [ofStmt]

/--
Fuelled parser for preorder-encoded concrete started TM1 statements.

The returned tail is the unconsumed suffix after one complete statement.
-/
def parseWithFuel {tc : Turing.ToPartrec.Code} :
    Nat → List (PartrecStartedTM1StmtNode tc) →
      Option (Stmt tc × List (PartrecStartedTM1StmtNode tc))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, node :: rest =>
      match node with
      | move d =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM1.Stmt.move d p.1, p.2)
      | write f =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM1.Stmt.write f p.1, p.2)
      | load f =>
          (parseWithFuel fuel rest).map fun p =>
            (Turing.TM1.Stmt.load f p.1, p.2)
      | branch f =>
          (parseWithFuel fuel rest).bind fun left =>
            (parseWithFuel fuel left.2).map fun right =>
              (Turing.TM1.Stmt.branch f left.1 right.1, right.2)
      | goto f => some (Turing.TM1.Stmt.goto f, rest)
      | halt => some (Turing.TM1.Stmt.halt, rest)

/-- Parse a preorder list using its own length as fuel. -/
def parse? {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    Option (Stmt tc × List (PartrecStartedTM1StmtNode tc)) :=
  parseWithFuel nodes.length nodes

set_option linter.flexible false in
theorem parseWithFuel_mono {tc : Turing.ToPartrec.Code}
    {fuel fuel' : Nat} (h : fuel ≤ fuel')
    (nodes : List (PartrecStartedTM1StmtNode tc))
    {out : Stmt tc × List (PartrecStartedTM1StmtNode tc)}
    (hparse : parseWithFuel (tc := tc) fuel nodes = some out) :
    parseWithFuel (tc := tc) fuel' nodes = some out := by
  induction fuel generalizing fuel' nodes out with
  | zero =>
      simp [parseWithFuel] at hparse
  | succ fuel ih =>
      cases fuel' with
      | zero =>
          omega
      | succ fuel' =>
          cases nodes with
          | nil =>
              simp [parseWithFuel] at hparse
          | cons node rest =>
              cases node with
              | move d =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | write f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | load f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                    simp [hp] at hparse
                  rcases p with ⟨q, tail⟩
                  simp at hparse
                  subst out
                  have hp' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := (q, tail)) (by simpa using hp)
                  simp [hp']
              | branch f =>
                  simp [parseWithFuel] at hparse ⊢
                  rcases hleft : parseWithFuel (tc := tc) fuel rest with _ | left <;>
                    simp [hleft] at hparse
                  rcases hright : parseWithFuel (tc := tc) fuel left.2 with _ | right <;>
                    simp [hright] at hparse
                  rcases right with ⟨q₂, tail⟩
                  simp at hparse
                  subst out
                  have hleft' := ih (Nat.succ_le_succ_iff.1 h) rest
                    (out := left) (by simpa using hleft)
                  have hright' := ih (Nat.succ_le_succ_iff.1 h) left.2
                    (out := (q₂, tail)) (by simpa using hright)
                  simp [hleft', hright']
              | goto f =>
                  simp [parseWithFuel] at hparse ⊢
                  exact hparse
              | halt =>
                  simp [parseWithFuel] at hparse ⊢
                  exact hparse

set_option linter.flexible false in
theorem parseWithFuel_eq_ofStmt_append {tc : Turing.ToPartrec.Code}
    {fuel : Nat} {nodes : List (PartrecStartedTM1StmtNode tc)}
    {out : Stmt tc × List (PartrecStartedTM1StmtNode tc)}
    (hparse : parseWithFuel (tc := tc) fuel nodes = some out) :
    nodes = ofStmt out.1 ++ out.2 := by
  induction fuel generalizing nodes out with
  | zero =>
      simp [parseWithFuel] at hparse
  | succ fuel ih =>
      cases nodes with
      | nil =>
          simp [parseWithFuel] at hparse
      | cons node rest =>
          cases node with
          | move d =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | write f =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | load f =>
              simp [parseWithFuel] at hparse
              rcases hp : parseWithFuel (tc := tc) fuel rest with _ | p <;>
                simp [hp] at hparse
              rcases p with ⟨q, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q, tail)) (by simpa using hp)
              simp [ofStmt, hrest]
          | branch f =>
              simp [parseWithFuel] at hparse
              rcases hleft : parseWithFuel (tc := tc) fuel rest with _ | left <;>
                simp [hleft] at hparse
              rcases hright : parseWithFuel (tc := tc) fuel left.2 with _ | right <;>
                simp [hright] at hparse
              rcases left with ⟨q₁, mid⟩
              rcases right with ⟨q₂, tail⟩
              simp at hparse
              subst out
              have hrest := ih (nodes := rest) (out := (q₁, mid)) (by simpa using hleft)
              have hmid := ih (nodes := mid) (out := (q₂, tail)) (by simpa using hright)
              simp [ofStmt, hrest, hmid, List.append_assoc]
          | goto f =>
              simp [parseWithFuel] at hparse
              subst out
              simp [ofStmt]
          | halt =>
              simp [parseWithFuel] at hparse
              subst out
              simp [ofStmt]

theorem parse?_eq_some_empty_ofStmt {tc : Turing.ToPartrec.Code}
    {nodes : List (PartrecStartedTM1StmtNode tc)} {stmt : Stmt tc}
    (hparse : parse? (tc := tc) nodes = some (stmt, [])) :
    nodes = ofStmt stmt := by
  have hsound := parseWithFuel_eq_ofStmt_append (tc := tc) hparse
  simpa [parse?] using hsound

set_option linter.flexible false in
theorem parseWithFuel_complete_prefix {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) (slots final : Nat)
    (hvalid : nodes.foldl validStep (true, slots + 1) = (true, final))
    (hfinal : final ≤ slots) :
    ∃ stmt tail,
      parseWithFuel (tc := tc) nodes.length nodes = some (stmt, tail) ∧
        tail.foldl validStep (true, slots) = (true, final) := by
  induction hlen : nodes.length using Nat.strong_induction_on
      generalizing nodes slots final with
  | _ n ih =>
      subst hlen
      cases nodes with
      | nil =>
          simp at hvalid
          omega
      | cons node rest =>
          cases node with
          | move d =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM1.Stmt.move d stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | write f =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM1.Stmt.write f stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | load f =>
              have hrest :
                  rest.foldl validStep (true, slots + 1) = (true, final) := by
                simpa [validStep, arity] using hvalid
              rcases ih rest.length (by simp) rest slots final hrest hfinal rfl with
                ⟨stmt, tail, hparse, htail⟩
              refine ⟨Turing.TM1.Stmt.load f stmt, tail, ?_, htail⟩
              simp [parseWithFuel, hparse]
          | branch f =>
              have hrest :
                  rest.foldl validStep (true, (slots + 1) + 1) = (true, final) := by
                simpa [validStep, arity, Nat.add_assoc] using hvalid
              have hfinalLeft : final ≤ slots + 1 := by omega
              rcases ih rest.length (by simp) rest (slots + 1) final hrest hfinalLeft rfl with
                ⟨left, mid, hleft, hmidValid⟩
              have hrest_eq : rest = ofStmt left ++ mid :=
                parseWithFuel_eq_ofStmt_append (tc := tc) hleft
              have hmid_lt : mid.length < (PartrecStartedTM1StmtNode.branch f :: rest).length := by
                rw [hrest_eq]
                have hpos := ofStmt_length_pos (tc := tc) left
                simp
                omega
              rcases ih mid.length hmid_lt mid slots final hmidValid hfinal rfl with
                ⟨right, tail, hright, htail⟩
              have hmid_le_rest : mid.length ≤ rest.length := by
                rw [hrest_eq]
                simp
              have hrightBig := parseWithFuel_mono
                (tc := tc)
                (fuel := mid.length)
                (fuel' := rest.length)
                hmid_le_rest
                mid
                hright
              refine ⟨Turing.TM1.Stmt.branch f left right, tail, ?_, htail⟩
              simp [parseWithFuel, hleft, hrightBig]
          | goto f =>
              have htail : rest.foldl validStep (true, slots) = (true, final) := by
                simpa [validStep, arity] using hvalid
              refine ⟨Turing.TM1.Stmt.goto f, rest, ?_, htail⟩
              simp [parseWithFuel]
          | halt =>
              have htail : rest.foldl validStep (true, slots) = (true, final) := by
                simpa [validStep, arity] using hvalid
              refine ⟨Turing.TM1.Stmt.halt, rest, ?_, htail⟩
              simp [parseWithFuel]

set_option linter.flexible false in
theorem parseWithFuel_ofStmt_append {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM1StmtNode tc)) :
    parseWithFuel (tc := tc) (ofStmt stmt).length (ofStmt stmt ++ tail) =
      some (stmt, tail) := by
  induction stmt generalizing tail with
  | move d q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | write f q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | load f q ih =>
      simp [ofStmt, parseWithFuel]
      exact ih tail
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp [ofStmt, parseWithFuel]
      have hleft :
          parseWithFuel (tc := tc) (ofStmt q₁).length
              (ofStmt q₁ ++ ofStmt q₂ ++ tail) =
            some (q₁, ofStmt q₂ ++ tail) := by
        simpa [List.append_assoc] using ih₁ (ofStmt q₂ ++ tail)
      have hleft' :
          parseWithFuel (tc := tc) (ofStmt q₁).length
              (ofStmt q₁ ++ (ofStmt q₂ ++ tail)) =
            some (q₁, ofStmt q₂ ++ tail) := by
        simpa [List.append_assoc] using hleft
      have hleftBig := parseWithFuel_mono
        (tc := tc)
        (fuel := (ofStmt q₁).length)
        (fuel' := (ofStmt q₁).length + (ofStmt q₂).length)
        (by omega)
        (ofStmt q₁ ++ (ofStmt q₂ ++ tail))
        hleft'
      have hright :
          parseWithFuel (tc := tc) (ofStmt q₂).length
              (ofStmt q₂ ++ tail) =
            some (q₂, tail) := ih₂ tail
      have hrightBig := parseWithFuel_mono
        (tc := tc)
        (fuel := (ofStmt q₂).length)
        (fuel' := (ofStmt q₁).length + (ofStmt q₂).length)
        (by omega)
        (ofStmt q₂ ++ tail)
        hright
      simp [hleftBig, hrightBig]
  | goto f =>
      simp [ofStmt, parseWithFuel]
  | halt =>
      simp [ofStmt, parseWithFuel]

theorem parse?_ofStmt {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    parse? (tc := tc) (ofStmt stmt) = some (stmt, []) := by
  unfold parse?
  simpa using parseWithFuel_ofStmt_append (tc := tc) stmt []

theorem parse?_eq_some_of_valid {tc : Turing.ToPartrec.Code}
    {nodes : List (PartrecStartedTM1StmtNode tc)}
    (hvalid : Valid (tc := tc) nodes) :
    ∃ stmt : Stmt tc, parse? (tc := tc) nodes = some (stmt, []) := by
  rcases parseWithFuel_complete_prefix (tc := tc) nodes 0 0 hvalid (by omega) with
    ⟨stmt, tail, hparse, htail⟩
  have htail_nil : tail = [] :=
    (foldl_validStep_true_zero_eq_true_zero_iff tail).1 htail
  subst tail
  exact ⟨stmt, by simpa [parse?] using hparse⟩

theorem ofStmt_injective {tc : Turing.ToPartrec.Code} :
    Function.Injective (ofStmt (tc := tc)) := by
  intro a b h
  have ha := parse?_ofStmt (tc := tc) a
  rw [h] at ha
  rw [parse?_ofStmt (tc := tc) b] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

set_option linter.flexible false in
theorem ofStmt_foldl_validStep {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (slots : Nat) :
    (ofStmt stmt).foldl validStep (true, slots + 1) = (true, slots) := by
  induction stmt generalizing slots with
  | move d q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | write f q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | load f q ih =>
      simp [ofStmt, validStep, arity]
      exact ih slots
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp [ofStmt, validStep, arity, List.foldl_append]
      rw [ih₁ (slots + 1)]
      exact ih₂ slots
  | goto f =>
      simp [ofStmt, validStep, arity]
  | halt =>
      simp [ofStmt, validStep, arity]

theorem valid_ofStmt {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    Valid (tc := tc) (ofStmt stmt) := by
  unfold Valid
  simpa using ofStmt_foldl_validStep (tc := tc) stmt 0

/-- Valid preorder-list representation of a concrete started TM1 statement. -/
abbrev ValidCode (tc : Turing.ToPartrec.Code) : Type :=
  { nodes : List (PartrecStartedTM1StmtNode tc) // Valid (tc := tc) nodes }

def toValidCode {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) : ValidCode tc :=
  ⟨ofStmt stmt, valid_ofStmt stmt⟩

theorem toValidCode_injective {tc : Turing.ToPartrec.Code} :
    Function.Injective (toValidCode (tc := tc)) := by
  intro a b h
  exact ofStmt_injective (congrArg Subtype.val h)

theorem toValidCode_surjective {tc : Turing.ToPartrec.Code} :
    Function.Surjective (toValidCode (tc := tc)) := by
  intro code
  rcases parse?_eq_some_of_valid (tc := tc) code.2 with ⟨stmt, hparse⟩
  refine ⟨stmt, Subtype.ext ?_⟩
  exact (parse?_eq_some_empty_ofStmt (tc := tc) hparse).symm

noncomputable def stmtEquivValidCode (tc : Turing.ToPartrec.Code) :
    Stmt tc ≃ ValidCode tc :=
  Equiv.ofBijective (toValidCode (tc := tc))
    ⟨toValidCode_injective (tc := tc), toValidCode_surjective (tc := tc)⟩

noncomputable instance instPrimcodableValidCode (tc : Turing.ToPartrec.Code) :
    Primcodable (ValidCode tc) :=
  Primcodable.subtype (valid_primrecPred tc)

noncomputable instance instPrimcodableStmt (tc : Turing.ToPartrec.Code) :
    Primcodable (Stmt tc) :=
  Primcodable.ofEquiv (ValidCode tc) (stmtEquivValidCode tc)

theorem toValidCode_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (toValidCode : Stmt tc → ValidCode tc) := by
  simpa [stmtEquivValidCode] using
    (Primrec.of_equiv (e := stmtEquivValidCode tc) :
      Primrec (stmtEquivValidCode tc))

noncomputable def ofValidCode {tc : Turing.ToPartrec.Code}
    (code : ValidCode tc) : Stmt tc :=
  (stmtEquivValidCode tc).symm code

theorem ofValidCode_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (ofValidCode (tc := tc)) := by
  change @Primrec (ValidCode tc) (Stmt tc) (instPrimcodableValidCode tc)
    (Primcodable.ofEquiv (ValidCode tc) (stmtEquivValidCode tc))
    (stmtEquivValidCode tc).symm
  exact Primrec.of_equiv_symm

theorem ofValidCode_toValidCode {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    ofValidCode (toValidCode stmt) = stmt := by
  unfold ofValidCode
  exact (stmtEquivValidCode tc).left_inv stmt

theorem toValidCode_ofValidCode {tc : Turing.ToPartrec.Code} (code : ValidCode tc) :
    toValidCode (ofValidCode code) = code := by
  unfold ofValidCode
  exact (stmtEquivValidCode tc).right_inv code

theorem ofStmt_ofValidCode {tc : Turing.ToPartrec.Code} (code : ValidCode tc) :
    ofStmt (ofValidCode code) = code.1 := by
  have h := congrArg Subtype.val (toValidCode_ofValidCode (tc := tc) code)
  simpa [toValidCode] using h

theorem ofValidCode_ofStmt {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    ofValidCode ⟨ofStmt stmt, valid_ofStmt stmt⟩ = stmt := by
  simpa [toValidCode] using ofValidCode_toValidCode (tc := tc) stmt

theorem ofStmt_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (ofStmt : Stmt tc → List (PartrecStartedTM1StmtNode tc)) := by
  letI : Primcodable (ValidCode tc) := instPrimcodableValidCode tc
  have hval : Primrec (fun code : ValidCode tc => code.1) :=
    Primrec.subtype_val (hp := valid_primrecPred tc)
  exact (hval.comp (toValidCode_primrec tc)).of_eq fun stmt => rfl

theorem ofStmt_length_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (fun stmt : Stmt tc => (ofStmt stmt).length) :=
  Primrec.list_length.comp (ofStmt_primrec tc)

def ofStmtHead? {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) : Option (PartrecStartedTM1StmtNode tc) :=
  (ofStmt stmt).head?

theorem ofStmtHead?_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (ofStmtHead? (tc := tc)) :=
  Primrec.list_head?.comp (ofStmt_primrec tc)

def ofStmtTail {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) : List (PartrecStartedTM1StmtNode tc) :=
  (ofStmt stmt).tail

theorem ofStmtTail_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (ofStmtTail (tc := tc)) :=
  Primrec.list_tail.comp (ofStmt_primrec tc)

theorem ofStmtTail_length_lt {tc : Turing.ToPartrec.Code} (stmt : Stmt tc) :
    (ofStmtTail stmt).length < (ofStmt stmt).length := by
  cases stmt <;> simp [ofStmtTail, ofStmt]

def properTails {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    List (List (PartrecStartedTM1StmtNode tc)) :=
  (List.range nodes.length).map fun i => nodes.drop (i + 1)

theorem properTails_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (properTails (tc := tc)) := by
  unfold properTails
  refine Primrec.list_map (Primrec.list_range.comp Primrec.list_length) ?_
  exact Primrec.list_drop.comp
    (Primrec.succ.comp Primrec₂.right) Primrec₂.left

theorem mem_properTails_length_lt {tc : Turing.ToPartrec.Code}
    {nodes tail : List (PartrecStartedTM1StmtNode tc)}
    (htail : tail ∈ properTails nodes) :
    tail.length < nodes.length := by
  unfold properTails at htail
  rcases List.mem_map.1 htail with ⟨i, hi, rfl⟩
  have hi' : i < nodes.length := List.mem_range.1 hi
  rw [List.length_drop]
  omega

def firstStmtComplete {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) (i : Nat) : Bool :=
  decide ((nodes.take (i + 1)).foldl validStep (true, 1) = (true, 0))

theorem firstStmtComplete_primrec (tc : Turing.ToPartrec.Code) :
    Primrec₂ (firstStmtComplete (tc := tc)) := by
  apply Primrec₂.mk
  let takePrefix :
      List (PartrecStartedTM1StmtNode tc) × Nat → List (PartrecStartedTM1StmtNode tc) :=
    fun p => p.1.take (p.2 + 1)
  have htake : Primrec takePrefix :=
    Primrec.list_take.comp (Primrec.succ.comp Primrec.snd) Primrec.fst
  have hfold : Primrec (fun p : List (PartrecStartedTM1StmtNode tc) × Nat =>
      (takePrefix p).foldl validStep (true, 1)) :=
    Primrec.list_foldl htake (Primrec.const (true, 1))
      (((validStep_primrec tc).comp Primrec.snd).to₂)
  have hpred : PrimrecPred (fun p : List (PartrecStartedTM1StmtNode tc) × Nat =>
      (takePrefix p).foldl validStep (true, 1) = (true, 0)) :=
    Primrec.eq.comp hfold (Primrec.const (true, 0))
  exact (hpred.decide).of_eq fun p => by
    simp [firstStmtComplete, takePrefix]

def firstStmtLength {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) : Nat :=
  ((List.range nodes.length).findIdx fun i => firstStmtComplete nodes i) + 1

theorem firstStmtLength_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (firstStmtLength (tc := tc)) := by
  unfold firstStmtLength
  exact Primrec.succ.comp
    (Primrec.list_findIdx (Primrec.list_range.comp Primrec.list_length)
      (firstStmtComplete_primrec tc))

def firstStmtNodes {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    List (PartrecStartedTM1StmtNode tc) :=
  nodes.take (firstStmtLength nodes)

theorem firstStmtNodes_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (firstStmtNodes (tc := tc)) := by
  unfold firstStmtNodes
  exact Primrec.list_take.comp (firstStmtLength_primrec tc) Primrec.id

def afterFirstStmtNodes {tc : Turing.ToPartrec.Code}
    (nodes : List (PartrecStartedTM1StmtNode tc)) :
    List (PartrecStartedTM1StmtNode tc) :=
  nodes.drop (firstStmtLength nodes)

theorem afterFirstStmtNodes_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (afterFirstStmtNodes (tc := tc)) := by
  unfold afterFirstStmtNodes
  exact Primrec.list_drop.comp (firstStmtLength_primrec tc) Primrec.id

theorem take_ofStmt_foldl_validStep_ne_complete {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) {k : Nat} (hk : k < (ofStmt stmt).length) :
    ((ofStmt stmt).take k).foldl validStep (true, 1) ≠ (true, 0) := by
  intro hcomplete
  have htotal := ofStmt_foldl_validStep (tc := tc) stmt 0
  simp only [Nat.zero_add] at htotal
  have hsplit :
      (ofStmt stmt).foldl validStep (true, 1) =
        ((ofStmt stmt).drop k).foldl validStep
          (((ofStmt stmt).take k).foldl validStep (true, 1)) := by
    rw [← List.foldl_append]
    rw [List.take_append_drop]
  rw [hsplit, hcomplete] at htotal
  have hdropNil :
      (ofStmt stmt).drop k = [] :=
    (foldl_validStep_true_zero_eq_true_zero_iff ((ofStmt stmt).drop k)).1 htotal
  have hdropLen : 0 < ((ofStmt stmt).drop k).length := by
    rw [List.length_drop]
    omega
  rw [hdropNil] at hdropLen
  simp at hdropLen

theorem firstStmtComplete_ofStmt_append_false {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM1StmtNode tc)) {i : Nat}
    (hi : i + 1 < (ofStmt stmt).length) :
    firstStmtComplete (ofStmt stmt ++ tail) i = false := by
  unfold firstStmtComplete
  have htake :
      (ofStmt stmt ++ tail).take (i + 1) = (ofStmt stmt).take (i + 1) := by
    exact List.take_append_of_le_length (Nat.le_of_lt hi)
  have hne := take_ofStmt_foldl_validStep_ne_complete
    (tc := tc) stmt (k := i + 1) hi
  simp [htake, hne]

theorem firstStmtComplete_ofStmt_append_last {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM1StmtNode tc)) :
    firstStmtComplete (ofStmt stmt ++ tail) ((ofStmt stmt).length - 1) = true := by
  unfold firstStmtComplete
  have hpos := ofStmt_length_pos (tc := tc) stmt
  have hsucc : (ofStmt stmt).length - 1 + 1 = (ofStmt stmt).length := by
    omega
  rw [hsucc]
  simp [ofStmt_foldl_validStep]

theorem firstStmtLength_ofStmt_append {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM1StmtNode tc)) :
    firstStmtLength (ofStmt stmt ++ tail) = (ofStmt stmt).length := by
  unfold firstStmtLength
  let n := (ofStmt stmt).length
  have hpos : 0 < n := by
    simpa [n] using ofStmt_length_pos (tc := tc) stmt
  have hidx :
      (List.range (ofStmt stmt ++ tail).length).findIdx
          (fun i => firstStmtComplete (ofStmt stmt ++ tail) i) =
        n - 1 := by
    have hlt : n - 1 < (List.range (ofStmt stmt ++ tail).length).length := by
      simp [n]
      omega
    apply (List.findIdx_eq hlt).2
    constructor
    · simpa [n] using firstStmtComplete_ofStmt_append_last
        (tc := tc) stmt tail
    · intro j hj
      have hj' : j + 1 < n := by
        omega
      simpa [n] using firstStmtComplete_ofStmt_append_false
        (tc := tc) stmt tail (i := j) hj'
  rw [hidx]
  omega

theorem firstStmtNodes_ofStmt_append {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM1StmtNode tc)) :
    firstStmtNodes (ofStmt stmt ++ tail) = ofStmt stmt := by
  unfold firstStmtNodes
  rw [firstStmtLength_ofStmt_append (tc := tc) stmt tail]
  exact List.take_left

theorem afterFirstStmtNodes_ofStmt_append {tc : Turing.ToPartrec.Code}
    (stmt : Stmt tc) (tail : List (PartrecStartedTM1StmtNode tc)) :
    afterFirstStmtNodes (ofStmt stmt ++ tail) = tail := by
  unfold afterFirstStmtNodes
  rw [firstStmtLength_ofStmt_append (tc := tc) stmt tail]
  exact List.drop_append_length

end PartrecStartedTM1StmtNode

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
