/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.NatPartrecToToPartrec
import LeanWang.PartrecToTM2Support
import LeanWang.UniversalCode

/-!
# A fixed universal Mathlib TM0 machine

Only the input of the universal evaluator varies.  In particular, none of the
finite supports below has to be computed from the source program: the evaluator
code is fixed before the TM2-to-TM1-to-TM0 translations are applied.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Semantic

open Turing

abbrev Stack := Turing.PartrecToTM2.K'
abbrev StackSymbol (_ : Stack) := Turing.PartrecToTM2.Γ'
abbrev Var := Option Turing.PartrecToTM2.Γ'

/-- Relabel the targets of a TM2 statement. -/
def relabelStmt {K : Type u} {Γ : K → Type v} {Λ : Type w} {Λ' : Type x}
    {σ : Type y} (f : Λ → Λ') :
    Turing.TM2.Stmt Γ Λ σ → Turing.TM2.Stmt Γ Λ' σ
  | .push k g q => .push k g (relabelStmt f q)
  | .peek k g q => .peek k g (relabelStmt f q)
  | .pop k g q => .pop k g (relabelStmt f q)
  | .load g q => .load g (relabelStmt f q)
  | .branch g q r => .branch g (relabelStmt f q) (relabelStmt f r)
  | .goto g => .goto (f ∘ g)
  | .halt => .halt

theorem relabelStmt_supports {K : Type u} {Γ : K → Type v}
    {Λ : Type w} {Λ' : Type x} {σ : Type y} {S : Finset Λ} {S' : Finset Λ'}
    (f : Λ → Λ') (hf : ∀ q ∈ S, f q ∈ S') :
    ∀ q : Turing.TM2.Stmt Γ Λ σ,
      Turing.TM2.SupportsStmt S q →
        Turing.TM2.SupportsStmt S' (relabelStmt f q) := by
  intro q
  induction q with
  | push _ _ _ ih => exact ih
  | peek _ _ _ ih => exact ih
  | pop _ _ _ ih => exact ih
  | load _ _ ih => exact ih
  | branch _ _ _ ihq ihr => exact fun h => ⟨ihq h.1, ihr h.2⟩
  | goto g => exact fun h v => hf (g v) (h v)
  | halt => exact fun _ => trivial

/-- Relabeling commutes with execution of one TM2 statement. -/
theorem relabelCfg_stepAux {K : Type u} {Γ : K → Type v} {Λ : Type w}
    {Λ' : Type x} {σ : Type y} [DecidableEq K] (f : Λ → Λ')
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ({ l := (Turing.TM2.stepAux q v S).l.map f
       var := (Turing.TM2.stepAux q v S).var
       stk := (Turing.TM2.stepAux q v S).stk } :
      Turing.TM2.Cfg Γ Λ' σ) =
      Turing.TM2.stepAux (relabelStmt f q) v S := by
  induction q generalizing v S with
  | push _ _ _ ih => exact ih _ _
  | peek _ _ _ ih => exact ih _ _
  | pop _ _ _ ih => exact ih _ _
  | load _ _ ih => exact ih _ _
  | branch p _ _ ihq ihr =>
      cases h : p v <;> simp [Turing.TM2.stepAux, relabelStmt, h, ihq, ihr]
  | goto _ => rfl
  | halt => rfl

/-- The fixed list-language universal evaluator. -/
def code : Turing.ToPartrec.Code :=
  NatPartrecToToPartrec.translate UniversalCode.universalCode

/-- A wrapper whose default value is the fixed evaluator's start label. -/
structure Label where
  val : Turing.PartrecToTM2.Λ'

namespace Label

def wrap (q : Turing.PartrecToTM2.Λ') : Label := ⟨q⟩

@[simp] theorem wrap_val (q : Turing.PartrecToTM2.Λ') : (wrap q).val = q := rfl

theorem wrap_injective : Function.Injective wrap := by
  intro q r h
  cases h
  rfl

instance : Inhabited Label :=
  ⟨wrap (PartrecToTM2Support.startLabel code)⟩

instance : DecidableEq Label := Classical.decEq Label

end Label

/-- The fixed evaluator with its start label installed as `default`. -/
def tm2 : Label → Turing.TM2.Stmt StackSymbol Label Var :=
  fun q => relabelStmt Label.wrap (Turing.PartrecToTM2.tr q.val)

/-- Its fixed finite set of reachable labels. -/
def tm2Support : Finset Label :=
  (PartrecToTM2Support.labels code).map ⟨Label.wrap, Label.wrap_injective⟩

theorem mem_tm2Support (q : Label) :
    q ∈ tm2Support ↔ q.val ∈ PartrecToTM2Support.labels code := by
  constructor
  · rintro h
    rcases Finset.mem_map.1 h with ⟨r, hr, hq⟩
    cases hq
    exact hr
  · intro h
    exact Finset.mem_map.2 ⟨q.val, h, by cases q; rfl⟩

theorem tm2_supports : Turing.TM2.Supports tm2 tm2Support := by
  constructor
  · exact Finset.mem_map.2
      ⟨PartrecToTM2Support.startLabel code,
        PartrecToTM2Support.startLabel_mem_labels code, rfl⟩
  · intro q hq
    exact relabelStmt_supports Label.wrap
      (fun r hr => (mem_tm2Support (Label.wrap r)).2 hr)
      (Turing.PartrecToTM2.tr q.val)
      ((PartrecToTM2Support.tr_supports_labels code).2 q.val
        ((mem_tm2Support q).1 hq))

/-- Mathlib's standard finite-support TM2-to-TM1 translation, applied once. -/
def tm1 := Turing.TM2to1.tr tm2

def tm1Support := Turing.TM2to1.trSupp tm2 tm2Support

theorem tm1_supports : Turing.TM1.Supports tm1 tm1Support :=
  Turing.TM2to1.tr_supports (M := tm2) tm2_supports

/-- Mathlib's standard finite-support TM1-to-TM0 translation, applied once. -/
def tm0 := Turing.TM1to0.tr tm1

def tm0Support := Turing.TM1to0.trStmts tm1 tm1Support

theorem tm0_supports : Turing.TM0.Supports tm0 (tm0Support : Set _) :=
  Turing.TM1to0.tr_supports (M := tm1) tm1_supports

private theorem trNum_eq (n : Num) :
    Turing.PartrecToTM2.trNum n =
      if (n : Nat) = 0 then []
      else
        (if (n : Nat).bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) ::
            Turing.PartrecToTM2.trNat (n : Nat).div2 := by
  cases n with
  | zero => rfl
  | pos n =>
      cases n with
      | one => rfl
      | bit0 a =>
          have hpos : (a : Nat) ≠ 0 := Nat.ne_of_gt (PosNum.cast_pos a)
          have hdiv : ((a : Nat) + (a : Nat)).div2 = (a : Nat) := by
            rw [Nat.div2_val, ← two_mul]
            simp
          have htr : Turing.PartrecToTM2.trNat (a : Nat) =
              Turing.PartrecToTM2.trPosNum a := by
            simp [Turing.PartrecToTM2.trNat, Turing.PartrecToTM2.trNum]
          simp [Turing.PartrecToTM2.trNum, Turing.PartrecToTM2.trPosNum,
            hpos, hdiv, htr]
      | bit1 a =>
          have hpos : (a : Nat) ≠ 0 := Nat.ne_of_gt (PosNum.cast_pos a)
          have hdiv : ((a : Nat) + (a : Nat)).div2 = (a : Nat) := by
            rw [Nat.div2_val, ← two_mul]
            simp
          have htr : Turing.PartrecToTM2.trNat (a : Nat) =
              Turing.PartrecToTM2.trPosNum a := by
            simp [Turing.PartrecToTM2.trNat, Turing.PartrecToTM2.trNum]
          simp [Turing.PartrecToTM2.trNum, Turing.PartrecToTM2.trPosNum,
            hpos, hdiv, htr]

private theorem trNat_eq (n : Nat) :
    Turing.PartrecToTM2.trNat n =
      if n = 0 then []
      else
        (if n.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) ::
            Turing.PartrecToTM2.trNat n.div2 := by
  simpa [Turing.PartrecToTM2.trNat] using trNum_eq (n : Num)

private def trNatStep (prior : List (List Turing.PartrecToTM2.Γ')) :
    Option (List Turing.PartrecToTM2.Γ') :=
  let n := prior.length
  if n = 0 then some []
  else
    prior[n.div2]?.map fun tail =>
      (if n.bodd then Turing.PartrecToTM2.Γ'.bit1
        else Turing.PartrecToTM2.Γ'.bit0) :: tail

private theorem trNatStep_primrec : Primrec trNatStep := by
  unfold trNatStep
  have hn : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior.length) := Primrec.list_length
  have hzero : PrimrecPred (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior.length = 0) := Primrec.eq.comp hn (Primrec.const 0)
  have hlookup : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior[prior.length.div2]?) :=
    Primrec.list_getElem?.comp Primrec.id (Primrec.nat_div2.comp hn)
  have hdigit : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      if prior.length.bodd then Turing.PartrecToTM2.Γ'.bit1
      else Turing.PartrecToTM2.Γ'.bit0) :=
    (Primrec.cond (Primrec.nat_bodd.comp hn)
      (Primrec.const Turing.PartrecToTM2.Γ'.bit1)
      (Primrec.const Turing.PartrecToTM2.Γ'.bit0)).of_eq fun prior => by
        cases prior.length.bodd <;> simp
  have hcons : Primrec₂ (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      fun tail : List Turing.PartrecToTM2.Γ' =>
        (if prior.length.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) :: tail) := by
    apply Primrec₂.mk
    exact Primrec.list_cons.comp (hdigit.comp Primrec.fst) Primrec.snd
  have hnext : Primrec (fun prior : List (List Turing.PartrecToTM2.Γ') =>
      prior[prior.length.div2]?.map fun tail =>
        (if prior.length.bodd then Turing.PartrecToTM2.Γ'.bit1
          else Turing.PartrecToTM2.Γ'.bit0) :: tail) :=
    Primrec.option_map hlookup hcons
  exact Primrec.ite hzero
    (Primrec.const (some ([] : List Turing.PartrecToTM2.Γ'))) hnext

private theorem trNat_primrec : Primrec Turing.PartrecToTM2.trNat := by
  have hrec : Primrec₂ (fun _ : Unit => Turing.PartrecToTM2.trNat) :=
    Primrec.nat_strong_rec
      (fun _ : Unit => Turing.PartrecToTM2.trNat)
      (show Primrec₂ (fun _ : Unit => fun prior => trNatStep prior) from
        Primrec₂.mk (trNatStep_primrec.comp
          (Primrec.snd : Primrec
            (fun p : Unit × List (List Turing.PartrecToTM2.Γ') => p.2))))
      (by
        intro _ n
        unfold trNatStep
        simp only [List.length_map, List.length_range]
        by_cases hn : n = 0
        · subst n
          simp [trNat_eq]
        · have hlt : n.div2 < n := Nat.binaryRec_decreasing hn
          rw [if_neg hn, trNat_eq n, if_neg hn]
          simp [List.getElem?_map, List.getElem?_range hlt])
  exact hrec.comp (Primrec.const ()) Primrec.id

private def stackVectorEquiv :
    (∀ _ : Stack, Option Turing.PartrecToTM2.Γ') ≃
      Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' ×
        Option Turing.PartrecToTM2.Γ' × Option Turing.PartrecToTM2.Γ' where
  toFun f := (f .main, f .rev, f .aux, f .stack)
  invFun p
    | .main => p.1
    | .rev => p.2.1
    | .aux => p.2.2.1
    | .stack => p.2.2.2
  left_inv f := by
    funext k
    cases k <;> rfl
  right_inv p := by
    rcases p with ⟨a, b, c, d⟩
    rfl

private instance instPrimcodableStackVector :
    Primcodable (∀ _ : Stack, Option Turing.PartrecToTM2.Γ') :=
  Primcodable.ofEquiv _ stackVectorEquiv

private instance instPrimcodableSourceSymbol :
    Primcodable (Turing.TM2to1.Γ' Stack StackSymbol) :=
  inferInstanceAs
    (Primcodable (Bool × (∀ _ : Stack, Option Turing.PartrecToTM2.Γ')))

private def rawInput (n : Nat) :=
  Turing.TM2to1.trInit (Γ := StackSymbol) Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList [n])

private theorem rawInput_primrec : Primrec rawInput := by
  have hstack : Primrec (fun n : Nat => Turing.PartrecToTM2.trList [n]) := by
    unfold Turing.PartrecToTM2.trList
    simpa using Primrec.list_append.comp trNat_primrec
      (Primrec.const [Turing.PartrecToTM2.Γ'.cons])
  let cell : Turing.PartrecToTM2.Γ' →
      Turing.TM2to1.Γ' Stack StackSymbol := fun a =>
    (false, Function.update (fun _ : Stack => none)
      Turing.PartrecToTM2.K'.main (some a))
  have hcell : Primrec cell := Primrec.dom_finite cell
  have hmapped : Primrec (fun n =>
      (Turing.PartrecToTM2.trList [n]).reverse.map cell) := by
    refine Primrec.list_map (Primrec.list_reverse.comp hstack) ?_
    exact Primrec₂.mk (hcell.comp Primrec.snd)
  let mark : Turing.TM2to1.Γ' Stack StackSymbol →
      Turing.TM2to1.Γ' Stack StackSymbol := fun a => (true, a.2)
  have hmark : Primrec mark := Primrec.dom_finite mark
  exact (Primrec.list_cons.comp
    (hmark.comp (Primrec.list_headI.comp hmapped))
    (Primrec.list_tail.comp hmapped)).of_eq fun n => by rfl

/-- Numeric input supplied to the fixed universal evaluator. -/
def sourceInput (c : Nat.Partrec.Code) : Nat := Nat.pair (Encodable.encode c) 0

theorem sourceInput_primrec : Primrec sourceInput := by
  exact Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)

theorem sourceInput_computable : Computable sourceInput := sourceInput_primrec.to_comp

/-- The tape input passed through Mathlib's two fixed machine translations. -/
def input (c : Nat.Partrec.Code) :=
  Turing.TM2to1.trInit (Γ := StackSymbol) Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList [sourceInput c])

theorem input_primrec : Primrec input := rawInput_primrec.comp sourceInput_primrec

theorem input_computable : Computable input := input_primrec.to_comp

theorem tm2_eval_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM2.eval tm2 Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList [sourceInput c])).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  let originalInit := Turing.PartrecToTM2.init code [sourceInput c]
  let relabeledInit : Turing.TM2.Cfg StackSymbol Label Var :=
    { l := (originalInit.l.map Label.wrap)
      var := originalInit.var
      stk := originalInit.stk }
  have hinit : relabeledInit =
      Turing.TM2.init Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [sourceInput c]) := by
    change
      (Turing.TM2.Cfg.mk
        (some (Label.wrap (PartrecToTM2Support.startLabel code)))
        (none : Var)
        (Turing.PartrecToTM2.K'.elim
          (Turing.PartrecToTM2.trList [sourceInput c]) [] [] []) :
          Turing.TM2.Cfg StackSymbol Label Var) =
      Turing.TM2.Cfg.mk (some (default : Label)) (default : Var)
        (Function.update (fun _ : Stack => []) Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList [sourceInput c]))
    rw [Turing.TM2.Cfg.mk.injEq]
    refine ⟨rfl, rfl, ?_⟩
    funext k
    cases k <;> simp
  have hstep : StateTransition.Respects
      (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.TM2.step tm2)
      (fun a b =>
        ({ l := a.l.map Label.wrap, var := a.var, stk := a.stk } :
          Turing.TM2.Cfg StackSymbol Label Var) = b) := by
    intro a b hab
    subst b
    cases a with
    | mk l var stk =>
      cases l with
      | none => rfl
      | some q =>
        refine ⟨_, rfl, Relation.TransGen.single ?_⟩
        exact congrArg some
          (relabelCfg_stepAux Label.wrap (Turing.PartrecToTM2.tr q) var stk).symm
  rw [Turing.TM2.eval]
  rw [show Turing.TM2.init Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList [sourceInput c]) = relabeledInit from hinit.symm]
  change (Part.map (fun c => c.stk Turing.PartrecToTM2.K'.main)
      (StateTransition.eval (Turing.TM2.step tm2) relabeledInit)).Dom ↔ _
  rw [show (Part.map (fun c => c.stk Turing.PartrecToTM2.K'.main)
      (StateTransition.eval (Turing.TM2.step tm2) relabeledInit)).Dom ↔
      (StateTransition.eval (Turing.TM2.step tm2) relabeledInit).Dom by rfl]
  rw [show (StateTransition.eval (Turing.TM2.step tm2) relabeledInit).Dom ↔
      (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr) originalInit).Dom from
    StateTransition.tr_eval_dom hstep rfl]
  change (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init
        (NatPartrecToToPartrec.translate UniversalCode.universalCode)
        [sourceInput c])).Dom ↔ _
  rw [NatPartrecToToPartrec.translate_tm2_dom_at]
  rw [sourceInput, UniversalCode.universalCode_eval]

theorem tm0_eval_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM0.eval tm0 (input c)).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  rw [tm0, Turing.TM1to0.tr_eval]
  exact (Turing.TM2to1.tr_eval_dom tm2 Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList [sourceInput c])).trans (tm2_eval_dom_iff c)

end UniversalTM0Semantic
end LeanWang
