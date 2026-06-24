/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachine
import LeanWang.TM0FiniteCompiler
import LeanWang.ToPartrecEncoding

/-!
Executable finite one-sided TM0 program data for a folded simulation of Mathlib's TM0.

Mathlib's Turing.TM0 configurations use a two-sided tape. The local
FiniteTM0Program model used by the current Wang-tile layer has a one-sided
Nat-indexed tape. This module contains the concrete folded alphabet, states,
transition rows, and finite program data.
-/
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

abbrev SourceSymbol : Type :=
  Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol

abbrev SourceLabel (tc : Turing.ToPartrec.Code) : Type :=
  Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)

abbrev SourceStmt (tc : Turing.ToPartrec.Code) : Type :=
  TM0Route.PartrecStartedTM0Stmt tc

abbrev SourceStmtNode (tc : Turing.ToPartrec.Code) : Type :=
  TM0Route.PartrecStartedTM1StmtNode tc

abbrev SourceStmtNodes (tc : Turing.ToPartrec.Code) : Type :=
  List (SourceStmtNode tc)

abbrev EncodedTrAuxDep (tc : Turing.ToPartrec.Code) : Type :=
  SourceStmtNodes tc × PartrecVar × SourceSymbol

/-- Mathlib's default/start label for the TM1-to-TM0 translated machine. -/
def sourceDefaultLabel (tc : Turing.ToPartrec.Code) : SourceLabel tc :=
  (some (TM0Route.partrecStartedTM1Machine tc default), default)

theorem sourceDefaultLabel_eq_default (tc : Turing.ToPartrec.Code) :
    sourceDefaultLabel tc = (default : SourceLabel tc) := by
  rfl

/-- Which half of a folded one-sided cell is the simulated two-sided head reading? -/
inductive FoldSide where
  | left
  | right
deriving DecidableEq, Repr

namespace FoldSide

def toBool : FoldSide → Bool
  | left => false
  | right => true

def ofBool : Bool → FoldSide
  | false => left
  | true => right

def equivBool : FoldSide ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := by
    intro side
    cases side <;> rfl
  right_inv := by
    intro bit
    cases bit <;> rfl

def code : FoldSide → Nat
  | left => 0
  | right => 1

end FoldSide

instance instPrimcodableFoldSide : Primcodable FoldSide :=
  Primcodable.ofEquiv Bool FoldSide.equivBool

def foldSideList : List FoldSide :=
  [FoldSide.left, FoldSide.right]

theorem foldSideList_nodup : foldSideList.Nodup := by
  simp [foldSideList]

theorem mem_foldSideList (s : FoldSide) : s ∈ foldSideList := by
  cases s <;> simp [foldSideList]

instance instFintypeFoldSide : Fintype FoldSide where
  elems := ⟨foldSideList, foldSideList_nodup⟩
  complete := mem_foldSideList

namespace FoldSide

theorem toBool_primrec : Primrec FoldSide.toBool := by
  simpa [FoldSide.equivBool] using
    (Primrec.of_equiv (e := FoldSide.equivBool) : Primrec FoldSide.equivBool)

theorem ofBool_primrec : Primrec FoldSide.ofBool := by
  simpa [FoldSide.equivBool] using
    (Primrec.of_equiv_symm (e := FoldSide.equivBool) :
      Primrec FoldSide.equivBool.symm)

theorem code_primrec : Primrec FoldSide.code := by
  refine (Primrec.cond toBool_primrec (Primrec.const 1) (Primrec.const 0)).of_eq ?_
  intro side
  cases side <;> rfl

end FoldSide

/-- Boolean code for Mathlib tape directions. -/
def dirToBool : Turing.Dir → Bool
  | Turing.Dir.left => false
  | Turing.Dir.right => true

def dirOfBool : Bool → Turing.Dir
  | false => Turing.Dir.left
  | true => Turing.Dir.right

def dirEquivBool : Turing.Dir ≃ Bool where
  toFun := dirToBool
  invFun := dirOfBool
  left_inv := by
    intro dir
    cases dir <;> rfl
  right_inv := by
    intro bit
    cases bit <;> rfl

instance instPrimcodableTuringDir : Primcodable Turing.Dir :=
  Primcodable.ofEquiv Bool dirEquivBool

def dirList : List Turing.Dir :=
  [Turing.Dir.left, Turing.Dir.right]

theorem dirList_nodup : dirList.Nodup := by
  simp [dirList]

theorem mem_dirList (dir : Turing.Dir) : dir ∈ dirList := by
  cases dir <;> simp [dirList]

instance instFintypeTuringDir : Fintype Turing.Dir where
  elems := ⟨dirList, dirList_nodup⟩
  complete := mem_dirList

def tm0StmtToSum : Turing.TM0.Stmt SourceSymbol → Turing.Dir ⊕ SourceSymbol
  | Turing.TM0.Stmt.move dir => Sum.inl dir
  | Turing.TM0.Stmt.write a => Sum.inr a

def tm0StmtOfSum : Turing.Dir ⊕ SourceSymbol → Turing.TM0.Stmt SourceSymbol
  | Sum.inl dir => Turing.TM0.Stmt.move dir
  | Sum.inr a => Turing.TM0.Stmt.write a

def tm0StmtEquivSum : Turing.TM0.Stmt SourceSymbol ≃ Turing.Dir ⊕ SourceSymbol where
  toFun := tm0StmtToSum
  invFun := tm0StmtOfSum
  left_inv := by
    intro stmt
    cases stmt <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

instance instPrimcodableSourceTM0Stmt :
    Primcodable (Turing.TM0.Stmt SourceSymbol) :=
  Primcodable.ofEquiv (Turing.Dir ⊕ SourceSymbol) tm0StmtEquivSum

theorem tm0StmtToSum_primrec : Primrec tm0StmtToSum := by
  simpa [tm0StmtEquivSum] using
    (Primrec.of_equiv (e := tm0StmtEquivSum) : Primrec tm0StmtEquivSum)

theorem tm0StmtOfSum_primrec : Primrec tm0StmtOfSum := by
  simpa [tm0StmtEquivSum] using
    (Primrec.of_equiv_symm (e := tm0StmtEquivSum) :
      Primrec tm0StmtEquivSum.symm)

theorem tm0StmtMove_primrec : Primrec (Turing.TM0.Stmt.move (Γ := SourceSymbol)) := by
  exact tm0StmtOfSum_primrec.comp Primrec.sumInl

theorem tm0StmtWrite_primrec : Primrec (Turing.TM0.Stmt.write (Γ := SourceSymbol)) := by
  exact tm0StmtOfSum_primrec.comp Primrec.sumInr

def trAuxMeasure (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) : Nat :=
  (TM0Route.PartrecStartedTM1StmtNode.ofStmt p.1).length

theorem trAuxMeasure_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxMeasure tc) := by
  unfold trAuxMeasure
  exact (TM0Route.PartrecStartedTM1StmtNode.ofStmt_length_primrec tc).comp Primrec.fst

def trAuxDeps (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) :
    List (SourceStmt tc × PartrecVar × SourceSymbol) :=
  match p with
  | (Turing.TM1.Stmt.move _ _, _, _) => []
  | (Turing.TM1.Stmt.write _ _, _, _) => []
  | (Turing.TM1.Stmt.load f q, v, a) => [(q, f a v, a)]
  | (Turing.TM1.Stmt.branch f q₁ q₂, v, a) =>
      if f a v then [(q₁, v, a)] else [(q₂, v, a)]
  | (Turing.TM1.Stmt.goto _, _, _) => []
  | (Turing.TM1.Stmt.halt, _, _) => []

def encodedTrAuxDepSingleton {tc : Turing.ToPartrec.Code}
    (nodes : SourceStmtNodes tc) (v : PartrecVar) (a : SourceSymbol) :
    List (EncodedTrAuxDep tc) :=
  [(nodes, v, a)]

theorem encodedTrAuxDepSingleton_primrec (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : SourceStmtNodes tc × PartrecVar × SourceSymbol =>
      encodedTrAuxDepSingleton p.1 p.2.1 p.2.2) := by
  unfold encodedTrAuxDepSingleton
  exact Primrec.list_cons.comp Primrec.id (Primrec.const [])

def trAuxDepsNodeDataOfCode (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol)
    (code : TM0Route.PartrecStartedTM1StmtNode.Code tc) : List (EncodedTrAuxDep tc) :=
  let tail := TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1
  match code with
  | Sum.inr (Sum.inr (Sum.inl f)) =>
      encodedTrAuxDepSingleton tail (f p.2.2 p.2.1) p.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl f))) =>
      if f p.2.2 p.2.1 then
        encodedTrAuxDepSingleton
          (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes tail) p.2.1 p.2.2
      else
        encodedTrAuxDepSingleton
          (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes tail) p.2.1 p.2.2
  | _ => []

def trAuxDepsNodeDataOfHead (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol)
    (node : SourceStmtNode tc) : List (EncodedTrAuxDep tc) :=
  let tail := TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1
  match node with
  | TM0Route.PartrecStartedTM1StmtNode.load f =>
      encodedTrAuxDepSingleton tail (f p.2.2 p.2.1) p.2.2
  | TM0Route.PartrecStartedTM1StmtNode.branch f =>
      if f p.2.2 p.2.1 then
        encodedTrAuxDepSingleton
          (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes tail) p.2.1 p.2.2
      else
        encodedTrAuxDepSingleton
          (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes tail) p.2.1 p.2.2
  | _ => []

theorem trAuxDepsNodeDataOfCode_toCode
    (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol)
    (node : SourceStmtNode tc) :
    trAuxDepsNodeDataOfCode tc p
        (TM0Route.PartrecStartedTM1StmtNode.toCode node) =
      trAuxDepsNodeDataOfHead tc p node := by
  cases node <;> rfl

set_option maxHeartbeats 800000 in
-- Nested case analysis over the encoded TM1 statement node sum type is expensive to elaborate.
theorem trAuxDepsNodeDataOfCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p :
      (SourceStmt tc × PartrecVar × SourceSymbol) ×
          TM0Route.PartrecStartedTM1StmtNode.Code tc =>
        trAuxDepsNodeDataOfCode tc p.1 p.2) := by
  have hload : Primrec₂
      (fun p :
        (SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc =>
        fun f : SourceSymbol → PartrecVar → PartrecVar =>
          encodedTrAuxDepSingleton
            (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1)
            (f p.1.2.2 p.1.2.1) p.1.2.2) := by
    apply Primrec₂.mk
    have hstmt : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → PartrecVar) =>
          p.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have htail : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → PartrecVar) =>
          TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1) :=
      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail_primrec tc).comp hstmt
    have hv : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → PartrecVar) =>
          p.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have ha : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → PartrecVar) =>
          p.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have happ : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → PartrecVar) =>
          p.2 p.1.1.2.2 p.1.1.2.1) :=
      (TM0Route.partrecStartedTM0SymbolPartrecVarFunction_app_primrec PartrecVar).comp
        (Primrec.pair Primrec.snd (Primrec.pair ha hv))
    exact (encodedTrAuxDepSingleton_primrec tc).comp
      (Primrec.pair htail (Primrec.pair happ ha))
  have hbranch : Primrec₂
      (fun p :
        (SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc =>
        fun f : SourceSymbol → PartrecVar → Bool =>
          if f p.1.2.2 p.1.2.1 then
            encodedTrAuxDepSingleton
              (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
              p.1.2.1 p.1.2.2
          else
            encodedTrAuxDepSingleton
              (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
              p.1.2.1 p.1.2.2) := by
    apply Primrec₂.mk
    have hstmt : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          p.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have htail : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1) :=
      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail_primrec tc).comp hstmt
    have hfirst : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
            (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1)) :=
      (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes_primrec tc).comp htail
    have hafter : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
            (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1)) :=
      (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes_primrec tc).comp htail
    have hv : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          p.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have ha : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          p.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hcond : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          p.2 p.1.1.2.2 p.1.1.2.1) :=
      (TM0Route.partrecStartedTM0SymbolPartrecVarFunction_app_primrec Bool).comp
        (Primrec.pair Primrec.snd (Primrec.pair ha hv))
    have hthen : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          encodedTrAuxDepSingleton
            (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
              (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
            p.1.1.2.1 p.1.1.2.2) :=
      (encodedTrAuxDepSingleton_primrec tc).comp
        (Primrec.pair hfirst (Primrec.pair hv ha))
    have helse : Primrec (fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            (SourceSymbol → PartrecVar → Bool) =>
          encodedTrAuxDepSingleton
            (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
              (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
            p.1.1.2.1 p.1.1.2.2) :=
      (encodedTrAuxDepSingleton_primrec tc).comp
        (Primrec.pair hafter (Primrec.pair hv ha))
    exact (Primrec.cond hcond hthen helse).of_eq fun p => by
      by_cases h : p.2 p.1.1.2.2 p.1.1.2.1 <;> simp [h]
  have hbranchTail : Primrec₂
      (fun p :
        (SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc =>
        fun c : TM0Route.PartrecStartedTM1StmtNode.BranchTailCode tc =>
          match c with
          | Sum.inl f => if f p.1.2.2 p.1.2.1 then
              encodedTrAuxDepSingleton
                (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                  (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                p.1.2.1 p.1.2.2
            else
              encodedTrAuxDepSingleton
                (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                  (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                p.1.2.1 p.1.2.2
          | Sum.inr _ => []) := by
    apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (f := fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            TM0Route.PartrecStartedTM1StmtNode.BranchTailCode tc => p.2)
      (g := fun p f =>
        if f p.1.1.2.2 p.1.1.2.1 then
          encodedTrAuxDepSingleton
            (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
              (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
            p.1.1.2.1 p.1.1.2.2
        else
          encodedTrAuxDepSingleton
            (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
              (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
            p.1.1.2.1 p.1.1.2.2)
      (h := fun _ _ => ([] : List (EncodedTrAuxDep tc)))
      Primrec.snd
      (hbranch.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (Primrec.const []).to₂).of_eq ?_
    intro p
    cases p.2 <;> rfl
  have hloadTail : Primrec₂
      (fun p :
        (SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc =>
        fun c : TM0Route.PartrecStartedTM1StmtNode.LoadTailCode tc =>
          match c with
          | Sum.inl f =>
              encodedTrAuxDepSingleton
                (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1)
                (f p.1.2.2 p.1.2.1) p.1.2.2
          | Sum.inr c => match c with
              | Sum.inl f => if f p.1.2.2 p.1.2.1 then
                  encodedTrAuxDepSingleton
                    (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                    p.1.2.1 p.1.2.2
                else
                  encodedTrAuxDepSingleton
                    (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                    p.1.2.1 p.1.2.2
              | Sum.inr _ => []) := by
    apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (f := fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            TM0Route.PartrecStartedTM1StmtNode.LoadTailCode tc => p.2)
      (g := fun p f =>
        encodedTrAuxDepSingleton
          (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1)
          (f p.1.1.2.2 p.1.1.2.1) p.1.1.2.2)
      (h := fun p c =>
        match c with
        | Sum.inl f => if f p.1.1.2.2 p.1.1.2.1 then
            encodedTrAuxDepSingleton
              (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
              p.1.1.2.1 p.1.1.2.2
          else
            encodedTrAuxDepSingleton
              (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
              p.1.1.2.1 p.1.1.2.2
        | Sum.inr _ => [])
      Primrec.snd
      (hload.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (hbranchTail.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).of_eq ?_
    intro p
    cases p.2 <;> rfl
  have hwriteTail : Primrec₂
      (fun p :
        (SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc =>
        fun c : TM0Route.PartrecStartedTM1StmtNode.WriteTailCode tc =>
          match c with
          | Sum.inl _ => []
          | Sum.inr c => match c with
              | Sum.inl f =>
                  encodedTrAuxDepSingleton
                    (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1)
                    (f p.1.2.2 p.1.2.1) p.1.2.2
              | Sum.inr c => match c with
                  | Sum.inl f => if f p.1.2.2 p.1.2.1 then
                      encodedTrAuxDepSingleton
                        (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                          (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                        p.1.2.1 p.1.2.2
                    else
                      encodedTrAuxDepSingleton
                        (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                          (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                        p.1.2.1 p.1.2.2
                  | Sum.inr _ => []) := by
    apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (f := fun p :
        ((SourceStmt tc × PartrecVar × SourceSymbol) ×
            TM0Route.PartrecStartedTM1StmtNode.Code tc) ×
            TM0Route.PartrecStartedTM1StmtNode.WriteTailCode tc => p.2)
      (g := fun _ _ => ([] : List (EncodedTrAuxDep tc)))
      (h := fun p c =>
        match c with
        | Sum.inl f =>
            encodedTrAuxDepSingleton
              (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1)
              (f p.1.1.2.2 p.1.1.2.1) p.1.1.2.2
        | Sum.inr c => match c with
            | Sum.inl f => if f p.1.1.2.2 p.1.1.2.1 then
                encodedTrAuxDepSingleton
                  (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                    (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
                  p.1.1.2.1 p.1.1.2.2
              else
                encodedTrAuxDepSingleton
                  (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                    (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1.1))
                  p.1.1.2.1 p.1.1.2.2
            | Sum.inr _ => [])
      Primrec.snd (Primrec.const []).to₂
      (hloadTail.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).of_eq ?_
    intro p
    cases p.2 <;> rfl
  refine (Primrec.sumCasesOn
    (f := fun p :
      (SourceStmt tc × PartrecVar × SourceSymbol) ×
          TM0Route.PartrecStartedTM1StmtNode.Code tc => p.2)
    (g := fun _ _ => ([] : List (EncodedTrAuxDep tc)))
    (h := fun p c =>
      match c with
      | Sum.inl _ => []
      | Sum.inr c => match c with
          | Sum.inl f =>
              encodedTrAuxDepSingleton
                (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1)
                (f p.1.2.2 p.1.2.1) p.1.2.2
          | Sum.inr c => match c with
              | Sum.inl f => if f p.1.2.2 p.1.2.1 then
                  encodedTrAuxDepSingleton
                    (TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes
                      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                    p.1.2.1 p.1.2.2
                else
                  encodedTrAuxDepSingleton
                    (TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes
                      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail p.1.1))
                    p.1.2.1 p.1.2.2
              | Sum.inr _ => [])
    Primrec.snd (Primrec.const []).to₂ hwriteTail).of_eq ?_
  intro p
  cases p.2 with
  | inl _ =>
      rfl
  | inr c =>
      cases c with
      | inl _ =>
          rfl
      | inr c =>
          cases c with
          | inl _ =>
              rfl
          | inr c =>
              cases c with
              | inl _ =>
                  rfl
              | inr c =>
                  cases c <;> rfl

theorem trAuxDepsNodeDataOfHead_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : (SourceStmt tc × PartrecVar × SourceSymbol) × SourceStmtNode tc =>
      trAuxDepsNodeDataOfHead tc p.1 p.2) := by
  have hcode : Primrec (fun p :
      (SourceStmt tc × PartrecVar × SourceSymbol) × SourceStmtNode tc =>
        TM0Route.PartrecStartedTM1StmtNode.toCode p.2) :=
    (TM0Route.PartrecStartedTM1StmtNode.toCode_primrec tc).comp Primrec.snd
  exact ((trAuxDepsNodeDataOfCode_primrec_fixed tc).comp
    (Primrec.pair Primrec.fst hcode)).of_eq fun p => by
      rw [trAuxDepsNodeDataOfCode_toCode]

def trAuxDepsNodeData (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) : List (EncodedTrAuxDep tc) :=
  match TM0Route.PartrecStartedTM1StmtNode.ofStmtHead? p.1 with
  | none => []
  | some node => trAuxDepsNodeDataOfHead tc p node

theorem trAuxDepsNodeData_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxDepsNodeData tc) := by
  have hhead : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      TM0Route.PartrecStartedTM1StmtNode.ofStmtHead? p.1) :=
    (TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?_primrec tc).comp Primrec.fst
  have hnone : Primrec (fun _p : SourceStmt tc × PartrecVar × SourceSymbol =>
      ([] : List (EncodedTrAuxDep tc))) :=
    Primrec.const []
  have hsome : Primrec₂
      (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
        fun node : SourceStmtNode tc => trAuxDepsNodeDataOfHead tc p node) := by
    apply Primrec₂.mk
    exact trAuxDepsNodeDataOfHead_primrec_fixed tc
  exact (Primrec.option_casesOn hhead hnone hsome).of_eq fun p => by
    generalize h :
      TM0Route.PartrecStartedTM1StmtNode.ofStmtHead? p.1 = head
    cases head <;> simp [trAuxDepsNodeData, h]

def trAuxDepsEncoded (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) : List (EncodedTrAuxDep tc) :=
  (trAuxDeps tc p).map fun p' =>
    (TM0Route.PartrecStartedTM1StmtNode.ofStmt p'.1, p'.2.1, p'.2.2)

theorem trAuxDepsNodeData_eq_encoded
    (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) :
    trAuxDepsNodeData tc p = trAuxDepsEncoded tc p := by
  rcases p with ⟨stmt, v, a⟩
  cases stmt with
  | move d q =>
      rfl
  | write f q =>
      rfl
  | load f q =>
      simp [trAuxDepsNodeData, trAuxDepsNodeDataOfHead, trAuxDepsEncoded,
        trAuxDeps, TM0Route.PartrecStartedTM1StmtNode.ofStmt,
        TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?,
        TM0Route.PartrecStartedTM1StmtNode.ofStmtTail,
        encodedTrAuxDepSingleton]
  | branch f q₁ q₂ =>
      by_cases h : f a v
      · simp [trAuxDepsNodeData, trAuxDepsNodeDataOfHead, trAuxDepsEncoded,
          trAuxDeps, h, TM0Route.PartrecStartedTM1StmtNode.ofStmt,
          TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?,
          TM0Route.PartrecStartedTM1StmtNode.ofStmtTail,
          TM0Route.PartrecStartedTM1StmtNode.firstStmtNodes_ofStmt_append,
          encodedTrAuxDepSingleton]
      · simp [trAuxDepsNodeData, trAuxDepsNodeDataOfHead, trAuxDepsEncoded,
          trAuxDeps, h, TM0Route.PartrecStartedTM1StmtNode.ofStmt,
          TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?,
          TM0Route.PartrecStartedTM1StmtNode.ofStmtTail,
          TM0Route.PartrecStartedTM1StmtNode.afterFirstStmtNodes_ofStmt_append,
          encodedTrAuxDepSingleton]
  | goto f =>
      rfl
  | halt =>
      rfl

/-- A total proof-carrying wrapper for encoded `trAux` dependency statement nodes. -/
noncomputable def encodedTrAuxDepValidCode (tc : Turing.ToPartrec.Code)
    (dep : EncodedTrAuxDep tc) :
    TM0Route.PartrecStartedTM1StmtNode.ValidCode tc :=
  if h : TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1 then
    ⟨dep.1, h⟩
  else
    TM0Route.PartrecStartedTM1StmtNode.toValidCode
      (Turing.TM1.Stmt.halt : SourceStmt tc)

theorem encodedTrAuxDepValidCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (encodedTrAuxDepValidCode tc) := by
  letI : Primcodable (TM0Route.PartrecStartedTM1StmtNode.ValidCode tc) :=
    TM0Route.PartrecStartedTM1StmtNode.instPrimcodableValidCode tc
  have hvalid : PrimrecPred (fun dep : EncodedTrAuxDep tc =>
      TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1) :=
    (TM0Route.PartrecStartedTM1StmtNode.valid_primrecPred tc).comp Primrec.fst
  have hval : Primrec (fun dep : EncodedTrAuxDep tc =>
      if TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1 then
        dep.1
      else
        TM0Route.PartrecStartedTM1StmtNode.ofStmt
          (Turing.TM1.Stmt.halt : SourceStmt tc)) :=
    Primrec.ite hvalid Primrec.fst
      (Primrec.const
        (TM0Route.PartrecStartedTM1StmtNode.ofStmt
          (Turing.TM1.Stmt.halt : SourceStmt tc)))
  have hval' : Primrec (fun dep : EncodedTrAuxDep tc =>
      (encodedTrAuxDepValidCode tc dep).1) :=
    hval.of_eq fun dep => by
      unfold encodedTrAuxDepValidCode
      by_cases h : TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1 <;>
        simp [h, TM0Route.PartrecStartedTM1StmtNode.toValidCode]
  exact Primrec.subtype_val_iff.1 hval'

theorem encodedTrAuxDepValidCode_ofStmt
    {tc : Turing.ToPartrec.Code} (stmt : SourceStmt tc)
    (v : PartrecVar) (a : SourceSymbol) :
    encodedTrAuxDepValidCode tc
        (TM0Route.PartrecStartedTM1StmtNode.ofStmt stmt, v, a) =
      TM0Route.PartrecStartedTM1StmtNode.toValidCode stmt := by
  apply Subtype.ext
  simp [encodedTrAuxDepValidCode,
    TM0Route.PartrecStartedTM1StmtNode.valid_ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.toValidCode]

/--
Decode one encoded dependency. Invalid statement-node lists are discarded; the
lists produced by `trAuxDepsNodeData` are all valid, so no data is lost there.
-/
noncomputable def decodeEncodedTrAuxDep? (tc : Turing.ToPartrec.Code)
    (dep : EncodedTrAuxDep tc) :
    Option (SourceStmt tc × PartrecVar × SourceSymbol) :=
  if TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1 then
    some
      (TM0Route.PartrecStartedTM1StmtNode.ofValidCode
        (encodedTrAuxDepValidCode tc dep), dep.2.1, dep.2.2)
  else
    none

theorem decodeEncodedTrAuxDep?_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (decodeEncodedTrAuxDep? tc) := by
  have hvalid : PrimrecPred (fun dep : EncodedTrAuxDep tc =>
      TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1) :=
    (TM0Route.PartrecStartedTM1StmtNode.valid_primrecPred tc).comp Primrec.fst
  have hstmt : Primrec (fun dep : EncodedTrAuxDep tc =>
      TM0Route.PartrecStartedTM1StmtNode.ofValidCode
        (encodedTrAuxDepValidCode tc dep)) :=
    (TM0Route.PartrecStartedTM1StmtNode.ofValidCode_primrec tc).comp
      (encodedTrAuxDepValidCode_primrec_fixed tc)
  have hsome : Primrec (fun dep : EncodedTrAuxDep tc =>
      some
        (TM0Route.PartrecStartedTM1StmtNode.ofValidCode
          (encodedTrAuxDepValidCode tc dep), dep.2.1, dep.2.2)) :=
    Primrec.option_some.comp (Primrec.pair hstmt Primrec.snd)
  exact (Primrec.ite hvalid hsome (Primrec.const none)).of_eq fun dep => by
    unfold decodeEncodedTrAuxDep?
    by_cases h : TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc) dep.1 <;>
      simp [h]

theorem decodeEncodedTrAuxDep?_ofStmt
    {tc : Turing.ToPartrec.Code} (stmt : SourceStmt tc)
    (v : PartrecVar) (a : SourceSymbol) :
    decodeEncodedTrAuxDep? tc
        (TM0Route.PartrecStartedTM1StmtNode.ofStmt stmt, v, a) =
      some (stmt, v, a) := by
  simp [decodeEncodedTrAuxDep?,
    encodedTrAuxDepValidCode_ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.valid_ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.ofValidCode_toValidCode]

noncomputable def trAuxDepsDecodedData (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) :
    List (SourceStmt tc × PartrecVar × SourceSymbol) :=
  (trAuxDepsNodeData tc p).filterMap (decodeEncodedTrAuxDep? tc)

theorem trAuxDepsDecodedData_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxDepsDecodedData tc) := by
  unfold trAuxDepsDecodedData
  exact Primrec.listFilterMap (trAuxDepsNodeData_primrec_fixed tc)
    (Primrec₂.mk (decodeEncodedTrAuxDep?_primrec_fixed tc |>.comp Primrec.snd))

theorem trAuxDepsDecodedData_eq
    (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) :
    trAuxDepsDecodedData tc p = trAuxDeps tc p := by
  unfold trAuxDepsDecodedData
  rw [trAuxDepsNodeData_eq_encoded]
  unfold trAuxDepsEncoded
  induction trAuxDeps tc p with
  | nil =>
      rfl
  | cons dep deps ih =>
      rcases dep with ⟨stmt, v, a⟩
      simp [decodeEncodedTrAuxDep?_ofStmt, ih]

theorem trAuxDeps_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxDeps tc) :=
  (trAuxDepsDecodedData_primrec_fixed tc).of_eq fun p =>
    trAuxDepsDecodedData_eq tc p

theorem trAuxDeps_measure_lt (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol)
    (p' : SourceStmt tc × PartrecVar × SourceSymbol)
    (hp' : p' ∈ trAuxDeps tc p) :
    trAuxMeasure tc p' < trAuxMeasure tc p := by
  rcases p with ⟨stmt, v, a⟩
  cases stmt with
  | move d q =>
      simp [trAuxDeps] at hp'
  | write f q =>
      simp [trAuxDeps] at hp'
  | load f q =>
      simp [trAuxDeps] at hp'
      subst p'
      simp [trAuxMeasure, TM0Route.PartrecStartedTM1StmtNode.ofStmt]
  | branch f q₁ q₂ =>
      by_cases h : f a v
      · simp [trAuxDeps, h] at hp'
        subst p'
        simp [trAuxMeasure, TM0Route.PartrecStartedTM1StmtNode.ofStmt]
        omega
      · simp [trAuxDeps, h] at hp'
        subst p'
        simp [trAuxMeasure, TM0Route.PartrecStartedTM1StmtNode.ofStmt]
        omega
  | goto f =>
      simp [trAuxDeps] at hp'
  | halt =>
      simp [trAuxDeps] at hp'

noncomputable def trAuxTailValidCode (tc : Turing.ToPartrec.Code)
    (stmt : SourceStmt tc) :
    TM0Route.PartrecStartedTM1StmtNode.ValidCode tc :=
  if h : TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc)
      (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt) then
    ⟨TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt, h⟩
  else
    TM0Route.PartrecStartedTM1StmtNode.toValidCode
      (Turing.TM1.Stmt.halt : SourceStmt tc)

theorem trAuxTailValidCode_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxTailValidCode tc) := by
  letI : Primcodable (TM0Route.PartrecStartedTM1StmtNode.ValidCode tc) :=
    TM0Route.PartrecStartedTM1StmtNode.instPrimcodableValidCode tc
  have htail : Primrec (fun stmt : SourceStmt tc =>
      TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt) :=
    TM0Route.PartrecStartedTM1StmtNode.ofStmtTail_primrec tc
  have hvalid : PrimrecPred (fun stmt : SourceStmt tc =>
      TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc)
        (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt)) :=
    (TM0Route.PartrecStartedTM1StmtNode.valid_primrecPred tc).comp htail
  have hval : Primrec (fun stmt : SourceStmt tc =>
      if TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc)
          (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt) then
        TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt
      else
        TM0Route.PartrecStartedTM1StmtNode.ofStmt
          (Turing.TM1.Stmt.halt : SourceStmt tc)) :=
    Primrec.ite hvalid htail
      (Primrec.const
        (TM0Route.PartrecStartedTM1StmtNode.ofStmt
          (Turing.TM1.Stmt.halt : SourceStmt tc)))
  have hval' : Primrec (fun stmt : SourceStmt tc =>
      (trAuxTailValidCode tc stmt).1) :=
    hval.of_eq fun stmt => by
      unfold trAuxTailValidCode
      by_cases h : TM0Route.PartrecStartedTM1StmtNode.Valid (tc := tc)
          (TM0Route.PartrecStartedTM1StmtNode.ofStmtTail stmt) <;>
        simp [h, TM0Route.PartrecStartedTM1StmtNode.toValidCode]
  exact Primrec.subtype_val_iff.1 hval'

noncomputable def trAuxTail (tc : Turing.ToPartrec.Code)
    (stmt : SourceStmt tc) : SourceStmt tc :=
  TM0Route.PartrecStartedTM1StmtNode.ofValidCode
    (trAuxTailValidCode tc stmt)

theorem trAuxTail_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxTail tc) := by
  exact (TM0Route.PartrecStartedTM1StmtNode.ofValidCode_primrec tc).comp
    (trAuxTailValidCode_primrec_fixed tc)

def trAuxBody (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol)
    (rec : List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol)) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  match p with
  | (Turing.TM1.Stmt.move d q, v, _) =>
      some ((some q, v), Turing.TM0.Stmt.move d)
  | (Turing.TM1.Stmt.write f q, v, a) =>
      some ((some q, v), Turing.TM0.Stmt.write (f a v))
  | (Turing.TM1.Stmt.load _ _, _, _) => rec.head?
  | (Turing.TM1.Stmt.branch _ _ _, _, _) => rec.head?
  | (Turing.TM1.Stmt.goto f, v, a) =>
      some ((some (TM0Route.partrecStartedTM1Machine tc (f a v)), v),
        Turing.TM0.Stmt.write a)
  | (Turing.TM1.Stmt.halt, v, a) =>
      some ((none, v), Turing.TM0.Stmt.write a)

noncomputable def trAuxMoveBody (tc : Turing.ToPartrec.Code)
    (p : (Turing.Dir × SourceStmt tc) × PartrecVar) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  some ((some p.1.2, p.2), Turing.TM0.Stmt.move p.1.1)

theorem trAuxMoveBody_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxMoveBody tc) := by
  have hlabel : Primrec (fun p : (Turing.Dir × SourceStmt tc) × PartrecVar =>
      ((some p.1.2, p.2) : SourceLabel tc)) :=
    Primrec.pair (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hstmt : Primrec (fun p : (Turing.Dir × SourceStmt tc) × PartrecVar =>
      Turing.TM0.Stmt.move (Γ := SourceSymbol) p.1.1) :=
    tm0StmtMove_primrec.comp (Primrec.fst.comp Primrec.fst)
  exact Primrec.option_some.comp (Primrec.pair hlabel hstmt)

noncomputable def trAuxWriteBody (tc : Turing.ToPartrec.Code)
    (p : (TM0Route.PartrecStartedTM1StmtNode.WriteCode × SourceStmt tc) ×
      PartrecVar × SourceSymbol) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  some ((some p.1.2, p.2.1), Turing.TM0.Stmt.write (p.1.1 p.2.2 p.2.1))

theorem trAuxWritePayload_primrec :
    Primrec (fun p :
      TM0Route.PartrecStartedTM1StmtNode.WriteCode × PartrecVar × SourceSymbol =>
      p.1 p.2.2 p.2.1) :=
  Primrec.dom_finite _

theorem trAuxWriteBody_primrec₂_fixed (tc : Turing.ToPartrec.Code) :
    Primrec₂ (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      fun f : TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
        some (((some p.1, p.2.1) : SourceLabel tc),
          Turing.TM0.Stmt.write (Γ := SourceSymbol) (f p.2.2 p.2.1))) := by
  apply Primrec₂.mk
  have hlabel : Primrec (fun p :
      (SourceStmt tc × PartrecVar × SourceSymbol) ×
        TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      ((some p.1.1, p.1.2.1) : SourceLabel tc)) :=
    Primrec.pair
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hpayload : Primrec (fun p :
      (SourceStmt tc × PartrecVar × SourceSymbol) ×
        TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      p.2 p.1.2.2 p.1.2.1) :=
    trAuxWritePayload_primrec.comp
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hstmt : Primrec (fun p :
      (SourceStmt tc × PartrecVar × SourceSymbol) ×
        TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      Turing.TM0.Stmt.write (Γ := SourceSymbol) (p.2 p.1.2.2 p.1.2.1)) :=
    tm0StmtWrite_primrec.comp hpayload
  exact Primrec.option_some.comp (Primrec.pair hlabel hstmt)

def trAuxHeadBodyFromDeps (tc : Turing.ToPartrec.Code)
    (rec : List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol)) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  rec.head?

theorem trAuxHeadBodyFromDeps_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxHeadBodyFromDeps tc) :=
  Primrec.list_head?

noncomputable def trAuxGotoBody (tc : Turing.ToPartrec.Code)
    (p : TM0Route.PartrecStartedTM1StmtNode.GotoCode tc × PartrecVar × SourceSymbol) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  some ((some (TM0Route.partrecStartedTM1Machine tc (p.1 p.2.2 p.2.1)), p.2.1),
    Turing.TM0.Stmt.write p.2.2)

theorem trAuxGotoBody_primrec₂_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec₂ (fun p : PartrecVar × SourceSymbol =>
      fun f : TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
        some (((some (TM0Route.partrecStartedTM1Machine tc (f p.2 p.1)), p.1) :
          SourceLabel tc), Turing.TM0.Stmt.write (Γ := SourceSymbol) p.2)) := by
  apply Primrec₂.mk
  have htarget : Primrec (fun p :
      (PartrecVar × SourceSymbol) × TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
      p.2 p.1.2 p.1.1) :=
    (TM0Route.partrecStartedTM0SymbolPartrecVarFunction_app_primrec
      (TM0Route.PartrecStartedTM1Label tc)).comp
      (Primrec.pair Primrec.snd
        (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)))
  have hstmt : Primrec (fun p :
      (PartrecVar × SourceSymbol) × TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
      TM0Route.partrecStartedTM1Machine tc (p.2 p.1.2 p.1.1)) :=
    hmachine.comp htarget
  have hlabel : Primrec (fun p :
      (PartrecVar × SourceSymbol) × TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
      ((some (TM0Route.partrecStartedTM1Machine tc (p.2 p.1.2 p.1.1)), p.1.1) :
        SourceLabel tc)) :=
    Primrec.pair (Primrec.option_some.comp hstmt) (Primrec.fst.comp Primrec.fst)
  have htm0 : Primrec (fun p :
      (PartrecVar × SourceSymbol) × TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
      Turing.TM0.Stmt.write (Γ := SourceSymbol) p.1.2) :=
    tm0StmtWrite_primrec.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.option_some.comp (Primrec.pair hlabel htm0)

theorem trAuxGotoBody_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (trAuxGotoBody tc) :=
  (trAuxGotoBody_primrec₂_fixed_of_machine tc hmachine).comp
    Primrec.snd Primrec.fst

noncomputable def trAuxHaltBody (tc : Turing.ToPartrec.Code)
    (p : PartrecVar × SourceSymbol) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  some ((none, p.1), Turing.TM0.Stmt.write p.2)

theorem trAuxHaltBody_primrec_fixed (tc : Turing.ToPartrec.Code) :
    Primrec (trAuxHaltBody tc) := by
  have hlabel : Primrec (fun p : PartrecVar × SourceSymbol =>
      ((none, p.1) : SourceLabel tc)) :=
    Primrec.pair (Primrec.const (none : Option (SourceStmt tc))) Primrec.fst
  have hstmt : Primrec (fun p : PartrecVar × SourceSymbol =>
      Turing.TM0.Stmt.write (Γ := SourceSymbol) p.2) :=
    tm0StmtWrite_primrec.comp Primrec.snd
  exact Primrec.option_some.comp (Primrec.pair hlabel hstmt)

/-- Input data for one statement-node reconstruction step of `trAux`. -/
abbrev TrAuxBodyForHeadInput (tc : Turing.ToPartrec.Code) : Type :=
  ((SourceStmt tc × PartrecVar × SourceSymbol) × SourceStmtNode tc) ×
    List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol)

noncomputable def trAuxBodyForHead (tc : Turing.ToPartrec.Code)
    (p : TrAuxBodyForHeadInput tc) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  let tail := trAuxTail tc p.1.1.1
  match p.1.2 with
  | TM0Route.PartrecStartedTM1StmtNode.move d =>
      trAuxMoveBody tc ((d, tail), p.1.1.2.1)
  | TM0Route.PartrecStartedTM1StmtNode.write f =>
      trAuxWriteBody tc ((f, tail), p.1.1.2.1, p.1.1.2.2)
  | TM0Route.PartrecStartedTM1StmtNode.load _ =>
      trAuxHeadBodyFromDeps tc p.2
  | TM0Route.PartrecStartedTM1StmtNode.branch _ =>
      trAuxHeadBodyFromDeps tc p.2
  | TM0Route.PartrecStartedTM1StmtNode.goto f =>
      trAuxGotoBody tc (f, p.1.1.2.1, p.1.1.2.2)
  | TM0Route.PartrecStartedTM1StmtNode.halt =>
      trAuxHaltBody tc (p.1.1.2.1, p.1.1.2.2)

theorem trAuxBodyForHeadMove_primrec₂_fixed (tc : Turing.ToPartrec.Code) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : Bool × PUnit =>
        trAuxMoveBody tc
          ((TM0Route.PartrecStartedTM1StmtNode.dirOfBool payload.1,
            trAuxTail tc p.1.1.1), p.1.1.2.1)) := by
  apply Primrec₂.mk
  have hdir : Primrec (fun p : TrAuxBodyForHeadInput tc × Bool × PUnit =>
      TM0Route.PartrecStartedTM1StmtNode.dirOfBool p.2.1) :=
    (Primrec.dom_finite _).comp (Primrec.fst.comp Primrec.snd)
  have htail : Primrec (fun p : TrAuxBodyForHeadInput tc × Bool × PUnit =>
      trAuxTail tc p.1.1.1.1) :=
    (trAuxTail_primrec_fixed tc).comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hvar : Primrec (fun p : TrAuxBodyForHeadInput tc × Bool × PUnit =>
      p.1.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  exact (trAuxMoveBody_primrec_fixed tc).comp
    (Primrec.pair (Primrec.pair hdir htail) hvar)

theorem trAuxBodyForHeadWrite_primrec₂_fixed (tc : Turing.ToPartrec.Code) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
        trAuxWriteBody tc
          ((payload, trAuxTail tc p.1.1.1), p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have htail : Primrec (fun p :
      TrAuxBodyForHeadInput tc × TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      trAuxTail tc p.1.1.1.1) :=
    (trAuxTail_primrec_fixed tc).comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hvar : Primrec (fun p :
      TrAuxBodyForHeadInput tc × TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      p.1.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hsym : Primrec (fun p :
      TrAuxBodyForHeadInput tc × TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      p.1.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hargs : Primrec (fun p :
      TrAuxBodyForHeadInput tc × TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
      ((trAuxTail tc p.1.1.1.1, p.1.1.1.2.1, p.1.1.1.2.2) :
        SourceStmt tc × PartrecVar × SourceSymbol)) :=
    Primrec.pair htail (Primrec.pair hvar hsym)
  exact ((trAuxWriteBody_primrec₂_fixed tc).comp hargs Primrec.snd).of_eq fun _ => rfl

theorem trAuxBodyForHeadLoad_primrec₂_fixed (tc : Turing.ToPartrec.Code) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun _payload : TM0Route.PartrecStartedTM1StmtNode.LoadCode =>
        trAuxHeadBodyFromDeps tc p.2) := by
  apply Primrec₂.mk
  exact (trAuxHeadBodyFromDeps_primrec_fixed tc).comp (Primrec.snd.comp Primrec.fst)

theorem trAuxBodyForHeadBranch_primrec₂_fixed (tc : Turing.ToPartrec.Code) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun _payload : TM0Route.PartrecStartedTM1StmtNode.BranchCode =>
        trAuxHeadBodyFromDeps tc p.2) := by
  apply Primrec₂.mk
  exact (trAuxHeadBodyFromDeps_primrec_fixed tc).comp (Primrec.snd.comp Primrec.fst)

theorem trAuxBodyForHeadGoto_primrec₂_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
        trAuxGotoBody tc (payload, p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have hvarsym : Primrec (fun p :
      TrAuxBodyForHeadInput tc × TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
      (p.1.1.1.2.1, p.1.1.1.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  exact ((trAuxGotoBody_primrec₂_fixed_of_machine tc hmachine).comp hvarsym
    Primrec.snd).of_eq fun _ => rfl

theorem trAuxBodyForHeadHalt_primrec₂_fixed (tc : Turing.ToPartrec.Code) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun _payload : PUnit =>
        trAuxHaltBody tc (p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have hvarsym : Primrec (fun p : TrAuxBodyForHeadInput tc × PUnit =>
      (p.1.1.1.2.1, p.1.1.1.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  exact (trAuxHaltBody_primrec_fixed tc).comp hvarsym

theorem trAuxBodyForHeadGotoHalt_primrec₂_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : TM0Route.PartrecStartedTM1StmtNode.GotoHaltCode tc =>
        match payload with
        | Sum.inl f => trAuxGotoBody tc (f, p.1.1.2.1, p.1.1.2.2)
        | Sum.inr _ => trAuxHaltBody tc (p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have hgoto : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.GotoHaltCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.GotoCode tc =>
          trAuxGotoBody tc (payload, p.1.1.1.2.1, p.1.1.1.2.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadGoto_primrec₂_fixed_of_machine tc hmachine).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hhalt : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.GotoHaltCode tc =>
        fun _payload : PUnit =>
          trAuxHaltBody tc (p.1.1.1.2.1, p.1.1.1.2.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadHalt_primrec₂_fixed tc).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.sumCasesOn Primrec.snd hgoto hhalt).of_eq fun p => by
    cases p.2 <;> rfl

theorem trAuxBodyForHeadBranchTail_primrec₂_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : TM0Route.PartrecStartedTM1StmtNode.BranchTailCode tc =>
        match payload with
        | Sum.inl _ => trAuxHeadBodyFromDeps tc p.2
        | Sum.inr c =>
            match c with
            | Sum.inl f => trAuxGotoBody tc (f, p.1.1.2.1, p.1.1.2.2)
            | Sum.inr _ => trAuxHaltBody tc (p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have hbranch : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.BranchTailCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.BranchCode =>
          trAuxHeadBodyFromDeps tc p.1.2) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadBranch_primrec₂_fixed tc).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hgotoHalt : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.BranchTailCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.GotoHaltCode tc =>
          match payload with
          | Sum.inl f => trAuxGotoBody tc (f, p.1.1.1.2.1, p.1.1.1.2.2)
          | Sum.inr _ => trAuxHaltBody tc (p.1.1.1.2.1, p.1.1.1.2.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadGotoHalt_primrec₂_fixed_of_machine tc hmachine).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.sumCasesOn Primrec.snd hbranch hgotoHalt).of_eq fun p => by
    cases p.2 <;> rfl

theorem trAuxBodyForHeadLoadTail_primrec₂_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : TM0Route.PartrecStartedTM1StmtNode.LoadTailCode tc =>
        match payload with
        | Sum.inl _ => trAuxHeadBodyFromDeps tc p.2
        | Sum.inr c =>
            match c with
            | Sum.inl _ => trAuxHeadBodyFromDeps tc p.2
            | Sum.inr c =>
                match c with
                | Sum.inl f => trAuxGotoBody tc (f, p.1.1.2.1, p.1.1.2.2)
                | Sum.inr _ => trAuxHaltBody tc (p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have hload : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.LoadTailCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.LoadCode =>
          trAuxHeadBodyFromDeps tc p.1.2) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadLoad_primrec₂_fixed tc).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hbranchTail : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.LoadTailCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.BranchTailCode tc =>
          match payload with
          | Sum.inl _ => trAuxHeadBodyFromDeps tc p.1.2
          | Sum.inr c =>
              match c with
              | Sum.inl f => trAuxGotoBody tc (f, p.1.1.1.2.1, p.1.1.1.2.2)
              | Sum.inr _ => trAuxHaltBody tc (p.1.1.1.2.1, p.1.1.1.2.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadBranchTail_primrec₂_fixed_of_machine tc hmachine).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.sumCasesOn Primrec.snd hload hbranchTail).of_eq fun p => by
    cases p.2 <;> rfl

theorem trAuxBodyForHeadWriteTail_primrec₂_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec₂ (fun p : TrAuxBodyForHeadInput tc =>
      fun payload : TM0Route.PartrecStartedTM1StmtNode.WriteTailCode tc =>
        match payload with
        | Sum.inl f =>
            trAuxWriteBody tc ((f, trAuxTail tc p.1.1.1), p.1.1.2.1, p.1.1.2.2)
        | Sum.inr c =>
            match c with
            | Sum.inl _ => trAuxHeadBodyFromDeps tc p.2
            | Sum.inr c =>
                match c with
                | Sum.inl _ => trAuxHeadBodyFromDeps tc p.2
                | Sum.inr c =>
                    match c with
                    | Sum.inl f => trAuxGotoBody tc (f, p.1.1.2.1, p.1.1.2.2)
                    | Sum.inr _ => trAuxHaltBody tc (p.1.1.2.1, p.1.1.2.2)) := by
  apply Primrec₂.mk
  have hwrite : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.WriteTailCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.WriteCode =>
          trAuxWriteBody tc
            ((payload, trAuxTail tc p.1.1.1.1), p.1.1.1.2.1, p.1.1.1.2.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadWrite_primrec₂_fixed tc).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hloadTail : Primrec₂
      (fun p : TrAuxBodyForHeadInput tc ×
          TM0Route.PartrecStartedTM1StmtNode.WriteTailCode tc =>
        fun payload : TM0Route.PartrecStartedTM1StmtNode.LoadTailCode tc =>
          match payload with
          | Sum.inl _ => trAuxHeadBodyFromDeps tc p.1.2
          | Sum.inr c =>
              match c with
              | Sum.inl _ => trAuxHeadBodyFromDeps tc p.1.2
              | Sum.inr c =>
                  match c with
                  | Sum.inl f => trAuxGotoBody tc (f, p.1.1.1.2.1, p.1.1.1.2.2)
                  | Sum.inr _ => trAuxHaltBody tc (p.1.1.1.2.1, p.1.1.1.2.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHeadLoadTail_primrec₂_fixed_of_machine tc hmachine).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.sumCasesOn Primrec.snd hwrite hloadTail).of_eq fun p => by
    cases p.2 <;> rfl

theorem trAuxBodyForHead_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (trAuxBodyForHead tc) := by
  have hcode : Primrec (fun p : TrAuxBodyForHeadInput tc =>
      TM0Route.PartrecStartedTM1StmtNode.toCode p.1.2) :=
    (TM0Route.PartrecStartedTM1StmtNode.toCode_primrec tc).comp
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.sumCasesOn hcode
    (trAuxBodyForHeadMove_primrec₂_fixed tc)
    (trAuxBodyForHeadWriteTail_primrec₂_fixed_of_machine tc hmachine)).of_eq fun p => by
      rcases p with ⟨⟨stmt, node⟩, deps⟩
      cases node with
      | move d =>
          cases d <;> rfl
      | write _ => rfl
      | load _ => rfl
      | branch _ => rfl
      | goto _ => rfl
      | halt => rfl

noncomputable def trAuxBodyFromHead? (tc : Turing.ToPartrec.Code)
    (p : (SourceStmt tc × PartrecVar × SourceSymbol) ×
      List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol)) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  match TM0Route.PartrecStartedTM1StmtNode.ofStmtHead? p.1.1 with
  | none => none
  | some node => trAuxBodyForHead tc ((p.1, node), p.2)

theorem trAuxBodyFromHead?_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (trAuxBodyFromHead? tc) := by
  have hhead : Primrec (fun p : (SourceStmt tc × PartrecVar × SourceSymbol) ×
      List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) =>
      TM0Route.PartrecStartedTM1StmtNode.ofStmtHead? p.1.1) :=
    (TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?_primrec tc).comp
      (Primrec.fst.comp Primrec.fst)
  have hnone : Primrec (fun _p : (SourceStmt tc × PartrecVar × SourceSymbol) ×
      List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) =>
      (none : Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol))) :=
    Primrec.const none
  have hsome : Primrec₂
      (fun p : (SourceStmt tc × PartrecVar × SourceSymbol) ×
          List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) =>
        fun node : SourceStmtNode tc => trAuxBodyForHead tc ((p.1, node), p.2)) := by
    apply Primrec₂.mk
    exact (trAuxBodyForHead_primrec_fixed_of_machine tc hmachine).comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.option_casesOn hhead hnone hsome).of_eq fun p => by
    generalize h :
      TM0Route.PartrecStartedTM1StmtNode.ofStmtHead? p.1.1 = head
    cases head <;> simp [trAuxBodyFromHead?, h]

theorem trAuxTail_move (tc : Turing.ToPartrec.Code)
    (d : Turing.Dir) (q : SourceStmt tc) :
    trAuxTail tc (Turing.TM1.Stmt.move d q) = q := by
  simp [trAuxTail, trAuxTailValidCode, TM0Route.PartrecStartedTM1StmtNode.ofStmtTail,
    TM0Route.PartrecStartedTM1StmtNode.ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.valid_ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.ofValidCode_ofStmt]

theorem trAuxTail_write (tc : Turing.ToPartrec.Code)
    (f : TM0Route.PartrecStartedTM1StmtNode.WriteCode) (q : SourceStmt tc) :
    trAuxTail tc (Turing.TM1.Stmt.write f q) = q := by
  simp [trAuxTail, trAuxTailValidCode, TM0Route.PartrecStartedTM1StmtNode.ofStmtTail,
    TM0Route.PartrecStartedTM1StmtNode.ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.valid_ofStmt,
    TM0Route.PartrecStartedTM1StmtNode.ofValidCode_ofStmt]

theorem trAuxBodyFromHead?_eq_body (tc : Turing.ToPartrec.Code)
    (p : (SourceStmt tc × PartrecVar × SourceSymbol) ×
      List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol)) :
    trAuxBodyFromHead? tc p = trAuxBody tc p.1 p.2 := by
  rcases p with ⟨⟨stmt, v, a⟩, rec⟩
  cases stmt with
  | move d q =>
      cases d <;>
        simp [trAuxBodyFromHead?, trAuxBodyForHead, trAuxBody, trAuxMoveBody,
          trAuxTail_move, TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?,
          TM0Route.PartrecStartedTM1StmtNode.ofStmt]
  | write f q =>
      simp [trAuxBodyFromHead?, trAuxBodyForHead, trAuxBody, trAuxWriteBody,
        trAuxTail_write, TM0Route.PartrecStartedTM1StmtNode.ofStmtHead?,
        TM0Route.PartrecStartedTM1StmtNode.ofStmt]
  | load f q =>
      rfl
  | branch f q₁ q₂ =>
      rfl
  | goto f =>
      rfl
  | halt =>
      rfl

theorem trAuxBody_correct (tc : Turing.ToPartrec.Code)
    (p : SourceStmt tc × PartrecVar × SourceSymbol) :
    trAuxBody tc p
        ((trAuxDeps tc p).map fun p' =>
          Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p'.2.2 p'.1 p'.2.1) =
      some (Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1) := by
  rcases p with ⟨stmt, v, a⟩
  cases stmt with
  | move d q =>
      rfl
  | write f q =>
      rfl
  | load f q =>
      rfl
  | branch f q₁ q₂ =>
      by_cases h : f a v <;>
        simp [trAuxBody, trAuxDeps, Turing.TM1to0.trAux, h]
  | goto f =>
      rfl
  | halt =>
      rfl

theorem trAux_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1) := by
  let f : SourceStmt tc × PartrecVar × SourceSymbol →
      SourceLabel tc × Turing.TM0.Stmt SourceSymbol :=
    fun p => Turing.TM1to0.trAux
      (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1
  let g : SourceStmt tc × PartrecVar × SourceSymbol →
      List (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) →
        Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
    fun p rec => trAuxBodyFromHead? tc (p, rec)
  have hg : Primrec₂ g := by
    apply Primrec₂.mk
    exact trAuxBodyFromHead?_primrec_fixed_of_machine tc hmachine
  have hbody : ∀ p, g p ((trAuxDeps tc p).map f) = some (f p) := by
    intro p
    dsimp [g, f]
    rw [trAuxBodyFromHead?_eq_body]
    exact trAuxBody_correct tc p
  exact Primrec.nat_omega_rec' f
    (trAuxMeasure_primrec_fixed tc)
    (trAuxDeps_primrec_fixed tc)
    hg
    (trAuxDeps_measure_lt tc)
    hbody

def sourceMachineStepOfStmt (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (a : SourceSymbol) :
    Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol) :=
  match stmt with
  | none => none
  | some stmt =>
      some (Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) a stmt v)

theorem sourceMachineStepOfStmt_eq_machine (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (a : SourceSymbol) :
    sourceMachineStepOfStmt tc q.1 q.2 a =
      TM0Route.partrecStartedTM0Machine tc q a := by
  rcases q with ⟨stmt | none, v⟩ <;> rfl

theorem sourceMachineStepOfStmt_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × SourceSymbol =>
      sourceMachineStepOfStmt tc p.1 p.2.1 p.2.2) := by
  have hstmtOpt : Primrec (fun p : Option (SourceStmt tc) × PartrecVar × SourceSymbol =>
      p.1) := Primrec.fst
  have hnone : Primrec (fun _p : Option (SourceStmt tc) × PartrecVar × SourceSymbol =>
      (none : Option (SourceLabel tc × Turing.TM0.Stmt SourceSymbol))) :=
    Primrec.const none
  have hsome : Primrec₂
      (fun p : Option (SourceStmt tc) × PartrecVar × SourceSymbol =>
        fun stmt : SourceStmt tc =>
          some (Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc)
            p.2.2 stmt p.2.1)) := by
    apply Primrec₂.mk
    exact Primrec.option_some.comp
      (haux.comp
        (Primrec.pair Primrec.snd
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  exact (Primrec.option_casesOn hstmtOpt hnone hsome).of_eq fun p => by
    rcases p with ⟨stmtOpt, v, a⟩
    cases stmtOpt <;> rfl

theorem sourceMachineStepOfStmt_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × SourceSymbol =>
      sourceMachineStepOfStmt tc p.1 p.2.1 p.2.2) :=
  sourceMachineStepOfStmt_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem sourceMachine_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : SourceLabel tc × SourceSymbol =>
      TM0Route.partrecStartedTM0Machine tc p.1 p.2) := by
  exact (sourceMachineStepOfStmt_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)) |>.of_eq
    fun p => (sourceMachineStepOfStmt_eq_machine tc p.1 p.2)

theorem sourceMachine_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : SourceLabel tc × SourceSymbol =>
      TM0Route.partrecStartedTM0Machine tc p.1 p.2) :=
  sourceMachine_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

def foldedSymbolCode (marked : Bool) (left right : SourceSymbol) : Nat :=
  Nat.pair (if marked then 1 else 0)
    (Nat.pair
      (TM0Route.partrecStartedTM0SymbolCode left)
      (TM0Route.partrecStartedTM0SymbolCode right))

theorem foldedSymbolCode_primrec :
    Primrec (fun p : Bool × SourceSymbol × SourceSymbol =>
      foldedSymbolCode p.1 p.2.1 p.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : Bool × SourceSymbol × SourceSymbol =>
    foldedSymbolCode p.1 p.2.1 p.2.2)

def foldedSymbolList : List Nat :=
  [false, true].flatMap fun marked =>
    TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
      TM0Route.partrecStartedTM0SymbolList.map fun right =>
        foldedSymbolCode marked left right

def foldedBlank : Nat :=
  foldedSymbolCode false default default

def foldedOriginSymbol (a : SourceSymbol) : Nat :=
  foldedSymbolCode true default a

theorem foldedOriginSymbol_primrec : Primrec foldedOriginSymbol := by
  classical
  exact Primrec.dom_finite foldedOriginSymbol

def foldedRead (side : FoldSide) (left right : SourceSymbol) : SourceSymbol :=
  match side with
  | FoldSide.left => left
  | FoldSide.right => right

theorem foldedRead_primrec :
    Primrec (fun p : FoldSide × SourceSymbol × SourceSymbol =>
      foldedRead p.1 p.2.1 p.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × SourceSymbol × SourceSymbol =>
    foldedRead p.1 p.2.1 p.2.2)

def foldedWrite (side : FoldSide) (new left right : SourceSymbol) : Nat :=
  match side with
  | FoldSide.left => foldedSymbolCode false new right
  | FoldSide.right => foldedSymbolCode false left new

theorem foldedWrite_primrec :
    Primrec (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
      foldedWrite p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
    foldedWrite p.1 p.2.1 p.2.2.1 p.2.2.2)

def foldedWriteMarked (side : FoldSide) (new left right : SourceSymbol) : Nat :=
  match side with
  | FoldSide.left => foldedSymbolCode true new right
  | FoldSide.right => foldedSymbolCode true left new

theorem foldedWriteMarked_primrec :
    Primrec (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
      foldedWriteMarked p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × SourceSymbol × SourceSymbol × SourceSymbol =>
    foldedWriteMarked p.1 p.2.1 p.2.2.1 p.2.2.2)

def stateTagSim : Nat := 0
def stateTagInit : Nat := 1
def stateTagReturn : Nat := 2

def taggedState (tag payload : Nat) : Nat :=
  Nat.pair tag payload

theorem taggedState_primrec :
    Primrec (fun p : Nat × Nat => taggedState p.1 p.2) := by
  exact Primrec₂.natPair.comp Primrec.fst Primrec.snd

/-- State used while simulating a Mathlib TM0 label on one side of the folded tape. -/
def foldedSimStateCode (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (q : SourceLabel tc) : Nat :=
  taggedState stateTagSim
    (Nat.pair side.code (TM0FiniteCompiler.stateCode tc q))

def foldedSimStateOfCode (side : FoldSide) (qCode : Nat) : Nat :=
  taggedState stateTagSim (Nat.pair side.code qCode)

theorem foldedSimStateOfCode_primrec :
    Primrec (fun p : FoldSide × Nat => foldedSimStateOfCode p.1 p.2) := by
  unfold foldedSimStateOfCode taggedState
  exact Primrec₂.natPair.comp (Primrec.const stateTagSim)
    (Primrec₂.natPair.comp (FoldSide.code_primrec.comp Primrec.fst) Primrec.snd)

theorem foldedSimStateCode_eq_ofCode (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (q : SourceLabel tc) :
    foldedSimStateCode tc side q =
      foldedSimStateOfCode side (TM0FiniteCompiler.stateCode tc q) := by
  rfl

theorem foldedSimStateOfCode_eq_foldedSimStateCode_iff
    {tc : Turing.ToPartrec.Code} {side side' : FoldSide} {qCode : Nat}
    {q : SourceLabel tc} :
    foldedSimStateOfCode side qCode = foldedSimStateCode tc side' q ↔
      side = side' ∧ qCode = TM0FiniteCompiler.stateCode tc q := by
  unfold foldedSimStateOfCode foldedSimStateCode taggedState
  constructor
  · intro h
    have hpayload := (Nat.pair_eq_pair.mp h).2
    have hparts := Nat.pair_eq_pair.mp hpayload
    have hside : side = side' := by
      cases side <;> cases side' <;> simp [FoldSide.code] at hparts ⊢
    exact ⟨hside, hparts.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem foldedSimStateCode_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : FoldSide × SourceLabel tc =>
      foldedSimStateCode tc p.1 p.2) := by
  exact (foldedSimStateOfCode_primrec.comp
    (Primrec.pair Primrec.fst
      (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp Primrec.snd))).of_eq
    fun _ => rfl

def foldedSimStartStateCode : Nat :=
  foldedSimStateOfCode FoldSide.right TM0Route.partrecStartedTM0Start

def initWriteOriginState : Nat :=
  taggedState stateTagInit 0

/-- Prelude state that moves from an initialized right-side input cell to the next cell. -/
def initMoveRightState (i : Nat) : Nat :=
  taggedState stateTagInit (2 * i + 1)

theorem initMoveRightState_primrec : Primrec initMoveRightState := by
  unfold initMoveRightState taggedState stateTagInit
  have hpayload : Primrec (fun i : Nat => 2 * i + 1) :=
    Primrec.succ.comp ((Primrec.nat_mul).comp (Primrec.const 2) Primrec.id)
  exact Primrec₂.natPair.comp (Primrec.const 1) hpayload

/-- Prelude state that writes right-side input cell `i + 1`. -/
def initWriteRightState (i : Nat) : Nat :=
  taggedState stateTagInit (2 * i + 2)

theorem initWriteRightState_primrec : Primrec initWriteRightState := by
  unfold initWriteRightState taggedState stateTagInit
  have hpayload : Primrec (fun i : Nat => 2 * i + 2) :=
    Primrec.succ.comp (Primrec.succ.comp ((Primrec.nat_mul).comp (Primrec.const 2) Primrec.id))
  exact Primrec₂.natPair.comp (Primrec.const 1) hpayload

/-- Prelude state with `i` left moves remaining before simulation starts. -/
def initReturnState (i : Nat) : Nat :=
  taggedState stateTagReturn i

theorem initReturnState_primrec : Primrec initReturnState := by
  unfold initReturnState taggedState stateTagReturn
  exact Primrec₂.natPair.comp (Primrec.const 2) Primrec.id

def foldedStartState : Nat :=
  initWriteOriginState

def foldedSimStartState (_tc : Turing.ToPartrec.Code) : Nat :=
  foldedSimStartStateCode

theorem foldedSimStartState_eq (tc : Turing.ToPartrec.Code) : foldedSimStartState tc =
    taggedState stateTagSim (Nat.pair FoldSide.right.code TM0Route.partrecStartedTM0Start) := by
  simp [foldedSimStartState, foldedSimStartStateCode, foldedSimStateOfCode,
    taggedState, TM0Route.partrecStartedTM0Start]

theorem foldedSimStartState_primrec :
    Primrec (fun _tc : Turing.ToPartrec.Code => foldedSimStartState _tc) := by
  refine (Primrec.const
    (taggedState stateTagSim (Nat.pair FoldSide.right.code
      TM0Route.partrecStartedTM0Start))).of_eq ?_
  intro tc
  exact (foldedSimStartState_eq (tc := tc)).symm

def foldedInitStateList : List Nat :=
  [initWriteOriginState, initReturnState 0] ++
    (List.range TM0Route.partrecStartedTM0Input.length).flatMap fun i =>
      [initMoveRightState i, initWriteRightState i, initReturnState i]

def foldedSimStateListOfCodes (qCodes : List Nat) : List Nat :=
  qCodes.flatMap fun qCode =>
    foldSideList.map fun side => foldedSimStateOfCode side qCode

theorem foldedSimStateListOfCodes_primrec : Primrec foldedSimStateListOfCodes := by
  unfold foldedSimStateListOfCodes
  refine Primrec.list_flatMap Primrec.id ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.const foldSideList) ?_
  apply Primrec₂.mk
  exact foldedSimStateOfCode_primrec.comp
    (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))

def foldedSimStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  foldedSimStateListOfCodes (TM0Route.partrecStartedTM0States tc)

theorem foldedSimStateList_primrec : Primrec foldedSimStateList := by
  unfold foldedSimStateList
  exact foldedSimStateListOfCodes_primrec.comp
    TM0Route.partrecStartedTM0States_primrec

theorem foldedSimStateList_computable : Computable foldedSimStateList :=
  foldedSimStateList_primrec.to_comp

def foldedStateListOfCodes (qCodes : List Nat) : List Nat :=
  foldedInitStateList ++ foldedSimStateListOfCodes qCodes

theorem foldedStateListOfCodes_primrec : Primrec foldedStateListOfCodes := by
  unfold foldedStateListOfCodes
  exact Primrec.list_append.comp (Primrec.const foldedInitStateList)
    foldedSimStateListOfCodes_primrec

def foldedStateListForCount (stateCount : Nat) : List Nat :=
  foldedStateListOfCodes (List.range stateCount)

theorem foldedStateListForCount_primrec : Primrec foldedStateListForCount := by
  unfold foldedStateListForCount
  exact foldedStateListOfCodes_primrec.comp Primrec.list_range

def foldedStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  foldedStateListOfCodes (TM0Route.partrecStartedTM0States tc)

theorem foldedStateList_primrec : Primrec foldedStateList := by
  unfold foldedStateList
  exact foldedStateListOfCodes_primrec.comp
    TM0Route.partrecStartedTM0States_primrec

theorem foldedStateList_computable : Computable foldedStateList :=
  foldedStateList_primrec.to_comp

def inputSymbol (i : Nat) : SourceSymbol :=
  TM0Route.partrecStartedTM0Input.getI i

theorem inputSymbol_primrec : Primrec inputSymbol := by
  unfold inputSymbol
  exact Primrec.list_getI.comp
    (Primrec.const TM0Route.partrecStartedTM0Input) Primrec.id

def nextAfterOrigin : Nat :=
  if TM0Route.partrecStartedTM0Input.length ≤ 1 then
    initReturnState 0
  else
    initMoveRightState 0

def mkRow (state read next : Nat) (stmt : PostStmt) : PostTransition where
  state := state
  read := read
  next := next
  stmt := stmt

theorem mkRow_matchesInput_of_state_ne_data {state state' read read' next : Nat}
    {stmt : PostStmt} (hstate : state ≠ state') :
    (mkRow state read next stmt).matchesInput state' read' = false := by
  simp [mkRow, PostTransition.matchesInput, hstate]

theorem mkRow_primrec :
    Primrec (fun p : Nat × Nat × Nat × PostStmt =>
      mkRow p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact PostTransition.mk_primrec

theorem postStmtMove_primrec : Primrec PostStmt.move := by
  exact PostStmt.ofSum_primrec.comp Primrec.sumInl

theorem postStmtWrite_primrec : Primrec PostStmt.write := by
  exact PostStmt.ofSum_primrec.comp Primrec.sumInr

def initWriteOriginRow : PostTransition :=
  mkRow initWriteOriginState foldedBlank nextAfterOrigin
    (PostStmt.write (foldedOriginSymbol (inputSymbol 0)))

def initMoveRightRow (i read : Nat) : PostTransition :=
  mkRow (initMoveRightState i) read (initWriteRightState i) (PostStmt.move Move.right)

theorem initMoveRightRow_primrec :
    Primrec (fun p : Nat × Nat => initMoveRightRow p.1 p.2) := by
  unfold initMoveRightRow
  exact mkRow_primrec.comp
    (Primrec.pair (initMoveRightState_primrec.comp Primrec.fst)
      (Primrec.pair Primrec.snd
        (Primrec.pair (initWriteRightState_primrec.comp Primrec.fst)
          (Primrec.const (PostStmt.move Move.right)))))

def initMoveRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).flatMap fun i =>
    foldedSymbolList.map fun read => initMoveRightRow i read

def nextAfterWriteRight (i : Nat) : Nat :=
  if i + 2 < TM0Route.partrecStartedTM0Input.length then
    initMoveRightState (i + 1)
  else
    initReturnState (i + 1)

theorem nextAfterWriteRight_primrec : Primrec nextAfterWriteRight := by
  unfold nextAfterWriteRight
  have hlt : PrimrecPred (fun i : Nat => i + 2 < TM0Route.partrecStartedTM0Input.length) := by
    exact Primrec.nat_lt.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 2))
      (Primrec.const TM0Route.partrecStartedTM0Input.length)
  have hmove : Primrec (fun i : Nat => initMoveRightState (i + 1)) :=
    initMoveRightState_primrec.comp (Primrec.succ)
  have hreturn : Primrec (fun i : Nat => initReturnState (i + 1)) :=
    initReturnState_primrec.comp (Primrec.succ)
  exact Primrec.ite hlt hmove hreturn

def initWriteRightRow (i : Nat) : PostTransition :=
  mkRow (initWriteRightState i) foldedBlank (nextAfterWriteRight i)
    (PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1))))

theorem initWriteRightRow_primrec : Primrec initWriteRightRow := by
  unfold initWriteRightRow
  have hinput : Primrec (fun i : Nat => inputSymbol (i + 1)) :=
    inputSymbol_primrec.comp Primrec.succ
  have hwriteSymbol : Primrec (fun i : Nat =>
      foldedSymbolCode false default (inputSymbol (i + 1))) := by
    exact foldedSymbolCode_primrec.comp
      (Primrec.pair (Primrec.const false)
        (Primrec.pair (Primrec.const default) hinput))
  have hstmt : Primrec (fun i : Nat =>
      PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1)))) :=
    postStmtWrite_primrec.comp hwriteSymbol
  exact mkRow_primrec.comp
    (Primrec.pair initWriteRightState_primrec
      (Primrec.pair (Primrec.const foldedBlank)
        (Primrec.pair nextAfterWriteRight_primrec hstmt)))

def initWriteRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).map fun i =>
    initWriteRightRow i

theorem initWriteRightRows_primrec :
    Primrec (fun _tc : Turing.ToPartrec.Code => initWriteRightRows) := by
  exact Primrec.const initWriteRightRows

def initReturnRow (_tc : Turing.ToPartrec.Code) (i read : Nat) : PostTransition :=
  if i = 0 then
    mkRow (initReturnState 0) read foldedSimStartStateCode (PostStmt.write read)
  else
    mkRow (initReturnState i) read (initReturnState (i - 1)) (PostStmt.move Move.left)

theorem initReturnRow_primrec :
    Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat =>
      initReturnRow p.1 p.2.1 p.2.2) := by
  unfold initReturnRow
  have hiZero : PrimrecPred (fun p : Turing.ToPartrec.Code × Nat × Nat => p.2.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hread : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hwriteStmt : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat =>
      PostStmt.write p.2.2) :=
    postStmtWrite_primrec.comp hread
  have hzero : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat =>
      mkRow (initReturnState 0) p.2.2 (foldedSimStartState p.1)
        (PostStmt.write p.2.2)) :=
    mkRow_primrec.comp
      (Primrec.pair (Primrec.const (initReturnState 0))
        (Primrec.pair hread
          (Primrec.pair (foldedSimStartState_primrec.comp Primrec.fst) hwriteStmt)))
  have hi : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hpredState : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat =>
      initReturnState (p.2.1 - 1)) :=
    initReturnState_primrec.comp
      (Primrec.nat_sub.comp hi (Primrec.const 1))
  have hmoveStmt : Primrec (fun _p : Turing.ToPartrec.Code × Nat × Nat =>
      PostStmt.move Move.left) :=
    Primrec.const (PostStmt.move Move.left)
  have hsucc : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat =>
      mkRow (initReturnState p.2.1) p.2.2 (initReturnState (p.2.1 - 1))
        (PostStmt.move Move.left)) :=
    mkRow_primrec.comp
      (Primrec.pair (initReturnState_primrec.comp hi)
        (Primrec.pair hread (Primrec.pair hpredState hmoveStmt)))
  exact Primrec.ite hiZero hzero hsucc

def initReturnIndexList : List Nat :=
  0 :: List.range TM0Route.partrecStartedTM0Input.length

def initReturnRowsData : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow default i read

def initReturnRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow tc i read

theorem initReturnRows_eq_data (tc : Turing.ToPartrec.Code) :
    initReturnRows tc = initReturnRowsData := rfl

theorem initReturnRows_primrec : Primrec initReturnRows := by
  refine (Primrec.const initReturnRowsData).of_eq ?_
  intro tc
  exact (initReturnRows_eq_data tc).symm

def initRowsData : List PostTransition :=
  initWriteOriginRow :: (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData))

def initRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initWriteOriginRow :: (initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc))

theorem initRows_eq_data (tc : Turing.ToPartrec.Code) :
    initRows tc = initRowsData := rfl

theorem initRows_primrec : Primrec initRows := by
  refine (Primrec.const initRowsData).of_eq ?_
  intro tc
  exact (initRows_eq_data tc).symm

def foldedMoveNextSide (side : FoldSide) (marked : Bool) (dir : Turing.Dir) : FoldSide :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => FoldSide.left
  | FoldSide.left, true, Turing.Dir.right => FoldSide.right
  | _, _, _ => side

theorem foldedMoveNextSide_primrec :
    Primrec (fun p : FoldSide × Bool × Turing.Dir =>
      foldedMoveNextSide p.1 p.2.1 p.2.2) := by
  classical
  exact Primrec.dom_finite (fun p : FoldSide × Bool × Turing.Dir =>
    foldedMoveNextSide p.1 p.2.1 p.2.2)

def foldedMoveStmt (side : FoldSide) (marked : Bool) (cell : Nat)
    (dir : Turing.Dir) : PostStmt :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => PostStmt.write cell
  | FoldSide.left, true, Turing.Dir.right => PostStmt.write cell
  | FoldSide.right, _, Turing.Dir.right => PostStmt.move Move.right
  | FoldSide.right, _, Turing.Dir.left => PostStmt.move Move.left
  | FoldSide.left, _, Turing.Dir.left => PostStmt.move Move.right
  | FoldSide.left, _, Turing.Dir.right => PostStmt.move Move.left

theorem foldedMoveStmt_primrec :
    Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      foldedMoveStmt p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let f : FoldSide × Bool × Nat × Turing.Dir → PostStmt := fun p =>
    if p.1 = FoldSide.right then
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.left then
          PostStmt.write p.2.2.1
        else
          PostStmt.move Move.right
      else
        if p.2.2.2 = Turing.Dir.right then
          PostStmt.move Move.right
        else
          PostStmt.move Move.left
    else
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.right then
          PostStmt.write p.2.2.1
        else
          PostStmt.move Move.right
      else
        if p.2.2.2 = Turing.Dir.left then
          PostStmt.move Move.right
        else
          PostStmt.move Move.left
  have hsideRight : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.1 = FoldSide.right) :=
    Primrec.eq.comp Primrec.fst (Primrec.const FoldSide.right)
  have hmarked : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.2.1 = true) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true)
  have htail : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2) :=
    Primrec.snd.comp
      (Primrec.snd : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2))
  have hcellSel : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.1) :=
    Primrec.fst.comp htail
  have hdirSel : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.2) :=
    Primrec.snd.comp htail
  have hdirLeft : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.2.2.2 = Turing.Dir.left) :=
    Primrec.eq.comp hdirSel (Primrec.const Turing.Dir.left)
  have hdirRight : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.2.2.2 = Turing.Dir.right) :=
    Primrec.eq.comp hdirSel (Primrec.const Turing.Dir.right)
  have hwrite : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      PostStmt.write p.2.2.1) :=
    postStmtWrite_primrec.comp hcellSel
  have hmoveLeft : Primrec (fun _ : FoldSide × Bool × Nat × Turing.Dir =>
      PostStmt.move Move.left) :=
    Primrec.const (PostStmt.move Move.left)
  have hmoveRight : Primrec (fun _ : FoldSide × Bool × Nat × Turing.Dir =>
      PostStmt.move Move.right) :=
    Primrec.const (PostStmt.move Move.right)
  have hrightMarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.left then
        PostStmt.write p.2.2.1
      else
        PostStmt.move Move.right) :=
    Primrec.ite hdirLeft hwrite hmoveRight
  have hrightUnmarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.right then
        PostStmt.move Move.right
      else
        PostStmt.move Move.left) :=
    Primrec.ite hdirRight hmoveRight hmoveLeft
  have hleftMarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.right then
        PostStmt.write p.2.2.1
      else
        PostStmt.move Move.right) :=
    Primrec.ite hdirRight hwrite hmoveRight
  have hleftUnmarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.left then
        PostStmt.move Move.right
      else
        PostStmt.move Move.left) :=
    Primrec.ite hdirLeft hmoveRight hmoveLeft
  have hright : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.left then
          PostStmt.write p.2.2.1
        else
          PostStmt.move Move.right
      else
        if p.2.2.2 = Turing.Dir.right then
          PostStmt.move Move.right
        else
          PostStmt.move Move.left) :=
    Primrec.ite hmarked hrightMarked hrightUnmarked
  have hleft : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.right then
          PostStmt.write p.2.2.1
        else
          PostStmt.move Move.right
      else
        if p.2.2.2 = Turing.Dir.left then
          PostStmt.move Move.right
        else
          PostStmt.move Move.left) :=
    Primrec.ite hmarked hleftMarked hleftUnmarked
  have hf : Primrec f :=
    Primrec.ite hsideRight hright hleft
  exact hf.of_eq fun p => by
    rcases p with ⟨side, marked, cell, dir⟩
    cases side <;> cases marked <;> cases dir <;> rfl

def foldedMoveHead (side : FoldSide) (marked : Bool) (head : Nat)
    (dir : Turing.Dir) : Nat :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => head
  | FoldSide.left, true, Turing.Dir.right => head
  | FoldSide.right, _, Turing.Dir.right => head + 1
  | FoldSide.right, _, Turing.Dir.left => head.pred
  | FoldSide.left, _, Turing.Dir.left => head + 1
  | FoldSide.left, _, Turing.Dir.right => head.pred

theorem foldedMoveHead_primrec :
    Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      foldedMoveHead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let f : FoldSide × Bool × Nat × Turing.Dir → Nat := fun p =>
    if p.1 = FoldSide.right then
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.left then
          p.2.2.1
        else
          p.2.2.1 + 1
      else
        if p.2.2.2 = Turing.Dir.right then
          p.2.2.1 + 1
        else
          p.2.2.1.pred
    else
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.right then
          p.2.2.1
        else
          p.2.2.1 + 1
      else
        if p.2.2.2 = Turing.Dir.left then
          p.2.2.1 + 1
        else
          p.2.2.1.pred
  have hsideRight : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.1 = FoldSide.right) :=
    Primrec.eq.comp Primrec.fst (Primrec.const FoldSide.right)
  have hmarked : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.2.1 = true) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true)
  have htail : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2) :=
    Primrec.snd.comp
      (Primrec.snd : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2))
  have hheadSel : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.1) :=
    Primrec.fst.comp htail
  have hdirSel : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.2) :=
    Primrec.snd.comp htail
  have hdirLeft : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.2.2.2 = Turing.Dir.left) :=
    Primrec.eq.comp hdirSel (Primrec.const Turing.Dir.left)
  have hdirRight : PrimrecPred (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      p.2.2.2 = Turing.Dir.right) :=
    Primrec.eq.comp hdirSel (Primrec.const Turing.Dir.right)
  have hstay : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.1) :=
    hheadSel
  have hsucc : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.1 + 1) :=
    Primrec.succ.comp hheadSel
  have hpred : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir => p.2.2.1.pred) :=
    Primrec.pred.comp hheadSel
  have hrightMarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.left then p.2.2.1 else p.2.2.1 + 1) :=
    Primrec.ite hdirLeft hstay hsucc
  have hrightUnmarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.right then p.2.2.1 + 1 else p.2.2.1.pred) :=
    Primrec.ite hdirRight hsucc hpred
  have hleftMarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.right then p.2.2.1 else p.2.2.1 + 1) :=
    Primrec.ite hdirRight hstay hsucc
  have hleftUnmarked : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.2.2 = Turing.Dir.left then p.2.2.1 + 1 else p.2.2.1.pred) :=
    Primrec.ite hdirLeft hsucc hpred
  have hright : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.left then
          p.2.2.1
        else
          p.2.2.1 + 1
      else
        if p.2.2.2 = Turing.Dir.right then
          p.2.2.1 + 1
        else
          p.2.2.1.pred) :=
    Primrec.ite hmarked hrightMarked hrightUnmarked
  have hleft : Primrec (fun p : FoldSide × Bool × Nat × Turing.Dir =>
      if p.2.1 = true then
        if p.2.2.2 = Turing.Dir.right then
          p.2.2.1
        else
          p.2.2.1 + 1
      else
        if p.2.2.2 = Turing.Dir.left then
          p.2.2.1 + 1
        else
          p.2.2.1.pred) :=
    Primrec.ite hmarked hleftMarked hleftUnmarked
  have hf : Primrec f :=
    Primrec.ite hsideRight hright hleft
  exact hf.of_eq fun p => by
    rcases p with ⟨side, marked, head, dir⟩
    cases side <;> cases marked <;> cases dir <;> rfl

def foldedWriteForStmt (side : FoldSide) (marked : Bool)
    (new left right : SourceSymbol) : Nat :=
  if marked then
    foldedWriteMarked side new left right
  else
    foldedWrite side new left right

theorem foldedWriteForStmt_primrec :
    Primrec (fun p : FoldSide × Bool × SourceSymbol × SourceSymbol × SourceSymbol =>
      foldedWriteForStmt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  classical
  exact Primrec.dom_finite
    (fun p : FoldSide × Bool × SourceSymbol × SourceSymbol × SourceSymbol =>
      foldedWriteForStmt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

def simRowOfStepCode
    (side : FoldSide) (marked : Bool)
    (qCode q'Code : Nat) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : PostTransition :=
  let read := foldedSymbolCode marked left right
  match stmt with
  | Turing.TM0.Stmt.write new =>
      mkRow (foldedSimStateOfCode side qCode) read
        (foldedSimStateOfCode side q'Code)
        (PostStmt.write (foldedWriteForStmt side marked new left right))
  | Turing.TM0.Stmt.move dir =>
      mkRow (foldedSimStateOfCode side qCode) read
        (foldedSimStateOfCode (foldedMoveNextSide side marked dir) q'Code)
        (foldedMoveStmt side marked read dir)

/-- Numeric data needed to generate one folded finite-TM0 simulation row. -/
abbrev SimStepData :=
  FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
    Turing.TM0.Stmt SourceSymbol

/--
Generate one folded finite-TM0 row from numeric transition data.

The hard computability problem is producing the list of these descriptors from
the Mathlib TM0 transition function; once such a list is available, turning it
into finite-TM0 rows is primitive recursive.
-/
def simStepDataRow (p : SimStepData) : PostTransition :=
  simRowOfStepCode p.1 p.2.1 p.2.2.1 p.2.2.2.1
    p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2

theorem simStepDataRow_matchesInput_of_currentCode_ne
    {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {marked marked' : Bool}
    {qCode q'Code : Nat} {q : SourceLabel tc}
    {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hcode : qCode ≠ TM0FiniteCompiler.stateCode tc q) :
    (simStepDataRow (side', marked', qCode, q'Code, left', right', stmt)).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  have hstate : foldedSimStateOfCode side' qCode ≠ foldedSimStateCode tc side q := by
    intro h
    exact hcode (foldedSimStateOfCode_eq_foldedSimStateCode_iff.1 h).2
  cases stmt <;> simp [simStepDataRow, simRowOfStepCode, mkRow,
    PostTransition.matchesInput, hstate]

theorem simStepDataRow_matchesInput_of_currentCode_ne'
    {tc : Turing.ToPartrec.Code} {p : SimStepData}
    {side : FoldSide} {marked : Bool} {q : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc q) :
    (simStepDataRow p).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  rcases p with ⟨side', marked', qCode, q'Code, left', right', stmt⟩
  exact simStepDataRow_matchesInput_of_currentCode_ne
    (tc := tc) (side := side) (side' := side') (marked := marked)
    (marked' := marked') (qCode := qCode) (q'Code := q'Code) (q := q)
    (left := left) (right := right) (left' := left') (right' := right')
    (stmt := stmt) hcode

set_option maxHeartbeats 800000 in
-- The nested product selectors in this row-level primitive-recursive proof take
-- longer than the default heartbeat budget to elaborate.
theorem simRowOfStepCode_primrec :
    Primrec (fun p : FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
        Turing.TM0.Stmt SourceSymbol =>
      simRowOfStepCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let readFn :
      FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
          Turing.TM0.Stmt SourceSymbol → Nat := fun p =>
    foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
  let currentState :
      FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
          Turing.TM0.Stmt SourceSymbol → Nat := fun p =>
    foldedSimStateOfCode p.1 p.2.2.1
  let q'CodeFn :
      FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
          Turing.TM0.Stmt SourceSymbol → Nat := fun p =>
    p.2.2.2.1
  let leftFn :
      FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
          Turing.TM0.Stmt SourceSymbol → SourceSymbol := fun p =>
    p.2.2.2.2.1
  let rightFn :
      FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
          Turing.TM0.Stmt SourceSymbol → SourceSymbol := fun p =>
    p.2.2.2.2.2.1
  let stmtSum :
      FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
          Turing.TM0.Stmt SourceSymbol → Turing.Dir ⊕ SourceSymbol := fun p =>
    tm0StmtToSum p.2.2.2.2.2.2
  have hmarked : Primrec (fun p : FoldSide × Bool × Nat × Nat × SourceSymbol ×
      SourceSymbol × Turing.TM0.Stmt SourceSymbol => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hleft : Primrec leftFn :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      Primrec.snd)))
  have hright : Primrec rightFn :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))
  have hstmtSum : Primrec stmtSum :=
    tm0StmtToSum_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd)))))
  have hread : Primrec readFn := by
    exact foldedSymbolCode_primrec.comp
      (Primrec.pair hmarked (Primrec.pair hleft hright))
  have hcurrent : Primrec currentState := by
    exact foldedSimStateOfCode_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hq' : Primrec q'CodeFn :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hwrite :
      Primrec₂
        (fun p : FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol =>
          fun new : SourceSymbol =>
            mkRow (foldedSimStateOfCode p.1 p.2.2.1)
              (foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
              (foldedSimStateOfCode p.1 p.2.2.2.1)
              (PostStmt.write
                (foldedWriteForStmt p.1 p.2.1 new p.2.2.2.2.1 p.2.2.2.2.2.1))) := by
    apply Primrec₂.mk
    have hnew : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × SourceSymbol => p.2) :=
      Primrec.snd
    have hbase : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × SourceSymbol => p.1) :=
      Primrec.fst
    have hwriteSymbol : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × SourceSymbol =>
          foldedWriteForStmt p.1.1 p.1.2.1 p.2 p.1.2.2.2.2.1 p.1.2.2.2.2.2.1) := by
      exact foldedWriteForStmt_primrec.comp
        (Primrec.pair (Primrec.fst.comp hbase)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hbase))
              (Primrec.pair hnew
                (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp (Primrec.snd.comp hbase)))))
                  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp (Primrec.snd.comp hbase))))))))))
    exact mkRow_primrec.comp
      (Primrec.pair (hcurrent.comp hbase)
        (Primrec.pair (hread.comp hbase)
          (Primrec.pair
            (foldedSimStateOfCode_primrec.comp
              (Primrec.pair (Primrec.fst.comp hbase) (hq'.comp hbase)))
            (postStmtWrite_primrec.comp hwriteSymbol))))
  have hmove :
      Primrec₂
        (fun p : FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol =>
          fun dir : Turing.Dir =>
            mkRow (foldedSimStateOfCode p.1 p.2.2.1)
              (foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
              (foldedSimStateOfCode (foldedMoveNextSide p.1 p.2.1 dir) p.2.2.2.1)
              (foldedMoveStmt p.1 p.2.1
                (foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) dir)) := by
    apply Primrec₂.mk
    have hdir : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × Turing.Dir => p.2) :=
      Primrec.snd
    have hbase : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × Turing.Dir => p.1) :=
      Primrec.fst
    have hnextSide : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × Turing.Dir =>
          foldedMoveNextSide p.1.1 p.1.2.1 p.2) := by
      exact foldedMoveNextSide_primrec.comp
        (Primrec.pair (Primrec.fst.comp hbase)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hbase)) hdir))
    have hstmt : Primrec (fun p :
        (FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
            Turing.TM0.Stmt SourceSymbol) × Turing.Dir =>
          foldedMoveStmt p.1.1 p.1.2.1
            (foldedSymbolCode p.1.2.1 p.1.2.2.2.2.1 p.1.2.2.2.2.2.1) p.2) := by
      exact foldedMoveStmt_primrec.comp
        (Primrec.pair (Primrec.fst.comp hbase)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hbase))
            (Primrec.pair (hread.comp hbase) hdir)))
    exact mkRow_primrec.comp
      (Primrec.pair (hcurrent.comp hbase)
        (Primrec.pair (hread.comp hbase)
          (Primrec.pair
            (foldedSimStateOfCode_primrec.comp
              (Primrec.pair hnextSide (hq'.comp hbase)))
            hstmt)))
  refine (Primrec.sumCasesOn
    (α := FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
      Turing.TM0.Stmt SourceSymbol)
    (β := Turing.Dir) (γ := SourceSymbol) (σ := PostTransition)
    (f := stmtSum)
    (g := fun p dir =>
      mkRow (foldedSimStateOfCode p.1 p.2.2.1)
        (foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
        (foldedSimStateOfCode (foldedMoveNextSide p.1 p.2.1 dir) p.2.2.2.1)
        (foldedMoveStmt p.1 p.2.1
          (foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) dir))
    (h := fun p new =>
      mkRow (foldedSimStateOfCode p.1 p.2.2.1)
        (foldedSymbolCode p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
        (foldedSimStateOfCode p.1 p.2.2.2.1)
        (PostStmt.write
          (foldedWriteForStmt p.1 p.2.1 new p.2.2.2.2.1 p.2.2.2.2.2.1)))
    hstmtSum hmove hwrite).of_eq ?_
  intro p
  rcases p with ⟨side, marked, qCode, q'Code, left, right, stmt⟩
  cases stmt <;> rfl

theorem simStepDataRow_primrec : Primrec simStepDataRow :=
  simRowOfStepCode_primrec

/-- Generate folded finite-TM0 simulation rows from numeric transition data. -/
def simRowsOfStepData (steps : List SimStepData) : List PostTransition :=
  steps.map simStepDataRow

theorem simRowsOfStepData_primrec : Primrec simRowsOfStepData := by
  unfold simRowsOfStepData
  have hrow : Primrec₂ fun _steps : List SimStepData => fun p : SimStepData =>
      simStepDataRow p := by
    apply Primrec₂.mk
    exact simStepDataRow_primrec.comp Primrec.snd
  exact Primrec.list_map Primrec.id hrow

theorem simRowsOfStepData_computable : Computable simRowsOfStepData :=
  simRowsOfStepData_primrec.to_comp

theorem simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
    {tc : Turing.ToPartrec.Code} {steps : List SimStepData}
    {side : FoldSide} {marked : Bool} {q : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : ∀ p ∈ steps, p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc q) :
    (simRowsOfStepData steps).find? (fun e =>
        e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right)) =
      none := by
  induction steps with
  | nil =>
      simp [simRowsOfStepData]
  | cons p ps ih =>
      have hhead :
          (simStepDataRow p).matchesInput
              (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
            false :=
        simStepDataRow_matchesInput_of_currentCode_ne' (hcode p (by simp))
      have htail :
          (simRowsOfStepData ps).find? (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none := by
        exact ih fun r hr => hcode r (by simp [hr])
      change (simStepDataRow p :: simRowsOfStepData ps).find? (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) = none
      simp [hhead, htail]

private theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx] at h
      · simp [hx]
        have hxs : xs.find? p = none := by
          simpa [hx] using h
        simpa [hx] using ih hxs

theorem initWriteOriginState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) :
    initWriteOriginState ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteOriginState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initMoveRightState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initMoveRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initMoveRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initWriteRightState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initWriteRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initReturnState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initReturnState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initReturnState foldedSimStateCode taggedState stateTagReturn stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initMoveRightRows_find?_eq_none_of_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initMoveRightState j ≠ foldedSimStateCode tc side q :=
          initMoveRightState_ne_foldedSimStateCode_data tc j side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput
                    (foldedSimStateCode tc side q) read = false :=
              mkRow_matchesInput_of_state_ne_data hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initWriteRightRows_find?_eq_none_of_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initWriteRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hstate : initWriteRightState j ≠ foldedSimStateCode tc side q :=
        initWriteRightState_ne_foldedSimStateCode_data tc j side q
      have hmiss :
          (initWriteRightRow j).matchesInput (foldedSimStateCode tc side q) read = false :=
        mkRow_matchesInput_of_state_ne_data hstate
      simp [hmiss, ih]

theorem initReturnRowsData_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initReturnRowsData.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initReturnRowsData
  induction initReturnIndexList with
  | nil =>
      simp
  | cons i indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initReturnRow default i r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initReturnState i ≠ foldedSimStateCode tc side q :=
          initReturnState_ne_foldedSimStateCode_data tc i side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initReturnRow default i r).matchesInput
                    (foldedSimStateCode tc side q) read = false := by
              by_cases hi0 : i = 0
              · subst i
                exact mkRow_matchesInput_of_state_ne_data hstate
              · unfold initReturnRow
                rw [if_neg hi0]
                exact mkRow_matchesInput_of_state_ne_data hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initRowsData_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initRowsData.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  have horigin :
      initWriteOriginRow.matchesInput (foldedSimStateCode tc side q) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne_data
      (initWriteOriginState_ne_foldedSimStateCode_data tc side q)
  have hmove := initMoveRightRows_find?_eq_none_of_foldedSimStateCode_data tc side q read
  have hwrite := initWriteRightRows_find?_eq_none_of_foldedSimStateCode_data tc side q read
  have hreturn := initReturnRowsData_find?_eq_none_of_foldedSimStateCode tc side q read
  unfold initRowsData
  have htail :
      (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData)).find?
          (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
        none := by
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

theorem simRowsOfStepData_find?_append_eq_of_forall_currentCode_ne
    {tc : Turing.ToPartrec.Code} {pref suffix : List SimStepData}
    {side : FoldSide} {marked : Bool} {q : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : ∀ p ∈ pref, p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc q) :
    (simRowsOfStepData (pref ++ suffix)).find? (fun e =>
        e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right)) =
      (simRowsOfStepData suffix).find? (fun e =>
        e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right)) := by
  rw [show simRowsOfStepData (pref ++ suffix) =
      simRowsOfStepData pref ++ simRowsOfStepData suffix by
    simp [simRowsOfStepData]]
  exact find?_append_of_eq_none
    (simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
      (tc := tc) (steps := pref) (side := side) (marked := marked) (q := q)
      (left := left) (right := right) hcode)

def simRowOfStep (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : PostTransition :=
  let read := foldedSymbolCode marked left right
  match stmt with
  | Turing.TM0.Stmt.write new =>
      mkRow (foldedSimStateCode tc side q) read
        (foldedSimStateCode tc side q')
        (PostStmt.write (foldedWriteForStmt side marked new left right))
  | Turing.TM0.Stmt.move dir =>
      mkRow (foldedSimStateCode tc side q) read
        (foldedSimStateCode tc (foldedMoveNextSide side marked dir) q')
        (foldedMoveStmt side marked read dir)

theorem simRowOfStep_eq_code (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    simRowOfStep tc side marked q q' left right stmt =
      simRowOfStepCode side marked
        (TM0FiniteCompiler.stateCode tc q) (TM0FiniteCompiler.stateCode tc q')
        left right stmt := by
  cases stmt <;> rfl

def simTransitionOfStep (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option PostTransition :=
  match TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) with
  | none => none
  | some (q', stmt) => some (simRowOfStep tc side marked q q' left right stmt)

/-- Numeric descriptor for one semantic folded simulation step. -/
def simStepDataOfStep (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : SimStepData :=
  (side, marked, TM0FiniteCompiler.stateCode tc q,
    TM0FiniteCompiler.stateCode tc q', left, right, stmt)

def simStepDataOfStepCode
    (side : FoldSide) (marked : Bool)
    (qCode q'Code : Nat) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : SimStepData :=
  (side, marked, qCode, q'Code, left, right, stmt)

theorem simStepDataOfStep_eq_code (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    simStepDataOfStep tc side marked q q' left right stmt =
      simStepDataOfStepCode side marked
        (TM0FiniteCompiler.stateCode tc q)
        (TM0FiniteCompiler.stateCode tc q') left right stmt := by
  rfl

theorem simStepDataOfStepCode_primrec :
    Primrec (fun p : FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
        Turing.TM0.Stmt SourceSymbol =>
      simStepDataOfStepCode p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  unfold simStepDataOfStepCode
  exact Primrec.id

theorem simStepDataOfStep_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : FoldSide × Bool × SourceLabel tc × SourceLabel tc ×
        SourceSymbol × SourceSymbol × Turing.TM0.Stmt SourceSymbol =>
      simStepDataOfStep tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  unfold simStepDataOfStep
  exact Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair
        (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.pair
          (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.snd))))
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))))))

theorem simStepDataRow_ofStep (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    simStepDataRow (simStepDataOfStep tc side marked q q' left right stmt) =
      simRowOfStep tc side marked q q' left right stmt := by
  rw [simRowOfStep_eq_code]
  rfl

/-- Descriptor-level version of `simTransitionOfStep`. -/
def simStepDataOfTransition (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option SimStepData :=
  match TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) with
  | none => none
  | some (q', stmt) => some (simStepDataOfStep tc side marked q q' left right stmt)

def simStepDataOfStmtTransition (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option SimStepData :=
  match sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none => none
  | some (q', tm0Stmt) => some (simStepDataOfStep tc side marked (stmt, v) q' left right tm0Stmt)

def simStepDataOfStmtTransitionWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option SimStepData :=
  match sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none => none
  | some (q', tm0Stmt) =>
      some (simStepDataOfStepCode side marked qCode
        (TM0FiniteCompiler.stateCode tc q') left right tm0Stmt)

theorem simStepDataOfStmtTransition_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) :
    simStepDataOfStmtTransition tc stmt v side marked left right =
      simStepDataOfStmtTransitionWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side marked left right := by
  unfold simStepDataOfStmtTransition simStepDataOfStmtTransitionWithCode
  cases sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none =>
      rfl
  | some step =>
      cases step
      rfl

theorem simStepDataOfStmtTransitionWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol × SourceSymbol =>
      simStepDataOfStmtTransitionWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let readFn :
      Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool × SourceSymbol ×
        SourceSymbol → SourceSymbol := fun p =>
    foldedRead p.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2
  have hread : Primrec readFn := by
    exact foldedRead_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))
  have hlookup : Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar ×
      FoldSide × Bool × SourceSymbol × SourceSymbol =>
      sourceMachineStepOfStmt tc p.2.1 p.2.2.1 (readFn p)) := by
    exact (sourceMachineStepOfStmt_primrec_fixed_of_trAux tc haux).comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hread))
  have hsome : Primrec₂
      (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
          SourceSymbol × SourceSymbol =>
        fun step : SourceLabel tc × Turing.TM0.Stmt SourceSymbol =>
          simStepDataOfStepCode p.2.2.2.1 p.2.2.2.2.1 p.1
            (TM0FiniteCompiler.stateCode tc step.1)
            p.2.2.2.2.2.1 p.2.2.2.2.2.2 step.2) := by
    apply Primrec₂.mk
    exact simStepDataOfStepCode_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
          Primrec.fst))))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.fst)))))
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.pair
              (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp
                (Primrec.fst.comp Primrec.snd))
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
                (Primrec.pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
                  (Primrec.snd.comp Primrec.snd)))))))
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold simStepDataOfStmtTransitionWithCode readFn
    cases sourceMachineStepOfStmt tc p.2.1 p.2.2.1
        (foldedRead p.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) <;> rfl

theorem simStepDataOfStmtTransition_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) :
    simStepDataOfStmtTransition tc q.1 q.2 side marked left right =
      simStepDataOfTransition tc q side marked left right := by
  rcases q with ⟨stmt, v⟩
  unfold simStepDataOfStmtTransition simStepDataOfTransition
  rw [sourceMachineStepOfStmt_eq_machine]
  cases h : TM0Route.partrecStartedTM0Machine tc (stmt, v) (foldedRead side left right) <;>
    simp

theorem simStepDataOfStmtTransition_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol × SourceSymbol =>
      simStepDataOfStmtTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) := by
  let readFn :
      Option (SourceStmt tc) × PartrecVar × FoldSide × Bool × SourceSymbol ×
        SourceSymbol → SourceSymbol := fun p =>
    foldedRead p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
  have hread : Primrec readFn := by
    exact foldedRead_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd))))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd))))))
  have hlookup : Primrec (fun p : Option (SourceStmt tc) × PartrecVar ×
      FoldSide × Bool × SourceSymbol × SourceSymbol =>
      sourceMachineStepOfStmt tc p.1 p.2.1 (readFn p)) := by
    exact (sourceMachineStepOfStmt_primrec_fixed_of_trAux tc haux).comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd) hread))
  have hsome : Primrec₂
      (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
          SourceSymbol × SourceSymbol =>
        fun step : SourceLabel tc × Turing.TM0.Stmt SourceSymbol =>
          simStepDataOfStep tc p.2.2.1 p.2.2.2.1 (p.1, p.2.1) step.1
            p.2.2.2.2.1 p.2.2.2.2.2 step.2) := by
    apply Primrec₂.mk
    exact (simStepDataOfStep_primrec_fixed tc).comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.fst))))
          (Primrec.pair
            (Primrec.pair (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
            (Primrec.pair (Primrec.fst.comp Primrec.snd)
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
                (Primrec.pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
                  (Primrec.snd.comp Primrec.snd)))))))
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold simStepDataOfStmtTransition readFn
    cases sourceMachineStepOfStmt tc p.1 p.2.1
        (foldedRead p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) <;> rfl

theorem simStepDataOfStmtTransition_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol × SourceSymbol =>
      simStepDataOfStmtTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) :=
  simStepDataOfStmtTransition_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataOfTransition_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)]
    (hstep : Primrec (fun p : SourceLabel tc × SourceSymbol =>
      TM0Route.partrecStartedTM0Machine tc p.1 p.2)) :
    Primrec (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol × SourceSymbol =>
      simStepDataOfTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let readFn : SourceLabel tc × FoldSide × Bool × SourceSymbol × SourceSymbol →
      SourceSymbol := fun p => foldedRead p.2.1 p.2.2.2.1 p.2.2.2.2
  have hread : Primrec readFn := by
    exact foldedRead_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hlookup : Primrec (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol ×
      SourceSymbol =>
      TM0Route.partrecStartedTM0Machine tc p.1 (readFn p)) := by
    exact hstep.comp (Primrec.pair Primrec.fst hread)
  have hsome : Primrec₂ (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol ×
      SourceSymbol => fun step : SourceLabel tc × Turing.TM0.Stmt SourceSymbol =>
      simStepDataOfStep tc p.2.1 p.2.2.1 p.1 step.1 p.2.2.2.1 p.2.2.2.2
        step.2) := by
    apply Primrec₂.mk
    exact (simStepDataOfStep_primrec_fixed tc).comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair (Primrec.fst.comp Primrec.fst)
            (Primrec.pair (Primrec.fst.comp Primrec.snd)
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp Primrec.fst))))
                (Primrec.pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp Primrec.fst))))
                  (Primrec.snd.comp Primrec.snd)))))))
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold simStepDataOfTransition readFn
    cases TM0Route.partrecStartedTM0Machine tc p.1 (foldedRead p.2.1 p.2.2.2.1 p.2.2.2.2)
    · rfl
    · rfl

theorem simStepDataOfTransition_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol × SourceSymbol =>
      simStepDataOfTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  simStepDataOfTransition_primrec_fixed_of_machine tc
    (sourceMachine_primrec_fixed_of_trAux tc haux)

def simStepDataForStmtRightSymbols (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left : SourceSymbol) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
    simStepDataOfStmtTransition tc stmt v side marked left right

def simStepDataForStmtRightSymbolsWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left : SourceSymbol) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
    simStepDataOfStmtTransitionWithCode tc qCode stmt v side marked left right

theorem simStepDataForStmtRightSymbols_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left : SourceSymbol) :
    simStepDataForStmtRightSymbols tc stmt v side marked left =
      simStepDataForStmtRightSymbolsWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side marked left := by
  unfold simStepDataForStmtRightSymbols simStepDataForStmtRightSymbolsWithCode
  apply List.filterMap_congr
  intro right _hright
  exact simStepDataOfStmtTransition_eq_withCode tc stmt v side marked left right

theorem simStepDataForStmtRightSymbolsWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol =>
      simStepDataForStmtRightSymbolsWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold simStepDataForStmtRightSymbolsWithCode
  have htransition := simStepDataOfStmtTransitionWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.listFilterMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact htransition.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
              (Primrec.pair
                (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
                Primrec.snd))))))

theorem simStepDataForStmtRightSymbols_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol =>
      simStepDataForStmtRightSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold simStepDataForStmtRightSymbols
  have htransition := simStepDataOfStmtTransition_primrec_fixed_of_trAux tc haux
  refine Primrec.listFilterMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact htransition.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp Primrec.fst))))
              Primrec.snd)))))

theorem simStepDataForStmtRightSymbols_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol =>
      simStepDataForStmtRightSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  simStepDataForStmtRightSymbols_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

def simStepDataForStmtLeftSymbols (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
    simStepDataForStmtRightSymbols tc stmt v side marked left

def simStepDataForStmtLeftSymbolsWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
    simStepDataForStmtRightSymbolsWithCode tc qCode stmt v side marked left

theorem simStepDataForStmtLeftSymbols_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) :
    simStepDataForStmtLeftSymbols tc stmt v side marked =
      simStepDataForStmtLeftSymbolsWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side marked := by
  unfold simStepDataForStmtLeftSymbols simStepDataForStmtLeftSymbolsWithCode
  apply List.flatMap_congr
  intro left _hleft
  exact simStepDataForStmtRightSymbols_eq_withCode tc stmt v side marked left

theorem simStepDataForStmtLeftSymbolsWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool =>
      simStepDataForStmtLeftSymbolsWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2) := by
  unfold simStepDataForStmtLeftSymbolsWithCode
  have hright := simStepDataForStmtRightSymbolsWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact hright.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp Primrec.fst))))
              Primrec.snd)))))

theorem simStepDataForStmtLeftSymbols_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide) (marked : Bool) :
    simStepDataForStmtLeftSymbols tc q.1 q.2 side marked =
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simStepDataOfTransition tc q side marked left right := by
  rcases q with ⟨stmt, v⟩
  unfold simStepDataForStmtLeftSymbols simStepDataForStmtRightSymbols
  apply List.flatMap_congr
  intro left hleft
  apply List.filterMap_congr
  intro right hright
  exact simStepDataOfStmtTransition_eq_of_label tc (stmt, v) side marked left right

theorem simStepDataForStmtLeftSymbols_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool =>
      simStepDataForStmtLeftSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold simStepDataForStmtLeftSymbols
  have hright := simStepDataForStmtRightSymbols_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact hright.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))))

theorem simStepDataForStmtLeftSymbols_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool =>
      simStepDataForStmtLeftSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  simStepDataForStmtLeftSymbols_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

def simStepDataForStmtMarked (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide) :
    List SimStepData :=
  [false, true].flatMap fun marked =>
    simStepDataForStmtLeftSymbols tc stmt v side marked

def simStepDataForStmtMarkedWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide) :
    List SimStepData :=
  [false, true].flatMap fun marked =>
    simStepDataForStmtLeftSymbolsWithCode tc qCode stmt v side marked

theorem simStepDataForStmtMarked_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide) :
    simStepDataForStmtMarked tc stmt v side =
      simStepDataForStmtMarkedWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side := by
  unfold simStepDataForStmtMarked simStepDataForStmtMarkedWithCode
  apply List.flatMap_congr
  intro marked _hmarked
  exact simStepDataForStmtLeftSymbols_eq_withCode tc stmt v side marked

theorem simStepDataForStmtMarkedWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide =>
      simStepDataForStmtMarkedWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold simStepDataForStmtMarkedWithCode
  have hleft := simStepDataForStmtLeftSymbolsWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
  apply Primrec₂.mk
  exact hleft.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))))

theorem simStepDataForStmtMarked_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide) :
    simStepDataForStmtMarked tc q.1 q.2 side =
      [false, true].flatMap fun marked =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
          TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
            simStepDataOfTransition tc q side marked left right := by
  unfold simStepDataForStmtMarked
  apply List.flatMap_congr
  intro marked hmarked
  exact simStepDataForStmtLeftSymbols_eq_of_label tc q side marked

theorem simStepDataForStmtMarked_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide =>
      simStepDataForStmtMarked tc p.1 p.2.1 p.2.2) := by
  unfold simStepDataForStmtMarked
  have hleft := simStepDataForStmtLeftSymbols_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
  apply Primrec₂.mk
  exact hleft.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)))

theorem simStepDataForStmtMarked_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide =>
      simStepDataForStmtMarked tc p.1 p.2.1 p.2.2) :=
  simStepDataForStmtMarked_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simTransitionOfStep_eq_map_stepData (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) :
    simTransitionOfStep tc q side marked left right =
      (simStepDataOfTransition tc q side marked left right).map simStepDataRow := by
  unfold simTransitionOfStep simStepDataOfTransition
  cases h : TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) with
  | none =>
      rfl
  | some step =>
      rcases step with ⟨q', stmt⟩
      simp [simStepDataRow_ofStep]

private theorem filterMap_simTransition_eq_map_stepData {α : Type}
    (xs : List α) (f : α → Option SimStepData) :
    xs.filterMap (fun x => (f x).map simStepDataRow) =
      simRowsOfStepData (xs.filterMap f) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      cases h : f x <;> simp [h, simRowsOfStepData, ih]

private theorem flatMap_getElem?_range_length {α β : Type}
    (xs : List α) (f : α → List β) :
    (List.range xs.length).flatMap (fun i => (xs[i]?).elim [] f) =
    xs.flatMap f := by
  induction xs using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton xs x ih =>
      rw [List.length_append, List.length_singleton]
      rw [show xs.length + 1 = Nat.succ xs.length by omega]
      rw [List.range_succ, List.flatMap_append]
      have hprefix :
          (List.range xs.length).flatMap (fun i => ((xs ++ [x])[i]?).elim [] f) =
          (List.range xs.length).flatMap (fun i => (xs[i]?).elim [] f) := by
        apply List.flatMap_congr
        intro i hi
        have hi_lt : i < xs.length := by
          simpa [List.mem_range] using hi
        rw [List.getElem?_append_left hi_lt]
      rw [hprefix, ih]
      simp

/-- Descriptor-level folded simulation rows for one source label. -/
def simStepDataForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List SimStepData :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simStepDataOfTransition tc q side marked left right

def simStepDataForStmtLabel (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) : List SimStepData :=
  foldSideList.flatMap fun side =>
    simStepDataForStmtMarked tc stmt v side

def simStepDataForStmtLabelWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) : List SimStepData :=
  foldSideList.flatMap fun side =>
    simStepDataForStmtMarkedWithCode tc qCode stmt v side

theorem simStepDataForStmtLabel_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) :
    simStepDataForStmtLabel tc stmt v =
      simStepDataForStmtLabelWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v := by
  unfold simStepDataForStmtLabel simStepDataForStmtLabelWithCode
  apply List.flatMap_congr
  intro side _hside
  exact simStepDataForStmtMarked_eq_withCode tc stmt v side

theorem simStepDataForStmtLabelWithCode_none
    (tc : Turing.ToPartrec.Code) (qCode : Nat) (v : PartrecVar) :
    simStepDataForStmtLabelWithCode tc qCode none v = [] := by
  unfold simStepDataForStmtLabelWithCode simStepDataForStmtMarkedWithCode
    simStepDataForStmtLeftSymbolsWithCode simStepDataForStmtRightSymbolsWithCode
    simStepDataOfStmtTransitionWithCode sourceMachineStepOfStmt
  simp

theorem simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabelWithCode tc p.1 p.2.1 p.2.2) := by
  unfold simStepDataForStmtLabelWithCode
  have hmarked := simStepDataForStmtMarkedWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const foldSideList) ?_
  apply Primrec₂.mk
  exact hmarked.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)))

theorem simStepDataForStmtLabelWithCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabelWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForStmtLabelWithCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabelWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForStmtLabelWithCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataOfStmtTransitionWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {p : SimStepData}
    (h : simStepDataOfStmtTransitionWithCode tc qCode stmt v side marked left right =
      some p) :
    p.2.2.1 = qCode := by
  unfold simStepDataOfStmtTransitionWithCode at h
  cases hstep : sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none =>
      simp [hstep] at h
  | some step =>
      rcases step with ⟨q', tm0Stmt⟩
      have hp :
          simStepDataOfStepCode side marked qCode
            (TM0FiniteCompiler.stateCode tc q') left right tm0Stmt = p := by
        simpa [hstep] using h
      rw [← hp]
      rfl

theorem mem_simStepDataForStmtRightSymbolsWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {marked : Bool} {left : SourceSymbol}
    {p : SimStepData}
    (h : p ∈ simStepDataForStmtRightSymbolsWithCode tc qCode stmt v side marked left) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtRightSymbolsWithCode at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨right, _hright, hright⟩
  exact simStepDataOfStmtTransitionWithCode_currentCode hright

theorem mem_simStepDataForStmtLeftSymbolsWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {marked : Bool} {p : SimStepData}
    (h : p ∈ simStepDataForStmtLeftSymbolsWithCode tc qCode stmt v side marked) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtLeftSymbolsWithCode at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨left, _hleft, hleft⟩
  exact mem_simStepDataForStmtRightSymbolsWithCode_currentCode hleft

theorem mem_simStepDataForStmtMarkedWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {p : SimStepData}
    (h : p ∈ simStepDataForStmtMarkedWithCode tc qCode stmt v side) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtMarkedWithCode at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨marked, _hmarked, hmarked⟩
  exact mem_simStepDataForStmtLeftSymbolsWithCode_currentCode hmarked

theorem mem_simStepDataForStmtLabelWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {p : SimStepData}
    (h : p ∈ simStepDataForStmtLabelWithCode tc qCode stmt v) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtLabelWithCode at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨side, _hside, hside⟩
  exact mem_simStepDataForStmtMarkedWithCode_currentCode hside

theorem simStepDataForStmtLabel_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) :
    simStepDataForStmtLabel tc q.1 q.2 = simStepDataForLabel tc q := by
  unfold simStepDataForStmtLabel simStepDataForLabel
  apply List.flatMap_congr
  intro side hside
  exact simStepDataForStmtMarked_eq_of_label tc q side

theorem simStepDataForStmtLabel_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabel tc p.1 p.2) := by
  unfold simStepDataForStmtLabel
  have hmarked := simStepDataForStmtMarked_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const foldSideList) ?_
  apply Primrec₂.mk
  exact hmarked.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem simStepDataForStmtLabel_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabel tc p.1 p.2) :=
  simStepDataForStmtLabel_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

/--
Descriptor rows for a source-label index. This is a numeric outer enumeration
of the same semantic labels used by `simStepData`, avoiding a dependent label
as the externally visible iterator.
-/
def simStepDataForLabelIndex (tc : Turing.ToPartrec.Code) (i : Nat) :
    List SimStepData :=
  ((TM0Route.partrecStartedTM0LabelList tc)[i]?).elim [] (simStepDataForLabel tc)

/--
Offset form of `simStepDataForLabelIndex`, using the statement-decoder-based
label index from `TM0Route`. The extra `fuel` and statement offset `k` expose
the recursive state needed for the eventual primitive-recursive proof of the
descriptor list.
-/
def simStepDataForLabelIndexFrom
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i).elim []
    (simStepDataForLabel tc)

/--
Label lookup for the offset descriptor decoder, paired with the numeric finite
state code of the decoded current label.
-/
def labelAtByStatementFromWithStateCode?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (SourceLabel tc × Nat) :=
  (TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i).map
    fun q => (q, TM0FiniteCompiler.stateCode tc q)

/--
Position-code for the rectangular statement/variable label decoder.

The support list is `default :: labelList`, while the rectangular label list
itself starts with the same default label `(none, default)`.  To agree with the
forced start/default state, that duplicated label is coded as `0`; all other
rectangular positions use the shifted support-list position.
-/
def labelPositionCode {tc : Turing.ToPartrec.Code}
    (k i : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) : Nat :=
  if ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc then
    0
  else
    1 + k * TM0Route.partrecVarList.length + i

theorem labelPositionCode_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Option (SourceStmt tc) × PartrecVar =>
      labelPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let rect : Nat × Nat × Option (SourceStmt tc) × PartrecVar → Nat := fun p =>
    1 + p.1 * TM0Route.partrecVarList.length + p.2.1
  have hrect : Primrec rect := by
    exact Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1)
        (Primrec.nat_mul.comp Primrec.fst
          (Primrec.const TM0Route.partrecVarList.length)))
      (Primrec.fst.comp Primrec.snd)
  have hdefault : PrimrecPred
      (fun p : Nat × Nat × Option (SourceStmt tc) × PartrecVar =>
        ((p.2.2.1, p.2.2.2) : SourceLabel tc) = sourceDefaultLabel tc) :=
    Primrec.eq.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const (sourceDefaultLabel tc))
  exact (Primrec.ite hdefault
    (Primrec.const 0) hrect).of_eq fun p => by
      unfold labelPositionCode rect
      rfl

/-- One step of the position-coded offset label lookup. -/
def labelAtByStatementFromWithPositionCodeStep?
    (tc : Turing.ToPartrec.Code)
    (s : Option (SourceLabel tc × Nat) × Nat × Nat) :
    Option (SourceLabel tc × Nat) × Nat × Nat :=
  match s.1 with
  | some r => (some r, s.2)
  | none =>
      match TM0Route.partrecVarList[s.2.2]? with
      | some v =>
          ((TM0Route.partrecStartedTM0StatementAt? tc s.2.1).map fun stmt =>
            ((stmt, v), labelPositionCode s.2.1 s.2.2 stmt v),
            s.2.1, s.2.2)
      | none =>
          (none, s.2.1 + 1, s.2.2 - TM0Route.partrecVarList.length)

/--
Offset label lookup paired with the numeric position in the rectangular
statement-by-variable enumeration, including the leading default state.

The duplicated default label is mapped to state `0`; all other decoded
statement/variable positions use their support-list position.
-/
def labelAtByStatementFromWithPositionCode?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (SourceLabel tc × Nat) :=
  ((labelAtByStatementFromWithPositionCodeStep? tc)^[fuel] (none, k, i)).1

theorem labelAtByStatementFromWithPositionCodeStep?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (labelAtByStatementFromWithPositionCodeStep? tc) := by
  let State := Option (SourceLabel tc × Nat) × Nat × Nat
  let found : State → Option (SourceLabel tc × Nat) := fun s => s.1
  let offset : State → Nat := fun s => s.2.1
  let index : State → Nat := fun s => s.2.2
  have hfound : Primrec found := Primrec.fst
  have hoffset : Primrec offset := Primrec.fst.comp Primrec.snd
  have hindex : Primrec index := Primrec.snd.comp Primrec.snd
  have hstmt : Primrec (TM0Route.partrecStartedTM0StatementAt? tc) :=
    TM0Route.partrecStartedTM0StatementAt?_primrec_fixed tc
  have hnoneStep : Primrec (fun s : State =>
      ((none : Option (SourceLabel tc × Nat)),
        (offset s + 1, index s - TM0Route.partrecVarList.length))) := by
    exact Primrec.pair (Primrec.const (none : Option (SourceLabel tc × Nat)))
      (Primrec.pair (Primrec.succ.comp hoffset)
        (Primrec.nat_sub.comp hindex (Primrec.const TM0Route.partrecVarList.length)))
  have hsomeBlock : Primrec₂ (fun s : State => fun v : PartrecVar =>
      ((TM0Route.partrecStartedTM0StatementAt? tc (offset s)).map fun stmt =>
        ((stmt, v), labelPositionCode (offset s) (index s) stmt v),
        offset s, index s)) := by
    apply Primrec₂.mk
    let base : State × PartrecVar → State := fun p => p.1
    let vArg : State × PartrecVar → PartrecVar := fun p => p.2
    have hbase : Primrec base := Primrec.fst
    have hvArg : Primrec vArg := Primrec.snd
    have hoffsetBase : Primrec (fun p : State × PartrecVar => offset (base p)) :=
      hoffset.comp hbase
    have hindexBase : Primrec (fun p : State × PartrecVar => index (base p)) :=
      hindex.comp hbase
    have hget : Primrec (fun p : State × PartrecVar =>
        TM0Route.partrecStartedTM0StatementAt? tc (offset (base p))) :=
      hstmt.comp hoffsetBase
    have hpair : Primrec₂ (fun p : State × PartrecVar =>
        fun stmt : Option (SourceStmt tc) =>
          ((stmt, vArg p), labelPositionCode (offset (base p)) (index (base p)) stmt
            (vArg p))) := by
      apply Primrec₂.mk
      have hcode : Primrec (fun p : (State × PartrecVar) × Option (SourceStmt tc) =>
          labelPositionCode (offset (base p.1)) (index (base p.1)) p.2 (vArg p.1)) := by
        exact (labelPositionCode_primrec_fixed tc).comp
          (Primrec.pair
            (hoffsetBase.comp Primrec.fst)
            (Primrec.pair
              (hindexBase.comp Primrec.fst)
              (Primrec.pair Primrec.snd (hvArg.comp Primrec.fst))))
      exact Primrec.pair
        (Primrec.pair Primrec.snd (hvArg.comp Primrec.fst))
        hcode
    have hmap : Primrec (fun p : State × PartrecVar =>
        (TM0Route.partrecStartedTM0StatementAt? tc (offset (base p))).map
          fun stmt =>
            ((stmt, vArg p), labelPositionCode (offset (base p)) (index (base p)) stmt
              (vArg p))) :=
      Primrec.option_map hget hpair
    exact Primrec.pair hmap (Primrec.pair hoffsetBase hindexBase)
  have hnone : Primrec (fun s : State =>
      match TM0Route.partrecVarList[index s]? with
      | some v =>
          ((TM0Route.partrecStartedTM0StatementAt? tc (offset s)).map fun stmt =>
            ((stmt, v), labelPositionCode (offset s) (index s) stmt v),
            offset s, index s)
      | none =>
          ((none : Option (SourceLabel tc × Nat)),
            (offset s + 1, index s - TM0Route.partrecVarList.length))) := by
    have hlookup : Primrec (fun s : State => TM0Route.partrecVarList[index s]?) :=
      (Primrec.list_getElem?₁ TM0Route.partrecVarList).comp hindex
    exact (Primrec.option_casesOn hlookup hnoneStep hsomeBlock).of_eq fun s => by
      cases TM0Route.partrecVarList[index s]? <;> rfl
  have hsomeFound : Primrec₂ (fun s : State => fun r : SourceLabel tc × Nat =>
      (some r, s.2)) := by
    apply Primrec₂.mk
    exact Primrec.pair (Primrec.option_some.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.option_casesOn hfound hnone hsomeFound).of_eq fun s => by
    rcases s with ⟨r, k, i⟩
    cases r <;> rfl

theorem labelAtByStatementFromWithPositionCode?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      labelAtByStatementFromWithPositionCode? tc p.1 p.2.1 p.2.2) := by
  let step := labelAtByStatementFromWithPositionCodeStep? tc
  let init : Nat × Nat × Nat → Option (SourceLabel tc × Nat) × Nat × Nat :=
    fun p => (none, p.2.1, p.2.2)
  have hstep : Primrec step :=
    labelAtByStatementFromWithPositionCodeStep?_primrec_fixed tc
  have hinit : Primrec init :=
    Primrec.pair (Primrec.const (none : Option (SourceLabel tc × Nat))) Primrec.snd
  have hiter : Primrec (fun p : Nat × Nat × Nat => (step^[p.1]) (init p)) := by
    exact Primrec.nat_iterate Primrec.fst hinit ((hstep.comp Primrec.snd).to₂)
  exact (Primrec.fst.comp hiter).of_eq fun p => by
    rfl

theorem labelAtByStatementFromWithPositionCodeStep?_fixed_of_found
    (tc : Turing.ToPartrec.Code) (r : SourceLabel tc × Nat) (k i : Nat) :
    labelAtByStatementFromWithPositionCodeStep? tc (some r, k, i) =
      (some r, k, i) := by
  rfl

theorem labelAtByStatementFromWithPositionCodeStep?_fixed_of_stmt_none
    (tc : Turing.ToPartrec.Code) {k i : Nat} {v : PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = none) :
    labelAtByStatementFromWithPositionCodeStep? tc (none, k, i) =
      (none, k, i) := by
  unfold labelAtByStatementFromWithPositionCodeStep?
  simp [hv, hstmt]

theorem labelAtByStatementFromWithPositionCode?_zero
    (tc : Turing.ToPartrec.Code) (k i : Nat) :
    labelAtByStatementFromWithPositionCode? tc 0 k i = none := by
  rfl

theorem labelAtByStatementFromWithPositionCode?_succ_of_var_none
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    (hv : TM0Route.partrecVarList[i]? = none) :
    labelAtByStatementFromWithPositionCode? tc (fuel + 1) k i =
      labelAtByStatementFromWithPositionCode? tc fuel
        (k + 1) (i - TM0Route.partrecVarList.length) := by
  unfold labelAtByStatementFromWithPositionCode?
  rw [Function.iterate_succ_apply]
  unfold labelAtByStatementFromWithPositionCodeStep?
  simp [hv]

theorem labelAtByStatementFromWithPositionCode?_succ_of_stmt_none
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {v : PartrecVar}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = none) :
    labelAtByStatementFromWithPositionCode? tc (fuel + 1) k i = none := by
  unfold labelAtByStatementFromWithPositionCode?
  rw [Function.iterate_succ_apply]
  have hfixed := labelAtByStatementFromWithPositionCodeStep?_fixed_of_stmt_none
    tc hv hstmt
  rw [hfixed]
  rw [Function.iterate_fixed hfixed fuel]

theorem labelAtByStatementFromWithPositionCode?_succ_of_stmt_some
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {v : PartrecVar}
    {stmt : Option (SourceStmt tc)}
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt) :
    labelAtByStatementFromWithPositionCode? tc (fuel + 1) k i =
      some ((((stmt, v) : SourceLabel tc),
        labelPositionCode k i stmt v)) := by
  unfold labelAtByStatementFromWithPositionCode?
  rw [Function.iterate_succ_apply]
  unfold labelAtByStatementFromWithPositionCodeStep?
  simp only [hv, hstmt, Option.map_some]
  have hfixed := labelAtByStatementFromWithPositionCodeStep?_fixed_of_found
    tc ((((stmt, v) : SourceLabel tc),
      labelPositionCode k i stmt v)) k i
  change ((labelAtByStatementFromWithPositionCodeStep? tc)^[fuel]
      (some ((((stmt, v) : SourceLabel tc),
        labelPositionCode k i stmt v)), k, i)).1 =
    some ((((stmt, v) : SourceLabel tc),
      labelPositionCode k i stmt v))
  rw [Function.iterate_fixed hfixed fuel]
  rfl

theorem labelAtByStatementFromWithPositionCode?_of_div_mod
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    {stmt : Option (SourceStmt tc)} {v : PartrecVar}
    (hblock : i / TM0Route.partrecVarList.length < fuel)
    (hv : TM0Route.partrecVarList[i % TM0Route.partrecVarList.length]? = some v)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc
        (k + i / TM0Route.partrecVarList.length) = some stmt) :
    labelAtByStatementFromWithPositionCode? tc fuel k i =
      some ((((stmt, v) : SourceLabel tc),
        labelPositionCode (k + i / TM0Route.partrecVarList.length)
          (i % TM0Route.partrecVarList.length) stmt v)) := by
  induction fuel generalizing k i with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ hblock)
  | succ fuel ih =>
      by_cases hi : i < TM0Route.partrecVarList.length
      · have hdiv : i / TM0Route.partrecVarList.length = 0 := Nat.div_eq_of_lt hi
        have hmod : i % TM0Route.partrecVarList.length = i := Nat.mod_eq_of_lt hi
        have hvi : TM0Route.partrecVarList[i]? = some v := by
          simpa [hmod] using hv
        rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some
          (tc := tc) (fuel := fuel) (k := k) (i := i) (v := v)
          (stmt := stmt) hvi (by simpa [hdiv] using hstmt)]
        · simp [hdiv, hmod]
      · have hle : TM0Route.partrecVarList.length ≤ i := le_of_not_gt hi
        have hvnone : TM0Route.partrecVarList[i]? = none := by
          rw [List.getElem?_eq_none_iff]
          exact hle
        rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hvnone]
        have hlen : 0 < TM0Route.partrecVarList.length := by
          simp [TM0Route.partrecVarList]
        have hdiv :
            i / TM0Route.partrecVarList.length =
              (i - TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length + 1 := by
          calc
            i / TM0Route.partrecVarList.length =
                ((i - TM0Route.partrecVarList.length) +
                    TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length := by
              rw [Nat.sub_add_cancel hle]
            _ = (i - TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length + 1 := by
              rw [Nat.add_div_right _ hlen]
        have hblock' :
            (i - TM0Route.partrecVarList.length) /
                TM0Route.partrecVarList.length < fuel := by
          have hsucc :
              (i - TM0Route.partrecVarList.length) /
                  TM0Route.partrecVarList.length + 1 < fuel + 1 := by
            simpa [hdiv] using hblock
          exact Nat.succ_lt_succ_iff.1 hsucc
        have hmod :
            (i - TM0Route.partrecVarList.length) %
                TM0Route.partrecVarList.length =
              i % TM0Route.partrecVarList.length := by
          rw [← Nat.add_mod_right (i - TM0Route.partrecVarList.length)
            TM0Route.partrecVarList.length]
          have hsum :
              i - TM0Route.partrecVarList.length +
                  TM0Route.partrecVarList.length = i :=
            Nat.sub_add_cancel hle
          rw [hsum]
        have hv' :
            TM0Route.partrecVarList[
              (i - TM0Route.partrecVarList.length) %
                TM0Route.partrecVarList.length]? = some v := by
          simpa [hmod] using hv
        have hstmt' :
            TM0Route.partrecStartedTM0StatementAt? tc
                (k + 1 +
                  (i - TM0Route.partrecVarList.length) /
                    TM0Route.partrecVarList.length) = some stmt := by
          simpa [hdiv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstmt
        simpa [hdiv, hmod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (k := k + 1) hblock' hv' hstmt'

theorem labelPositionCode_mem_states_of_statementAt?
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    labelPositionCode k i stmt v ∈ TM0Route.partrecStartedTM0States tc := by
  by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
  · simpa [labelPositionCode, hdefault, TM0Route.partrecStartedTM0Start] using
      TM0Route.partrecStartedTM0Start_mem_states tc
  · rw [show labelPositionCode k i stmt v =
        1 + k * TM0Route.partrecVarList.length + i by
      simp [labelPositionCode, hdefault]]
    exact TM0Route.partrecStartedTM0_position_mem_states_of_statementAt?
      tc hstmt hv

theorem labelPositionCode_support_get?_of_statementAt?
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    (TM0Route.partrecStartedTM0LabelSupportList tc)[labelPositionCode k i stmt v]? =
      some ((stmt, v) : SourceLabel tc) := by
  by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
  · rw [show labelPositionCode k i stmt v = 0 by simp [labelPositionCode, hdefault]]
    rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero]
    rw [← sourceDefaultLabel_eq_default tc]
    exact congrArg some hdefault.symm
  · rw [show labelPositionCode k i stmt v =
        1 + k * TM0Route.partrecVarList.length + i by
      simp [labelPositionCode, hdefault]]
    exact TM0Route.partrecStartedTM0LabelSupportList_get_position_of_statementAt?
      tc hstmt hv

/--
If the statement-support list has no duplicates, the rectangular
statement/variable position is the first occurrence of its label in the support
list.
-/
theorem labelPositionCode_minimal_of_statementList_nodup
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hnodup : (TM0Route.partrecStartedTM0StatementList tc).Nodup)
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v) :
    ∀ m, m < labelPositionCode k i stmt v →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠
        some ((stmt, v) : SourceLabel tc) := by
  by_cases hdefault : ((stmt, v) : SourceLabel tc) = sourceDefaultLabel tc
  · simp [labelPositionCode, hdefault]
  · intro m hm hget
    have hcode :
        labelPositionCode k i stmt v = 1 + k * TM0Route.partrecVarList.length + i := by
      simp [labelPositionCode, hdefault]
    rw [hcode] at hm
    cases m with
    | zero =>
        rw [TM0Route.partrecStartedTM0LabelSupportList_get_zero] at hget
        have hq : (default : SourceLabel tc) = ((stmt, v) : SourceLabel tc) :=
          Option.some.inj hget
        have hqDefault : ((stmt, v) : SourceLabel tc) = (default : SourceLabel tc) :=
          hq.symm
        exact hdefault (hqDefault.trans (sourceDefaultLabel_eq_default tc).symm)
    | succ m =>
        unfold TM0Route.partrecStartedTM0LabelSupportList at hget
        simp only [List.getElem?_cons_succ] at hget
        unfold TM0Route.partrecStartedTM0LabelList at hget
        have hstmtList :
            (TM0Route.partrecStartedTM0StatementList tc)[k]? = some stmt := by
          simpa [TM0Route.partrecStartedTM0StatementAt?_eq_getElem? tc k] using hstmt
        have hrectGet :
            ((TM0Route.partrecStartedTM0StatementList tc).flatMap fun stmt =>
              TM0Route.partrecVarList.map fun v =>
                ((stmt, v) : SourceLabel tc))[k * TM0Route.partrecVarList.length + i]? =
              some ((stmt, v) : SourceLabel tc) := by
          exact TM0Route.flatMap_constMap_getElem?_of_getElem?
            (TM0Route.partrecStartedTM0StatementList tc) TM0Route.partrecVarList
            hstmtList hv
        have hrectNodup :
            ((TM0Route.partrecStartedTM0StatementList tc).flatMap fun stmt =>
              TM0Route.partrecVarList.map fun v =>
                ((stmt, v) : SourceLabel tc)).Nodup := by
          simpa only [SProd.sprod, List.product] using
            hnodup.product TM0Route.partrecVarList_nodup
        rcases List.getElem?_eq_some_iff.1 hget with ⟨hmLen, hmGet⟩
        rcases List.getElem?_eq_some_iff.1 hrectGet with ⟨hposLen, hposGet⟩
        have hmEq : m = k * TM0Route.partrecVarList.length + i := by
          exact (hrectNodup.getElem_inj_iff
            (i := m) (hi := hmLen)
            (j := k * TM0Route.partrecVarList.length + i) (hj := hposLen)).1 (by
              exact hmGet.trans hposGet.symm)
        omega

private theorem idxOf_eq_of_getElem?_eq_some_of_forall_lt_ne
    {α : Type} [DecidableEq α] (xs : List α) {n : Nat} {x : α}
    (hget : xs[n]? = some x)
    (hmin : ∀ m, m < n → xs[m]? ≠ some x) :
    xs.idxOf x = n := by
  induction xs generalizing n with
  | nil =>
      simp at hget
  | cons y ys ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst y
          simp
      | succ n =>
          simp only [List.getElem?_cons_succ] at hget
          have hyne : y ≠ x := by
            have h0 := hmin 0 (Nat.succ_pos n)
            simp only [List.getElem?_cons_zero] at h0
            intro hy
            subst y
            exact h0 rfl
          have hminTail : ∀ m, m < n → ys[m]? ≠ some x := by
            intro m hm
            have hs := hmin (m + 1) (Nat.succ_lt_succ hm)
            simpa only [List.getElem?_cons_succ] using hs
          rw [List.idxOf_cons_ne ys hyne, ih hget hminTail]

theorem stateCode_eq_of_support_get?_minimal
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc} {n : Nat}
    (hget : (TM0Route.partrecStartedTM0LabelSupportList tc)[n]? = some q)
    (hmin : ∀ m, m < n →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q) :
    TM0FiniteCompiler.stateCode tc q = n := by
  unfold TM0FiniteCompiler.stateCode
  exact idxOf_eq_of_getElem?_eq_some_of_forall_lt_ne
    (TM0Route.partrecStartedTM0LabelSupportList tc) hget hmin

theorem labelPositionCode_eq_stateCode_of_minimal
    (tc : Turing.ToPartrec.Code) {k i : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar}
    (hstmt : TM0Route.partrecStartedTM0StatementAt? tc k = some stmt)
    (hv : TM0Route.partrecVarList[i]? = some v)
    (hmin : ∀ m, m < labelPositionCode k i stmt v →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠
        some ((stmt, v) : SourceLabel tc)) :
    labelPositionCode k i stmt v = TM0FiniteCompiler.stateCode tc ((stmt, v) : SourceLabel tc) := by
  symm
  exact stateCode_eq_of_support_get?_minimal
    (labelPositionCode_support_get?_of_statementAt? tc hstmt hv) hmin

theorem labelAtByStatementFromWithPositionCode?_fst_eq
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    (labelAtByStatementFromWithPositionCode? tc fuel k i).map Prod.fst =
      TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero,
        TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero]
  | succ fuel ih =>
      rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_succ]
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv]
          exact ih (k + 1) (i - TM0Route.partrecVarList.length)
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt]
              simp
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt]
              rfl

theorem labelAtByStatementFromWithPositionCode?_code_mem_states
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    q.2 ∈ TM0Route.partrecStartedTM0States tc := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              exact labelPositionCode_mem_states_of_statementAt? tc hstmt hv

theorem labelAtByStatementFromWithPositionCode?_support_get?
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    (TM0Route.partrecStartedTM0LabelSupportList tc)[q.2]? = some q.1 := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              exact labelPositionCode_support_get?_of_statementAt? tc hstmt hv

theorem labelAtByStatementFromWithPositionCode?_label_eq_of_code_eq_stateCode
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    {target : SourceLabel tc}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target) :
    q.1 = target := by
  have hqget := labelAtByStatementFromWithPositionCode?_support_get? tc h
  have htargetget :
      (TM0Route.partrecStartedTM0LabelSupportList tc)[
          TM0FiniteCompiler.stateCode tc target]? = some target := by
    unfold TM0FiniteCompiler.stateCode
    exact List.getElem?_idxOf htarget
  rw [hcode] at hqget
  rw [htargetget] at hqget
  exact (Option.some.inj hqget).symm

theorem labelAtByStatementFromWithPositionCode?_minimal_of_statementList_nodup
    (tc : Turing.ToPartrec.Code)
    (hnodup : (TM0Route.partrecStartedTM0StatementList tc).Nodup)
    {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q) :
    ∀ m, m < q.2 →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1 := by
  induction fuel generalizing k i with
  | zero =>
      simp [labelAtByStatementFromWithPositionCode?_zero] at h
  | succ fuel ih =>
      cases hv : TM0Route.partrecVarList[i]? with
      | none =>
          rw [labelAtByStatementFromWithPositionCode?_succ_of_var_none tc hv] at h
          exact ih h
      | some v =>
          cases hstmt : TM0Route.partrecStartedTM0StatementAt? tc k with
          | none =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_none tc hv hstmt] at h
              simp at h
          | some stmt =>
              rw [labelAtByStatementFromWithPositionCode?_succ_of_stmt_some tc hv hstmt] at h
              cases h
              exact labelPositionCode_minimal_of_statementList_nodup
                tc hnodup hstmt hv

theorem labelAtByStatementFromWithPositionCode?_code_eq_stateCode_of_minimal
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat} {q : SourceLabel tc × Nat}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (hmin : ∀ m, m < q.2 →
      (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    q.2 = TM0FiniteCompiler.stateCode tc q.1 := by
  symm
  exact stateCode_eq_of_support_get?_minimal
    (labelAtByStatementFromWithPositionCode?_support_get? tc h) hmin

theorem labelAtByStatementFromWithPositionCode?_eq_stateCode_of_minimal
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    (hmin : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    labelAtByStatementFromWithPositionCode? tc fuel k i =
      labelAtByStatementFromWithStateCode? tc fuel k i := by
  unfold labelAtByStatementFromWithStateCode?
  cases hq : labelAtByStatementFromWithPositionCode? tc fuel k i with
  | none =>
      have hnone :
          TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i = none := by
        have hmap := congrArg (Option.map Prod.fst) hq
        simpa [labelAtByStatementFromWithPositionCode?_fst_eq tc fuel k i] using hmap
      simp [hnone]
  | some q =>
      have hlabel :
          TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i = some q.1 := by
        have hmap := congrArg (Option.map Prod.fst) hq
        simpa [labelAtByStatementFromWithPositionCode?_fst_eq tc fuel k i] using hmap
      have hcode : q.2 = TM0FiniteCompiler.stateCode tc q.1 :=
        labelAtByStatementFromWithPositionCode?_code_eq_stateCode_of_minimal
          tc hq (hmin q hq)
      rcases q with ⟨qLabel, qCode⟩
      change qCode = TM0FiniteCompiler.stateCode tc qLabel at hcode
      subst qCode
      simp [hlabel]

theorem labelAtByStatementFromWithStateCode?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      labelAtByStatementFromWithStateCode? tc p.1 p.2.1 p.2.2) := by
  have hlookup := TM0Route.partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hstate : Primrec (fun q : SourceLabel tc => TM0FiniteCompiler.stateCode tc q) :=
    TM0FiniteCompiler.stateCode_primrec_fixed tc
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc =>
      (q, TM0FiniteCompiler.stateCode tc q)) := by
    apply Primrec₂.mk
    exact Primrec.pair Primrec.snd (hstate.comp Primrec.snd)
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold labelAtByStatementFromWithStateCode?
    cases TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2 <;> rfl

/--
Offset label lookup paired with the numeric current-state code computed by the
executable support-position search.
-/
def labelAtByStatementFromWithSearchCode?
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    Option (SourceLabel tc × Nat) :=
  (TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i).map
    fun q => (q, TM0FiniteCompiler.stateCodeBySupportSearch tc
      (TM0Route.partrecStartedTM0StatementCount tc) q)

theorem labelAtByStatementFromWithSearchCode?_primrec_fixed
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : Nat × Nat × Nat =>
      labelAtByStatementFromWithSearchCode? tc p.1 p.2.1 p.2.2) := by
  have hlookup := TM0Route.partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hsearch : Primrec (fun q : SourceLabel tc =>
      TM0FiniteCompiler.stateCodeBySupportSearch tc
        (TM0Route.partrecStartedTM0StatementCount tc) q) := by
    exact (TM0FiniteCompiler.stateCodeBySupportSearch_primrec_fixed tc).comp
      (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
        Primrec.id)
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc =>
      (q, TM0FiniteCompiler.stateCodeBySupportSearch tc
        (TM0Route.partrecStartedTM0StatementCount tc) q)) := by
    apply Primrec₂.mk
    exact Primrec.pair Primrec.snd (hsearch.comp Primrec.snd)
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold labelAtByStatementFromWithSearchCode?
    cases TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2 <;> rfl

theorem labelAtByStatementFromWithSearchCode?_eq_stateCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    labelAtByStatementFromWithSearchCode? tc fuel k i =
      labelAtByStatementFromWithStateCode? tc fuel k i := by
  unfold labelAtByStatementFromWithSearchCode? labelAtByStatementFromWithStateCode?
  cases h : TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i with
  | none =>
      rfl
  | some q =>
      simp only [Option.map_some]
      rw [TM0FiniteCompiler.stateCodeBySupportSearch_eq_stateCode tc q
        (TM0Route.mem_partrecStartedTM0LabelSupportList_of_labelAtByStatementFrom?_eq_some h)]

/--
Offset label-index decoder factored through the numeric folded state code.

This has the same behavior as `simStepDataForLabelIndexFrom`, but its row
generator takes the state code as a separate natural number. This is the shape
needed by the source-level computability proof, where dependent labels should
only be used to decode statements and variables, not to hide the numeric state
fed to the finite program.
-/
def simStepDataForLabelIndexFromWithCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (labelAtByStatementFromWithStateCode? tc fuel k i).elim []
    (fun q => simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2)

def simStepDataForLabelIndexFromWithSearchCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (labelAtByStatementFromWithSearchCode? tc fuel k i).elim []
    (fun q => simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2)

/--
Offset label-index decoder using the explicit rectangular statement/variable
position as the numeric current-state code.

This is not used by the semantic route yet: it records the cleaner numeric
decoder target where the state code is computed directly from the decoded
statement offset and variable index rather than by searching the finite support
list.
-/
def simStepDataForLabelIndexFromWithPositionCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    List SimStepData :=
  (labelAtByStatementFromWithPositionCode? tc fuel k i).elim []
    (fun q => simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2)

theorem mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat} {p : SimStepData}
    (h : p ∈ simStepDataForLabelIndexFromWithPositionCode tc fuel k i) :
    ∃ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q ∧
        p.2.2.1 = q.2 ∧
        (TM0Route.partrecStartedTM0LabelSupportList tc)[p.2.2.1]? = some q.1 := by
  unfold simStepDataForLabelIndexFromWithPositionCode at h
  cases hq : labelAtByStatementFromWithPositionCode? tc fuel k i with
  | none =>
      rw [hq] at h
      cases h
  | some q =>
      have hmem : p ∈ simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2 := by
        simpa [hq] using h
      have hcode : p.2.2.1 = q.2 :=
        mem_simStepDataForStmtLabelWithCode_currentCode hmem
      refine ⟨q, rfl, hcode, ?_⟩
      rw [hcode]
      exact labelAtByStatementFromWithPositionCode?_support_get? tc hq

theorem mem_simStepDataForLabelIndexFromWithPositionCode_currentCode_ne
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat} {target : SourceLabel tc}
    {p : SimStepData}
    (hcode : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target)
    (h : p ∈ simStepDataForLabelIndexFromWithPositionCode tc fuel k i) :
    p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc target := by
  rcases mem_simStepDataForLabelIndexFromWithPositionCode_current_support_get?
      (tc := tc) (fuel := fuel) (k := k) (i := i) h with
    ⟨q, hq, hpcode, _hget⟩
  rw [hpcode]
  exact hcode q hq

theorem simRowsOfStepDataForLabelIndexFromWithPositionCode_find?_eq_none_of_currentCode_ne
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat}
    {side : FoldSide} {marked : Bool} {target : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        q.2 ≠ TM0FiniteCompiler.stateCode tc target) :
    (simRowsOfStepData
        (simStepDataForLabelIndexFromWithPositionCode tc fuel k i)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side target)
            (foldedSymbolCode marked left right)) =
      none := by
  exact simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
    (tc := tc)
    (steps := simStepDataForLabelIndexFromWithPositionCode tc fuel k i)
    (side := side) (marked := marked) (q := target)
    (left := left) (right := right)
    (fun p hp =>
      mem_simStepDataForLabelIndexFromWithPositionCode_currentCode_ne
        (tc := tc) (fuel := fuel) (k := k) (i := i)
        (target := target) hcode hp)

theorem simStepDataForLabelIndexFromWithPositionCode_eq_target_of_currentCode_eq_stateCode
    {tc : Turing.ToPartrec.Code} {fuel k i : Nat}
    {q : SourceLabel tc × Nat} {target : SourceLabel tc}
    (h : labelAtByStatementFromWithPositionCode? tc fuel k i = some q)
    (htarget : target ∈ TM0Route.partrecStartedTM0LabelSupportList tc)
    (hcode : q.2 = TM0FiniteCompiler.stateCode tc target) :
    simStepDataForLabelIndexFromWithPositionCode tc fuel k i =
      simStepDataForStmtLabelWithCode tc
        (TM0FiniteCompiler.stateCode tc target) target.1 target.2 := by
  have hlabel :=
    labelAtByStatementFromWithPositionCode?_label_eq_of_code_eq_stateCode
      tc h htarget hcode
  unfold simStepDataForLabelIndexFromWithPositionCode
  rw [h]
  simp [hlabel, hcode]

theorem simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    simStepDataForLabelIndexFromWithSearchCode tc fuel k i =
      simStepDataForLabelIndexFromWithCode tc fuel k i := by
  unfold simStepDataForLabelIndexFromWithSearchCode simStepDataForLabelIndexFromWithCode
  rw [labelAtByStatementFromWithSearchCode?_eq_stateCode]

theorem simStepDataForLabelIndexFrom_eq_withCode
    (tc : Turing.ToPartrec.Code) (fuel k i : Nat) :
    simStepDataForLabelIndexFrom tc fuel k i =
      simStepDataForLabelIndexFromWithCode tc fuel k i := by
  unfold simStepDataForLabelIndexFrom simStepDataForLabelIndexFromWithCode
    labelAtByStatementFromWithStateCode?
  cases h : TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc fuel k i with
  | none =>
      simp only [Option.map_none, Option.elim_none]
  | some q =>
      simp only [Option.elim_some, Option.map_some]
      rw [← simStepDataForStmtLabel_eq_of_label tc q,
        simStepDataForStmtLabel_eq_withCode tc q.1 q.2]
      rfl

theorem simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
    (tc : Turing.ToPartrec.Code) {fuel k i : Nat}
    (hmin : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc fuel k i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simStepDataForLabelIndexFromWithPositionCode tc fuel k i =
      simStepDataForLabelIndexFromWithCode tc fuel k i := by
  unfold simStepDataForLabelIndexFromWithPositionCode simStepDataForLabelIndexFromWithCode
  rw [labelAtByStatementFromWithPositionCode?_eq_stateCode_of_minimal tc hmin]

/--
Canonical offset start for `simStepDataForLabelIndexFrom`: scan from statement
offset `0` with exactly the computed statement-support count as fuel.
-/
def simStepDataForLabelIndexStart (tc : Turing.ToPartrec.Code) (i : Nat) :
    List SimStepData :=
  simStepDataForLabelIndexFrom tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

/-- Canonical offset start for the numeric-state offset decoder. -/
def simStepDataForLabelIndexStartWithCode (tc : Turing.ToPartrec.Code) (i : Nat) :
    List SimStepData :=
  simStepDataForLabelIndexFromWithCode tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

/-- Canonical offset start for the bounded-search numeric-state decoder. -/
def simStepDataForLabelIndexStartWithSearchCode
    (tc : Turing.ToPartrec.Code) (i : Nat) : List SimStepData :=
  simStepDataForLabelIndexFromWithSearchCode tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

/-- Canonical offset start for the position-coded offset decoder. -/
def simStepDataForLabelIndexStartWithPositionCode
    (tc : Turing.ToPartrec.Code) (i : Nat) : List SimStepData :=
  simStepDataForLabelIndexFromWithPositionCode tc
    (TM0Route.partrecStartedTM0StatementCount tc) 0 i

theorem simStepDataForLabelIndex_eq_labelAt
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndex tc i =
      (TM0Route.partrecStartedTM0LabelAt? tc i).elim [] (simStepDataForLabel tc) := by
  unfold simStepDataForLabelIndex
  rw [TM0Route.partrecStartedTM0LabelAt?_eq_getElem?]

theorem simStepDataForLabelIndex_eq_labelAtByStatement
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndex tc i =
      (TM0Route.partrecStartedTM0LabelAtByStatement? tc i).elim []
        (simStepDataForLabel tc) := by
  rw [simStepDataForLabelIndex_eq_labelAt,
    TM0Route.partrecStartedTM0LabelAtByStatement?_eq_labelAt]

theorem simStepDataForLabelIndexFrom_zero_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexFrom tc
        (TM0Route.partrecStartedTM0StatementCount tc) 0 i =
      simStepDataForLabelIndex tc i := by
  unfold simStepDataForLabelIndexFrom
  rw [TM0Route.partrecStartedTM0LabelAtByStatementFrom?_zero_eq]
  rw [simStepDataForLabelIndex_eq_labelAtByStatement]

theorem simStepDataForLabelIndexStart_eq_withCode
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStart tc i =
      simStepDataForLabelIndexStartWithCode tc i := by
  unfold simStepDataForLabelIndexStart simStepDataForLabelIndexStartWithCode
  exact simStepDataForLabelIndexFrom_eq_withCode
    tc (TM0Route.partrecStartedTM0StatementCount tc) 0 i

theorem simStepDataForLabelIndexStartWithSearchCode_eq_withCode
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStartWithSearchCode tc i =
      simStepDataForLabelIndexStartWithCode tc i := by
  unfold simStepDataForLabelIndexStartWithSearchCode simStepDataForLabelIndexStartWithCode
  exact simStepDataForLabelIndexFromWithSearchCode_eq_withCode
    tc (TM0Route.partrecStartedTM0StatementCount tc) 0 i

theorem simStepDataForLabelIndexFrom_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom tc p.1 p.2.1 p.2.2) := by
  have hlookup := TM0Route.partrecStartedTM0LabelAtByStatementFrom?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabel_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc =>
      simStepDataForStmtLabel tc q.1 q.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFrom
    cases h : TM0Route.partrecStartedTM0LabelAtByStatementFrom? tc p.1 p.2.1 p.2.2 with
    | none =>
        rfl
    | some q =>
        exact simStepDataForStmtLabel_eq_of_label tc q

theorem simStepDataForLabelIndexFromWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode tc p.1 p.2.1 p.2.2) := by
  have hlookup := labelAtByStatementFromWithStateCode?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc × Nat =>
      simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFromWithCode
    cases labelAtByStatementFromWithStateCode? tc p.1 p.2.1 p.2.2 <;> rfl

theorem simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode tc p.1 p.2.1 p.2.2) := by
  have hlookup := labelAtByStatementFromWithSearchCode?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc × Nat =>
      simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFromWithSearchCode
    cases labelAtByStatementFromWithSearchCode? tc p.1 p.2.1 p.2.2 <;> rfl

theorem simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode tc p.1 p.2.1 p.2.2) := by
  have hlookup := labelAtByStatementFromWithPositionCode?_primrec_fixed tc
  have hlabel := simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc haux
  have hnone : Primrec (fun _p : Nat × Nat × Nat => ([] : List SimStepData)) :=
    Primrec.const []
  have hsome : Primrec₂ (fun _p : Nat × Nat × Nat => fun q : SourceLabel tc × Nat =>
      simStepDataForStmtLabelWithCode tc q.2 q.1.1 q.1.2) := by
    apply Primrec₂.mk
    exact hlabel.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.option_casesOn hlookup hnone hsome).of_eq fun p => by
    unfold simStepDataForLabelIndexFromWithPositionCode
    cases labelAtByStatementFromWithPositionCode? tc p.1 p.2.1 p.2.2 <;> rfl

theorem simStepDataForLabelIndexFromWithCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFromWithCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFromWithSearchCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFromWithPositionCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexFrom_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFrom_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexFrom_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom tc p.1 p.2.1 p.2.2) :=
  simStepDataForLabelIndexFrom_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStart_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStart tc i = simStepDataForLabelIndex tc i := by
  unfold simStepDataForLabelIndexStart
  exact simStepDataForLabelIndexFrom_zero_eq tc i

theorem simStepDataForLabelIndexStartWithCode_eq
    (tc : Turing.ToPartrec.Code) (i : Nat) :
    simStepDataForLabelIndexStartWithCode tc i =
      simStepDataForLabelIndex tc i := by
  rw [← simStepDataForLabelIndexStart_eq_withCode]
  exact simStepDataForLabelIndexStart_eq tc i

theorem simStepDataForLabelIndexStart_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStart tc) := by
  unfold simStepDataForLabelIndexStart
  exact (simStepDataForLabelIndexFrom_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStartWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStartWithCode tc) := by
  unfold simStepDataForLabelIndexStartWithCode
  exact (simStepDataForLabelIndexFromWithCode_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStartWithSearchCode tc) := by
  unfold simStepDataForLabelIndexStartWithSearchCode
  exact (simStepDataForLabelIndexFromWithSearchCode_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndexStartWithPositionCode tc) := by
  unfold simStepDataForLabelIndexStartWithPositionCode
  exact (simStepDataForLabelIndexFromWithPositionCode_primrec_fixed_of_trAux tc haux).comp
    (Primrec.pair (Primrec.const (TM0Route.partrecStartedTM0StatementCount tc))
      (Primrec.pair (Primrec.const 0) Primrec.id))

theorem simStepDataForLabelIndexStart_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStart tc) :=
  simStepDataForLabelIndexStart_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStartWithCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStartWithCode tc) :=
  simStepDataForLabelIndexStartWithCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStartWithSearchCode tc) :=
  simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndexStartWithPositionCode tc) :=
  simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndexStart_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStart tc) :=
  simStepDataForLabelIndexStart_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStartWithCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStartWithCode tc) :=
  simStepDataForLabelIndexStartWithCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStartWithSearchCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStartWithSearchCode tc) :=
  simStepDataForLabelIndexStartWithSearchCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndexStartWithPositionCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndexStartWithPositionCode tc) :=
  simStepDataForLabelIndexStartWithPositionCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataForLabelIndex_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (simStepDataForLabelIndex tc) :=
  (simStepDataForLabelIndexStart_primrec_fixed_of_trAux tc haux).of_eq fun i =>
    simStepDataForLabelIndexStart_eq tc i

theorem simStepDataForLabelIndex_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (simStepDataForLabelIndex tc) :=
  simStepDataForLabelIndex_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForLabelIndex_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (simStepDataForLabelIndex tc) :=
  simStepDataForLabelIndex_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

/--
Indexed mirror of `simStepData`. This is definitionally driven by the
primitive-recursive label count; the theorem below connects it to the semantic
label-list enumeration.
-/
def simStepDataByLabelIndex (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndex tc)

/-- Indexed descriptor enumeration through the numeric-state decoder path. -/
def simStepDataByLabelIndexWithCode (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndexStartWithCode tc)

/-- Indexed descriptor enumeration through the bounded-search decoder path. -/
def simStepDataByLabelIndexWithSearchCode
    (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndexStartWithSearchCode tc)

/-- Indexed descriptor enumeration through the position-coded decoder path. -/
def simStepDataByLabelIndexWithPositionCode
    (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (List.range (TM0Route.partrecStartedTM0LabelCount tc)).flatMap
    (simStepDataForLabelIndexStartWithPositionCode tc)

theorem simStepDataByLabelIndex_primrec_of_forLabelIndex
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndex p.1 p.2)) :
    Primrec simStepDataByLabelIndex := by
  unfold simStepDataByLabelIndex
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem simStepDataByLabelIndexWithCode_primrec_of_forLabelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec simStepDataByLabelIndexWithCode := by
  unfold simStepDataByLabelIndexWithCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem simStepDataByLabelIndexWithSearchCode_primrec_of_forLabelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec simStepDataByLabelIndexWithSearchCode := by
  unfold simStepDataByLabelIndexWithSearchCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

theorem simStepDataByLabelIndexWithPositionCode_primrec_of_forLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec simStepDataByLabelIndexWithPositionCode := by
  unfold simStepDataByLabelIndexWithPositionCode
  refine Primrec.list_flatMap
    (Primrec.list_range.comp TM0Route.partrecStartedTM0LabelCount_primrec) ?_
  apply Primrec₂.mk
  exact hindex

def simRowsForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List PostTransition :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simTransitionOfStep tc q side marked left right

def simRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q => simRowsForLabel tc q

theorem simRowsForLabel_eq_stepData (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    simRowsForLabel tc q = simRowsOfStepData (simStepDataForLabel tc q) := by
  unfold simRowsForLabel simStepDataForLabel
  simp only [simTransitionOfStep_eq_map_stepData]
  simp [simRowsOfStepData, filterMap_simTransition_eq_map_stepData,
    List.map_flatMap]

/-- Descriptor-level folded simulation rows. -/
def simStepData (tc : Turing.ToPartrec.Code) : List SimStepData :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q => simStepDataForLabel tc q

theorem simStepDataByLabelIndex_eq (tc : Turing.ToPartrec.Code) :
    simStepDataByLabelIndex tc = simStepData tc := by
  unfold simStepDataByLabelIndex simStepDataForLabelIndex simStepData
  rw [← TM0Route.partrecStartedTM0LabelList_length tc]
  exact flatMap_getElem?_range_length
    (TM0Route.partrecStartedTM0LabelList tc) (fun q => simStepDataForLabel tc q)

theorem simStepDataByLabelIndexWithCode_eq (tc : Turing.ToPartrec.Code) :
    simStepDataByLabelIndexWithCode tc = simStepData tc := by
  unfold simStepDataByLabelIndexWithCode
  rw [← simStepDataByLabelIndex_eq tc]
  unfold simStepDataByLabelIndex
  apply List.flatMap_congr
  intro i _hi
  exact simStepDataForLabelIndexStartWithCode_eq tc i

theorem simStepDataByLabelIndexWithSearchCode_eq (tc : Turing.ToPartrec.Code) :
    simStepDataByLabelIndexWithSearchCode tc = simStepData tc := by
  unfold simStepDataByLabelIndexWithSearchCode
  rw [← simStepDataByLabelIndexWithCode_eq tc]
  unfold simStepDataByLabelIndexWithCode
  apply List.flatMap_congr
  intro i _hi
  exact simStepDataForLabelIndexStartWithSearchCode_eq_withCode tc i

theorem simStepDataForLabelIndexStartWithPositionCode_eq_withCode_of_minimal
    (tc : Turing.ToPartrec.Code) {i : Nat}
    (hmin : ∀ q : SourceLabel tc × Nat,
      labelAtByStatementFromWithPositionCode? tc
          (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
        ∀ m, m < q.2 →
          (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simStepDataForLabelIndexStartWithPositionCode tc i =
      simStepDataForLabelIndexStartWithCode tc i := by
  unfold simStepDataForLabelIndexStartWithPositionCode
    simStepDataForLabelIndexStartWithCode
  exact simStepDataForLabelIndexFromWithPositionCode_eq_withCode_of_minimal
    tc hmin

theorem simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal
    (tc : Turing.ToPartrec.Code)
    (hmin : ∀ i, i < TM0Route.partrecStartedTM0LabelCount tc →
      ∀ q : SourceLabel tc × Nat,
        labelAtByStatementFromWithPositionCode? tc
            (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simStepDataByLabelIndexWithPositionCode tc =
      simStepDataByLabelIndexWithCode tc := by
  unfold simStepDataByLabelIndexWithPositionCode simStepDataByLabelIndexWithCode
  apply List.flatMap_congr
  intro i hi
  have hiCount : i < TM0Route.partrecStartedTM0LabelCount tc := by
    simpa [List.mem_range] using hi
  exact simStepDataForLabelIndexStartWithPositionCode_eq_withCode_of_minimal
    tc (hmin i hiCount)

theorem simRows_eq_stepData (tc : Turing.ToPartrec.Code) :
    simRows tc = simRowsOfStepData (simStepData tc) := by
  unfold simRows simStepData
  simp [simRowsForLabel_eq_stepData, simRowsOfStepData, List.map_flatMap]

theorem simRowsOfStepDataByLabelIndexWithPositionCode_eq_of_minimal
    (tc : Turing.ToPartrec.Code)
    (hmin : ∀ i, i < TM0Route.partrecStartedTM0LabelCount tc →
      ∀ q : SourceLabel tc × Nat,
        labelAtByStatementFromWithPositionCode? tc
            (TM0Route.partrecStartedTM0StatementCount tc) 0 i = some q →
          ∀ m, m < q.2 →
            (TM0Route.partrecStartedTM0LabelSupportList tc)[m]? ≠ some q.1) :
    simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) =
      simRows tc := by
  rw [simStepDataByLabelIndexWithPositionCode_eq_withCode_of_minimal tc hmin]
  rw [simStepDataByLabelIndexWithCode_eq]
  exact (simRows_eq_stepData tc).symm

def programOfParts (qCodes : List Nat) (init sim : List PostTransition) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateListOfCodes qCodes
  blank := foldedBlank
  start := foldedStartState
  table := init ++ sim

theorem programOfParts_primrec :
    Primrec (fun p : List Nat × List PostTransition × List PostTransition =>
      programOfParts p.1 p.2.1 p.2.2) := by
  unfold programOfParts
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const foldedSymbolList)
      (Primrec.pair (foldedStateListOfCodes_primrec.comp Primrec.fst)
        (Primrec.pair (Primrec.const foldedBlank)
          (Primrec.pair (Primrec.const foldedStartState)
            (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
              (Primrec.snd.comp Primrec.snd))))))

def programOfCountAndRows (stateCount : Nat) (init sim : List PostTransition) :
    FiniteTM0Program :=
  programOfParts (List.range stateCount) init sim

theorem programOfCountAndRows_primrec :
    Primrec (fun p : Nat × List PostTransition × List PostTransition =>
      programOfCountAndRows p.1 p.2.1 p.2.2) := by
  unfold programOfCountAndRows
  exact programOfParts_primrec.comp
    (Primrec.pair (Primrec.list_range.comp Primrec.fst) Primrec.snd)

def programOfCountAndSimRows (stateCount : Nat) (sim : List PostTransition) :
    FiniteTM0Program :=
  programOfCountAndRows stateCount initRowsData sim

theorem programOfCountAndSimRows_primrec :
    Primrec (fun p : Nat × List PostTransition =>
      programOfCountAndSimRows p.1 p.2) := by
  unfold programOfCountAndSimRows
  exact programOfCountAndRows_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.const initRowsData) Primrec.snd))

theorem programOfCountAndSimRows_computable :
    Computable (fun p : Nat × List PostTransition =>
      programOfCountAndSimRows p.1 p.2) :=
  programOfCountAndSimRows_primrec.to_comp

/--
Build normalized folded program data from a numeric state count and a list of
numeric simulation-step descriptors.
-/
def programDataOfStepData (stateCount : Nat) (steps : List SimStepData) :
    FiniteTM0Program :=
  programOfCountAndSimRows stateCount (simRowsOfStepData steps)

theorem programDataOfStepData_primrec :
    Primrec (fun p : Nat × List SimStepData =>
      programDataOfStepData p.1 p.2) := by
  unfold programDataOfStepData
  exact programOfCountAndSimRows_primrec.comp
    (Primrec.pair Primrec.fst (simRowsOfStepData_primrec.comp Primrec.snd))

theorem programDataOfStepData_computable :
    Computable (fun p : Nat × List SimStepData =>
      programDataOfStepData p.1 p.2) :=
  programDataOfStepData_primrec.to_comp

def appendSimRows (P : FiniteTM0Program) (sim : List PostTransition) : FiniteTM0Program :=
  { P with table := P.table ++ sim }

theorem appendSimRows_primrec :
    Primrec (fun p : FiniteTM0Program × List PostTransition =>
      appendSimRows p.1 p.2) := by
  unfold appendSimRows
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (PostProgram.symbols_primrec.comp Primrec.fst)
      (Primrec.pair (PostProgram.states_primrec.comp Primrec.fst)
        (Primrec.pair (PostProgram.blank_primrec.comp Primrec.fst)
          (Primrec.pair (PostProgram.start_primrec.comp Primrec.fst)
            (Primrec.list_append.comp
              (PostProgram.table_primrec.comp Primrec.fst) Primrec.snd)))))

theorem appendSimRows_computable :
    Computable (fun p : FiniteTM0Program × List PostTransition =>
      appendSimRows p.1 p.2) :=
  appendSimRows_primrec.to_comp

def program (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programOfCountAndRows (TM0Route.partrecStartedTM0StateCount tc) (initRows tc) (simRows tc)

theorem program_eq_programOfParts (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfParts (TM0Route.partrecStartedTM0States tc) (initRows tc) (simRows tc) := rfl

theorem program_eq_programOfCountAndRows (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfCountAndRows (TM0Route.partrecStartedTM0StateCount tc)
        (initRows tc) (simRows tc) := rfl

theorem program_eq_programOfCountAndSimRows (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfCountAndSimRows (TM0Route.partrecStartedTM0StateCount tc) (simRows tc) := by
  rw [program_eq_programOfCountAndRows, programOfCountAndSimRows, initRows_eq_data]

/--
Normalized form of `program` that exposes the constant initial rows
definitionally.
-/
def programData (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programOfCountAndSimRows (TM0Route.partrecStartedTM0StateCount tc) (simRows tc)

theorem programData_eq_program (tc : Turing.ToPartrec.Code) :
    programData tc = program tc :=
  (program_eq_programOfCountAndSimRows tc).symm

/--
Finite folded program generated from position-coded descriptors.

Unlike `programData`, this may contain extra noncanonical simulation rows when
the statement support list has duplicates.  Those rows are intended to be
handled semantically by proving that canonical execution never selects them.
-/
def positionProgramData (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programDataOfStepData (TM0Route.partrecStartedTM0StateCount tc)
    (simStepDataByLabelIndexWithPositionCode tc)

theorem positionProgramData_eq_programOfCountAndSimRows
    (tc : Turing.ToPartrec.Code) :
    positionProgramData tc =
      programOfCountAndSimRows (TM0Route.partrecStartedTM0StateCount tc)
        (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)) := by
  rfl

theorem positionProgramData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode) :
    Primrec positionProgramData := by
  unfold positionProgramData
  exact programDataOfStepData_primrec.comp
    (Primrec.pair TM0Route.partrecStartedTM0StateCount_primrec hsteps)

theorem positionProgramData_computable_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode) :
    Computable positionProgramData :=
  (positionProgramData_primrec_of_simStepDataByLabelIndexWithPositionCode hsteps).to_comp

theorem positionProgramData_primrec_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Primrec positionProgramData :=
  positionProgramData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (simStepDataByLabelIndexWithPositionCode_primrec_of_forLabelIndexStartWithPositionCode
      hindex)

theorem positionProgramData_computable_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2)) :
    Computable positionProgramData :=
  (positionProgramData_primrec_of_simStepDataForLabelIndexStartWithPositionCode hindex).to_comp

theorem positionProgramData_primrec_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec positionProgramData :=
  positionProgramData_primrec_of_simStepDataForLabelIndexStartWithPositionCode <| by
    unfold simStepDataForLabelIndexStartWithPositionCode
    exact hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (TM0Route.partrecStartedTM0StatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))

theorem positionProgramData_computable_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable positionProgramData :=
  (positionProgramData_primrec_of_simStepDataForLabelIndexFromWithPositionCode hindex).to_comp

/--
The remaining computability obligation for `programData` can be reduced to a
primitive-recursive list of numeric step descriptors whose generated rows are
exactly the semantic `simRows`.
-/
theorem programData_primrec_of_stepData
    (stepData : Turing.ToPartrec.Code → List SimStepData)
    (hsteps : Primrec stepData)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (stepData tc) = simRows tc) :
    Primrec programData := by
  have hdata : Primrec fun tc : Turing.ToPartrec.Code =>
      programDataOfStepData (TM0Route.partrecStartedTM0StateCount tc) (stepData tc) :=
    programDataOfStepData_primrec.comp
      (Primrec.pair TM0Route.partrecStartedTM0StateCount_primrec hsteps)
  exact hdata.of_eq fun tc => by
    unfold programData programDataOfStepData
    rw [hrows tc]

theorem programData_computable_of_stepData
    (stepData : Turing.ToPartrec.Code → List SimStepData)
    (hsteps : Primrec stepData)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (stepData tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_stepData stepData hsteps hrows).to_comp

/--
The remaining global computability target for normalized folded program data is
the primitive recursiveness of the descriptor list `simStepData`.
-/
theorem programData_primrec_of_simStepData
    (hsteps : Primrec simStepData) :
    Primrec programData :=
  programData_primrec_of_stepData simStepData hsteps
    fun tc => (simRows_eq_stepData tc).symm

theorem programData_computable_of_simStepData
    (hsteps : Primrec simStepData) :
    Computable programData :=
  (programData_primrec_of_simStepData hsteps).to_comp

/--
Indexed descriptor enumeration is enough for computability of normalized
folded program data.
-/
theorem programData_primrec_of_simStepDataByLabelIndex
    (hsteps : Primrec simStepDataByLabelIndex) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndex hsteps fun tc => by
    rw [simStepDataByLabelIndex_eq, ← simRows_eq_stepData]

theorem programData_computable_of_simStepDataByLabelIndex
    (hsteps : Primrec simStepDataByLabelIndex) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndex hsteps).to_comp

theorem programData_primrec_of_simStepDataByLabelIndexWithCode
    (hsteps : Primrec simStepDataByLabelIndexWithCode) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndexWithCode hsteps fun tc => by
    rw [simStepDataByLabelIndexWithCode_eq, ← simRows_eq_stepData]

theorem programData_computable_of_simStepDataByLabelIndexWithCode
    (hsteps : Primrec simStepDataByLabelIndexWithCode) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndexWithCode hsteps).to_comp

theorem programData_primrec_of_simStepDataByLabelIndexWithSearchCode
    (hsteps : Primrec simStepDataByLabelIndexWithSearchCode) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndexWithSearchCode hsteps fun tc => by
    rw [simStepDataByLabelIndexWithSearchCode_eq, ← simRows_eq_stepData]

theorem programData_computable_of_simStepDataByLabelIndexWithSearchCode
    (hsteps : Primrec simStepDataByLabelIndexWithSearchCode) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndexWithSearchCode hsteps).to_comp

/--
Position-coded indexed descriptors are enough for computability once their
generated rows are proved to be the semantic folded simulation rows. This
isolates the remaining equality/uniqueness work for the position-code route.
-/
theorem programData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Primrec programData :=
  programData_primrec_of_stepData simStepDataByLabelIndexWithPositionCode hsteps hrows

theorem programData_computable_of_simStepDataByLabelIndexWithPositionCode
    (hsteps : Primrec simStepDataByLabelIndexWithPositionCode)
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_simStepDataByLabelIndexWithPositionCode hsteps hrows).to_comp

theorem programData_primrec_of_simStepDataForLabelIndex
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndex p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndex
    (simStepDataByLabelIndex_primrec_of_forLabelIndex hindex)

theorem programData_computable_of_simStepDataForLabelIndex
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndex p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndex hindex).to_comp

/--
The offset-start descriptor enumeration is enough for computability of
normalized folded program data. This is the form targeted by the remaining
structural decoder proof.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStart
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStart p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndex
    (hindex.of_eq fun p => by
      exact simStepDataForLabelIndexStart_eq p.1 p.2)

theorem programData_computable_of_simStepDataForLabelIndexStart
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStart p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStart hindex).to_comp

/--
The canonical numeric-state indexed descriptor decoder is enough for primitive
recursiveness of normalized folded program data.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndexWithCode
    (simStepDataByLabelIndexWithCode_primrec_of_forLabelIndexStartWithCode hindex)

theorem programData_computable_of_simStepDataForLabelIndexStartWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithCode p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStartWithCode hindex).to_comp

/--
The bounded-search numeric-state offset-start decoder is enough for primitive
recursiveness of normalized folded program data.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndexWithSearchCode
    (simStepDataByLabelIndexWithSearchCode_primrec_of_forLabelIndexStartWithSearchCode
      hindex)

theorem programData_computable_of_simStepDataForLabelIndexStartWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithSearchCode p.1 p.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStartWithSearchCode hindex).to_comp

/--
The position-coded offset-start descriptor decoder is enough for primitive
recursiveness of normalized folded program data once the resulting indexed rows
are identified with the semantic folded simulation rows.
-/
theorem programData_primrec_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Primrec programData :=
  programData_primrec_of_simStepDataByLabelIndexWithPositionCode
    (simStepDataByLabelIndexWithPositionCode_primrec_of_forLabelIndexStartWithPositionCode
      hindex)
    hrows

theorem programData_computable_of_simStepDataForLabelIndexStartWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat =>
      simStepDataForLabelIndexStartWithPositionCode p.1 p.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexStartWithPositionCode hindex hrows).to_comp

/--
The fully offset descriptor decoder is enough for primitive recursiveness of
normalized folded program data. This isolates the remaining local recursion:
given `(tc, fuel, statementOffset, residualIndex)`, produce the descriptor rows
for the decoded label.
-/
theorem programData_primrec_of_simStepDataForLabelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexStart <| by
    unfold simStepDataForLabelIndexStart
    exact hindex.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (TM0Route.partrecStartedTM0StatementCount_primrec.comp Primrec.fst)
          (Primrec.pair (Primrec.const 0) Primrec.snd)))

theorem programData_computable_of_simStepDataForLabelIndexFrom
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFrom p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFrom hindex).to_comp

/--
The numeric-state fully offset descriptor decoder is enough for primitive
recursiveness of normalized folded program data.
-/
theorem programData_primrec_of_simStepDataForLabelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexFrom
    (hindex.of_eq fun p =>
      (simStepDataForLabelIndexFrom_eq_withCode p.1 p.2.1 p.2.2.1 p.2.2.2).symm)

theorem programData_computable_of_simStepDataForLabelIndexFromWithCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFromWithCode hindex).to_comp

theorem programData_primrec_of_simStepDataForLabelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexFromWithCode
    (hindex.of_eq fun p =>
      simStepDataForLabelIndexFromWithSearchCode_eq_withCode
        p.1 p.2.1 p.2.2.1 p.2.2.2)

theorem programData_computable_of_simStepDataForLabelIndexFromWithSearchCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithSearchCode p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFromWithSearchCode hindex).to_comp

theorem programData_primrec_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Primrec programData :=
  programData_primrec_of_simStepDataForLabelIndexStartWithPositionCode
    (by
      unfold simStepDataForLabelIndexStartWithPositionCode
      exact hindex.comp
        (Primrec.pair Primrec.fst
          (Primrec.pair
            (TM0Route.partrecStartedTM0StatementCount_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const 0) Primrec.snd))))
    hrows

theorem programData_computable_of_simStepDataForLabelIndexFromWithPositionCode
    (hindex : Primrec (fun p : Turing.ToPartrec.Code × Nat × Nat × Nat =>
      simStepDataForLabelIndexFromWithPositionCode p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrows : ∀ tc : Turing.ToPartrec.Code,
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc) = simRows tc) :
    Computable programData :=
  (programData_primrec_of_simStepDataForLabelIndexFromWithPositionCode hindex hrows).to_comp

theorem programData_symbols (tc : Turing.ToPartrec.Code) :
    (programData tc).symbols = foldedSymbolList :=
  rfl

theorem programData_states (tc : Turing.ToPartrec.Code) :
    (programData tc).states = foldedStateList tc :=
  rfl

theorem programData_blank (tc : Turing.ToPartrec.Code) :
    (programData tc).blank = foldedBlank :=
  rfl

theorem programData_start (tc : Turing.ToPartrec.Code) :
    (programData tc).start = foldedStartState :=
  rfl

theorem programData_table (tc : Turing.ToPartrec.Code) :
    (programData tc).table = initRowsData ++ simRows tc :=
  rfl

def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc

theorem programHeader_primrec : Primrec programHeader := by
  unfold programHeader
  exact PostProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const foldedSymbolList)
      (Primrec.pair foldedStateList_primrec
        (Primrec.pair (Primrec.const foldedBlank)
          (Primrec.pair (Primrec.const foldedStartState) initRows_primrec))))

theorem programHeader_computable : Computable programHeader :=
  programHeader_primrec.to_comp

theorem programData_eq_programHeader_with_simRows (tc : Turing.ToPartrec.Code) :
    programData tc =
      { programHeader tc with table := (programHeader tc).table ++ simRows tc } := by
  rfl

theorem programData_eq_appendSimRows_programHeader (tc : Turing.ToPartrec.Code) :
    programData tc = appendSimRows (programHeader tc) (simRows tc) := by
  rfl

def programDataFromSimRows (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  appendSimRows (programHeader tc) (simRows tc)

theorem programDataFromSimRows_eq_programData (tc : Turing.ToPartrec.Code) :
    programDataFromSimRows tc = programData tc :=
  (programData_eq_appendSimRows_programHeader tc).symm

theorem positionProgramData_eq_appendSimRows_programHeader
    (tc : Turing.ToPartrec.Code) :
    positionProgramData tc =
      appendSimRows (programHeader tc)
        (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)) := by
  rfl

theorem positionProgramData_transition?_sim_eq_generated
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} :
    (positionProgramData tc).transition? (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) := by
  have hinit := initRowsData_find?_eq_none_of_foldedSimStateCode tc side q
    (foldedSymbolCode marked left right)
  unfold PostProgram.transition?
  change (initRowsData ++
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      (simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right))
  exact find?_append_of_eq_none hinit

end TM0FoldedCompiler

end LeanWang
