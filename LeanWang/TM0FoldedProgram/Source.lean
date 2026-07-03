/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachine
import LeanWang.TM0FiniteCompiler
import LeanWang.ToPartrecEncoding
import Mathlib.Data.List.Intervals

/-!
Source-machine coding and primitive-recursive setup for the folded compiler.
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

theorem default_mem_partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code) :
    (default : SourceLabel tc) ∈ TM0Route.partrecStartedTM0LabelList tc := by
  exact (TM0Route.mem_partrecStartedTM0LabelList tc default).2
    (TM0Route.partrecStartedTM0_supports tc).1

theorem sourceDefaultLabel_mem_partrecStartedTM0LabelList (tc : Turing.ToPartrec.Code) :
    sourceDefaultLabel tc ∈ TM0Route.partrecStartedTM0LabelList tc := by
  rw [sourceDefaultLabel_eq_default]
  exact default_mem_partrecStartedTM0LabelList tc

theorem exists_partrecStartedTM0LabelList_get?_default (tc : Turing.ToPartrec.Code) :
    ∃ n, n < TM0Route.partrecStartedTM0LabelCount tc ∧
      (TM0Route.partrecStartedTM0LabelList tc)[n]? = some (default : SourceLabel tc) := by
  rcases List.mem_iff_getElem?.1 (default_mem_partrecStartedTM0LabelList tc) with
    ⟨n, hn⟩
  refine ⟨n, ?_, hn⟩
  rw [← TM0Route.partrecStartedTM0LabelList_length tc]
  exact List.getElem?_eq_some_iff.1 hn |>.1

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

end TM0FoldedCompiler

end LeanWang
