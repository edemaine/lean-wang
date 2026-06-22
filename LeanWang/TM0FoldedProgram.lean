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

def initReturnRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow tc i read

theorem initReturnRows_primrec : Primrec initReturnRows := by
  unfold initReturnRows
  refine Primrec.list_flatMap (Primrec.const initReturnIndexList) ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.const foldedSymbolList) ?_
  apply Primrec₂.mk
  exact initReturnRow_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

def initRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initWriteOriginRow :: (initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc))

theorem initRows_primrec : Primrec initRows := by
  change Primrec (fun tc : Turing.ToPartrec.Code =>
    initWriteOriginRow :: (initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc)))
  have hwriteReturn : Primrec (fun tc : Turing.ToPartrec.Code =>
      initWriteRightRows ++ initReturnRows tc) :=
    Primrec.list_append.comp (Primrec.const initWriteRightRows) initReturnRows_primrec
  have htail : Primrec (fun tc : Turing.ToPartrec.Code =>
      initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc)) :=
    Primrec.list_append.comp (Primrec.const initMoveRightRows) hwriteReturn
  exact Primrec.list_cons.comp (Primrec.const initWriteOriginRow) htail

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

def simRowsForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List PostTransition :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simTransitionOfStep tc q side marked left right

def simRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q => simRowsForLabel tc q

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

def program (tc : Turing.ToPartrec.Code) : FiniteTM0Program :=
  programOfCountAndRows (TM0Route.partrecStartedTM0StateCount tc) (initRows tc) (simRows tc)

theorem program_eq_programOfParts (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfParts (TM0Route.partrecStartedTM0States tc) (initRows tc) (simRows tc) := rfl

theorem program_eq_programOfCountAndRows (tc : Turing.ToPartrec.Code) :
    program tc =
      programOfCountAndRows (TM0Route.partrecStartedTM0StateCount tc)
        (initRows tc) (simRows tc) := rfl

def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc

end TM0FoldedCompiler

end LeanWang
