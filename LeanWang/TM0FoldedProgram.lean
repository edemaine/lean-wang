/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachine
import LeanWang.TM0FiniteCompiler

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

def foldedSimStartState (tc : Turing.ToPartrec.Code) : Nat :=
  foldedSimStateCode tc FoldSide.right default

def foldedInitStateList : List Nat :=
  [initWriteOriginState, initReturnState 0] ++
    (List.range TM0Route.partrecStartedTM0Input.length).flatMap fun i =>
      [initMoveRightState i, initWriteRightState i, initReturnState i]

def foldedSimStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  (TM0Route.partrecStartedTM0LabelList tc).flatMap fun q =>
    foldSideList.map fun side => foldedSimStateCode tc side q

def foldedStateList (tc : Turing.ToPartrec.Code) : List Nat :=
  foldedInitStateList ++ foldedSimStateList tc

def inputSymbol (i : Nat) : SourceSymbol :=
  TM0Route.partrecStartedTM0Input.getI i

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

def initWriteRightRow (i : Nat) : PostTransition :=
  mkRow (initWriteRightState i) foldedBlank (nextAfterWriteRight i)
    (PostStmt.write (foldedSymbolCode false default (inputSymbol (i + 1))))

def initWriteRightRows : List PostTransition :=
  (List.range (TM0Route.partrecStartedTM0Input.length - 1)).map fun i =>
    initWriteRightRow i

def initReturnRow (tc : Turing.ToPartrec.Code) (i read : Nat) : PostTransition :=
  if i = 0 then
    mkRow (initReturnState 0) read (foldedSimStartState tc) (PostStmt.write read)
  else
    mkRow (initReturnState i) read (initReturnState (i - 1)) (PostStmt.move Move.left)

def initReturnIndexList : List Nat :=
  0 :: List.range TM0Route.partrecStartedTM0Input.length

def initReturnRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initReturnIndexList.flatMap fun i =>
    foldedSymbolList.map fun read => initReturnRow tc i read

def initRows (tc : Turing.ToPartrec.Code) : List PostTransition :=
  initWriteOriginRow :: initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc

def foldedMoveNextSide (side : FoldSide) (marked : Bool) (dir : Turing.Dir) : FoldSide :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => FoldSide.left
  | FoldSide.left, true, Turing.Dir.right => FoldSide.right
  | _, _, _ => side

def foldedMoveStmt (side : FoldSide) (marked : Bool) (cell : Nat)
    (dir : Turing.Dir) : PostStmt :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => PostStmt.write cell
  | FoldSide.left, true, Turing.Dir.right => PostStmt.write cell
  | FoldSide.right, _, Turing.Dir.right => PostStmt.move Move.right
  | FoldSide.right, _, Turing.Dir.left => PostStmt.move Move.left
  | FoldSide.left, _, Turing.Dir.left => PostStmt.move Move.right
  | FoldSide.left, _, Turing.Dir.right => PostStmt.move Move.left

def foldedMoveHead (side : FoldSide) (marked : Bool) (head : Nat)
    (dir : Turing.Dir) : Nat :=
  match side, marked, dir with
  | FoldSide.right, true, Turing.Dir.left => head
  | FoldSide.left, true, Turing.Dir.right => head
  | FoldSide.right, _, Turing.Dir.right => head + 1
  | FoldSide.right, _, Turing.Dir.left => head.pred
  | FoldSide.left, _, Turing.Dir.left => head + 1
  | FoldSide.left, _, Turing.Dir.right => head.pred

def foldedWriteForStmt (side : FoldSide) (marked : Bool)
    (new left right : SourceSymbol) : Nat :=
  if marked then
    foldedWriteMarked side new left right
  else
    foldedWrite side new left right

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

def program (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc ++ simRows tc

def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := foldedSymbolList
  states := foldedStateList tc
  blank := foldedBlank
  start := foldedStartState
  table := initRows tc

end TM0FoldedCompiler

end LeanWang
