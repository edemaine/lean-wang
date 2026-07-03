/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.FoldedAlphabet

/-!
Initialization rows for the folded one-sided finite TM0 program.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

def mkRow (state read next : Nat) (stmt : PostStmt) : PostTransition where
  state := state
  read := read
  next := next
  stmt := stmt

theorem mkRow_matchesInput_of_state_ne_data {state state' read read' next : Nat}
    {stmt : PostStmt} (hstate : state ≠ state') :
    (mkRow state read next stmt).matchesInput state' read' = false := by
  simp [mkRow, PostTransition.matchesInput, hstate]

theorem mkRow_matchesInput_of_read_ne {state read read' next : Nat}
    {stmt : PostStmt} (hread : read ≠ read') :
    (mkRow state read next stmt).matchesInput state read' = false := by
  simp [mkRow, PostTransition.matchesInput, hread]

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


end TM0FoldedCompiler

end LeanWang
