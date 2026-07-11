/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FixedDirectRows

/-!
Core folded simulation row constructors and primitive-recursion facts.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

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

end TM0FoldedCompiler

end LeanWang
