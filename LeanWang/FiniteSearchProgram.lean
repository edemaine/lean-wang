/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/
import LeanWang.Machine

/-!
Finite Boolean search programs.

This file builds a small generated `TableProgram` that scans a finite list of
Boolean markers. At state `i`, a `true` marker jumps to halt and a `false`
marker advances to state `i + 1`; after the list is exhausted, the machine loops
right forever on blank tape. This is a finite control-flow fragment of the
eventual fuel-search compiler.
-/

namespace LeanWang

namespace FiniteSearchProgram

def transition (halt i : Nat) (b : Bool) : TableTransition where
  state := i
  read := 0
  write := 0
  next := if b then halt else i + 1
  move := Move.right

def loopTransition (i : Nat) : TableTransition where
  state := i
  read := 0
  write := 0
  next := i
  move := Move.right

def foldStep (bs : List Bool)
    (s : List TableTransition × Nat) (b : Bool) :
    List TableTransition × Nat :=
  (s.1 ++ [transition (bs.length + 1) s.2 b], s.2 + 1)

def foldStep₂ (bs : List Bool) (p : (List TableTransition × Nat) × Bool) :
    List TableTransition × Nat :=
  foldStep bs p.1 p.2

def folded (bs : List Bool) : List TableTransition × Nat :=
  bs.foldl (fun s b => foldStep₂ bs (s, b)) ([], 0)

def transitions (bs : List Bool) : List TableTransition :=
  (folded bs).1 ++ [loopTransition (folded bs).2]

def program (bs : List Bool) : TableProgram where
  symbols := []
  states := List.range (bs.length + 1)
  blank := 0
  start := 0
  halt := bs.length + 1
  table := transitions bs

theorem transition_primrec :
    Primrec (fun p : Nat × Nat × Bool => transition p.1 p.2.1 p.2.2) := by
  unfold transition
  have hnext : Primrec (fun p : Nat × Nat × Bool =>
      if p.2.2 then p.1 else p.2.1 + 1) := by
    have hpred : PrimrecPred (fun p : Nat × Nat × Bool => p.2.2 = true) :=
      Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true)
    exact Primrec.ite hpred Primrec.fst
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  exact TableTransition.mk_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair hnext (Primrec.const Move.right)))))

theorem loopTransition_primrec :
    Primrec loopTransition := by
  unfold loopTransition
  exact TableTransition.mk_primrec.comp
    (Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair Primrec.id (Primrec.const Move.right)))))

theorem foldStep₂_primrec :
    Primrec₂ foldStep₂ := by
  apply Primrec₂.mk
  unfold foldStep₂ foldStep
  have hhalt : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.1.length + 1) :=
    Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)
  have hacc : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hstate : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hbit : Primrec (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
      p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have htransition : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        transition (p.1.length + 1) p.2.1.2 p.2.2) :=
    transition_primrec.comp (Primrec.pair hhalt (Primrec.pair hstate hbit))
  have hsingleton : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        [transition (p.1.length + 1) p.2.1.2 p.2.2]) :=
    Primrec.list_cons.comp htransition (Primrec.const [])
  have htransitions : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        p.2.1.1 ++ [transition (p.1.length + 1) p.2.1.2 p.2.2]) :=
    Primrec.list_append.comp hacc hsingleton
  have hnextState : Primrec
      (fun p : List Bool × ((List TableTransition × Nat) × Bool) =>
        p.2.1.2 + 1) :=
    Primrec.succ.comp hstate
  exact Primrec.pair htransitions hnextState

theorem folded_primrec :
    Primrec folded := by
  unfold folded
  exact Primrec.list_foldl Primrec.id
    (Primrec.const (([] : List TableTransition), 0)) foldStep₂_primrec

theorem transitions_primrec :
    Primrec transitions := by
  unfold transitions
  have hloop : Primrec (fun bs : List Bool => loopTransition (folded bs).2) :=
    loopTransition_primrec.comp (Primrec.snd.comp folded_primrec)
  have hsingleton : Primrec (fun bs : List Bool => [loopTransition (folded bs).2]) :=
    Primrec.list_cons.comp hloop (Primrec.const ([] : List TableTransition))
  exact Primrec.list_append.comp (Primrec.fst.comp folded_primrec) hsingleton

theorem program_primrec :
    Primrec program := by
  unfold program
  have hlengthSucc : Primrec (fun bs : List Bool => bs.length + 1) :=
    Primrec.succ.comp Primrec.list_length
  exact TableProgram.mk_primrec.comp
    (Primrec.pair (Primrec.const ([] : List Nat))
      (Primrec.pair (Primrec.list_range.comp hlengthSucc)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair (Primrec.const 0)
            (Primrec.pair hlengthSucc transitions_primrec)))))

theorem program_computable :
    Computable program :=
  program_primrec.to_comp

end FiniteSearchProgram

end LeanWang
