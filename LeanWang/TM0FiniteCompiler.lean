/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.PostMachine
import LeanWang.TM0Route

/-!
Finite one-sided TM0 program data extracted from the Mathlib TM0 route.

This file starts the concrete `TM0FiniteCompiler` construction. The current
definitions package the finite numeric headers: symbols, states, blank, and
start. The transition table will be generated from the supported Mathlib TM0
states and the explicit symbol list.
-/

noncomputable section

namespace LeanWang

namespace TM0FiniteCompiler

open TM0Route

/-- Numeric code for a supported translated TM0 state. -/
def stateCode (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc) : Nat := by
  classical
  exact
    if q = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) then
      TM0Route.partrecStartedTM0Start
    else
      TM0Route.partrecStartedTM0StateCodeOfMem tc q
        (TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq)

theorem stateCode_default (tc : Turing.ToPartrec.Code)
    (hq : (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) ∈
      TM0Route.partrecStartedTM0Labels tc) :
    stateCode tc (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)) hq =
      TM0Route.partrecStartedTM0Start := by
  classical
  simp [stateCode]

theorem stateCode_mem_states (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc) :
    stateCode tc q hq ∈ TM0Route.partrecStartedTM0States tc := by
  classical
  by_cases h : q = (default : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
  · simp [stateCode, h, TM0Route.partrecStartedTM0Start_mem_states]
  · simp [stateCode, h, TM0Route.partrecStartedTM0StateCodeOfMem_mem_states tc q
      (TM0Route.mem_partrecStartedTM0LabelSupportList_of_mem_labels hq)
    ]

theorem next_label_mem_of_step {tc : Turing.ToPartrec.Code}
    {q q' : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc)}
    {a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol}
    {stmt : Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol)}
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (hstep : TM0Route.partrecStartedTM0Machine tc q a = some (q', stmt)) :
    q' ∈ TM0Route.partrecStartedTM0Labels tc := by
  exact (TM0Route.partrecStartedTM0_supports tc).2
    (show (q', stmt) ∈ TM0Route.partrecStartedTM0Machine tc q a by
      rw [hstep]
      simp)
    hq

def moveOfDir : Turing.Dir → Move
  | Turing.Dir.left => Move.left
  | Turing.Dir.right => Move.right

def stmtOfTM0Stmt :
    Turing.TM0.Stmt
      (Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol) →
      PostStmt
  | Turing.TM0.Stmt.move d => PostStmt.move (moveOfDir d)
  | Turing.TM0.Stmt.write a => PostStmt.write (TM0Route.partrecStartedTM0SymbolCode a)

noncomputable def transitionOfStep (tc : Turing.ToPartrec.Code)
    (q : Turing.TM1to0.Λ' (TM0Route.partrecStartedTM1Machine tc))
    (hq : q ∈ TM0Route.partrecStartedTM0Labels tc)
    (a : Turing.TM2to1.Γ' TM0Route.PartrecStack TM0Route.PartrecStackSymbol) :
    Option PostTransition :=
  match hstep : TM0Route.partrecStartedTM0Machine tc q a with
  | none => none
  | some (q', stmt) =>
      some {
        state := stateCode tc q hq
        read := TM0Route.partrecStartedTM0SymbolCode a
        next := stateCode tc q' (next_label_mem_of_step hq hstep)
        stmt := stmtOfTM0Stmt stmt
      }

/--
Finite program header for the TM0 route.

The table is empty for now; subsequent chunks will replace it by the finite
transition rows obtained by enumerating supported labels and tape symbols.
-/
def programHeader (tc : Turing.ToPartrec.Code) : FiniteTM0Program where
  symbols := TM0Route.partrecStartedTM0Symbols
  states := TM0Route.partrecStartedTM0States tc
  blank := TM0Route.partrecStartedTM0Blank
  start := TM0Route.partrecStartedTM0Start
  table := []

@[simp]
theorem programHeader_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).symbols = TM0Route.partrecStartedTM0Symbols := rfl

@[simp]
theorem programHeader_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).states = TM0Route.partrecStartedTM0States tc := rfl

@[simp]
theorem programHeader_blank (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank = TM0Route.partrecStartedTM0Blank := rfl

@[simp]
theorem programHeader_start (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start = TM0Route.partrecStartedTM0Start := rfl

@[simp]
theorem programHeader_table (tc : Turing.ToPartrec.Code) :
    (programHeader tc).table = [] := rfl

theorem programHeader_blank_mem_symbols (tc : Turing.ToPartrec.Code) :
    (programHeader tc).blank ∈ (programHeader tc).symbols := by
  simp [TM0Route.partrecStartedTM0Blank_mem_symbols]

theorem programHeader_start_mem_states (tc : Turing.ToPartrec.Code) :
    (programHeader tc).start ∈ (programHeader tc).states := by
  simp [TM0Route.partrecStartedTM0Start_mem_states]

end TM0FiniteCompiler

end LeanWang
