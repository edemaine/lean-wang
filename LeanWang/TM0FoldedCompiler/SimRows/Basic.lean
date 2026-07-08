/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.Init
import LeanWang.TM0FoldedProgram.ProgramData

/-!
Basic support lemmas for folded simulation rows.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem simRowOfStep_state (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).state =
      foldedSimStateCode tc side q := by
  cases stmt <;> rfl

theorem simRowOfStep_read (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).read =
      foldedSymbolCode marked left right := by
  cases stmt <;> rfl

theorem simRowOfStep_matchesInput_of_label_ne {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {marked marked' : Bool}
    {q r r' : SourceLabel tc} {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hr : r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hne : r ≠ q) :
    (simRowOfStep tc side' marked' r r' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  have hstate : foldedSimStateCode tc side' r ≠ foldedSimStateCode tc side q := by
    intro h
    exact hne (foldedSimStateCode_injective_on_labels hr hq h).2
  cases stmt <;> exact mkRow_matchesInput_of_state_ne hstate

theorem simRowOfStep_state_mem_states (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    {q q' : SourceLabel tc} (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (left right : SourceSymbol) (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).state ∈ foldedStateList tc := by
  cases stmt <;> simp [simRowOfStep, mkRow, foldedSimStateCode_mem_states tc side hq]

theorem simRowOfStep_read_mem_symbols (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).read ∈ foldedSymbolList := by
  cases stmt <;> simp [simRowOfStep, mkRow, foldedSymbolCode_mem_symbols]

theorem simTransitionOfStep_matchesInput_of_label_ne {tc : Turing.ToPartrec.Code}
    {q r : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right left' right' : SourceSymbol} {e : PostTransition}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hr : r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hne : r ≠ q)
    (he : simTransitionOfStep tc r side' marked' left' right' = some e) :
    e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      false := by
  unfold simTransitionOfStep at he
  split at he
  · cases he
  · rename_i r' stmt hstep
    cases he
    exact simRowOfStep_matchesInput_of_label_ne hq hr hne

end TM0FoldedCompiler

end LeanWang
