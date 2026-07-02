/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramInitSteps

/-!
Full-program transition and step lemmas for simulated TM0 states.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem program_transition?_sim_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (program tc).transition? (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  have hinit := initRows_find?_eq_none_of_foldedSimStateCode tc side q
    (foldedSymbolCode marked left right)
  have hsim := simRows_find?_of_step
    (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
    (left := left) (right := right) (stmt := stmt) hqlist hstep
  unfold PostProgram.transition?
  change (initRows tc ++ simRows tc).find?
      (fun e =>
        e.matchesInput (foldedSimStateCode tc side q)
          (foldedSymbolCode marked left right)) =
    some (simRowOfStep tc side marked q q' left right stmt)
  rw [find?_append_of_eq_none hinit]
  exact hsim

theorem program_step_sim_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (program tc).step (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      some ((simRowOfStep tc side marked q q' left right stmt).next,
        (simRowOfStep tc side marked q q' left right stmt).stmt) := by
  have hfind := program_transition?_sim_of_step
    (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
    (left := left) (right := right) (stmt := stmt) hqlist hstep
  have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hqlist
  have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
    TM0FiniteCompiler.next_label_mem_of_step hqset hstep
  have hq'list : q' ∈ TM0Route.partrecStartedTM0LabelList tc :=
    (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
  have hnext :
      (simRowOfStep tc side marked q q' left right stmt).next ∈ foldedStateList tc :=
    simRowOfStep_next_mem_states tc side marked q hq'list left right stmt
  have hwrite := simRowOfStep_write_mem_symbols tc side marked q q' left right stmt
  unfold PostProgram.step
  rw [hfind]
  simp only [program_states, program_symbols, dite_eq_ite, Option.ite_none_right_eq_some]
  constructor
  · exact hnext
  cases hstmt : (simRowOfStep tc side marked q q' left right stmt).stmt with
  | move m =>
      simp
  | write b =>
      have hb : b ∈ foldedSymbolList := by
        simpa [hstmt] using hwrite
      simp [hb]

theorem program_transition?_sim_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (program tc).transition? (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      none := by
  have hinit := initRows_find?_eq_none_of_foldedSimStateCode tc side q
    (foldedSymbolCode marked left right)
  have hsim := simRows_find?_eq_none_of_no_step
    (tc := tc) (q := q) (side := side) (marked := marked)
    (left := left) (right := right) hqlist hstep
  unfold PostProgram.transition?
  change (initRows tc ++ simRows tc).find?
      (fun e =>
        e.matchesInput (foldedSimStateCode tc side q)
          (foldedSymbolCode marked left right)) =
    none
  rw [find?_append_of_eq_none hinit]
  exact hsim

theorem program_step_sim_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (program tc).step (foldedSimStateCode tc side q)
        (foldedSymbolCode marked left right) =
      none := by
  have hfind := program_transition?_sim_eq_none_of_no_step
    (tc := tc) (q := q) (side := side) (marked := marked)
    (left := left) (right := right) hqlist hstep
  simp [PostProgram.step, hfind]

end TM0FoldedCompiler

end LeanWang
