/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.SimRows.LabelSearch

/-!
Global lookup and support lemmas for folded simulation rows.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

private theorem find?_flatMap_simRowsForLabel_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (labels : List (SourceLabel tc))
    (hall : ∀ r, r ∈ labels → r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hqmem : q ∈ labels)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (labels.flatMap fun r => simRowsForLabel tc r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction labels with
  | nil =>
      cases hqmem
  | cons r labels ih =>
      simp only [List.mem_cons] at hqmem
      have hall_tail : ∀ s, s ∈ labels → s ∈ TM0Route.partrecStartedTM0LabelList tc := by
        intro s hs
        exact hall s (by simp [hs])
      by_cases hrq : r = q
      · subst r
        have hhead := simRowsForLabel_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hqmem_tail : q ∈ labels := by
          rcases hqmem with h | h
          · exact False.elim (hrq h.symm)
          · exact h
        have hr : r ∈ TM0Route.partrecStartedTM0LabelList tc :=
          hall r (by simp)
        have hq : q ∈ TM0Route.partrecStartedTM0LabelList tc :=
          hall q (by simp [hqmem])
        have hhead := simRowsForLabel_find?_eq_none_of_label_ne
          (tc := tc) (q := q) (r := r) (side := side) (marked := marked)
          (left := left) (right := right) hq hr hrq
        have htail := ih hall_tail hqmem_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem simRows_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (simRows tc).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold simRows
  exact find?_flatMap_simRowsForLabel_of_step_aux
    (TM0Route.partrecStartedTM0LabelList tc)
    (fun r hr => hr) hqlist hstep

private theorem find?_flatMap_simRowsForLabel_eq_none_of_no_step_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (labels : List (SourceLabel tc))
    (hall : ∀ r, r ∈ labels → r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (labels.flatMap fun r => simRowsForLabel tc r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction labels with
  | nil =>
      simp
  | cons r labels ih =>
      have hall_tail : ∀ s, s ∈ labels → s ∈ TM0Route.partrecStartedTM0LabelList tc := by
        intro s hs
        exact hall s (by simp [hs])
      by_cases hrq : r = q
      · subst r
        have hhead := simRowsForLabel_find?_eq_none_of_no_step
          (tc := tc) (q := q) (side := side) (marked := marked)
          (left := left) (right := right) hstep
        have htail := ih hall_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail
      · have hr : r ∈ TM0Route.partrecStartedTM0LabelList tc :=
          hall r (by simp)
        have hhead := simRowsForLabel_find?_eq_none_of_label_ne
          (tc := tc) (q := q) (r := r) (side := side) (marked := marked)
          (left := left) (right := right) hqlist hr hrq
        have htail := ih hall_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem simRows_find?_eq_none_of_no_step
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hqlist : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    (simRows tc).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  unfold simRows
  exact find?_flatMap_simRowsForLabel_eq_none_of_no_step_aux
    (TM0Route.partrecStartedTM0LabelList tc)
    (fun r hr => hr) hqlist hstep

theorem mem_simRows_state_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    e.state ∈ foldedStateList tc := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact simRowOfStep_state_mem_states tc side marked hq left right stmt

theorem mem_simRows_read_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    e.read ∈ foldedSymbolList := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact simRowOfStep_read_mem_symbols tc side marked q q' left right stmt

theorem mem_simRows_next_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    e.next ∈ foldedStateList tc := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    have hqset : q ∈ TM0Route.partrecStartedTM0Labels tc :=
      (TM0Route.mem_partrecStartedTM0LabelList tc q).1 hq
    have hq'set : q' ∈ TM0Route.partrecStartedTM0Labels tc :=
      TM0FiniteCompiler.next_label_mem_of_step hqset hstep
    have hq' : q' ∈ TM0Route.partrecStartedTM0LabelList tc :=
      (TM0Route.mem_partrecStartedTM0LabelList tc q').2 hq'set
    exact simRowOfStep_next_mem_states tc side marked q hq' left right stmt

theorem mem_simRows_write_mem {tc : Turing.ToPartrec.Code} {e : PostTransition}
    (he : e ∈ simRows tc) :
    match e.stmt with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ foldedSymbolList := by
  unfold simRows simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨q, _hq, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨side, _hside, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨marked, _hmarked, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨left, _hleft, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨right, _hright, hrow⟩
  unfold simTransitionOfStep at hrow
  split at hrow
  · cases hrow
  · rename_i q' stmt hstep
    cases hrow
    exact simRowOfStep_write_mem_symbols tc side marked q q' left right stmt


end TM0FoldedCompiler

end LeanWang
