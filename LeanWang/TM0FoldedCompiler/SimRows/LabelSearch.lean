/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.SimRows.Basic

/-!
Label-local lookup lemmas for folded simulation rows.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

private theorem find?_filterMap_simTransition_right_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (rights : List SourceSymbol) (hright : right ∈ rights)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (rights.filterMap fun r => simTransitionOfStep tc q side marked left r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction rights with
  | nil =>
      cases hright
  | cons r rights ih =>
      simp only [List.mem_cons] at hright
      by_cases hrr : r = right
      · subst r
        have hrow := simTransitionOfStep_eq_some_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp [hrow, simRowOfStep_matchesInput]
      · have hright_tail : right ∈ rights := by
          rcases hright with h | h
          · exact False.elim (hrr h.symm)
          · exact h
        have ih_tail := ih hright_tail
        cases hrow : simTransitionOfStep tc q side marked left r with
        | none =>
            simp [hrow, ih_tail]
        | some e =>
            have hread :
                foldedSymbolCode marked left r ≠ foldedSymbolCode marked left right := by
              intro hcode
              exact hrr (foldedSymbolCode_eq hcode).2.2
            have hmiss := simTransitionOfStep_matchesInput_of_read_ne
              (tc := tc) (q := q) (side := side) (marked := marked)
              (marked' := marked) (left := left) (right := right)
              (left' := left) (right' := r) hread hrow
            simp [hrow, hmiss, ih_tail]

private theorem find?_filterMap_simTransition_right_eq_none_of_read_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked marked' : Bool}
    {left left' right : SourceSymbol}
    (rights : List SourceSymbol)
    (hread : ∀ r : SourceSymbol,
      foldedSymbolCode marked' left' r ≠ foldedSymbolCode marked left right) :
    (rights.filterMap fun r => simTransitionOfStep tc q side marked' left' r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction rights with
  | nil =>
      simp
  | cons r rights ih =>
      cases hrow : simTransitionOfStep tc q side marked' left' r with
      | none =>
          simp [hrow, ih]
      | some e =>
          have hmiss := simTransitionOfStep_matchesInput_of_read_ne
            (tc := tc) (q := q) (side := side) (marked := marked)
            (marked' := marked') (left := left) (right := right)
            (left' := left') (right' := r) (hread r) hrow
          simp [hrow, hmiss, ih]

private theorem find?_filterMap_simTransition_right_eq_none_of_side_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right left' : SourceSymbol}
    (rights : List SourceSymbol) (hside : side' ≠ side) :
    (rights.filterMap fun r => simTransitionOfStep tc q side' marked' left' r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction rights with
  | nil =>
      simp
  | cons r rights ih =>
      cases hrow : simTransitionOfStep tc q side' marked' left' r with
      | none =>
          simp [hrow, ih]
      | some e =>
          have hmiss := simTransitionOfStep_matchesInput_of_side_ne
            (tc := tc) (q := q) (side := side) (side' := side')
            (marked := marked) (marked' := marked') (left := left) (right := right)
            (left' := left') (right' := r) hside hrow
          simp [hrow, hmiss, ih]

private theorem find?_flatMap_simTransition_left_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (lefts : List SourceSymbol) (hleft : left ∈ lefts)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (lefts.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side marked l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction lefts with
  | nil =>
      cases hleft
  | cons l lefts ih =>
      simp only [List.mem_cons] at hleft
      by_cases hll : l = left
      · subst l
        have hhead := simRowsForLabel_right_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hleft_tail : left ∈ lefts := by
          rcases hleft with h | h
          · exact False.elim (hll h.symm)
          · exact h
        have hhead :
            (TM0Route.partrecStartedTM0SymbolList.filterMap
                fun r => simTransitionOfStep tc q side marked l r).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) = none := by
          exact find?_filterMap_simTransition_right_eq_none_of_read_ne_aux
            (tc := tc) (q := q) (side := side) (marked := marked)
            (marked' := marked) (left := left) (right := right) (left' := l)
            TM0Route.partrecStartedTM0SymbolList
            (by
              intro r hcode
              exact hll (foldedSymbolCode_eq hcode).2.1)
        have htail := ih hleft_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

private theorem find?_flatMap_simTransition_left_eq_none_of_read_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked marked' : Bool}
    {left right : SourceSymbol}
    (lefts : List SourceSymbol)
    (hread : ∀ l r : SourceSymbol,
      foldedSymbolCode marked' l r ≠ foldedSymbolCode marked left right) :
    (lefts.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side marked' l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction lefts with
  | nil =>
      simp
  | cons l lefts ih =>
      have hhead :
          (TM0Route.partrecStartedTM0SymbolList.filterMap
              fun r => simTransitionOfStep tc q side marked' l r).find?
            (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none :=
        find?_filterMap_simTransition_right_eq_none_of_read_ne_aux
          (tc := tc) (q := q) (side := side) (marked := marked)
          (marked' := marked') (left := left) (right := right) (left' := l)
          TM0Route.partrecStartedTM0SymbolList (hread l)
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

private theorem find?_flatMap_simTransition_left_eq_none_of_side_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right : SourceSymbol}
    (lefts : List SourceSymbol) (hside : side' ≠ side) :
    (lefts.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side' marked' l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction lefts with
  | nil =>
      simp
  | cons l lefts ih =>
      have hhead :
          (TM0Route.partrecStartedTM0SymbolList.filterMap
              fun r => simTransitionOfStep tc q side' marked' l r).find?
            (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none :=
        find?_filterMap_simTransition_right_eq_none_of_side_ne_aux
          (tc := tc) (q := q) (side := side) (side' := side')
          (marked := marked) (marked' := marked') (left := left) (right := right)
          (left' := l) TM0Route.partrecStartedTM0SymbolList hside
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

private theorem find?_flatMap_simTransition_marked_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (markers : List Bool) (hmarked : marked ∈ markers)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (markers.flatMap fun m =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
          TM0Route.partrecStartedTM0SymbolList.filterMap
            fun r => simTransitionOfStep tc q side m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction markers with
  | nil =>
      cases hmarked
  | cons m markers ih =>
      simp only [List.mem_cons] at hmarked
      by_cases hmm : m = marked
      · subst m
        have hhead := simRowsForLabel_left_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hmarked_tail : marked ∈ markers := by
          rcases hmarked with h | h
          · exact False.elim (hmm h.symm)
          · exact h
        have hhead :
            (TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                TM0Route.partrecStartedTM0SymbolList.filterMap
                  fun r => simTransitionOfStep tc q side m l r).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) = none := by
          exact find?_flatMap_simTransition_left_eq_none_of_read_ne_aux
            (tc := tc) (q := q) (side := side) (marked := marked) (marked' := m)
            (left := left) (right := right) TM0Route.partrecStartedTM0SymbolList
            (by
              intro l r hcode
              exact hmm (foldedSymbolCode_eq hcode).1)
        have htail := ih hmarked_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

private theorem find?_flatMap_simTransition_marked_eq_none_of_side_ne_aux
    {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked : Bool}
    {left right : SourceSymbol} (markers : List Bool) (hside : side' ≠ side) :
    (markers.flatMap fun m =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
          TM0Route.partrecStartedTM0SymbolList.filterMap
            fun r => simTransitionOfStep tc q side' m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  induction markers with
  | nil =>
      simp
  | cons m markers ih =>
      have hhead :
          (TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
              TM0Route.partrecStartedTM0SymbolList.filterMap
                fun r => simTransitionOfStep tc q side' m l r).find?
            (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none :=
        find?_flatMap_simTransition_left_eq_none_of_side_ne_aux
          (tc := tc) (q := q) (side := side) (side' := side')
          (marked := marked) (marked' := m) (left := left) (right := right)
          TM0Route.partrecStartedTM0SymbolList hside
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

private theorem find?_flatMap_simTransition_side_of_step_aux
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (sides : List FoldSide) (hside_mem : side ∈ sides)
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (sides.flatMap fun s =>
        [false, true].flatMap fun m =>
          TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
            TM0Route.partrecStartedTM0SymbolList.filterMap
              fun r => simTransitionOfStep tc q s m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  induction sides with
  | nil =>
      cases hside_mem
  | cons s sides ih =>
      simp only [List.mem_cons] at hside_mem
      by_cases hss : s = side
      · subst s
        have hhead := simRowsForLabel_marked_find?_of_step
          (tc := tc) (q := q) (q' := q') (side := side) (marked := marked)
          (left := left) (right := right) (stmt := stmt) hstep
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hside_tail : side ∈ sides := by
          rcases hside_mem with h | h
          · exact False.elim (hss h.symm)
          · exact h
        have hhead :
            ([false, true].flatMap fun m =>
                TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                  TM0Route.partrecStartedTM0SymbolList.filterMap
                    fun r => simTransitionOfStep tc q s m l r).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) = none :=
          find?_flatMap_simTransition_marked_eq_none_of_side_ne_aux
            (tc := tc) (q := q) (side := side) (side' := s) (marked := marked)
            (left := left) (right := right) [false, true] hss
        have htail := ih hside_tail
        simp only [List.flatMap_cons]
        change (([false, true].flatMap fun m =>
              TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                TM0Route.partrecStartedTM0SymbolList.filterMap
                  fun r => simTransitionOfStep tc q s m l r) ++
            (sides.flatMap fun s =>
              [false, true].flatMap fun m =>
                TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
                  TM0Route.partrecStartedTM0SymbolList.filterMap
                    fun r => simTransitionOfStep tc q s m l r)).find?
              (fun e =>
                e.matchesInput (foldedSimStateCode tc side q)
                  (foldedSymbolCode marked left right)) =
            some (simRowOfStep tc side marked q q' left right stmt)
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem simRowsForLabel_find?_eq_none_of_label_ne
    {tc : Turing.ToPartrec.Code}
    {q r : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hq : q ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hr : r ∈ TM0Route.partrecStartedTM0LabelList tc)
    (hne : r ≠ q) :
    (simRowsForLabel tc r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      none := by
  apply find?_eq_none_of_forall_matchesInput_false
  intro e he
  unfold simRowsForLabel at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨s, _hs, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨m, _hm, he⟩
  rw [List.mem_flatMap] at he
  rcases he with ⟨l, _hl, he⟩
  rw [List.mem_filterMap] at he
  rcases he with ⟨a, _ha, hrow⟩
  exact simTransitionOfStep_matchesInput_of_label_ne
    (tc := tc) (q := q) (r := r) (side := side) (side' := s)
    (marked := marked) (marked' := m) (left := left) (right := right)
    (left' := l) (right' := a) hq hr hne hrow


end TM0FoldedCompiler

end LeanWang
