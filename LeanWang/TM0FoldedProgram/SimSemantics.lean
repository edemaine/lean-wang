/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.InitSearch

/-!
Semantic folded simulation rows and descriptor generation.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

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

@[simp]
theorem simRowOfStep_matchesInput (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = true := by
  cases stmt <;> simp [simRowOfStep, mkRow, PostTransition.matchesInput]

theorem simRowOfStep_matchesInput_of_side_ne {tc : Turing.ToPartrec.Code}
    {side side' : FoldSide} {marked marked' : Bool}
    {q q' : SourceLabel tc} {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hside : side' ≠ side) :
    (simRowOfStep tc side' marked' q q' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  have hstate :
      foldedSimStateCode tc side' q ≠ foldedSimStateCode tc side q := by
    intro h
    exact hside (foldedSimStateCode_side_of_same_label_eq h)
  cases stmt <;> exact mkRow_matchesInput_of_state_ne_data hstate

theorem simRowOfStep_matchesInput_of_read_ne {tc : Turing.ToPartrec.Code}
    {side : FoldSide} {marked marked' : Bool}
    {q q' : SourceLabel tc} {left right left' right' : SourceSymbol}
    {stmt : Turing.TM0.Stmt SourceSymbol}
    (hread :
      foldedSymbolCode marked' left' right' ≠ foldedSymbolCode marked left right) :
    (simRowOfStep tc side marked' q q' left' right' stmt).matchesInput
        (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) = false := by
  cases stmt <;> exact mkRow_matchesInput_of_read_ne hread

theorem foldedWriteForStmt_mem_symbols
    (side : FoldSide) (marked : Bool) (new left right : SourceSymbol) :
    foldedWriteForStmt side marked new left right ∈ foldedSymbolList := by
  unfold foldedWriteForStmt
  by_cases h : marked
  · simp [h, foldedWriteMarked_mem_symbols]
  · simp [h, foldedWrite_mem_symbols]

theorem simRowOfStep_next_mem_states (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q : SourceLabel tc) {q' : SourceLabel tc}
    (hq' : q' ∈ TM0Route.partrecStartedTM0LabelList tc)
    (left right : SourceSymbol) (stmt : Turing.TM0.Stmt SourceSymbol) :
    (simRowOfStep tc side marked q q' left right stmt).next ∈ foldedStateList tc := by
  cases stmt with
  | move dir =>
      simp [simRowOfStep, mkRow,
        foldedSimStateCode_mem_states tc (foldedMoveNextSide side marked dir) hq']
  | write new =>
      simp [simRowOfStep, mkRow, foldedSimStateCode_mem_states tc side hq']

theorem foldedMoveStmt_write_mem_symbols
    (side : FoldSide) (marked : Bool) (cell : Nat) (dir : Turing.Dir)
    (hcell : cell ∈ foldedSymbolList) :
    match foldedMoveStmt side marked cell dir with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ foldedSymbolList := by
  cases side <;> cases marked <;> cases dir <;> simp [foldedMoveStmt, hcell]

theorem simRowOfStep_write_mem_symbols (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    match (simRowOfStep tc side marked q q' left right stmt).stmt with
    | PostStmt.move _ => True
    | PostStmt.write b => b ∈ foldedSymbolList := by
  cases stmt with
  | move dir =>
      exact foldedMoveStmt_write_mem_symbols side marked
        (foldedSymbolCode marked left right) dir
        (foldedSymbolCode_mem_symbols marked left right)
  | write new =>
      exact foldedWriteForStmt_mem_symbols side marked new left right

theorem simTransitionOfStep_eq_some_of_step {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    simTransitionOfStep tc q side marked left right =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  unfold simTransitionOfStep
  rw [hstep]

theorem simTransitionOfStep_eq_none_of_no_step {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    simTransitionOfStep tc q side marked left right = none := by
  unfold simTransitionOfStep
  rw [hstep]

theorem simTransitionOfStep_matchesInput_of_side_ne {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side side' : FoldSide} {marked marked' : Bool}
    {left right left' right' : SourceSymbol} {e : PostTransition}
    (hside : side' ≠ side)
    (he : simTransitionOfStep tc q side' marked' left' right' = some e) :
    e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      false := by
  unfold simTransitionOfStep at he
  split at he
  · cases he
  · rename_i q' stmt hstep
    cases he
    exact simRowOfStep_matchesInput_of_side_ne hside

theorem simTransitionOfStep_matchesInput_of_read_ne {tc : Turing.ToPartrec.Code}
    {q : SourceLabel tc} {side : FoldSide} {marked marked' : Bool}
    {left right left' right' : SourceSymbol} {e : PostTransition}
    (hread :
      foldedSymbolCode marked' left' right' ≠ foldedSymbolCode marked left right)
    (he : simTransitionOfStep tc q side marked' left' right' = some e) :
    e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
      false := by
  unfold simTransitionOfStep at he
  split at he
  · cases he
  · rename_i q' stmt hstep
    cases he
    exact simRowOfStep_matchesInput_of_read_ne hread

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

theorem simRowsForLabel_right_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (TM0Route.partrecStartedTM0SymbolList.filterMap
        fun r => simTransitionOfStep tc q side marked left r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  exact find?_filterMap_simTransition_right_of_step_aux
    TM0Route.partrecStartedTM0SymbolList
    (TM0Route.mem_partrecStartedTM0SymbolList right) hstep

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
        exact program_find?_append_of_eq_some hhead
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
        rw [program_find?_append_of_eq_none hhead]
        exact htail

theorem simRowsForLabel_left_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    (TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
        TM0Route.partrecStartedTM0SymbolList.filterMap
          fun r => simTransitionOfStep tc q side marked l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  exact find?_flatMap_simTransition_left_of_step_aux
    TM0Route.partrecStartedTM0SymbolList
    (TM0Route.mem_partrecStartedTM0SymbolList left) hstep

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
      rw [program_find?_append_of_eq_none hhead]
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
      rw [program_find?_append_of_eq_none hhead]
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
        exact program_find?_append_of_eq_some hhead
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
        rw [program_find?_append_of_eq_none hhead]
        exact htail

theorem simRowsForLabel_marked_find?_of_step
    {tc : Turing.ToPartrec.Code}
    {q q' : SourceLabel tc} {side : FoldSide} {marked : Bool}
    {left right : SourceSymbol} {stmt : Turing.TM0.Stmt SourceSymbol}
    (hstep :
      TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) =
        some (q', stmt)) :
    ([false, true].flatMap fun m =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun l =>
          TM0Route.partrecStartedTM0SymbolList.filterMap
            fun r => simTransitionOfStep tc q side m l r).find?
        (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) =
      some (simRowOfStep tc side marked q q' left right stmt) := by
  exact find?_flatMap_simTransition_marked_of_step_aux
    [false, true] (by cases marked <;> simp) hstep

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
      rw [program_find?_append_of_eq_none hhead]
      exact ih

theorem program_find?_flatMap_simTransition_side_of_step_aux
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
        exact program_find?_append_of_eq_some hhead
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
        rw [program_find?_append_of_eq_none hhead]
        exact htail

/-- Numeric descriptor for one semantic folded simulation step. -/
def simStepDataOfStep (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : SimStepData :=
  (side, marked, TM0FiniteCompiler.stateCode tc q,
    TM0FiniteCompiler.stateCode tc q', left, right, stmt)

def simStepDataOfStepCode
    (side : FoldSide) (marked : Bool)
    (qCode q'Code : Nat) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) : SimStepData :=
  (side, marked, qCode, q'Code, left, right, stmt)

theorem simStepDataOfStep_eq_code (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    simStepDataOfStep tc side marked q q' left right stmt =
      simStepDataOfStepCode side marked
        (TM0FiniteCompiler.stateCode tc q)
        (TM0FiniteCompiler.stateCode tc q') left right stmt := by
  rfl

theorem simStepDataOfStepCode_primrec :
    Primrec (fun p : FoldSide × Bool × Nat × Nat × SourceSymbol × SourceSymbol ×
        Turing.TM0.Stmt SourceSymbol =>
      simStepDataOfStepCode p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  unfold simStepDataOfStepCode
  exact Primrec.id

theorem simStepDataOfStep_primrec_fixed (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)] :
    Primrec (fun p : FoldSide × Bool × SourceLabel tc × SourceLabel tc ×
        SourceSymbol × SourceSymbol × Turing.TM0.Stmt SourceSymbol =>
      simStepDataOfStep tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  unfold simStepDataOfStep
  exact Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair
        (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.pair
          (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.snd))))
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))))))

theorem simStepDataRow_ofStep (tc : Turing.ToPartrec.Code)
    (side : FoldSide) (marked : Bool)
    (q q' : SourceLabel tc) (left right : SourceSymbol)
    (stmt : Turing.TM0.Stmt SourceSymbol) :
    simStepDataRow (simStepDataOfStep tc side marked q q' left right stmt) =
      simRowOfStep tc side marked q q' left right stmt := by
  rw [simRowOfStep_eq_code]
  rfl

/-- Descriptor-level version of `simTransitionOfStep`. -/
def simStepDataOfTransition (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option SimStepData :=
  match TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) with
  | none => none
  | some (q', stmt) => some (simStepDataOfStep tc side marked q q' left right stmt)

def simStepDataOfStmtTransition (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option SimStepData :=
  match sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none => none
  | some (q', tm0Stmt) => some (simStepDataOfStep tc side marked (stmt, v) q' left right tm0Stmt)

def simStepDataOfStmtTransitionWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) : Option SimStepData :=
  match sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none => none
  | some (q', tm0Stmt) =>
      some (simStepDataOfStepCode side marked qCode
        (TM0FiniteCompiler.stateCode tc q') left right tm0Stmt)

theorem simStepDataOfStmtTransition_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) :
    simStepDataOfStmtTransition tc stmt v side marked left right =
      simStepDataOfStmtTransitionWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side marked left right := by
  unfold simStepDataOfStmtTransition simStepDataOfStmtTransitionWithCode
  cases sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none =>
      rfl
  | some step =>
      cases step
      rfl

theorem simStepDataOfStmtTransitionWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol × SourceSymbol =>
      simStepDataOfStmtTransitionWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let readFn :
      Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool × SourceSymbol ×
        SourceSymbol → SourceSymbol := fun p =>
    foldedRead p.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2
  have hread : Primrec readFn := by
    exact foldedRead_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))
  have hlookup : Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar ×
      FoldSide × Bool × SourceSymbol × SourceSymbol =>
      sourceMachineStepOfStmt tc p.2.1 p.2.2.1 (readFn p)) := by
    exact (sourceMachineStepOfStmt_primrec_fixed_of_trAux tc haux).comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hread))
  have hsome : Primrec₂
      (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
          SourceSymbol × SourceSymbol =>
        fun step : SourceLabel tc × Turing.TM0.Stmt SourceSymbol =>
          simStepDataOfStepCode p.2.2.2.1 p.2.2.2.2.1 p.1
            (TM0FiniteCompiler.stateCode tc step.1)
            p.2.2.2.2.2.1 p.2.2.2.2.2.2 step.2) := by
    apply Primrec₂.mk
    exact simStepDataOfStepCode_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
          Primrec.fst))))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.fst)))))
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.pair
              (TM0FiniteCompiler.stateCode_primrec_fixed tc |>.comp
                (Primrec.fst.comp Primrec.snd))
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
                (Primrec.pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
                  (Primrec.snd.comp Primrec.snd)))))))
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold simStepDataOfStmtTransitionWithCode readFn
    cases sourceMachineStepOfStmt tc p.2.1 p.2.2.1
        (foldedRead p.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) <;> rfl

theorem simStepDataOfStmtTransition_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) :
    simStepDataOfStmtTransition tc q.1 q.2 side marked left right =
      simStepDataOfTransition tc q side marked left right := by
  rcases q with ⟨stmt, v⟩
  unfold simStepDataOfStmtTransition simStepDataOfTransition
  rw [sourceMachineStepOfStmt_eq_machine]
  cases h : TM0Route.partrecStartedTM0Machine tc (stmt, v) (foldedRead side left right) <;>
    simp

theorem simStepDataOfStmtTransition_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol × SourceSymbol =>
      simStepDataOfStmtTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) := by
  let readFn :
      Option (SourceStmt tc) × PartrecVar × FoldSide × Bool × SourceSymbol ×
        SourceSymbol → SourceSymbol := fun p =>
    foldedRead p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
  have hread : Primrec readFn := by
    exact foldedRead_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd))))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd))))))
  have hlookup : Primrec (fun p : Option (SourceStmt tc) × PartrecVar ×
      FoldSide × Bool × SourceSymbol × SourceSymbol =>
      sourceMachineStepOfStmt tc p.1 p.2.1 (readFn p)) := by
    exact (sourceMachineStepOfStmt_primrec_fixed_of_trAux tc haux).comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd) hread))
  have hsome : Primrec₂
      (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
          SourceSymbol × SourceSymbol =>
        fun step : SourceLabel tc × Turing.TM0.Stmt SourceSymbol =>
          simStepDataOfStep tc p.2.2.1 p.2.2.2.1 (p.1, p.2.1) step.1
            p.2.2.2.2.1 p.2.2.2.2.2 step.2) := by
    apply Primrec₂.mk
    exact (simStepDataOfStep_primrec_fixed tc).comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.fst))))
          (Primrec.pair
            (Primrec.pair (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
            (Primrec.pair (Primrec.fst.comp Primrec.snd)
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
                (Primrec.pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
                  (Primrec.snd.comp Primrec.snd)))))))
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold simStepDataOfStmtTransition readFn
    cases sourceMachineStepOfStmt tc p.1 p.2.1
        (foldedRead p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) <;> rfl

theorem simStepDataOfStmtTransition_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol × SourceSymbol =>
      simStepDataOfStmtTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) :=
  simStepDataOfStmtTransition_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataOfTransition_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    [Primcodable (Turing.TM1.Stmt
      (Turing.TM2to1.Γ' PartrecStack PartrecStackSymbol)
      (Turing.TM2to1.Λ' PartrecStack PartrecStackSymbol (StartedLabel tc) PartrecVar)
      PartrecVar)]
    (hstep : Primrec (fun p : SourceLabel tc × SourceSymbol =>
      TM0Route.partrecStartedTM0Machine tc p.1 p.2)) :
    Primrec (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol × SourceSymbol =>
      simStepDataOfTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let readFn : SourceLabel tc × FoldSide × Bool × SourceSymbol × SourceSymbol →
      SourceSymbol := fun p => foldedRead p.2.1 p.2.2.2.1 p.2.2.2.2
  have hread : Primrec readFn := by
    exact foldedRead_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hlookup : Primrec (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol ×
      SourceSymbol =>
      TM0Route.partrecStartedTM0Machine tc p.1 (readFn p)) := by
    exact hstep.comp (Primrec.pair Primrec.fst hread)
  have hsome : Primrec₂ (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol ×
      SourceSymbol => fun step : SourceLabel tc × Turing.TM0.Stmt SourceSymbol =>
      simStepDataOfStep tc p.2.1 p.2.2.1 p.1 step.1 p.2.2.2.1 p.2.2.2.2
        step.2) := by
    apply Primrec₂.mk
    exact (simStepDataOfStep_primrec_fixed tc).comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair (Primrec.fst.comp Primrec.fst)
            (Primrec.pair (Primrec.fst.comp Primrec.snd)
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp Primrec.fst))))
                (Primrec.pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp Primrec.fst))))
                  (Primrec.snd.comp Primrec.snd)))))))
  exact (Primrec.option_map hlookup hsome).of_eq fun p => by
    unfold simStepDataOfTransition readFn
    cases TM0Route.partrecStartedTM0Machine tc p.1 (foldedRead p.2.1 p.2.2.2.1 p.2.2.2.2)
    · rfl
    · rfl

theorem simStepDataOfTransition_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : SourceLabel tc × FoldSide × Bool × SourceSymbol × SourceSymbol =>
      simStepDataOfTransition tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  simStepDataOfTransition_primrec_fixed_of_machine tc
    (sourceMachine_primrec_fixed_of_trAux tc haux)

def simStepDataForStmtRightSymbols (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left : SourceSymbol) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
    simStepDataOfStmtTransition tc stmt v side marked left right

def simStepDataForStmtRightSymbolsWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left : SourceSymbol) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
    simStepDataOfStmtTransitionWithCode tc qCode stmt v side marked left right

theorem simStepDataForStmtRightSymbols_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) (left : SourceSymbol) :
    simStepDataForStmtRightSymbols tc stmt v side marked left =
      simStepDataForStmtRightSymbolsWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side marked left := by
  unfold simStepDataForStmtRightSymbols simStepDataForStmtRightSymbolsWithCode
  apply List.filterMap_congr
  intro right _hright
  exact simStepDataOfStmtTransition_eq_withCode tc stmt v side marked left right

theorem simStepDataForStmtRightSymbolsWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol =>
      simStepDataForStmtRightSymbolsWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold simStepDataForStmtRightSymbolsWithCode
  have htransition := simStepDataOfStmtTransitionWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.listFilterMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact htransition.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
              (Primrec.pair
                (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
                Primrec.snd))))))

theorem simStepDataForStmtRightSymbols_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol =>
      simStepDataForStmtRightSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold simStepDataForStmtRightSymbols
  have htransition := simStepDataOfStmtTransition_primrec_fixed_of_trAux tc haux
  refine Primrec.listFilterMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact htransition.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp Primrec.fst))))
              Primrec.snd)))))

theorem simStepDataForStmtRightSymbols_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool ×
        SourceSymbol =>
      simStepDataForStmtRightSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  simStepDataForStmtRightSymbols_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

def simStepDataForStmtLeftSymbols (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
    simStepDataForStmtRightSymbols tc stmt v side marked left

def simStepDataForStmtLeftSymbolsWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) : List SimStepData :=
  TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
    simStepDataForStmtRightSymbolsWithCode tc qCode stmt v side marked left

theorem simStepDataForStmtLeftSymbols_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide)
    (marked : Bool) :
    simStepDataForStmtLeftSymbols tc stmt v side marked =
      simStepDataForStmtLeftSymbolsWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side marked := by
  unfold simStepDataForStmtLeftSymbols simStepDataForStmtLeftSymbolsWithCode
  apply List.flatMap_congr
  intro left _hleft
  exact simStepDataForStmtRightSymbols_eq_withCode tc stmt v side marked left

theorem simStepDataForStmtLeftSymbolsWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide × Bool =>
      simStepDataForStmtLeftSymbolsWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2) := by
  unfold simStepDataForStmtLeftSymbolsWithCode
  have hright := simStepDataForStmtRightSymbolsWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact hright.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp Primrec.fst))))
              Primrec.snd)))))

theorem simStepDataForStmtLeftSymbols_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide) (marked : Bool) :
    simStepDataForStmtLeftSymbols tc q.1 q.2 side marked =
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simStepDataOfTransition tc q side marked left right := by
  rcases q with ⟨stmt, v⟩
  unfold simStepDataForStmtLeftSymbols simStepDataForStmtRightSymbols
  apply List.flatMap_congr
  intro left hleft
  apply List.filterMap_congr
  intro right hright
  exact simStepDataOfStmtTransition_eq_of_label tc (stmt, v) side marked left right

theorem simStepDataForStmtLeftSymbols_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool =>
      simStepDataForStmtLeftSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold simStepDataForStmtLeftSymbols
  have hright := simStepDataForStmtRightSymbols_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const TM0Route.partrecStartedTM0SymbolList) ?_
  apply Primrec₂.mk
  exact hright.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))))

theorem simStepDataForStmtLeftSymbols_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide × Bool =>
      simStepDataForStmtLeftSymbols tc p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  simStepDataForStmtLeftSymbols_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

def simStepDataForStmtMarked (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide) :
    List SimStepData :=
  [false, true].flatMap fun marked =>
    simStepDataForStmtLeftSymbols tc stmt v side marked

def simStepDataForStmtMarkedWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide) :
    List SimStepData :=
  [false, true].flatMap fun marked =>
    simStepDataForStmtLeftSymbolsWithCode tc qCode stmt v side marked

theorem simStepDataForStmtMarked_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) (side : FoldSide) :
    simStepDataForStmtMarked tc stmt v side =
      simStepDataForStmtMarkedWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v side := by
  unfold simStepDataForStmtMarked simStepDataForStmtMarkedWithCode
  apply List.flatMap_congr
  intro marked _hmarked
  exact simStepDataForStmtLeftSymbols_eq_withCode tc stmt v side marked

theorem simStepDataForStmtMarkedWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar × FoldSide =>
      simStepDataForStmtMarkedWithCode tc p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold simStepDataForStmtMarkedWithCode
  have hleft := simStepDataForStmtLeftSymbolsWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
  apply Primrec₂.mk
  exact hleft.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))))

theorem simStepDataForStmtMarked_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide) :
    simStepDataForStmtMarked tc q.1 q.2 side =
      [false, true].flatMap fun marked =>
        TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
          TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
            simStepDataOfTransition tc q side marked left right := by
  unfold simStepDataForStmtMarked
  apply List.flatMap_congr
  intro marked hmarked
  exact simStepDataForStmtLeftSymbols_eq_of_label tc q side marked

theorem simStepDataForStmtMarked_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide =>
      simStepDataForStmtMarked tc p.1 p.2.1 p.2.2) := by
  unfold simStepDataForStmtMarked
  have hleft := simStepDataForStmtLeftSymbols_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
  apply Primrec₂.mk
  exact hleft.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)))

theorem simStepDataForStmtMarked_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar × FoldSide =>
      simStepDataForStmtMarked tc p.1 p.2.1 p.2.2) :=
  simStepDataForStmtMarked_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simTransitionOfStep_eq_map_stepData (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) (side : FoldSide)
    (marked : Bool) (left right : SourceSymbol) :
    simTransitionOfStep tc q side marked left right =
      (simStepDataOfTransition tc q side marked left right).map simStepDataRow := by
  unfold simTransitionOfStep simStepDataOfTransition
  cases h : TM0Route.partrecStartedTM0Machine tc q (foldedRead side left right) with
  | none =>
      rfl
  | some step =>
      rcases step with ⟨q', stmt⟩
      simp [simStepDataRow_ofStep]

theorem program_filterMap_simTransition_eq_map_stepData {α : Type}
    (xs : List α) (f : α → Option SimStepData) :
    xs.filterMap (fun x => (f x).map simStepDataRow) =
      simRowsOfStepData (xs.filterMap f) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      cases h : f x <;> simp [h, simRowsOfStepData, ih]

theorem program_flatMap_getElem?_range_length {α β : Type}
    (xs : List α) (f : α → List β) :
    (List.range xs.length).flatMap (fun i => (xs[i]?).elim [] f) =
    xs.flatMap f := by
  induction xs using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton xs x ih =>
      rw [List.length_append, List.length_singleton]
      rw [show xs.length + 1 = Nat.succ xs.length by omega]
      rw [List.range_succ, List.flatMap_append]
      have hprefix :
          (List.range xs.length).flatMap (fun i => ((xs ++ [x])[i]?).elim [] f) =
          (List.range xs.length).flatMap (fun i => (xs[i]?).elim [] f) := by
        apply List.flatMap_congr
        intro i hi
        have hi_lt : i < xs.length := by
          simpa [List.mem_range] using hi
        rw [List.getElem?_append_left hi_lt]
      rw [hprefix, ih]
      simp

/-- Descriptor-level folded simulation rows for one source label. -/
def simStepDataForLabel (tc : Turing.ToPartrec.Code) (q : SourceLabel tc) :
    List SimStepData :=
  foldSideList.flatMap fun side =>
    [false, true].flatMap fun marked =>
      TM0Route.partrecStartedTM0SymbolList.flatMap fun left =>
        TM0Route.partrecStartedTM0SymbolList.filterMap fun right =>
          simStepDataOfTransition tc q side marked left right

def simStepDataForStmtLabel (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) : List SimStepData :=
  foldSideList.flatMap fun side =>
    simStepDataForStmtMarked tc stmt v side

def simStepDataForStmtLabelWithCode (tc : Turing.ToPartrec.Code)
    (qCode : Nat) (stmt : Option (SourceStmt tc)) (v : PartrecVar) : List SimStepData :=
  foldSideList.flatMap fun side =>
    simStepDataForStmtMarkedWithCode tc qCode stmt v side

theorem simStepDataForStmtLabel_eq_withCode
    (tc : Turing.ToPartrec.Code)
    (stmt : Option (SourceStmt tc)) (v : PartrecVar) :
    simStepDataForStmtLabel tc stmt v =
      simStepDataForStmtLabelWithCode tc
        (TM0FiniteCompiler.stateCode tc (stmt, v))
        stmt v := by
  unfold simStepDataForStmtLabel simStepDataForStmtLabelWithCode
  apply List.flatMap_congr
  intro side _hside
  exact simStepDataForStmtMarked_eq_withCode tc stmt v side

theorem simStepDataForStmtLabelWithCode_none
    (tc : Turing.ToPartrec.Code) (qCode : Nat) (v : PartrecVar) :
    simStepDataForStmtLabelWithCode tc qCode none v = [] := by
  unfold simStepDataForStmtLabelWithCode simStepDataForStmtMarkedWithCode
    simStepDataForStmtLeftSymbolsWithCode simStepDataForStmtRightSymbolsWithCode
    simStepDataOfStmtTransitionWithCode sourceMachineStepOfStmt
  simp

theorem simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabelWithCode tc p.1 p.2.1 p.2.2) := by
  unfold simStepDataForStmtLabelWithCode
  have hmarked := simStepDataForStmtMarkedWithCode_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const foldSideList) ?_
  apply Primrec₂.mk
  exact hmarked.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)))

theorem simStepDataForStmtLabelWithCode_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabelWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForStmtLabelWithCode_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)

theorem simStepDataForStmtLabelWithCode_primrec_fixed
    (tc : Turing.ToPartrec.Code) :
    Primrec (fun p : Nat × Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabelWithCode tc p.1 p.2.1 p.2.2) :=
  simStepDataForStmtLabelWithCode_primrec_fixed_of_machine tc
    (TM0Route.partrecStartedTM1Machine_primrec tc)

theorem simStepDataOfStmtTransitionWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {p : SimStepData}
    (h : simStepDataOfStmtTransitionWithCode tc qCode stmt v side marked left right =
      some p) :
    p.2.2.1 = qCode := by
  unfold simStepDataOfStmtTransitionWithCode at h
  cases hstep : sourceMachineStepOfStmt tc stmt v (foldedRead side left right) with
  | none =>
      simp [hstep] at h
  | some step =>
      rcases step with ⟨q', tm0Stmt⟩
      have hp :
          simStepDataOfStepCode side marked qCode
            (TM0FiniteCompiler.stateCode tc q') left right tm0Stmt = p := by
        simpa [hstep] using h
      rw [← hp]
      rfl

theorem mem_simStepDataForStmtRightSymbolsWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {marked : Bool} {left : SourceSymbol}
    {p : SimStepData}
    (h : p ∈ simStepDataForStmtRightSymbolsWithCode tc qCode stmt v side marked left) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtRightSymbolsWithCode at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨right, _hright, hright⟩
  exact simStepDataOfStmtTransitionWithCode_currentCode hright

theorem mem_simStepDataForStmtLeftSymbolsWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {marked : Bool} {p : SimStepData}
    (h : p ∈ simStepDataForStmtLeftSymbolsWithCode tc qCode stmt v side marked) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtLeftSymbolsWithCode at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨left, _hleft, hleft⟩
  exact mem_simStepDataForStmtRightSymbolsWithCode_currentCode hleft

theorem mem_simStepDataForStmtMarkedWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {side : FoldSide} {p : SimStepData}
    (h : p ∈ simStepDataForStmtMarkedWithCode tc qCode stmt v side) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtMarkedWithCode at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨marked, _hmarked, hmarked⟩
  exact mem_simStepDataForStmtLeftSymbolsWithCode_currentCode hmarked

theorem mem_simStepDataForStmtLabelWithCode_currentCode
    {tc : Turing.ToPartrec.Code} {qCode : Nat} {stmt : Option (SourceStmt tc)}
    {v : PartrecVar} {p : SimStepData}
    (h : p ∈ simStepDataForStmtLabelWithCode tc qCode stmt v) :
    p.2.2.1 = qCode := by
  unfold simStepDataForStmtLabelWithCode at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨side, _hside, hside⟩
  exact mem_simStepDataForStmtMarkedWithCode_currentCode hside

theorem simStepDataForStmtLabel_eq_of_label (tc : Turing.ToPartrec.Code)
    (q : SourceLabel tc) :
    simStepDataForStmtLabel tc q.1 q.2 = simStepDataForLabel tc q := by
  unfold simStepDataForStmtLabel simStepDataForLabel
  apply List.flatMap_congr
  intro side hside
  exact simStepDataForStmtMarked_eq_of_label tc q side

theorem simStepDataForStmtLabel_primrec_fixed_of_trAux
    (tc : Turing.ToPartrec.Code)
    (haux : Primrec (fun p : SourceStmt tc × PartrecVar × SourceSymbol =>
      Turing.TM1to0.trAux (TM0Route.partrecStartedTM1Machine tc) p.2.2 p.1 p.2.1)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabel tc p.1 p.2) := by
  unfold simStepDataForStmtLabel
  have hmarked := simStepDataForStmtMarked_primrec_fixed_of_trAux tc haux
  refine Primrec.list_flatMap (Primrec.const foldSideList) ?_
  apply Primrec₂.mk
  exact hmarked.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem simStepDataForStmtLabel_primrec_fixed_of_machine
    (tc : Turing.ToPartrec.Code)
    (hmachine : Primrec (TM0Route.partrecStartedTM1Machine tc)) :
    Primrec (fun p : Option (SourceStmt tc) × PartrecVar =>
      simStepDataForStmtLabel tc p.1 p.2) :=
  simStepDataForStmtLabel_primrec_fixed_of_trAux tc
    (trAux_primrec_fixed_of_machine tc hmachine)


end TM0FoldedCompiler

end LeanWang
