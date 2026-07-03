/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram.SimCore

/-!
Find/search lemmas separating initialization rows from simulation rows.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
    {tc : Turing.ToPartrec.Code} {steps : List SimStepData}
    {side : FoldSide} {marked : Bool} {q : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : ∀ p ∈ steps, p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc q) :
    (simRowsOfStepData steps).find? (fun e =>
        e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right)) =
      none := by
  induction steps with
  | nil =>
      simp [simRowsOfStepData]
  | cons p ps ih =>
      have hhead :
          (simStepDataRow p).matchesInput
              (foldedSimStateCode tc side q) (foldedSymbolCode marked left right) =
            false :=
        simStepDataRow_matchesInput_of_currentCode_ne' (hcode p (by simp))
      have htail :
          (simRowsOfStepData ps).find? (fun e =>
              e.matchesInput (foldedSimStateCode tc side q)
                (foldedSymbolCode marked left right)) = none := by
        exact ih fun r hr => hcode r (by simp [hr])
      change (simStepDataRow p :: simRowsOfStepData ps).find? (fun e =>
          e.matchesInput (foldedSimStateCode tc side q)
            (foldedSymbolCode marked left right)) = none
      simp [hhead, htail]

theorem program_find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx] at h
      · simp [hx]
        have hxs : xs.find? p = none := by
          simpa [hx] using h
        simpa [hx] using ih hxs

theorem program_find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool}
    {a : α} (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa : x = a := by
          simpa [hx] using h
        subst a
        simp [hx]
      · have hxs : xs.find? p = some a := by
          simpa [hx] using h
        simp [hx, hxs]

theorem program_find?_eq_none_of_forall_matchesInput_false
    {xs : List PostTransition} {q a : Nat}
    (h : ∀ e ∈ xs, e.matchesInput q a = false) :
    xs.find? (fun e => e.matchesInput q a) = none := by
  induction xs with
  | nil =>
      simp
  | cons e xs ih =>
      have hhead : e.matchesInput q a = false := h e (by simp)
      have htail : xs.find? (fun e => e.matchesInput q a) = none := by
        apply ih
        intro e he
        exact h e (by simp [he])
      simp [hhead, htail]

theorem program_find?_flatMap_eq_none_of_forall
    {α β : Type} {xs : List α} {f : α → List β} {p : β → Bool}
    (h : ∀ x, x ∈ xs → (f x).find? p = none) :
    (xs.flatMap f).find? p = none := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [program_find?_append_of_eq_none (h x (by simp))]
      exact ih fun y hy => h y (by simp [hy])

theorem program_flatMap_range_split {α : Type} (f : Nat → List α) {n count : Nat}
    (hn : n < count) :
    (List.range count).flatMap f =
      (List.range n).flatMap f ++ f n ++ (List.Ico (n + 1) count).flatMap f := by
  have hsplit :
      List.range count = List.range n ++ n :: List.Ico (n + 1) count := by
    calc
      List.range count = List.Ico 0 count := by
        exact (List.Ico.zero_bot count).symm
      _ = List.Ico 0 n ++ List.Ico n count := by
        exact (List.Ico.append_consecutive (Nat.zero_le n) (le_of_lt hn)).symm
      _ = List.range n ++ n :: List.Ico (n + 1) count := by
        rw [List.Ico.zero_bot, List.Ico.eq_cons hn]
  rw [hsplit]
  simp [List.flatMap_append]

theorem initWriteOriginState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) :
    initWriteOriginState ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteOriginState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initMoveRightState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initMoveRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initMoveRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initWriteRightState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initWriteRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initReturnState_ne_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initReturnState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initReturnState foldedSimStateCode taggedState stateTagReturn stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initReturnState_injective :
    Function.Injective initReturnState := by
  intro i j h
  unfold initReturnState taggedState stateTagReturn at h
  exact (Nat.pair_eq_pair.mp h).2

theorem initWriteOriginState_ne_initReturnState (i : Nat) :
    initWriteOriginState ≠ initReturnState i := by
  intro h
  unfold initWriteOriginState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initMoveRightState_ne_initReturnState (i j : Nat) :
    initMoveRightState i ≠ initReturnState j := by
  intro h
  unfold initMoveRightState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initWriteRightState_ne_initReturnState (i j : Nat) :
    initWriteRightState i ≠ initReturnState j := by
  intro h
  unfold initWriteRightState initReturnState taggedState stateTagInit stateTagReturn at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

theorem initMoveRightRows_find?_eq_none_of_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initMoveRightState j ≠ foldedSimStateCode tc side q :=
          initMoveRightState_ne_foldedSimStateCode_data tc j side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput
                    (foldedSimStateCode tc side q) read = false :=
              mkRow_matchesInput_of_state_ne_data hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [program_find?_append_of_eq_none hhead]
      exact ih

theorem initWriteRightRows_find?_eq_none_of_foldedSimStateCode_data
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initWriteRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hstate : initWriteRightState j ≠ foldedSimStateCode tc side q :=
        initWriteRightState_ne_foldedSimStateCode_data tc j side q
      have hmiss :
          (initWriteRightRow j).matchesInput (foldedSimStateCode tc side q) read = false :=
        mkRow_matchesInput_of_state_ne_data hstate
      simp [hmiss, ih]

theorem initReturnRowsData_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initReturnRowsData.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initReturnRowsData
  induction initReturnIndexList with
  | nil =>
      simp
  | cons i indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initReturnRow default i r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initReturnState i ≠ foldedSimStateCode tc side q :=
          initReturnState_ne_foldedSimStateCode_data tc i side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initReturnRow default i r).matchesInput
                    (foldedSimStateCode tc side q) read = false := by
              by_cases hi0 : i = 0
              · subst i
                exact mkRow_matchesInput_of_state_ne_data hstate
              · unfold initReturnRow
                rw [if_neg hi0]
                exact mkRow_matchesInput_of_state_ne_data hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [program_find?_append_of_eq_none hhead]
      exact ih

private theorem find?_map_initReturnRowData_of_read
    (i read : Nat) (reads : List Nat)
    (hread : read ∈ reads) :
    (reads.map fun r => initReturnRow default i r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  induction reads with
  | nil =>
      cases hread
  | cons r reads ih =>
      simp only [List.mem_cons] at hread
      by_cases hr : r = read
      · subst r
        by_cases hi0 : i = 0
        · subst i
          simp [initReturnRow, mkRow, PostTransition.matchesInput]
        · simp [initReturnRow, hi0, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := by
          rcases hread with h | h
          · exact False.elim (hr h.symm)
          · exact h
        have hmiss :
            (initReturnRow default i r).matchesInput (initReturnState i) read = false := by
          by_cases hi0 : i = 0
          · subst i
            exact mkRow_matchesInput_of_read_ne hr
          · unfold initReturnRow
            rw [if_neg hi0]
            exact mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initReturnRowData_eq_none_of_index_ne
    {i j read : Nat} (hne : j ≠ i)
    (reads : List Nat) :
    (reads.map fun r => initReturnRow default j r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      none := by
  have hstate : initReturnState j ≠ initReturnState i := by
    intro h
    exact hne (initReturnState_injective h)
  induction reads with
  | nil =>
      simp
  | cons r reads ih =>
      have hmiss :
          (initReturnRow default j r).matchesInput (initReturnState i) read = false := by
        by_cases hj0 : j = 0
        · subst j
          exact mkRow_matchesInput_of_state_ne_data hstate
        · unfold initReturnRow
          rw [if_neg hj0]
          exact mkRow_matchesInput_of_state_ne_data hstate
      simp [hmiss, ih]

private theorem find?_flatMap_initReturnRowsData_aux
    (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initReturnRow default j r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        have hhead := find?_map_initReturnRowData_of_read i read foldedSymbolList hread
        simp only [List.flatMap_cons]
        exact program_find?_append_of_eq_some hhead
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hhead := find?_map_initReturnRowData_eq_none_of_index_ne
          (i := i) (j := j) (read := read) hji foldedSymbolList
        have htail := ih hi_tail
        simp only [List.flatMap_cons]
        rw [program_find?_append_of_eq_none hhead]
        exact htail

theorem initReturnRowsData_find?_of_mem {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    initReturnRowsData.find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  unfold initReturnRowsData
  exact find?_flatMap_initReturnRowsData_aux i read initReturnIndexList hi hread

theorem initMoveRightRows_find?_eq_none_of_initReturnState_data (i read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (initReturnState i) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (initReturnState i) read) = none := by
        have hstate : initMoveRightState j ≠ initReturnState i :=
          initMoveRightState_ne_initReturnState j i
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput (initReturnState i) read = false :=
              mkRow_matchesInput_of_state_ne_data hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [program_find?_append_of_eq_none hhead]
      exact ih

theorem initWriteRightRows_find?_eq_none_of_initReturnState_data (i read : Nat) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (initReturnState i) read) =
      none := by
  unfold initWriteRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hstate : initWriteRightState j ≠ initReturnState i :=
        initWriteRightState_ne_initReturnState j i
      have hmiss :
          (initWriteRightRow j).matchesInput (initReturnState i) read = false :=
        mkRow_matchesInput_of_state_ne_data hstate
      simp [hmiss, ih]

theorem initRowsData_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    initRowsData.find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  have horigin :
      initWriteOriginRow.matchesInput (foldedSimStateCode tc side q) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne_data
      (initWriteOriginState_ne_foldedSimStateCode_data tc side q)
  have hmove := initMoveRightRows_find?_eq_none_of_foldedSimStateCode_data tc side q read
  have hwrite := initWriteRightRows_find?_eq_none_of_foldedSimStateCode_data tc side q read
  have hreturn := initReturnRowsData_find?_eq_none_of_foldedSimStateCode tc side q read
  unfold initRowsData
  have htail :
      (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData)).find?
          (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
        none := by
    rw [program_find?_append_of_eq_none hmove]
    rw [program_find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

theorem simRowsOfStepData_find?_append_eq_of_forall_currentCode_ne
    {tc : Turing.ToPartrec.Code} {pref suffix : List SimStepData}
    {side : FoldSide} {marked : Bool} {q : SourceLabel tc}
    {left right : SourceSymbol}
    (hcode : ∀ p ∈ pref, p.2.2.1 ≠ TM0FiniteCompiler.stateCode tc q) :
    (simRowsOfStepData (pref ++ suffix)).find? (fun e =>
        e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right)) =
      (simRowsOfStepData suffix).find? (fun e =>
        e.matchesInput (foldedSimStateCode tc side q) (foldedSymbolCode marked left right)) := by
  rw [show simRowsOfStepData (pref ++ suffix) =
      simRowsOfStepData pref ++ simRowsOfStepData suffix by
    simp [simRowsOfStepData]]
  exact program_find?_append_of_eq_none
    (simRowsOfStepData_find?_eq_none_of_forall_currentCode_ne
      (tc := tc) (steps := pref) (side := side) (marked := marked) (q := q)
      (left := left) (right := right) hcode)


end TM0FoldedCompiler

end LeanWang
