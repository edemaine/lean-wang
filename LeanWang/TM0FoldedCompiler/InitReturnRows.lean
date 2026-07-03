/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.InitMoveRows

/-!
Lookup lemmas for return initialization rows and initialization-row misses.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem initReturnState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initReturnState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initReturnState foldedSimStateCode taggedState stateTagReturn stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

private theorem find?_map_initReturnRow_of_read
    (tc : Turing.ToPartrec.Code) (i read : Nat) (reads : List Nat)
    (hread : read ∈ reads) :
    (reads.map fun r => initReturnRow tc i r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow tc i read) := by
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
            (initReturnRow tc i r).matchesInput (initReturnState i) read = false := by
          by_cases hi0 : i = 0
          · subst i
            exact mkRow_matchesInput_of_read_ne hr
          · unfold initReturnRow
            rw [if_neg hi0]
            exact mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initReturnRow_eq_none_of_index_ne
    (tc : Turing.ToPartrec.Code) {i j read : Nat} (hne : j ≠ i)
    (reads : List Nat) :
    (reads.map fun r => initReturnRow tc j r).find?
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
          (initReturnRow tc j r).matchesInput (initReturnState i) read = false := by
        by_cases hj0 : j = 0
        · subst j
          exact mkRow_matchesInput_of_state_ne hstate
        · unfold initReturnRow
          rw [if_neg hj0]
          exact mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

private theorem find?_flatMap_initReturnRows_aux
    (tc : Turing.ToPartrec.Code) (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initReturnRow tc j r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow tc i read) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        have hhead := find?_map_initReturnRow_of_read tc i read foldedSymbolList hread
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hhead := find?_map_initReturnRow_eq_none_of_index_ne
          tc (i := i) (j := j) (read := read) hji foldedSymbolList
        have htail := ih hi_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem initReturnRows_find?_of_mem (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i ∈ initReturnIndexList)
    (hread : read ∈ foldedSymbolList) :
    (initReturnRows tc).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow tc i read) := by
  unfold initReturnRows
  exact find?_flatMap_initReturnRows_aux tc i read initReturnIndexList hi hread

theorem initReturnRows_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    (initReturnRows tc).find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  unfold initReturnRows
  induction initReturnIndexList with
  | nil =>
      simp
  | cons i indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initReturnRow tc i r).find?
              (fun e => e.matchesInput (foldedSimStateCode tc side q) read) = none := by
        have hstate : initReturnState i ≠ foldedSimStateCode tc side q :=
          initReturnState_ne_foldedSimStateCode tc i side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initReturnRow tc i r).matchesInput
                    (foldedSimStateCode tc side q) read = false := by
              by_cases hi0 : i = 0
              · subst i
                exact mkRow_matchesInput_of_state_ne hstate
              · unfold initReturnRow
                rw [if_neg hi0]
                exact mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initMoveRightRows_find?_eq_none_of_initReturnState (i read : Nat) :
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
              mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initWriteRightRows_find?_eq_none_of_initReturnState (i read : Nat) :
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
        mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

theorem initWriteRightRows_find?_eq_none_of_foldedSimStateCode
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
        initWriteRightState_ne_foldedSimStateCode tc j side q
      have hmiss :
          (initWriteRightRow j).matchesInput (foldedSimStateCode tc side q) read = false :=
        mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

theorem initRows_find?_eq_none_of_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (side : FoldSide) (q : SourceLabel tc) (read : Nat) :
    (initRows tc).find?
        (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
      none := by
  have horigin :
      initWriteOriginRow.matchesInput (foldedSimStateCode tc side q) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne
      (initWriteOriginState_ne_foldedSimStateCode tc side q)
  have hmove := initMoveRightRows_find?_eq_none_of_foldedSimStateCode tc side q read
  have hwrite := initWriteRightRows_find?_eq_none_of_foldedSimStateCode tc side q read
  have hreturn := initReturnRows_find?_eq_none_of_foldedSimStateCode tc side q read
  unfold initRows
  have htail :
      (initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc).find?
          (fun e => e.matchesInput (foldedSimStateCode tc side q) read) =
        none := by
    rw [show initMoveRightRows ++ initWriteRightRows ++ initReturnRows tc =
        initMoveRightRows ++ (initWriteRightRows ++ initReturnRows tc) by
      rw [List.append_assoc]]
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail


end TM0FoldedCompiler

end LeanWang
