/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.InitCore

/-!
Lookup lemmas for the right-moving initialization rows.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

private theorem find?_map_initMoveRightRow_of_read
    (i read : Nat) (reads : List Nat) (hread : read ∈ reads) :
    (reads.map fun r => initMoveRightRow i r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  induction reads with
  | nil =>
      cases hread
  | cons r reads ih =>
      simp only [List.mem_cons] at hread
      by_cases hr : r = read
      · subst r
        simp [initMoveRightRow, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := by
          rcases hread with h | h
          · exact False.elim (hr h.symm)
          · exact h
        have hmiss :
            (initMoveRightRow i r).matchesInput (initMoveRightState i) read = false := by
          exact mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initMoveRightRow_eq_none_of_index_ne
    {i j read : Nat} (hne : j ≠ i) (reads : List Nat) :
    (reads.map fun r => initMoveRightRow j r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      none := by
  have hstate : initMoveRightState j ≠ initMoveRightState i := by
    intro h
    exact hne (initMoveRightState_injective h)
  induction reads with
  | nil =>
      simp
  | cons r reads ih =>
      have hmiss :
          (initMoveRightRow j r).matchesInput (initMoveRightState i) read = false :=
        mkRow_matchesInput_of_state_ne hstate
      simp [hmiss, ih]

private theorem find?_flatMap_initMoveRightRows_aux
    (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initMoveRightRow j r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        have hhead := find?_map_initMoveRightRow_of_read i read foldedSymbolList hread
        simp only [List.flatMap_cons]
        exact find?_append_of_eq_some hhead
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hhead := find?_map_initMoveRightRow_eq_none_of_index_ne
          (i := i) (j := j) (read := read) hji foldedSymbolList
        have htail := ih hi_tail
        simp only [List.flatMap_cons]
        rw [find?_append_of_eq_none hhead]
        exact htail

theorem initMoveRightRows_find?_of_mem {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  unfold initMoveRightRows
  exact find?_flatMap_initMoveRightRows_aux i read
    (List.range (TM0Route.partrecStartedTM0Input.length - 1)) (List.mem_range.2 hi) hread

theorem initWriteRightState_injective :
    Function.Injective initWriteRightState := by
  intro i j h
  unfold initWriteRightState taggedState stateTagInit at h
  have hpayload := (Nat.pair_eq_pair.mp h).2
  omega

theorem initWriteRightState_ne_foldedSimStateCode
    (tc : Turing.ToPartrec.Code) (i : Nat) (side : FoldSide) (q : SourceLabel tc) :
    initWriteRightState i ≠ foldedSimStateCode tc side q := by
  intro h
  unfold initWriteRightState foldedSimStateCode taggedState stateTagInit stateTagSim at h
  have htag := (Nat.pair_eq_pair.mp h).1
  omega

private theorem find?_map_initWriteRightRows_aux
    (i : Nat) (indices : List Nat) (hi : i ∈ indices) :
    (indices.map fun j => initWriteRightRow j).find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRow i) := by
  induction indices with
  | nil =>
      cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        simp [initWriteRightRow, mkRow, PostTransition.matchesInput]
      · have hi_tail : i ∈ indices := by
          rcases hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        have hstate : initWriteRightState j ≠ initWriteRightState i := by
          intro h
          exact hji (initWriteRightState_injective h)
        have hmiss :
            (initWriteRightRow j).matchesInput (initWriteRightState i) foldedBlank = false :=
          mkRow_matchesInput_of_state_ne hstate
        simp [hmiss, ih hi_tail]

theorem initWriteRightRows_find?_of_mem {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    initWriteRightRows.find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRow i) := by
  unfold initWriteRightRows
  exact find?_map_initWriteRightRows_aux i
    (List.range (TM0Route.partrecStartedTM0Input.length - 1)) (List.mem_range.2 hi)

theorem initMoveRightRows_find?_eq_none_of_initWriteRightState (i read : Nat) :
    initMoveRightRows.find?
        (fun e => e.matchesInput (initWriteRightState i) read) =
      none := by
  unfold initMoveRightRows
  induction List.range (TM0Route.partrecStartedTM0Input.length - 1) with
  | nil =>
      simp
  | cons j indices ih =>
      have hhead :
          (foldedSymbolList.map fun r => initMoveRightRow j r).find?
              (fun e => e.matchesInput (initWriteRightState i) read) = none := by
        have hstate : initMoveRightState j ≠ initWriteRightState i :=
          initMoveRightState_ne_initWriteRightState j i
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput (initWriteRightState i) read = false :=
              mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih

theorem initMoveRightRows_find?_eq_none_of_foldedSimStateCode
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
          initMoveRightState_ne_foldedSimStateCode tc j side q
        induction foldedSymbolList with
        | nil =>
            simp
        | cons r reads ihReads =>
            have hmiss :
                (initMoveRightRow j r).matchesInput
                    (foldedSimStateCode tc side q) read = false :=
              mkRow_matchesInput_of_state_ne hstate
            simp [hmiss, ihReads]
      simp only [List.flatMap_cons]
      rw [find?_append_of_eq_none hhead]
      exact ih


end TM0FoldedCompiler

end LeanWang
