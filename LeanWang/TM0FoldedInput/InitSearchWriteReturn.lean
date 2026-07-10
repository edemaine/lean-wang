/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.InitSearch
import LeanWang.TM0FoldedCompiler.InitMoveRows

/-!
Write and rewind lookup lemmas for the data-parameterized initializer.
-/

namespace LeanWang

namespace TM0FoldedCompiler

private theorem find?_map_initWriteRightRowFor_aux
    (input : List SourceSymbol) (i : Nat) (indices : List Nat) (hi : i ∈ indices) :
    (indices.map fun j => initWriteRightRowFor input j).find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRowFor input i) := by
  induction indices with
  | nil => cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      by_cases hji : j = i
      · subst j
        simp [initWriteRightRowFor, mkRow, PostTransition.matchesInput]
      · have hiTail : i ∈ indices := hi.resolve_left (Ne.symm hji)
        have hstate : initWriteRightState j ≠ initWriteRightState i := by
          intro h
          exact hji (initWriteRightState_injective h)
        have hmiss :
            (initWriteRightRowFor input j).matchesInput
                (initWriteRightState i) foldedBlank = false :=
          mkRow_matchesInput_of_state_ne_data hstate
        simp [hmiss, ih hiTail]

theorem initWriteRightRowsFor_find?_of_mem
    {input : List SourceSymbol} {i : Nat} (hi : i < input.length - 1) :
    (initWriteRightRowsFor input).find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRowFor input i) := by
  unfold initWriteRightRowsFor
  exact find?_map_initWriteRightRowFor_aux input i _ (List.mem_range.2 hi)

private theorem initMoveRightRowsFor_find?_eq_none_of_write
    (input : List SourceSymbol) (i read : Nat) :
    (initMoveRightRowsFor input).find?
        (fun e => e.matchesInput (initWriteRightState i) read) = none := by
  unfold initMoveRightRowsFor
  apply program_find?_flatMap_eq_none_of_forall
  intro j _hj
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  rw [List.mem_map] at he
  rcases he with ⟨r, _hr, rfl⟩
  exact mkRow_matchesInput_of_state_ne_data
    (initMoveRightState_ne_initWriteRightState j i)

private theorem initWriteOriginRowFor_miss_write
    (input : List SourceSymbol) (i read : Nat) :
    (initWriteOriginRowFor input).matchesInput (initWriteRightState i) read = false := by
  exact mkRow_matchesInput_of_state_ne_data
    (initWriteOriginState_ne_initWriteRightState i)

theorem initRowsForInput_find?_write
    {input : List SourceSymbol} {i : Nat} (hi : i < input.length - 1) :
    (initRowsForInput input).find?
        (fun e => e.matchesInput (initWriteRightState i) foldedBlank) =
      some (initWriteRightRowFor input i) := by
  unfold initRowsForInput
  simp only [List.find?_cons]
  rw [initWriteOriginRowFor_miss_write]
  rw [program_find?_append_of_eq_none
    (initMoveRightRowsFor_find?_eq_none_of_write input i foldedBlank)]
  exact program_find?_append_of_eq_some
    (initWriteRightRowsFor_find?_of_mem hi)

private theorem find?_map_initReturnRowFor_of_read
    (i read : Nat) (reads : List Nat) (hread : read ∈ reads) :
    (reads.map fun r => initReturnRow default i r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  induction reads with
  | nil => cases hread
  | cons r reads ih =>
      simp only [List.mem_cons] at hread
      by_cases hr : r = read
      · subst r
        by_cases hi0 : i = 0
        · subst i
          simp [initReturnRow, mkRow, PostTransition.matchesInput]
        · simp [initReturnRow, hi0, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := hread.resolve_left (Ne.symm hr)
        have hmiss :
            (initReturnRow default i r).matchesInput (initReturnState i) read = false := by
          by_cases hi0 : i = 0
          · subst i
            exact mkRow_matchesInput_of_read_ne hr
          · unfold initReturnRow
            rw [if_neg hi0]
            exact mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initReturnRowFor_eq_none_of_index_ne
    {i j read : Nat} (hne : j ≠ i) (reads : List Nat) :
    (reads.map fun r => initReturnRow default j r).find?
        (fun e => e.matchesInput (initReturnState i) read) = none := by
  have hstate : initReturnState j ≠ initReturnState i := by
    intro h
    exact hne (initReturnState_injective h)
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  rw [List.mem_map] at he
  rcases he with ⟨r, _hr, rfl⟩
  by_cases hj0 : j = 0
  · subst j
    exact mkRow_matchesInput_of_state_ne_data hstate
  · unfold initReturnRow
    rw [if_neg hj0]
    exact mkRow_matchesInput_of_state_ne_data hstate

private theorem find?_flatMap_initReturnRowsFor_aux
    (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initReturnRow default j r).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  induction indices with
  | nil => cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      simp only [List.flatMap_cons]
      by_cases hji : j = i
      · subst j
        exact program_find?_append_of_eq_some
          (find?_map_initReturnRowFor_of_read i read foldedSymbolList hread)
      · have hiTail : i ∈ indices := hi.resolve_left (Ne.symm hji)
        rw [program_find?_append_of_eq_none
          (find?_map_initReturnRowFor_eq_none_of_index_ne hji foldedSymbolList)]
        exact ih hiTail

theorem initReturnRowsFor_find?_of_mem
    {input : List SourceSymbol} {i read : Nat}
    (hi : i ∈ initReturnIndexListFor input) (hread : read ∈ foldedSymbolList) :
    (initReturnRowsFor input).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  unfold initReturnRowsFor
  exact find?_flatMap_initReturnRowsFor_aux i read _ hi hread

private theorem initMoveRightRowsFor_find?_eq_none_of_return
    (input : List SourceSymbol) (i read : Nat) :
    (initMoveRightRowsFor input).find?
        (fun e => e.matchesInput (initReturnState i) read) = none := by
  unfold initMoveRightRowsFor
  apply program_find?_flatMap_eq_none_of_forall
  intro j _hj
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  rw [List.mem_map] at he
  rcases he with ⟨r, _hr, rfl⟩
  exact mkRow_matchesInput_of_state_ne_data
    (initMoveRightState_ne_initReturnState j i)

private theorem initWriteRightRowsFor_find?_eq_none_of_return
    (input : List SourceSymbol) (i read : Nat) :
    (initWriteRightRowsFor input).find?
        (fun e => e.matchesInput (initReturnState i) read) = none := by
  unfold initWriteRightRowsFor
  apply program_find?_eq_none_of_forall_matchesInput_false
  intro e he
  rw [List.mem_map] at he
  rcases he with ⟨j, _hj, rfl⟩
  exact mkRow_matchesInput_of_state_ne_data
    (initWriteRightState_ne_initReturnState j i)

private theorem initWriteOriginRowFor_miss_return
    (input : List SourceSymbol) (i read : Nat) :
    (initWriteOriginRowFor input).matchesInput (initReturnState i) read = false := by
  exact mkRow_matchesInput_of_state_ne_data
    (initWriteOriginState_ne_initReturnState i)

theorem initRowsForInput_find?_return
    {input : List SourceSymbol} {i read : Nat}
    (hi : i ∈ initReturnIndexListFor input) (hread : read ∈ foldedSymbolList) :
    (initRowsForInput input).find?
        (fun e => e.matchesInput (initReturnState i) read) =
      some (initReturnRow default i read) := by
  unfold initRowsForInput
  simp only [List.find?_cons]
  rw [initWriteOriginRowFor_miss_return]
  rw [program_find?_append_of_eq_none
    (initMoveRightRowsFor_find?_eq_none_of_return input i read)]
  rw [program_find?_append_of_eq_none
    (initWriteRightRowsFor_find?_eq_none_of_return input i read)]
  exact initReturnRowsFor_find?_of_mem hi hread

end TM0FoldedCompiler

end LeanWang
