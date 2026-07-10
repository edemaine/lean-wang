/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.Computability
import LeanWang.TM0FoldedCompiler.InitCore

/-!
Lookup and state-support lemmas for the data-parameterized initializer.
-/

namespace LeanWang

namespace TM0FoldedCompiler

theorem foldedStartState_mem_statesForInput
    (stateCount : Nat) (input : List SourceSymbol) :
    foldedStartState ∈ foldedStateListForInput stateCount input := by
  simp [foldedStateListForInput, foldedInitStateListFor, foldedStartState,
    initWriteOriginState]

theorem initMoveRightState_mem_statesForInput
    (stateCount : Nat) {input : List SourceSymbol} {i : Nat}
    (hi : i < input.length) :
    initMoveRightState i ∈ foldedStateListForInput stateCount input := by
  unfold foldedStateListForInput foldedInitStateListFor
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  exact ⟨i, List.mem_range.2 hi, by simp⟩

theorem initWriteRightState_mem_statesForInput
    (stateCount : Nat) {input : List SourceSymbol} {i : Nat}
    (hi : i < input.length) :
    initWriteRightState i ∈ foldedStateListForInput stateCount input := by
  unfold foldedStateListForInput foldedInitStateListFor
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  exact ⟨i, List.mem_range.2 hi, by simp⟩

theorem initReturnState_mem_statesForInput
    (stateCount : Nat) (input : List SourceSymbol) (i : Nat)
    (hi : i = 0 ∨ i < input.length) :
    initReturnState i ∈ foldedStateListForInput stateCount input := by
  rcases hi with rfl | hi
  · simp [foldedStateListForInput, foldedInitStateListFor]
  · unfold foldedStateListForInput foldedInitStateListFor
    apply List.mem_append_left
    apply List.mem_append_right
    rw [List.mem_flatMap]
    exact ⟨i, List.mem_range.2 hi, by simp⟩

theorem nextAfterOriginFor_mem_statesForInput
    (stateCount : Nat) (input : List SourceSymbol) :
    nextAfterOriginFor input ∈ foldedStateListForInput stateCount input := by
  unfold nextAfterOriginFor
  split
  · exact initReturnState_mem_statesForInput stateCount input 0 (Or.inl rfl)
  · exact initMoveRightState_mem_statesForInput stateCount
      (by omega)

theorem nextAfterWriteRightFor_mem_statesForInput
    (stateCount : Nat) {input : List SourceSymbol} {i : Nat}
    (hi : i + 1 < input.length) :
    nextAfterWriteRightFor input i ∈ foldedStateListForInput stateCount input := by
  unfold nextAfterWriteRightFor
  split
  · exact initMoveRightState_mem_statesForInput stateCount (by omega)
  · exact initReturnState_mem_statesForInput stateCount input (i + 1)
      (Or.inr hi)

theorem initRowsForInput_find?_start_blank (input : List SourceSymbol) :
    (initRowsForInput input).find?
        (fun e => e.matchesInput foldedStartState foldedBlank) =
      some (initWriteOriginRowFor input) := by
  unfold initRowsForInput initWriteOriginRowFor foldedStartState
  simp [mkRow, PostTransition.matchesInput]

private theorem find?_map_initMoveRightRowFor_of_read
    (i read : Nat) (reads : List Nat) (hread : read ∈ reads) :
    (reads.map fun r => initMoveRightRow i r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  induction reads with
  | nil => cases hread
  | cons r reads ih =>
      simp only [List.mem_cons] at hread
      by_cases hr : r = read
      · subst r
        simp [initMoveRightRow, mkRow, PostTransition.matchesInput]
      · have htail : read ∈ reads := hread.resolve_left (Ne.symm hr)
        have hmiss :
            (initMoveRightRow i r).matchesInput (initMoveRightState i) read = false :=
          mkRow_matchesInput_of_read_ne hr
        simp [hmiss, ih htail]

private theorem find?_map_initMoveRightRowFor_eq_none_of_index_ne
    {i j read : Nat} (hne : j ≠ i) (reads : List Nat) :
    (reads.map fun r => initMoveRightRow j r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) = none := by
  have hstate : initMoveRightState j ≠ initMoveRightState i := by
    intro h
    exact hne (initMoveRightState_injective h)
  induction reads with
  | nil => simp
  | cons r reads ih =>
      have hmiss :
          (initMoveRightRow j r).matchesInput (initMoveRightState i) read = false :=
        mkRow_matchesInput_of_state_ne_data hstate
      simp [hmiss, ih]

private theorem find?_flatMap_initMoveRightRowsFor_aux
    (i read : Nat) (indices : List Nat)
    (hi : i ∈ indices) (hread : read ∈ foldedSymbolList) :
    (indices.flatMap fun j => foldedSymbolList.map fun r => initMoveRightRow j r).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  induction indices with
  | nil => cases hi
  | cons j indices ih =>
      simp only [List.mem_cons] at hi
      simp only [List.flatMap_cons]
      by_cases hji : j = i
      · subst j
        exact program_find?_append_of_eq_some
          (find?_map_initMoveRightRowFor_of_read i read foldedSymbolList hread)
      · have hiTail : i ∈ indices := hi.resolve_left (Ne.symm hji)
        rw [program_find?_append_of_eq_none
          (find?_map_initMoveRightRowFor_eq_none_of_index_ne hji foldedSymbolList)]
        exact ih hiTail

theorem initMoveRightRowsFor_find?_of_mem
    {input : List SourceSymbol} {i read : Nat}
    (hi : i < input.length - 1) (hread : read ∈ foldedSymbolList) :
    (initMoveRightRowsFor input).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  unfold initMoveRightRowsFor
  exact find?_flatMap_initMoveRightRowsFor_aux i read _
    (List.mem_range.2 hi) hread

private theorem initWriteOriginRowFor_miss_move
    (input : List SourceSymbol) (i read : Nat) :
    (initWriteOriginRowFor input).matchesInput (initMoveRightState i) read = false := by
  exact mkRow_matchesInput_of_state_ne_data
    (initWriteOriginState_ne_initMoveRightState i)

theorem initRowsForInput_find?_move
    {input : List SourceSymbol} {i read : Nat}
    (hi : i < input.length - 1) (hread : read ∈ foldedSymbolList) :
    (initRowsForInput input).find?
        (fun e => e.matchesInput (initMoveRightState i) read) =
      some (initMoveRightRow i read) := by
  unfold initRowsForInput
  simp only [List.find?_cons]
  rw [initWriteOriginRowFor_miss_move]
  exact program_find?_append_of_eq_some
    (initMoveRightRowsFor_find?_of_mem hi hread)

end TM0FoldedCompiler

end LeanWang
