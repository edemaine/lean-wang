/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.InitRunCore

/-!
The complete execution of the data-parameterized initialization prelude.
-/

namespace LeanWang

namespace TM0FoldedCompiler

def afterOriginInitID (input : List SourceSymbol) : PostID where
  tape := writtenInputTape input 0
  head := 0
  state := some (nextAfterOriginFor input)

theorem nextID_initial_onInput
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    (positionProgramDataOnInput tc input).nextID
        (positionProgramDataOnInput tc input).initialID =
      afterOriginInitID input := by
  have hstep := positionProgramDataOnInput_step_start tc input
  rw [PostProgram.nextID_of_running
    (P := positionProgramDataOnInput tc input)
    (c := (positionProgramDataOnInput tc input).initialID)
    (q := foldedStartState) rfl]
  change
    (match (positionProgramDataOnInput tc input).step foldedStartState foldedBlank with
      | none => _
      | some (q', stmt) =>
          let r := PostProgram.applyStmt stmt (fun _ => foldedBlank) 0
          ({ tape := r.1, head := r.2, state := some q' } : PostID)) =
        afterOriginInitID input
  rw [hstep]
  rfl

theorem moveInitID_reaches_move_add
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol)
    (i n : Nat) (hbound : i + n < input.length - 1) :
    PostReaches (positionProgramDataOnInput tc input)
      (moveInitID input i) (moveInitID input (i + n)) := by
  induction n generalizing i with
  | zero =>
      simpa using PostReaches.refl
        (positionProgramDataOnInput tc input) (moveInitID input i)
  | succ n ih =>
      have hi : i < input.length - 1 := by omega
      have hmore : i + 2 < input.length := by omega
      have hmove := PostReaches.single (nextID_moveInitID tc hi)
      have hwrite := PostReaches.single (nextID_writeInitID tc hi)
      have hafter : afterWriteInitID input i = moveInitID input (i + 1) := by
        unfold afterWriteInitID moveInitID nextAfterWriteRightFor
        simp [hmore]
      rw [hafter] at hwrite
      have htail : PostReaches (positionProgramDataOnInput tc input)
          (moveInitID input (i + 1)) (moveInitID input ((i + 1) + n)) :=
        ih (i := i + 1) (by omega)
      have heq : (i + 1) + n = i + (n + 1) := by omega
      rw [heq] at htail
      exact (hmove.trans hwrite).trans htail

theorem moveInitID_reaches_return_last
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol)
    (last : Nat) (hlength : input.length = last + 1) (hlast : 0 < last) :
    PostReaches (positionProgramDataOnInput tc input)
      (moveInitID input 0) (returnInitID input last last) := by
  have hprefix : last - 1 < input.length - 1 := by omega
  have hpref := moveInitID_reaches_move_add tc input 0 (last - 1)
    (by simpa using hprefix)
  have hindex : last - 1 < input.length - 1 := by omega
  have hmove := PostReaches.single (nextID_moveInitID tc hindex)
  have hwrite := PostReaches.single (nextID_writeInitID tc hindex)
  have hafter : afterWriteInitID input (last - 1) =
      returnInitID input last last := by
    unfold afterWriteInitID returnInitID nextAfterWriteRightFor
    have hnot : ¬(last - 1 + 2 < input.length) := by omega
    have hpred : last - 1 + 1 = last := by omega
    simp [hnot, hpred]
  rw [hafter] at hwrite
  have hpref' : PostReaches (positionProgramDataOnInput tc input)
      (moveInitID input 0) (moveInitID input (last - 1)) := by
    simpa using hpref
  exact (hpref'.trans hmove).trans hwrite

theorem nextID_returnInitID_succ
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    {written i : Nat} (hwritten : written < input.length)
    (hi : i + 1 ≤ written) :
    (positionProgramDataOnInput tc input).nextID
        (returnInitID input written (i + 1)) =
      returnInitID input written i := by
  have hread : writtenInputTape input written (i + 1) ∈ foldedSymbolList :=
    writtenInputTape_mem_of_le input hi
  have hstep := positionProgramDataOnInput_step_return_succ tc
    (input := input) (i := i) (read := writtenInputTape input written (i + 1))
    (hi := by omega) hread
  rw [PostProgram.nextID_of_running
    (P := positionProgramDataOnInput tc input)
    (c := returnInitID input written (i + 1))
    (q := initReturnState (i + 1)) rfl]
  change
    (match (positionProgramDataOnInput tc input).step
        (initReturnState (i + 1)) (writtenInputTape input written (i + 1)) with
      | none => _
      | some (q', stmt) =>
          let r := PostProgram.applyStmt stmt (writtenInputTape input written) (i + 1)
          ({ tape := r.1, head := r.2, state := some q' } : PostID)) =
        returnInitID input written i
  rw [hstep]
  rfl

theorem returnInitID_reaches_zero
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    {written head : Nat} (hwritten : written < input.length) (hhead : head ≤ written) :
    PostReaches (positionProgramDataOnInput tc input)
      (returnInitID input written head) (returnInitID input written 0) := by
  induction head with
  | zero => exact PostReaches.refl _ _
  | succ head ih =>
      exact (PostReaches.single
        (nextID_returnInitID_succ tc hwritten hhead)).trans
          (ih (by omega))

theorem nextID_returnInitID_zero
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {written : Nat} :
    (positionProgramDataOnInput tc input).nextID
        (returnInitID input written 0) =
      simInitID input written := by
  have hread : writtenInputTape input written 0 ∈ foldedSymbolList :=
    writtenInputTape_mem_of_le input (Nat.zero_le written)
  have hstep := positionProgramDataOnInput_step_return_zero tc
    (input := input) (read := writtenInputTape input written 0) hread
  rw [PostProgram.nextID_of_running
    (P := positionProgramDataOnInput tc input)
    (c := returnInitID input written 0) (q := initReturnState 0) rfl]
  change
    (match (positionProgramDataOnInput tc input).step
        (initReturnState 0) (writtenInputTape input written 0) with
      | none => _
      | some (q', stmt) =>
          let r := PostProgram.applyStmt stmt (writtenInputTape input written) 0
          ({ tape := r.1, head := r.2, state := some q' } : PostID)) =
        simInitID input written
  rw [hstep]
  simp [PostProgram.applyStmt, simInitID, Function.update_eq_self]

theorem initialID_reaches_simInitID
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    PostReaches (positionProgramDataOnInput tc input)
      (positionProgramDataOnInput tc input).initialID
      (simInitID input (input.length - 1)) := by
  have horigin := PostReaches.single (nextID_initial_onInput tc input)
  cases input with
  | nil => contradiction
  | cons a tail =>
      cases tail with
      | nil =>
          have hafter : afterOriginInitID [a] = returnInitID [a] 0 0 := by
            simp [afterOriginInitID, returnInitID, nextAfterOriginFor]
          rw [hafter] at horigin
          have hfinal := PostReaches.single
            (nextID_returnInitID_zero (tc := tc) (input := [a]) (written := 0))
          simpa using horigin.trans hfinal
      | cons b tail =>
          let input := a :: b :: tail
          let last := (b :: tail).length
          have hlength : input.length = last + 1 := by simp [input, last]
          have hlast : 0 < last := by simp [last]
          have hafter : afterOriginInitID input = moveInitID input 0 := by
            unfold afterOriginInitID moveInitID nextAfterOriginFor
            simp [input]
          rw [hafter] at horigin
          have hforward := moveInitID_reaches_return_last
            tc input last hlength hlast
          have hreturn := returnInitID_reaches_zero tc
            (input := input) (written := last) (head := last)
            (by omega) (le_refl last)
          have hfinal := PostReaches.single
            (nextID_returnInitID_zero (tc := tc) (input := input) (written := last))
          have hall := ((horigin.trans hforward).trans hreturn).trans hfinal
          simpa [input, last] using hall

end TM0FoldedCompiler

end LeanWang
