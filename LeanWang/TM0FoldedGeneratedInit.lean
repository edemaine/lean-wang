/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedProgram

/-!
Initialization lemmas for the generated folded program data.

`TM0FoldedCompiler` proves the semantic initialization path for the canonical
finite program. This file records the matching facts for `positionProgramData`,
the generated program used while bridging semantic correctness to the executable
reduction data.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

private theorem find?_append_of_eq_none {α : Type} {xs ys : List α} {p : α → Bool}
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

private theorem find?_append_of_eq_some {α : Type} {xs ys : List α} {p : α → Bool}
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

private theorem initRowsData_find?_initReturn_zero {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    initRowsData.find? (fun e => e.matchesInput (initReturnState 0) read) =
      some (initReturnRow default 0 read) := by
  have horigin :
      initWriteOriginRow.matchesInput (initReturnState 0) read = false := by
    unfold initWriteOriginRow
    exact mkRow_matchesInput_of_state_ne_data
      (initWriteOriginState_ne_initReturnState 0)
  have hmove := initMoveRightRows_find?_eq_none_of_initReturnState_data 0 read
  have hwrite := initWriteRightRows_find?_eq_none_of_initReturnState_data 0 read
  have hreturn := initReturnRowsData_find?_of_mem
    (i := 0) (read := read) (by simp [initReturnIndexList]) hread
  unfold initRowsData
  have htail :
      (initMoveRightRows ++ (initWriteRightRows ++ initReturnRowsData)).find?
          (fun e => e.matchesInput (initReturnState 0) read) =
        some (initReturnRow default 0 read) := by
    rw [find?_append_of_eq_none hmove]
    rw [find?_append_of_eq_none hwrite]
    exact hreturn
  simpa [horigin] using htail

theorem positionProgramData_transition?_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (positionProgramData tc).transition? (initReturnState 0) read =
      some (initReturnRow default 0 read) := by
  unfold PostProgram.transition?
  change (initRowsData ++
      simRowsOfStepData (simStepDataByLabelIndexWithPositionCode tc)).find?
        (fun e => e.matchesInput (initReturnState 0) read) =
      some (initReturnRow default 0 read)
  exact find?_append_of_eq_some (initRowsData_find?_initReturn_zero hread)

theorem positionProgramData_step_initReturn_zero
    (tc : Turing.ToPartrec.Code) {read : Nat}
    (hread : read ∈ foldedSymbolList) :
    (positionProgramData tc).step (initReturnState 0) read =
      some (foldedSimStartState tc, PostStmt.write read) := by
  have hfind := positionProgramData_transition?_initReturn_zero tc hread
  have hnextCode : foldedSimStartStateCode ∈ foldedStateList tc := by
    simpa [foldedSimStartState] using foldedSimStartState_mem_states tc
  have hstep :
      (positionProgramData tc).step (initReturnState 0) read =
        some (foldedSimStartStateCode, PostStmt.write read) := by
    simp [PostProgram.step, hfind, initReturnRow, mkRow, hnextCode, hread]
  simpa [foldedSimStartState] using hstep

private theorem nextID_of_step_eq_some {P : PostProgram} {c : PostID}
    {q q' : Nat} {stmt : PostStmt}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', stmt)) :
    P.nextID c =
      let r := PostProgram.applyStmt stmt c.tape c.head
      { tape := r.1, head := r.2, state := some q' } := by
  rw [PostProgram.nextID_of_running (P := P) (c := c) (q := q) hstate, hstep]

theorem positionProgramData_nextID_initial (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).nextID (positionProgramData tc).initialID =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  have hstate : ((positionProgramData tc).initialID).state = some foldedStartState := rfl
  have hstep :
      (positionProgramData tc).step foldedStartState
          (((positionProgramData tc).initialID).tape ((positionProgramData tc).initialID).head) =
        some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
    exact positionProgramData_step_start_blank tc
  rw [nextID_of_step_eq_some hstate hstep]
  simp [PostProgram.initialID, PostProgram.applyStmt, nextAfterOrigin_eq_initReturnState_zero]

theorem positionProgramData_runEmpty_one (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).runEmpty 1 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  rw [show 1 = 0 + 1 by rfl, PostProgram.runEmpty_succ, PostProgram.runEmpty_zero]
  exact positionProgramData_nextID_initial tc

theorem positionProgramData_nextID_after_origin (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).nextID
        { tape := Function.update (fun _ => foldedBlank) 0
            (foldedOriginSymbol (inputSymbol 0)),
          head := 0,
          state := some (initReturnState 0) } =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) } := by
  let id : PostID :=
    { tape := Function.update (fun _ => foldedBlank) 0
        (foldedOriginSymbol (inputSymbol 0)),
      head := 0,
      state := some (initReturnState 0) }
  have hstate : id.state = some (initReturnState 0) := rfl
  have hread :
      id.tape id.head = foldedOriginSymbol (inputSymbol 0) := by
    simp [id]
  have hmem :
      foldedOriginSymbol (inputSymbol 0) ∈ foldedSymbolList :=
    foldedSymbolCode_mem_symbols true default (inputSymbol 0)
  have hstep :
      (positionProgramData tc).step (initReturnState 0) (id.tape id.head) =
        some (foldedSimStartState tc, PostStmt.write (id.tape id.head)) := by
    rw [hread]
    exact positionProgramData_step_initReturn_zero tc hmem
  change (positionProgramData tc).nextID id =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) }
  rw [nextID_of_step_eq_some hstate hstep]
  simp [id, PostProgram.applyStmt]

theorem positionProgramData_runEmpty_two (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).runEmpty 2 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) } := by
  rw [show 2 = 1 + 1 by rfl, PostProgram.runEmpty_succ,
    positionProgramData_runEmpty_one]
  exact positionProgramData_nextID_after_origin tc

theorem positionProgramData_runEmpty_add_two
    (tc : Turing.ToPartrec.Code) (n : Nat) :
    (positionProgramData tc).runEmpty (n + 2) =
      Nat.iterate (positionProgramData tc).nextID n
        ((positionProgramData tc).runEmpty 2) := by
  unfold PostProgram.runEmpty
  rw [Function.iterate_add_apply]

end TM0FoldedCompiler

end LeanWang
