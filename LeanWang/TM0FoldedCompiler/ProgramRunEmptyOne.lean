/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramInitReturn

/-!
First empty-run state for the folded program.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

private theorem nextID_of_step_eq_some {P : PostProgram} {c : PostID}
    {q q' : Nat} {stmt : PostStmt}
    (hstate : c.state = some q)
    (hstep : P.step q (c.tape c.head) = some (q', stmt)) :
    P.nextID c =
      let r := PostProgram.applyStmt stmt c.tape c.head
      { tape := r.1, head := r.2, state := some q' } := by
  rw [PostProgram.nextID_of_running (P := P) (c := c) (q := q) hstate, hstep]

theorem program_nextID_initial (tc : Turing.ToPartrec.Code) :
    (program tc).nextID (program tc).initialID =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  have hstate : ((program tc).initialID).state = some foldedStartState := rfl
  have hstep :
      (program tc).step foldedStartState
          (((program tc).initialID).tape ((program tc).initialID).head) =
        some (nextAfterOrigin, PostStmt.write (foldedOriginSymbol (inputSymbol 0))) := by
    exact program_step_start_blank tc
  rw [nextID_of_step_eq_some hstate hstep]
  simp [PostProgram.initialID, PostProgram.applyStmt, nextAfterOrigin_eq_initReturnState_zero]

theorem program_runEmpty_one (tc : Turing.ToPartrec.Code) :
    (program tc).runEmpty 1 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (initReturnState 0) } := by
  rw [show 1 = 0 + 1 by rfl, PostProgram.runEmpty_succ, PostProgram.runEmpty_zero]
  exact program_nextID_initial tc

end TM0FoldedCompiler

end LeanWang
