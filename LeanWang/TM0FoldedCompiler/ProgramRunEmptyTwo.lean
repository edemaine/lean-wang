/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.ProgramRunEmptyOne

/-!
Second empty-run state for the folded program.
-/

noncomputable section
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

theorem program_nextID_after_origin (tc : Turing.ToPartrec.Code) :
    (program tc).nextID
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
      (program tc).step (initReturnState 0) (id.tape id.head) =
        some (foldedSimStartState tc, PostStmt.write (id.tape id.head)) := by
    rw [hread]
    exact program_step_initReturn_zero tc hmem
  change (program tc).nextID id =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) }
  rw [nextID_of_step_eq_some hstate hstep]
  simp [id, PostProgram.applyStmt]

theorem program_runEmpty_two (tc : Turing.ToPartrec.Code) :
    (program tc).runEmpty 2 =
      { tape := Function.update (fun _ => foldedBlank) 0
          (foldedOriginSymbol (inputSymbol 0)),
        head := 0,
        state := some (foldedSimStartState tc) } := by
  rw [show 2 = 1 + 1 by rfl, PostProgram.runEmpty_succ, program_runEmpty_one]
  exact program_nextID_after_origin tc

end TM0FoldedCompiler

end LeanWang
