/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.InitReturnRows

/-!
Membership and state-support lemmas for origin/move/write initialization rows.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem initWriteOriginRow_mem_initRows (tc : Turing.ToPartrec.Code) :
    initWriteOriginRow ∈ initRows tc := by
  simp [initRows]

theorem initMoveRightRow_mem_initMoveRightRows {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    initMoveRightRow i read ∈ initMoveRightRows := by
  unfold initMoveRightRows
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  exact List.mem_map_of_mem hread

theorem initMoveRightRow_mem_initRows (tc : Turing.ToPartrec.Code) {i read : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1)
    (hread : read ∈ foldedSymbolList) :
    initMoveRightRow i read ∈ initRows tc := by
  unfold initRows
  simp [initMoveRightRow_mem_initMoveRightRows hi hread]

theorem nextAfterWriteRight_mem_states (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    nextAfterWriteRight i ∈ foldedStateList tc := by
  unfold nextAfterWriteRight
  by_cases hnext : i + 2 < TM0Route.partrecStartedTM0Input.length
  · rw [if_pos hnext]
    exact initMoveRightState_mem_states (tc := tc) (by omega)
  · rw [if_neg hnext]
    exact initReturnState_mem_states (tc := tc) (by omega)

theorem initWriteRightRow_mem_initWriteRightRows {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    initWriteRightRow i ∈ initWriteRightRows := by
  unfold initWriteRightRows
  exact List.mem_map_of_mem (List.mem_range.2 hi)

theorem initWriteRightRow_mem_initRows (tc : Turing.ToPartrec.Code) {i : Nat}
    (hi : i < TM0Route.partrecStartedTM0Input.length - 1) :
    initWriteRightRow i ∈ initRows tc := by
  unfold initRows
  simp [initWriteRightRow_mem_initWriteRightRows hi]

theorem initWriteRightRow_write_mem_symbols (i : Nat) :
    foldedSymbolCode false default (inputSymbol (i + 1)) ∈ foldedSymbolList := by
  exact foldedSymbolCode_mem_symbols false default (inputSymbol (i + 1))

end TM0FoldedCompiler

end LeanWang
