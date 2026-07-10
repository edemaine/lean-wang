/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.InitSteps

/-!
Operational reachability and tape invariants for the parameterized initializer.
-/

namespace LeanWang

namespace TM0FoldedCompiler

def PostReaches (P : PostProgram) (a b : PostID) : Prop :=
  ∃ n : Nat, Nat.iterate P.nextID n a = b

namespace PostReaches

theorem refl (P : PostProgram) (a : PostID) : PostReaches P a a :=
  ⟨0, rfl⟩

theorem single {P : PostProgram} {a b : PostID} (h : P.nextID a = b) :
    PostReaches P a b := by
  exact ⟨1, h⟩

theorem trans {P : PostProgram} {a b c : PostID}
    (hab : PostReaches P a b) (hbc : PostReaches P b c) :
    PostReaches P a c := by
  rcases hab with ⟨m, hm⟩
  rcases hbc with ⟨n, hn⟩
  refine ⟨n + m, ?_⟩
  rw [Function.iterate_add_apply, hm, hn]

end PostReaches

def writtenInputTape (input : List SourceSymbol) : Nat → Nat → Nat
  | 0 => Function.update (fun _ => foldedBlank) 0
      (foldedOriginSymbol (inputSymbolFor input 0))
  | k + 1 => Function.update (writtenInputTape input k) (k + 1)
      (foldedSymbolCode false default (inputSymbolFor input (k + 1)))

@[simp]
theorem writtenInputTape_zero_zero (input : List SourceSymbol) :
    writtenInputTape input 0 0 =
      foldedOriginSymbol (inputSymbolFor input 0) := by
  simp [writtenInputTape]

theorem writtenInputTape_at_succ (input : List SourceSymbol) (k : Nat) :
    writtenInputTape input (k + 1) (k + 1) =
      foldedSymbolCode false default (inputSymbolFor input (k + 1)) := by
  simp [writtenInputTape]

theorem writtenInputTape_eq_blank_of_lt
    (input : List SourceSymbol) {k j : Nat} (hkj : k < j) :
    writtenInputTape input k j = foldedBlank := by
  induction k with
  | zero =>
      rw [writtenInputTape, Function.update_of_ne (by omega : j ≠ 0)]
  | succ k ih =>
      rw [writtenInputTape]
      rw [Function.update_of_ne (by omega : j ≠ k + 1)]
      exact ih (by omega)

theorem writtenInputTape_current_mem
    (input : List SourceSymbol) (k : Nat) :
    writtenInputTape input k k ∈ foldedSymbolList := by
  cases k with
  | zero =>
      rw [writtenInputTape_zero_zero]
      exact foldedOriginSymbol_mem_symbols _
  | succ k =>
      rw [writtenInputTape_at_succ]
      exact foldedSymbolCode_mem_symbols _ _ _

theorem writtenInputTape_mem_of_le
    (input : List SourceSymbol) {written j : Nat} (hj : j ≤ written) :
    writtenInputTape input written j ∈ foldedSymbolList := by
  induction written with
  | zero =>
      have : j = 0 := by omega
      subst j
      exact writtenInputTape_current_mem input 0
  | succ written ih =>
      by_cases hlast : j = written + 1
      · subst j
        exact writtenInputTape_current_mem input (written + 1)
      · rw [writtenInputTape, Function.update_of_ne hlast]
        exact ih (by omega)

def moveInitID (input : List SourceSymbol) (i : Nat) : PostID where
  tape := writtenInputTape input i
  head := i
  state := some (initMoveRightState i)

def writeInitID (input : List SourceSymbol) (i : Nat) : PostID where
  tape := writtenInputTape input i
  head := i + 1
  state := some (initWriteRightState i)

def afterWriteInitID (input : List SourceSymbol) (i : Nat) : PostID where
  tape := writtenInputTape input (i + 1)
  head := i + 1
  state := some (nextAfterWriteRightFor input i)

def returnInitID (input : List SourceSymbol) (written head : Nat) : PostID where
  tape := writtenInputTape input written
  head := head
  state := some (initReturnState head)

def simInitID (input : List SourceSymbol) (written : Nat) : PostID where
  tape := writtenInputTape input written
  head := 0
  state := some foldedSimStartStateCode

theorem nextID_moveInitID
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {i : Nat}
    (hi : i < input.length - 1) :
    (positionProgramDataOnInput tc input).nextID (moveInitID input i) =
      writeInitID input i := by
  have hread : writtenInputTape input i i ∈ foldedSymbolList :=
    writtenInputTape_current_mem input i
  have hstep := positionProgramDataOnInput_step_move tc hi hread
  rw [PostProgram.nextID_of_running
    (P := positionProgramDataOnInput tc input) (c := moveInitID input i)
    (q := initMoveRightState i) rfl]
  change
    (match (positionProgramDataOnInput tc input).step
        (initMoveRightState i) (writtenInputTape input i i) with
      | none => ({ tape := writtenInputTape input i, head := i, state := none } : PostID)
      | some (q', stmt) =>
          let r := PostProgram.applyStmt stmt (writtenInputTape input i) i
          ({ tape := r.1, head := r.2, state := some q' } : PostID)) =
        writeInitID input i
  rw [hstep]
  rfl

theorem nextID_writeInitID
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol} {i : Nat}
    (hi : i < input.length - 1) :
    (positionProgramDataOnInput tc input).nextID (writeInitID input i) =
      afterWriteInitID input i := by
  have hblank : writtenInputTape input i (i + 1) = foldedBlank :=
    writtenInputTape_eq_blank_of_lt input (by omega)
  have hstep := positionProgramDataOnInput_step_write tc hi
  rw [PostProgram.nextID_of_running
    (P := positionProgramDataOnInput tc input) (c := writeInitID input i)
    (q := initWriteRightState i) rfl]
  change
    (match (positionProgramDataOnInput tc input).step
        (initWriteRightState i) (writtenInputTape input i (i + 1)) with
      | none =>
          ({ tape := writtenInputTape input i, head := i + 1, state := none } : PostID)
      | some (q', stmt) =>
          let r := PostProgram.applyStmt stmt (writtenInputTape input i) (i + 1)
          ({ tape := r.1, head := r.2, state := some q' } : PostID)) =
        afterWriteInitID input i
  rw [hblank, hstep]
  rfl

end TM0FoldedCompiler

end LeanWang
