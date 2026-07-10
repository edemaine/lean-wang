/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.InitRun
import LeanWang.TM0FoldedCompiler.FoldedTape

/-!
Identification of the completed input prelude with Mathlib's initial TM0 tape.
-/

namespace LeanWang

namespace TM0FoldedCompiler

theorem writtenInputTape_zero
    (input : List SourceSymbol) (written : Nat) :
    writtenInputTape input written 0 =
      foldedOriginSymbol (inputSymbolFor input 0) := by
  induction written with
  | zero => exact writtenInputTape_zero_zero input
  | succ written ih =>
      rw [writtenInputTape, Function.update_of_ne (by omega : 0 ≠ written + 1)]
      exact ih

theorem writtenInputTape_succ_of_le
    (input : List SourceSymbol) {written j : Nat} (hj : j + 1 ≤ written) :
    writtenInputTape input written (j + 1) =
      foldedSymbolCode false default (inputSymbolFor input (j + 1)) := by
  induction written with
  | zero => omega
  | succ written ih =>
      by_cases hlast : j + 1 = written + 1
      · have hjw : j = written := by omega
        subst j
        exact writtenInputTape_at_succ input written
      · rw [writtenInputTape, Function.update_of_ne hlast]
        exact ih (by omega)

theorem foldedCellOfTapeAt_init_right_zero_for
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) (i : Nat) :
    foldedCellOfTapeAt
        (Turing.TM0.init (Λ := SourceLabel tc) input).Tape
        FoldSide.right 0 i =
      if i = 0 then
        foldedOriginSymbol (inputSymbolFor input 0)
      else
        foldedSymbolCode false default (inputSymbolFor input i) := by
  cases i with
  | zero =>
      have hleft : sourceOffset FoldSide.right 0 (leftAbs 0) = Int.negSucc 0 := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
      have hright : sourceOffset FoldSide.right 0 (rightAbs 0) = 0 := by
        simp [sourceOffset, activeAbs, rightAbs]
      simp only [foldedCellOfTapeAt]
      rw [hleft, hright]
      have hget : input.headI = input.getI 0 :=
        (List.getI_zero_eq_headI (l := input)).symm
      simp [foldedOriginSymbol, inputSymbolFor, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        hget]
  | succ i =>
      have hleft : sourceOffset FoldSide.right 0 (leftAbs (i + 1)) =
          Int.negSucc (i + 1) := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
        omega
      have hright : sourceOffset FoldSide.right 0 (rightAbs (i + 1)) =
          Int.ofNat (i + 1) := by
        simp [sourceOffset, activeAbs, rightAbs]
      simp only [foldedCellOfTapeAt]
      rw [hleft, hright]
      have hget : input.tail.getI i = input.getI (i + 1) := by
        cases input <;> rfl
      simp [inputSymbolFor, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        hget]

theorem writtenInputTape_last_eq_foldedCell
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) (i : Nat) :
    writtenInputTape input (input.length - 1) i =
      foldedCellOfTapeAt
        (Turing.TM0.init (Λ := SourceLabel tc) input).Tape
        FoldSide.right 0 i := by
  rw [foldedCellOfTapeAt_init_right_zero_for]
  by_cases hi0 : i = 0
  · subst i
    simp [writtenInputTape_zero]
  · rw [if_neg hi0]
    cases i with
    | zero => contradiction
    | succ i =>
        by_cases hi : i + 1 < input.length
        · rw [writtenInputTape_succ_of_le input (by omega)]
        · have hlast : input.length - 1 < i + 1 := by
            have hpos : 0 < input.length := List.length_pos_of_ne_nil hinput
            omega
          rw [writtenInputTape_eq_blank_of_lt input hlast]
          have hdefault : input.getI (i + 1) = default :=
            List.getI_eq_default (l := input) (by omega)
          simp [inputSymbolFor, foldedBlank, hdefault]

theorem FoldedConfigRel_simInitID
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    FoldedConfigRel tc
      (Turing.TM0.init (Λ := SourceLabel tc) input)
      (simInitID input (input.length - 1)) := by
  refine ⟨FoldSide.right, ?_, ?_, ?_⟩
  · simpa [Turing.TM0.init] using default_mem_partrecStartedTM0LabelList tc
  · simp [simInitID, foldedSimStateCode, foldedSimStartStateCode,
      foldedSimStateOfCode, TM0FiniteCompiler.stateCode_default,
      TM0Route.partrecStartedTM0Start, Turing.TM0.init]
  · intro i
    exact writtenInputTape_last_eq_foldedCell tc hinput i

end TM0FoldedCompiler

end LeanWang
