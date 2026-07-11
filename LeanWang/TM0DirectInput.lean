/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTiles
import LeanWang.PostMachineInput
import LeanWang.TM0FoldedInput.Halting

/-!
# Starting the folded TM0 simulation directly from its finite input tape

The generated write/rewind prelude is bypassed.  Its completed folded tape is
placed directly on the bottom Wang row, and the same simulation table starts in
the folded simulation state.
-/

noncomputable section

namespace LeanWang
namespace TM0DirectInput

open TM0FoldedCompiler

def inputWord (input : List SourceSymbol) : List Nat :=
  (List.range input.length).map
    (writtenInputTape input (input.length - 1))

theorem inputWord_tape_eq_written
    {input : List SourceSymbol} (hinput : input ≠ []) (position : Nat) :
    MachineInput.tape foldedBlank (inputWord input) position =
      writtenInputTape input (input.length - 1) position := by
  by_cases hposition : position < input.length
  · simp [MachineInput.tape, inputWord, hposition]
  · have hlast : input.length - 1 < position := by
      have hpositive : 0 < input.length := List.length_pos_of_ne_nil hinput
      omega
    rw [writtenInputTape_eq_blank_of_lt input hlast]
    simp [MachineInput.tape, inputWord, hposition]

def program (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    PostProgram :=
  { positionProgramDataOnInput tc input with
    start := foldedSimStartStateCode }

@[simp] theorem program_symbols (tc : Turing.ToPartrec.Code)
    (input : List SourceSymbol) :
    (program tc input).symbols = foldedSymbolList :=
  rfl

@[simp] theorem program_blank (tc : Turing.ToPartrec.Code)
    (input : List SourceSymbol) :
    (program tc input).blank = foldedBlank :=
  rfl

@[simp] theorem program_start (tc : Turing.ToPartrec.Code)
    (input : List SourceSymbol) :
    (program tc input).start = foldedSimStartStateCode :=
  rfl

theorem program_nextID (tc : Turing.ToPartrec.Code)
    (input : List SourceSymbol) (id : PostID) :
    (program tc input).nextID id =
      (positionProgramDataOnInput tc input).nextID id :=
  rfl

def initialPostID (input : List SourceSymbol) : PostID :=
  simInitID input (input.length - 1)

theorem input_supported
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    MachineInput.Supported (program tc input).toTableProgram.toMachine
      (inputWord input) := by
  intro symbol hsymbol
  rw [inputWord, List.mem_map] at hsymbol
  rcases hsymbol with ⟨position, hposition, rfl⟩
  simp only [List.mem_range] at hposition
  change writtenInputTape input (input.length - 1) position ∈
    PostProgram.tableSupportedSymbols (program tc input)
  apply PostProgram.symbol_mem_tableSupportedSymbols
  rw [program_symbols]
  exact writtenInputTape_mem_of_le input (by
    have hpositive : 0 < input.length := List.length_pos_of_ne_nil hinput
    omega)

theorem initialID_eq_tableID
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    MachineInput.initialID
        (program tc input).toTableProgram.toMachine (inputWord input) =
      PostProgram.tableIDOfPostID (initialPostID input) := by
  apply ID.ext
  · funext position
    exact inputWord_tape_eq_written hinput position
  · rfl
  · rfl

theorem initialPostID_tapeSupported
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    PostProgram.TapeSupported (program tc input) (initialPostID input) := by
  intro position
  change writtenInputTape input (input.length - 1) position ∈
    PostProgram.tableSupportedSymbols (program tc input)
  by_cases hposition : position ≤ input.length - 1
  · apply PostProgram.symbol_mem_tableSupportedSymbols
    rw [program_symbols]
    exact writtenInputTape_mem_of_le input hposition
  · rw [writtenInputTape_eq_blank_of_lt input (by omega)]
    exact PostProgram.blank_mem_tableSupportedSymbols (program tc input)

theorem machine_halts_iff_tableHalts
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    MachineInput.Halts (program tc input).toTableProgram.toMachine
        (inputWord input) ↔
      PostMachineInput.tableHalts (program tc input) (initialPostID input) := by
  unfold MachineInput.Halts PostMachineInput.tableHalts
  apply exists_congr
  intro steps
  have hinitial := initialID_eq_tableID tc hinput
  simp only [MachineInput.run, PostMachineInput.tableRun]
  rw [hinitial]
  simp only [TableProgram.toMachine_halt]

theorem postHalts_program_iff
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    PostMachineInput.postHalts (program tc input) (initialPostID input) ↔
      TM0FoldedCompiler.PostHaltsFrom
        (positionProgramDataOnInput tc input) (initialPostID input) := by
  unfold PostMachineInput.postHalts TM0FoldedCompiler.PostHaltsFrom
  have hnext : (program tc input).nextID =
      (positionProgramDataOnInput tc input).nextID := by
    funext id
    exact program_nextID tc input id
  simp only [PostMachineInput.postRun, hnext]

theorem machine_halts_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    MachineInput.Halts (program tc input).toTableProgram.toMachine
        (inputWord input) ↔
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc) input).Dom := by
  rw [machine_halts_iff_tableHalts tc hinput]
  rw [PostMachineInput.tableHalts_iff_postHalts
    (initialPostID_tapeSupported tc input)]
  rw [postHalts_program_iff]
  exact ⟨tm0_eval_dom_of_inputProgram_haltsFrom_sim tc hinput,
    inputProgram_haltsFrom_sim_of_tm0_eval_dom tc hinput⟩

end TM0DirectInput
end LeanWang
