/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTiles
import LeanWang.PostMachineInput
import LeanWang.TM0DirectInput
import LeanWang.TM0FixedDirectCorrect

/-!
# Direct fixed-TM0 simulation on a finite input

The computable input word is shared with the old folded construction, but the
finite control is the direct semantic table from `TM0FixedDirectProgram`.
-/

noncomputable section

namespace LeanWang
namespace TM0FixedDirectInput

open TM0Route TM0FoldedCompiler TM0FixedDirectProgram TM0FixedDirectCorrect

def program (tc : Turing.ToPartrec.Code) : PostProgram :=
  programWithTable tc (rows tc)

def inputWord : List SourceSymbol → List Nat :=
  TM0DirectInput.inputWord

theorem inputWord_primrec : Primrec inputWord :=
  TM0DirectInput.inputWord_primrec

def initialPostID (input : List SourceSymbol) : PostID :=
  TM0DirectInput.initialPostID input

theorem input_supported
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    MachineInput.Supported (program tc).toTableProgram.toMachine
      (inputWord input) := by
  intro symbol hsymbol
  cases input with
  | nil => simp [inputWord, TM0DirectInput.inputWord] at hsymbol
  | cons first rest =>
      simp only [inputWord, TM0DirectInput.inputWord, List.mem_cons,
        List.mem_map] at hsymbol
      rcases hsymbol with rfl | ⟨symbol, _hmem, rfl⟩
      · apply PostProgram.symbol_mem_tableSupportedSymbols
        change foldedOriginSymbol first ∈ foldedSymbolList
        exact foldedOriginSymbol_mem_symbols first
      · apply PostProgram.symbol_mem_tableSupportedSymbols
        change foldedSymbolCode false default symbol ∈ foldedSymbolList
        exact foldedSymbolCode_mem_symbols false default symbol

theorem initialID_eq_tableID
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    MachineInput.initialID
        (program tc).toTableProgram.toMachine (inputWord input) =
      PostProgram.tableIDOfPostID (initialPostID input) := by
  apply ID.ext
  · funext position
    rfl
  · rfl
  · rfl

theorem initialPostID_tapeSupported
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    PostProgram.TapeSupported (program tc) (initialPostID input) := by
  intro position
  change MachineInput.tape foldedBlank (inputWord input) position ∈
    PostProgram.tableSupportedSymbols (program tc)
  cases hget : (inputWord input)[position]? with
  | none =>
      rw [MachineInput.tape, hget]
      simp only [Option.getD_none]
      exact PostProgram.blank_mem_tableSupportedSymbols (program tc)
  | some symbol =>
      rw [MachineInput.tape, hget, Option.getD_some]
      apply PostProgram.symbol_mem_tableSupportedSymbols
      change symbol ∈ foldedSymbolList
      have hmem : symbol ∈ inputWord input :=
        List.mem_iff_getElem?.2 ⟨position, hget⟩
      exact TM0DirectInput.inputWord_symbol_mem hmem

theorem machine_halts_iff_tableHalts
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    MachineInput.Halts (program tc).toTableProgram.toMachine
        (inputWord input) ↔
      PostMachineInput.tableHalts (program tc) (initialPostID input) := by
  unfold MachineInput.Halts PostMachineInput.tableHalts
  apply exists_congr
  intro steps
  have hinitial := initialID_eq_tableID tc input
  simp only [MachineInput.run, PostMachineInput.tableRun]
  rw [hinitial]
  simp only [TableProgram.toMachine_halt]

theorem postHalts_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    PostMachineInput.postHalts (program tc) (initialPostID input) ↔
      (Turing.TM0.eval (partrecStartedTM0Machine tc) input).Dom := by
  let step := Turing.TM0.step (partrecStartedTM0Machine tc)
  let initCfg := Turing.TM0.init (Λ := SourceLabel tc) input
  have hinitial : FoldedConfigRel tc initCfg (initialPostID input) :=
    TM0DirectInput.foldedConfigRel_initial tc hinput
  constructor
  · rintro ⟨steps, hhalt⟩
    rcases tm0_reaches_halt_of_direct_halts hinitial steps hhalt with
      ⟨cfg, hreach, hterminal⟩
    rw [Turing.TM0.eval]
    apply (part_dom_map_iff (fun c => c.Tape.right₀)
      (StateTransition.eval step initCfg)).2
    exact Part.dom_iff_mem.2 ⟨cfg,
      StateTransition.mem_eval.2 ⟨hreach, hterminal⟩⟩
  · intro hdom
    have hdomState : (StateTransition.eval step initCfg).Dom := by
      rw [Turing.TM0.eval] at hdom
      exact (part_dom_map_iff (fun c => c.Tape.right₀)
        (StateTransition.eval step initCfg)).1 hdom
    let haltCfg := (StateTransition.eval step initCfg).get hdomState
    have hmem : haltCfg ∈ StateTransition.eval step initCfg :=
      Part.get_mem hdomState
    rcases StateTransition.mem_eval.1 hmem with ⟨hreach, hterminal⟩
    exact FoldedConfigRel_direct_reaches_halt hinitial hreach hterminal

theorem machine_halts_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    MachineInput.Halts (program tc).toTableProgram.toMachine
        (inputWord input) ↔
      (Turing.TM0.eval (partrecStartedTM0Machine tc) input).Dom := by
  rw [machine_halts_iff_tableHalts tc input]
  rw [PostMachineInput.tableHalts_iff_postHalts
    (initialPostID_tapeSupported tc input)]
  exact postHalts_iff_tm0_eval_dom tc hinput

end TM0FixedDirectInput
end LeanWang
