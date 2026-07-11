/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTiles
import LeanWang.PostMachineInput
import LeanWang.TM0FixedDirectCorrect

/-!
# Direct fixed-TM0 simulation on a finite input

The source word is folded directly onto the initial one-sided tape, and the
finite control is the direct semantic table from `TM0FixedDirectProgram`.
-/

noncomputable section

namespace LeanWang
namespace TM0FixedDirectInput

open TM0Route TM0FoldedCompiler TM0FixedDirectProgram TM0FixedDirectGeometry
  TM0FixedDirectCorrect

def program (tc : Turing.ToPartrec.Code) : PostProgram :=
  programWithTable tc (rows tc)

private def directInputSymbolFor (input : List SourceSymbol) (position : Nat) :
    SourceSymbol :=
  input.getI position

def inputWord : List SourceSymbol → List Nat
  | [] => []
  | first :: rest =>
      foldedOriginSymbol first ::
        rest.map (foldedSymbolCode false default)

theorem inputWord_primrec : Primrec inputWord := by
  have hrest : Primrec (fun rest : List SourceSymbol =>
      rest.map (foldedSymbolCode false default)) := by
    refine Primrec.list_map Primrec.id ?_
    apply Primrec₂.mk
    exact foldedSymbolCode_primrec.comp
      (Primrec.pair (Primrec.const false)
        (Primrec.pair (Primrec.const default) Primrec.snd))
  have hcons : Primrec₂ (fun (_ : List SourceSymbol) =>
      fun p : SourceSymbol × List SourceSymbol =>
        foldedOriginSymbol p.1 ::
          p.2.map (foldedSymbolCode false default)) := by
    apply Primrec₂.mk
    exact Primrec.list_cons.comp
      (foldedOriginSymbol_primrec.comp (Primrec.fst.comp Primrec.snd))
      (hrest.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_casesOn Primrec.id (Primrec.const []) hcons).of_eq
    fun input => by cases input <;> rfl

def initialPostID (input : List SourceSymbol) : PostID where
  tape := MachineInput.tape foldedBlank (inputWord input)
  head := 0
  state := some foldedSimStartStateCode

theorem foldedCellOfTapeAt_init_right_zero
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) (position : Nat) :
    foldedCellOfTapeAt
        (Turing.TM0.init (Λ := SourceLabel tc) input).Tape
        FoldSide.right 0 position =
      if position = 0 then
        foldedOriginSymbol (directInputSymbolFor input 0)
      else
        foldedSymbolCode false default (directInputSymbolFor input position) := by
  cases position with
  | zero =>
      have hleft : sourceOffset FoldSide.right 0 (leftAbs 0) = Int.negSucc 0 := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
      have hright : sourceOffset FoldSide.right 0 (rightAbs 0) = 0 := by
        simp [sourceOffset, activeAbs, rightAbs]
      simp only [foldedCellOfTapeAt]
      rw [hleft, hright]
      have hget : input.headI = input.getI 0 :=
        (List.getI_zero_eq_headI (l := input)).symm
      simp [foldedOriginSymbol, directInputSymbolFor, Turing.TM0.init,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth,
        hget]
  | succ position =>
      have hleft : sourceOffset FoldSide.right 0 (leftAbs (position + 1)) =
          Int.negSucc (position + 1) := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
        omega
      have hright : sourceOffset FoldSide.right 0 (rightAbs (position + 1)) =
          Int.ofNat (position + 1) := by
        simp [sourceOffset, activeAbs, rightAbs]
      simp only [foldedCellOfTapeAt]
      rw [hleft, hright]
      have hget : input.tail.getI position = input.getI (position + 1) := by
        cases input <;> rfl
      simp [directInputSymbolFor, Turing.TM0.init, Turing.Tape.mk₁,
        Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth, hget]

theorem inputWord_tape_eq_foldedCell
    (tc : Turing.ToPartrec.Code)
    {input : List SourceSymbol} (hinput : input ≠ []) (position : Nat) :
    MachineInput.tape foldedBlank (inputWord input) position =
      foldedCellOfTapeAt
        (Turing.TM0.init (Λ := SourceLabel tc) input).Tape
        FoldSide.right 0 position := by
  rw [foldedCellOfTapeAt_init_right_zero]
  cases input with
  | nil => contradiction
  | cons first rest =>
      cases position with
      | zero => simp [MachineInput.tape, inputWord, directInputSymbolFor]
      | succ position =>
          by_cases hposition : position < rest.length
          · simp [MachineInput.tape, inputWord, directInputSymbolFor, hposition,
              List.getI_eq_getElem rest hposition]
          · have hdefault : rest.getI position = default :=
              List.getI_eq_default (l := rest) (by omega)
            simp [MachineInput.tape, inputWord, directInputSymbolFor, hposition,
              foldedBlank, hdefault]

theorem inputWord_symbol_mem {input : List SourceSymbol} {symbol : Nat}
    (hmem : symbol ∈ inputWord input) : symbol ∈ foldedSymbolList := by
  cases input with
  | nil => simp [inputWord] at hmem
  | cons first rest =>
      simp only [inputWord, List.mem_cons, List.mem_map] at hmem
      rcases hmem with rfl | ⟨source, _hsource, rfl⟩
      · exact foldedOriginSymbol_mem_symbols first
      · exact foldedSymbolCode_mem_symbols false default source

theorem foldedConfigRel_initial
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    FoldedConfigRel tc
      (Turing.TM0.init (Λ := SourceLabel tc) input) (initialPostID input) := by
  refine ⟨FoldSide.right, ?_, ?_, ?_⟩
  · simpa [Turing.TM0.init] using default_mem_partrecStartedTM0LabelList tc
  · simp [initialPostID, foldedSimStateCode, foldedSimStartStateCode,
      foldedSimStateOfCode, TM0FiniteCompiler.stateCode_default,
      partrecStartedTM0Start, Turing.TM0.init]
  · intro position
    exact inputWord_tape_eq_foldedCell tc hinput position

theorem input_supported
    (tc : Turing.ToPartrec.Code) (input : List SourceSymbol) :
    MachineInput.Supported (program tc).toTableProgram.toMachine
      (inputWord input) := by
  intro symbol hsymbol
  cases input with
  | nil => simp [inputWord] at hsymbol
  | cons first rest =>
      simp only [inputWord, List.mem_cons, List.mem_map] at hsymbol
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
      exact inputWord_symbol_mem hmem

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
    foldedConfigRel_initial tc hinput
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
