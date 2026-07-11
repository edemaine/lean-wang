/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalMachineCertificate
import LeanWang.UniversalTM0Folded

/-!
# Fixed universal Wang reduction

The program is a constant finite table.  A source code changes only the
primitive-recursive finite word placed on its initial tape.
-/

noncomputable section

namespace LeanWang
namespace UniversalDirectReduction

open Nat.Partrec (Code)

def postProgram : PostProgram := UniversalTM0Folded.program

def sourceInput (code : Code) : List UniversalTM0Folded.SourceSymbol :=
  UniversalTM0Semantic.input code

theorem sourceInput_ne_nil (code : Code) : sourceInput code ≠ [] := by
  simp [sourceInput, UniversalTM0Semantic.input, Turing.TM2to1.trInit]

def inputWord (code : Code) : List Nat :=
  UniversalTM0Folded.inputWord (sourceInput code)

theorem inputWord_computable : Computable inputWord :=
  UniversalTM0Folded.inputWord_computable.comp UniversalTM0Semantic.input_computable

def machine : Machine := postProgram.toTableProgram.toMachine

theorem input_supported (code : Code) :
    MachineInput.Supported machine (inputWord code) := by
  intro symbol hsymbol
  apply PostProgram.symbol_mem_tableSupportedSymbols
  exact UniversalTM0Folded.inputWord_symbol_mem hsymbol

theorem machine_halts_iff (code : Code) :
    MachineInput.Halts machine (inputWord code) ↔
      (Nat.Partrec.Code.eval code 0).Dom := by
  exact (UniversalTM0Folded.machine_halts_iff_tm0_eval_dom
    (sourceInput_ne_nil code)).trans (UniversalTM0Semantic.tm0_eval_dom_iff code)

def certificate : UniversalMachineCertificate where
  program := postProgram.toTableProgram
  input := inputWord
  input_computable := inputWord_computable
  input_supported := input_supported
  halts_iff := machine_halts_iff

end UniversalDirectReduction
end LeanWang
