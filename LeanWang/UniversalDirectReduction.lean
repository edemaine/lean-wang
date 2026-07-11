/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTilesData
import LeanWang.TM0DirectInput
import LeanWang.UniversalTM0
import LeanWang.UniversalMachineCertificate

/-!
# Direct finite-input universal Wang reduction

This is the semantic endpoint of the simplified machine argument.  The source
code is encoded only in the bottom Wang row; no machine initializer writes or
rewinds that input.
-/

noncomputable section

namespace LeanWang
namespace UniversalDirectReduction

open Nat.Partrec (Code)

def postProgram : PostProgram :=
  TM0DirectInput.program UniversalTM0.code

def inputWord (code : Code) : List Nat :=
  TM0DirectInput.inputWord (UniversalTM0.input code)

theorem inputWord_primrec : Primrec inputWord :=
  TM0DirectInput.inputWord_primrec.comp UniversalTM0.input_primrec

theorem inputWord_computable : Computable inputWord :=
  inputWord_primrec.to_comp

def machine : Machine :=
  postProgram.toTableProgram.toMachine

theorem input_supported (code : Code) :
    MachineInput.Supported machine (inputWord code) := by
  exact TM0DirectInput.input_supported UniversalTM0.code (UniversalTM0.input code)

theorem machine_halts_iff (code : Code) :
    MachineInput.Halts machine (inputWord code) ↔
      (Nat.Partrec.Code.eval code 0).Dom := by
  exact (TM0DirectInput.machine_halts_iff_tm0_eval_dom
    UniversalTM0.code (UniversalTM0.input_ne_nil code)).trans
      (UniversalTM0.eval_dom_iff code)

/-- The legacy folded construction packaged behind the fixed-machine interface. -/
def certificate : UniversalMachineCertificate where
  program := postProgram.toTableProgram
  input := inputWord
  input_computable := inputWord_computable
  input_supported := input_supported
  halts_iff := machine_halts_iff

def fixedDomino (code : Code) : TileSet × WangTile :=
  (MachineInputTiles.tiles machine (inputWord code),
    MachineInputTiles.seed machine (inputWord code))

theorem fixedDomino_correct (code : Code) :
    TilesQuarterWithSeed (fixedDomino code).1 (fixedDomino code).2 ↔
      ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  exact (MachineInputTiles.tilesQuarterWithSeed_iff_not_halts
    (input_supported code)).trans (not_congr (machine_halts_iff code))

def instanceInput (code : Code) : TableProgram × List Nat :=
  (postProgram.toTableProgram, inputWord code)

theorem instanceInput_primrec : Primrec instanceInput := by
  exact Primrec.pair (Primrec.const postProgram.toTableProgram)
    inputWord_primrec

def fixedTiles (code : Code) : TileSet :=
  MachineInputTilesData.tiles (instanceInput code).1 (instanceInput code).2

theorem fixedTiles_primrec : Primrec fixedTiles := by
  exact MachineInputTilesData.tiles_primrec.comp instanceInput_primrec

def fixedSeed (code : Code) : WangTile :=
  MachineInputTilesData.seed (instanceInput code).1 (instanceInput code).2

theorem fixedSeed_primrec : Primrec fixedSeed := by
  exact MachineInputTilesData.seed_primrec.comp instanceInput_primrec

/-- Executable finite-list presentation of `fixedDomino`. -/
def fixedDominoData (code : Code) : TileSet × WangTile :=
  certificate.fixedDominoData code

theorem fixedDominoData_primrec : Primrec fixedDominoData := by
  exact (Primrec.pair fixedTiles_primrec fixedSeed_primrec).of_eq fun _ => rfl

theorem fixedDominoData_computable : Computable fixedDominoData :=
  fixedDominoData_primrec.to_comp

theorem fixedDominoData_correct (code : Code) :
    TilesQuarterWithSeed (fixedDominoData code).1
        (fixedDominoData code).2 ↔
      ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  exact certificate.fixedDominoData_correct code

end UniversalDirectReduction
end LeanWang
