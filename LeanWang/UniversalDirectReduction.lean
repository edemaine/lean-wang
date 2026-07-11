/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0DirectInput
import LeanWang.UniversalTM0

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

def postProgram (code : Code) : PostProgram :=
  TM0DirectInput.program UniversalTM0.code (UniversalTM0.input code)

def inputWord (code : Code) : List Nat :=
  TM0DirectInput.inputWord (UniversalTM0.input code)

def machine (code : Code) : Machine :=
  (postProgram code).toTableProgram.toMachine

theorem input_supported (code : Code) :
    MachineInput.Supported (machine code) (inputWord code) := by
  exact TM0DirectInput.input_supported UniversalTM0.code
    (UniversalTM0.input_ne_nil code)

theorem machine_halts_iff (code : Code) :
    MachineInput.Halts (machine code) (inputWord code) ↔
      (Nat.Partrec.Code.eval code 0).Dom := by
  exact (TM0DirectInput.machine_halts_iff_tm0_eval_dom
    UniversalTM0.code (UniversalTM0.input_ne_nil code)).trans
      (UniversalTM0.eval_dom_iff code)

def fixedDomino (code : Code) : TileSet × WangTile :=
  (MachineInputTiles.tiles (machine code) (inputWord code),
    MachineInputTiles.seed (machine code) (inputWord code))

theorem fixedDomino_correct (code : Code) :
    TilesQuarterWithSeed (fixedDomino code).1 (fixedDomino code).2 ↔
      ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  exact (MachineInputTiles.tilesQuarterWithSeed_iff_not_halts
    (input_supported code)).trans (not_congr (machine_halts_iff code))

end UniversalDirectReduction
end LeanWang
