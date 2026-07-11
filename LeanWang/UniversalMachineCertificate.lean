/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTilesData

/-!
# Fixed universal machine certificates

The Wang reduction does not need a source-uniform machine compiler. It needs
one finite table program, a computable finite input word for each source code,
and the semantic fact that this fixed program halts exactly when that source
code halts on input zero.

This interface separates that short reduction argument from any particular
construction of the fixed universal machine.
-/

namespace LeanWang

open Nat.Partrec (Code)

/-- The exact fixed-machine theorem needed by the Wang reduction. -/
structure UniversalMachineCertificate where
  program : TableProgram
  input : Code → List Nat
  input_computable : Computable input
  input_supported : ∀ code,
    MachineInput.Supported program.toMachine (input code)
  halts_iff : ∀ code,
    MachineInput.Halts program.toMachine (input code) ↔
      (Nat.Partrec.Code.eval code 0).Dom

namespace UniversalMachineCertificate

def machine (U : UniversalMachineCertificate) : Machine :=
  U.program.toMachine

def instanceInput (U : UniversalMachineCertificate) (code : Code) :
    TableProgram × List Nat :=
  (U.program, U.input code)

theorem instanceInput_computable (U : UniversalMachineCertificate) :
    Computable U.instanceInput :=
  Computable.pair (Computable.const U.program) U.input_computable

def fixedTiles (U : UniversalMachineCertificate) (code : Code) : TileSet :=
  MachineInputTilesData.tiles U.program (U.input code)

theorem fixedTiles_computable (U : UniversalMachineCertificate) :
    Computable U.fixedTiles := by
  have h : Computable (fun code : Code =>
      MachineInputTilesData.tiles
        (U.instanceInput code).1 (U.instanceInput code).2) :=
    MachineInputTilesData.tiles_computable.comp U.instanceInput_computable
  exact h.of_eq fun code => by rfl

def fixedSeed (U : UniversalMachineCertificate) (code : Code) : WangTile :=
  MachineInputTilesData.seed U.program (U.input code)

theorem fixedSeed_computable (U : UniversalMachineCertificate) :
    Computable U.fixedSeed := by
  have h : Computable (fun code : Code =>
      MachineInputTilesData.seed
        (U.instanceInput code).1 (U.instanceInput code).2) :=
    MachineInputTilesData.seed_computable.comp U.instanceInput_computable
  exact h.of_eq fun code => by rfl

/-- Executable Wang data for the fixed machine on the source-dependent input. -/
def fixedDominoData (U : UniversalMachineCertificate) (code : Code) :
    TileSet × WangTile :=
  (U.fixedTiles code, U.fixedSeed code)

theorem fixedDominoData_computable (U : UniversalMachineCertificate) :
    Computable U.fixedDominoData :=
  Computable.pair U.fixedTiles_computable U.fixedSeed_computable

theorem fixedDominoData_correct (U : UniversalMachineCertificate) (code : Code) :
    TilesQuarterWithSeed (U.fixedDominoData code).1
        (U.fixedDominoData code).2 ↔
      ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  unfold fixedDominoData fixedTiles fixedSeed
  rw [MachineInputTilesData.seed_eq]
  rw [tilesQuarterWithSeed_congr
    (MachineInputTilesData.mem_tiles_iff U.program (U.input code))]
  exact (MachineInputTiles.tilesQuarterWithSeed_iff_not_halts
    (U.input_supported code)).trans (not_congr (U.halts_iff code))

end UniversalMachineCertificate

end LeanWang
