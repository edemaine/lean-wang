/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0Machine

/-!
# Executable input data for the fixed one-sided universal machine

Only the bottom history row depends on the source input.  Its cells are read
from the initial target configuration and its first successor; all normal
history tiles are constant because the target machine is fixed.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Machine

open UniversalTM0Semantic

private def inputCode (atOrigin : Bool) (symbol : Symbol) : Nat :=
  symbolCode ⟨atOrigin, default, symbol⟩

def tapeData (source : List Symbol) (position : Nat) : Nat :=
  if position = 0 then inputCode true (source.getI position)
  else inputCode false (source.getI position)

private def firstAction (symbol : Symbol) : Nat × Nat × Move :=
  machine.step machine.start (inputCode true symbol)

private def firstWrite (symbol : Symbol) : Nat :=
  (firstAction symbol).1

private def firstState (symbol : Symbol) : Nat :=
  (firstAction symbol).2.1

private def firstHead (symbol : Symbol) : Nat :=
  (firstAction symbol).2.2.apply 0

def nextTapeData (source : List Symbol) (position : Nat) : Nat :=
  if position = 0 then firstWrite (source.getI 0)
  else tapeData source position

def initialMachineCellData (source : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then .head machine.start (tapeData source position)
  else .plain (tapeData source position)

def nextMachineCellData (source : List Symbol) (position : Nat) : MachineCell :=
  let head := firstHead (source.getI 0)
  let state := firstState (source.getI 0)
  if position = head then .head state (nextTapeData source position)
  else .plain (nextTapeData source position)

def initialMachineLeftData (source : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then .boundary else initialMachineCellData source (position - 1)

def nextMachineLeftData (source : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then .boundary else nextMachineCellData source (position - 1)

def historyMachineTileData (source : List Symbol) (position : Nat) :
    MachineHistoryTile where
  prevLeft := initialMachineLeftData source position
  prevCenter := initialMachineCellData source position
  prevRight := initialMachineCellData source (position + 1)
  nextLeft := nextMachineLeftData source position
  nextCenter := nextMachineCellData source position
  nextRight := nextMachineCellData source (position + 1)

private theorem tapeData_eq (source : List Symbol) (position : Nat) :
    tapeData source position =
      MachineInput.tape machine.blank (input source) position := by
  change tapeData source position =
    (MachineInput.initialID machine (input source)).tape position
  rw [initialID_eq_toID]
  by_cases hposition : position = 0 <;>
    simp [toID, tapeData, inputCode, foldedSymbol_initial, sourceAt, hposition]

private theorem machine_start_ne_halt : machine.start ≠ machine.halt := by
  exact stateCode_run_ne_halt .right ⟨default, tm0_supports.1⟩

private theorem initial_state_ne_halt (source : List Symbol) :
    (MachineInput.initialID machine (input source)).state ≠ machine.halt := by
  simpa [MachineInput.initialID] using machine_start_ne_halt

private theorem initial_step_eq (source : List Symbol) :
    machine.step (MachineInput.initialID machine (input source)).state
        ((MachineInput.initialID machine (input source)).tape
          (MachineInput.initialID machine (input source)).head) =
      firstAction (source.getI 0) := by
  change machine.step machine.start
      (MachineInput.tape machine.blank (input source) 0) = _
  rw [← tapeData_eq]
  simp [tapeData, firstAction, inputCode]

private theorem run_one_tape_eq (source : List Symbol) (position : Nat) :
    (MachineInput.run machine (input source) 1).tape position =
      nextTapeData source position := by
  rw [show 1 = 0 + 1 by omega, MachineInput.run_succ, MachineInput.run_zero]
  by_cases hposition : position = 0
  · subst position
    change (machine.nextID
      (MachineInput.initialID machine (input source))).tape
        (MachineInput.initialID machine (input source)).head = _
    rw [Machine.nextID_tape_head_of_ne_halt (initial_state_ne_halt source)]
    rw [initial_step_eq]
    rfl
  · rw [Machine.nextID_tape_of_ne_head (by
        simpa [MachineInput.initialID] using hposition)]
    change MachineInput.tape machine.blank (input source) position = _
    rw [← tapeData_eq]
    simp [nextTapeData, hposition]

private theorem run_one_head_eq (source : List Symbol) :
    (MachineInput.run machine (input source) 1).head =
      firstHead (source.getI 0) := by
  rw [show 1 = 0 + 1 by omega, MachineInput.run_succ, MachineInput.run_zero]
  rw [Machine.nextID_head_of_ne_halt (initial_state_ne_halt source)]
  rw [initial_step_eq]
  rfl

private theorem run_one_state_eq (source : List Symbol) :
    (MachineInput.run machine (input source) 1).state =
      firstState (source.getI 0) := by
  rw [show 1 = 0 + 1 by omega, MachineInput.run_succ, MachineInput.run_zero]
  rw [Machine.nextID_state_of_ne_halt (initial_state_ne_halt source)]
  rw [initial_step_eq]
  rfl

theorem initialMachineCellData_eq (source : List Symbol) (position : Nat) :
    initialMachineCellData source position =
      (MachineInput.run machine (input source) 0).cellAt position := by
  rw [MachineInput.run_zero]
  by_cases hposition : position = 0 <;>
    simp [initialMachineCellData, MachineInput.initialID, ID.cellAt,
      hposition, tapeData_eq]

theorem nextMachineCellData_eq (source : List Symbol) (position : Nat) :
    nextMachineCellData source position =
      (MachineInput.run machine (input source) 1).cellAt position := by
  unfold nextMachineCellData ID.cellAt
  rw [run_one_head_eq, run_one_state_eq, run_one_tape_eq]

theorem historyMachineTileData_eq (source : List Symbol) (position : Nat) :
    historyMachineTileData source position =
      MachineInput.historyTile machine (input source) 0 position := by
  cases position <;>
    simp [historyMachineTileData, MachineInput.historyTile,
      MachineInput.runCell, MachineInput.runCellLeft,
      initialMachineLeftData, nextMachineLeftData,
      initialMachineCellData_eq, nextMachineCellData_eq, ID.cellAtLeft]

private theorem inputCode_primrec :
    Primrec (fun p : Bool × Symbol => inputCode p.1 p.2) :=
  Primrec.dom_finite _

theorem input_primrec : Primrec input := by
  have hfirst : Primrec (fun source : List Symbol =>
      inputCode true source.headI) :=
    inputCode_primrec.comp
      (Primrec.pair (Primrec.const true) Primrec.list_headI)
  have hmap : Primrec₂ (fun (_source : List Symbol) (symbol : Symbol) =>
      inputCode false symbol) := by
    apply Primrec₂.mk
    exact inputCode_primrec.comp
      (Primrec.pair (Primrec.const false) Primrec.snd)
  exact Primrec.list_cons.comp hfirst
    (Primrec.list_map Primrec.list_tail hmap)

theorem tapeData_primrec :
    Primrec (fun p : List Symbol × Nat => tapeData p.1 p.2) := by
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hget : Primrec (fun p : List Symbol × Nat => p.1.getI p.2) :=
    Primrec.list_getI.comp Primrec.fst Primrec.snd
  have htrue := inputCode_primrec.comp
    (Primrec.pair (Primrec.const true) hget)
  have hfalse := inputCode_primrec.comp
    (Primrec.pair (Primrec.const false) hget)
  exact Primrec.ite hzero htrue hfalse

private theorem firstWrite_primrec : Primrec firstWrite :=
  Primrec.dom_finite _

private theorem firstState_primrec : Primrec firstState :=
  Primrec.dom_finite _

private theorem firstHead_primrec : Primrec firstHead :=
  Primrec.dom_finite _

theorem nextTapeData_primrec :
    Primrec (fun p : List Symbol × Nat => nextTapeData p.1 p.2) := by
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hgetZero : Primrec (fun p : List Symbol × Nat => p.1.getI 0) :=
    Primrec.list_getI.comp Primrec.fst (Primrec.const 0)
  exact Primrec.ite hzero (firstWrite_primrec.comp hgetZero) tapeData_primrec

theorem initialMachineCellData_primrec :
    Primrec (fun p : List Symbol × Nat =>
      initialMachineCellData p.1 p.2) := by
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  exact Primrec.ite hzero
    (MachineCell.head_primrec.comp
      (Primrec.pair (Primrec.const machine.start) tapeData_primrec))
    (MachineCell.plain_primrec.comp tapeData_primrec)

theorem nextMachineCellData_primrec :
    Primrec (fun p : List Symbol × Nat => nextMachineCellData p.1 p.2) := by
  have hgetZero : Primrec (fun p : List Symbol × Nat => p.1.getI 0) :=
    Primrec.list_getI.comp Primrec.fst (Primrec.const 0)
  have hhead := firstHead_primrec.comp hgetZero
  have hstate := firstState_primrec.comp hgetZero
  have hatHead : PrimrecPred (fun p : List Symbol × Nat =>
      p.2 = firstHead (p.1.getI 0)) :=
    Primrec.eq.comp Primrec.snd hhead
  exact Primrec.ite hatHead
    (MachineCell.head_primrec.comp
      (Primrec.pair hstate nextTapeData_primrec))
    (MachineCell.plain_primrec.comp nextTapeData_primrec)

theorem initialMachineLeftData_primrec :
    Primrec (fun p : List Symbol × Nat =>
      initialMachineLeftData p.1 p.2) := by
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hpred : Primrec (fun p : List Symbol × Nat => (p.1, p.2 - 1)) :=
    Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd)
  exact Primrec.ite hzero (Primrec.const MachineCell.boundary)
    (initialMachineCellData_primrec.comp hpred)

theorem nextMachineLeftData_primrec :
    Primrec (fun p : List Symbol × Nat =>
      nextMachineLeftData p.1 p.2) := by
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hpred : Primrec (fun p : List Symbol × Nat => (p.1, p.2 - 1)) :=
    Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd)
  exact Primrec.ite hzero (Primrec.const MachineCell.boundary)
    (nextMachineCellData_primrec.comp hpred)

theorem historyMachineTileData_primrec :
    Primrec (fun p : List Symbol × Nat => historyMachineTileData p.1 p.2) := by
  have hsucc : Primrec (fun p : List Symbol × Nat => (p.1, p.2 + 1)) :=
    Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd)
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair initialMachineLeftData_primrec
      (Primrec.pair initialMachineCellData_primrec
        (Primrec.pair (initialMachineCellData_primrec.comp hsucc)
          (Primrec.pair nextMachineLeftData_primrec
            (Primrec.pair nextMachineCellData_primrec
              (nextMachineCellData_primrec.comp hsucc))))))

def tailData (source : List Symbol) : Nat :=
  MachineInputTiles.tailPosition (input source)

def initialTilesData (source : List Symbol) : TileSet :=
  ((List.range (tailData source)).map fun position =>
      MachineInputTiles.toWangTile position (position + 1)
        initialRowTag normalRowTag (historyMachineTileData source position)) ++
    [MachineInputTiles.toWangTile (tailData source) (tailData source)
      initialRowTag normalRowTag (historyMachineTileData source (tailData source))]

def tilesData (source : List Symbol) : TileSet :=
  initialTilesData source ++ MachineInputTiles.normalTiles machine

def seedData (source : List Symbol) : WangTile :=
  MachineInputTiles.toWangTile 0 1 initialRowTag normalRowTag
    (historyMachineTileData source 0)

theorem initialTilesData_eq (source : List Symbol) :
    initialTilesData source = MachineInputTiles.initialTiles machine (input source) := by
  simp [initialTilesData, tailData, MachineInputTiles.initialTiles,
    historyMachineTileData_eq]

theorem tilesData_eq (source : List Symbol) :
    tilesData source = MachineInputTiles.tiles machine (input source) := by
  simp [tilesData, MachineInputTiles.tiles, initialTilesData_eq]

theorem seedData_eq (source : List Symbol) :
    seedData source = MachineInputTiles.seed machine (input source) := by
  simp [seedData, MachineInputTiles.seed, MachineInputTiles.initialTile,
    MachineInputTiles.tailPosition, historyMachineTileData_eq]

theorem tailData_primrec : Primrec tailData := by
  unfold tailData MachineInputTiles.tailPosition
  exact Primrec.nat_add.comp (Primrec.list_length.comp input_primrec)
    (Primrec.const 3)

theorem initialTilesData_primrec : Primrec initialTilesData := by
  unfold initialTilesData
  have hrange := Primrec.list_range.comp tailData_primrec
  have hmap : Primrec₂ (fun source : List Symbol => fun position =>
      MachineInputTiles.toWangTile position (position + 1)
        initialRowTag normalRowTag (historyMachineTileData source position)) := by
    apply Primrec₂.mk
    exact MachineInputTiles.toWangTile_primrec.comp
      (Primrec.pair Primrec.snd
        (Primrec.pair (Primrec.succ.comp Primrec.snd)
          (Primrec.pair (Primrec.const initialRowTag)
            (Primrec.pair (Primrec.const normalRowTag)
              (historyMachineTileData_primrec.comp
                (Primrec.pair Primrec.fst Primrec.snd))))))
  have hinitial := Primrec.list_map hrange hmap
  have htailHistory := historyMachineTileData_primrec.comp
    (Primrec.pair Primrec.id tailData_primrec)
  have htail := MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair tailData_primrec
      (Primrec.pair tailData_primrec
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag) htailHistory))))
  exact Primrec.list_append.comp hinitial
    (Primrec.list_cons.comp htail (Primrec.const []))

theorem tilesData_primrec : Primrec tilesData := by
  unfold tilesData
  exact Primrec.list_append.comp initialTilesData_primrec
    (Primrec.const (MachineInputTiles.normalTiles machine))

theorem seedData_primrec : Primrec seedData := by
  unfold seedData
  exact MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const 1)
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag)
            (historyMachineTileData_primrec.comp
              (Primrec.pair Primrec.id (Primrec.const 0)))))))

theorem tiles_computable :
    Computable (fun source => MachineInputTiles.tiles machine (input source)) :=
  tilesData_primrec.to_comp.of_eq tilesData_eq

theorem seed_computable :
    Computable (fun source => MachineInputTiles.seed machine (input source)) :=
  seedData_primrec.to_comp.of_eq seedData_eq

def fixedDominoData (source : List Symbol) : TileSet × WangTile :=
  (MachineInputTiles.tiles machine (input source),
    MachineInputTiles.seed machine (input source))

theorem fixedDominoData_computable : Computable fixedDominoData := by
  exact tiles_computable.pair seed_computable

end UniversalTM0Machine
end LeanWang
