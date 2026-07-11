/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputTiles

/-!
# Finite-data presentation of input-parameterized machine tiles
-/

namespace LeanWang
namespace MachineInputTilesData

open MachineInput MachineInputTiles

def inputAt (program : TableProgram) (input : List Nat) (position : Nat) : Nat :=
  input.getD position program.blank

def initialCell (program : TableProgram) (input : List Nat)
    (position : Nat) : MachineCell :=
  if position = 0 then .head program.start (inputAt program input position)
  else .plain (inputAt program input position)

def initialLeft (program : TableProgram) (input : List Nat)
    (position : Nat) : MachineCell :=
  if position = 0 then .boundary else initialCell program input (position - 1)

def action (program : TableProgram) (input : List Nat) : Nat × Nat × Move :=
  program.toTableMachine.step program.start (inputAt program input 0)

def nextSymbol (program : TableProgram) (input : List Nat)
    (position : Nat) : Nat :=
  if position = 0 then (action program input).1 else inputAt program input position

def nextHead (program : TableProgram) (input : List Nat) : Nat :=
  (action program input).2.2.apply 0

def nextCell (program : TableProgram) (input : List Nat)
    (position : Nat) : MachineCell :=
  if program.start = program.halt then initialCell program input position
  else if position = nextHead program input then
    .head (action program input).2.1 (nextSymbol program input position)
  else .plain (nextSymbol program input position)

def nextLeft (program : TableProgram) (input : List Nat)
    (position : Nat) : MachineCell :=
  if position = 0 then .boundary else nextCell program input (position - 1)

def historyTile (program : TableProgram) (input : List Nat)
    (position : Nat) : MachineHistoryTile where
  prevLeft := initialLeft program input position
  prevCenter := initialCell program input position
  prevRight := initialCell program input (position + 1)
  nextLeft := nextLeft program input position
  nextCenter := nextCell program input position
  nextRight := nextCell program input (position + 1)

theorem inputAt_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      inputAt p.1 p.2.1 p.2.2) := by
  unfold inputAt
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
    (TableProgram.blank_primrec.comp Primrec.fst)

theorem initialCell_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      initialCell p.1 p.2.1 p.2.2) := by
  unfold initialCell
  have hzero : PrimrecPred (fun p : TableProgram × List Nat × Nat => p.2.2 = 0) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
  have hsymbol := inputAt_primrec
  exact Primrec.ite hzero
    (MachineCell.head_primrec.comp
      (Primrec.pair (TableProgram.start_primrec.comp Primrec.fst) hsymbol))
    (MachineCell.plain_primrec.comp hsymbol)

theorem initialLeft_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      initialLeft p.1 p.2.1 p.2.2) := by
  unfold initialLeft
  have hzero : PrimrecPred (fun p : TableProgram × List Nat × Nat => p.2.2 = 0) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
  have hpred : Primrec (fun p : TableProgram × List Nat × Nat =>
      (p.1, p.2.1, p.2.2 - 1)) :=
    Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pred.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.ite hzero (Primrec.const MachineCell.boundary)
    (initialCell_primrec.comp hpred)

theorem action_primrec :
    Primrec (fun p : TableProgram × List Nat => action p.1 p.2) := by
  unfold action
  exact TableProgram.step_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (TableProgram.start_primrec.comp Primrec.fst)
        (inputAt_primrec.comp
          (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd (Primrec.const 0))))))

theorem nextSymbol_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      nextSymbol p.1 p.2.1 p.2.2) := by
  unfold nextSymbol
  have hzero : PrimrecPred (fun p : TableProgram × List Nat × Nat => p.2.2 = 0) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
  have haction : Primrec (fun p : TableProgram × List Nat × Nat =>
      action p.1 p.2.1) := action_primrec.comp
        (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  exact Primrec.ite hzero (Primrec.fst.comp haction) inputAt_primrec

private theorem moveApply_primrec :
    Primrec (fun p : Move × Nat => p.1.apply p.2) := by
  exact (Primrec.cond (Move.toBool_primrec.comp Primrec.fst)
    (Primrec.succ.comp Primrec.snd)
    (Primrec.pred.comp Primrec.snd)).of_eq fun p => by
      cases p.1 <;> rfl

theorem nextHead_primrec :
    Primrec (fun p : TableProgram × List Nat => nextHead p.1 p.2) := by
  unfold nextHead
  exact moveApply_primrec.comp
    (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp action_primrec))
      (Primrec.const 0))

theorem nextCell_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      nextCell p.1 p.2.1 p.2.2) := by
  unfold nextCell
  have hhalt : PrimrecPred (fun p : TableProgram × List Nat × Nat =>
      p.1.start = p.1.halt) :=
    Primrec.eq.comp (TableProgram.start_primrec.comp Primrec.fst)
      (TableProgram.halt_primrec.comp Primrec.fst)
  have hp : Primrec (fun p : TableProgram × List Nat × Nat =>
      (p.1, p.2.1)) := Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hhead : PrimrecPred (fun p : TableProgram × List Nat × Nat =>
      p.2.2 = nextHead p.1 p.2.1) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (nextHead_primrec.comp hp)
  have haction := action_primrec.comp hp
  have hheadCell := MachineCell.head_primrec.comp
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp haction))
      nextSymbol_primrec)
  exact Primrec.ite hhalt initialCell_primrec
    (Primrec.ite hhead hheadCell
      (MachineCell.plain_primrec.comp nextSymbol_primrec))

theorem nextLeft_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      nextLeft p.1 p.2.1 p.2.2) := by
  unfold nextLeft
  have hzero : PrimrecPred (fun p : TableProgram × List Nat × Nat => p.2.2 = 0) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
  have hpred : Primrec (fun p : TableProgram × List Nat × Nat =>
      (p.1, p.2.1, p.2.2 - 1)) :=
    Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pred.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.ite hzero (Primrec.const MachineCell.boundary)
    (nextCell_primrec.comp hpred)

theorem historyTile_primrec :
    Primrec (fun p : TableProgram × List Nat × Nat =>
      historyTile p.1 p.2.1 p.2.2) := by
  unfold historyTile
  have hsucc : Primrec (fun p : TableProgram × List Nat × Nat =>
      (p.1, p.2.1, p.2.2 + 1)) :=
    Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair initialLeft_primrec
      (Primrec.pair initialCell_primrec
        (Primrec.pair (initialCell_primrec.comp hsucc)
          (Primrec.pair nextLeft_primrec
            (Primrec.pair nextCell_primrec (nextCell_primrec.comp hsucc))))))

theorem initialCell_eq (program : TableProgram) (input : List Nat)
    (position : Nat) :
    initialCell program input position =
      (MachineInput.initialID program.toMachine input).cellAt position := by
  by_cases hposition : position = 0
  · subst position
    simp [initialCell, inputAt, MachineInput.initialID, MachineInput.tape,
      ID.cellAt]
  · simp [initialCell, inputAt, MachineInput.initialID, MachineInput.tape,
      ID.cellAt, hposition]

theorem initialLeft_eq (program : TableProgram) (input : List Nat)
    (position : Nat) :
    initialLeft program input position =
      (MachineInput.initialID program.toMachine input).cellAtLeft position := by
  cases position with
  | zero => simp [initialLeft]
  | succ position =>
      simp only [initialLeft, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        ID.cellAtLeft_succ]
      rw [show position + 1 - 1 = position by omega]
      rw [initialCell_eq]

theorem nextCell_eq (program : TableProgram) (input : List Nat)
    (position : Nat) :
    nextCell program input position =
      (program.toMachine.nextID
        (MachineInput.initialID program.toMachine input)).cellAt position := by
  rcases haction : program.toTableMachine.step program.start
      (inputAt program input 0) with ⟨write, state, move⟩
  simp only [inputAt] at haction
  have htmBlank : program.toTableMachine.blank = program.blank := rfl
  have htmStart : program.toTableMachine.start = program.start := rfl
  have htmHalt : program.toTableMachine.halt = program.halt := rfl
  by_cases hhalt : program.start = program.halt
  · rw [nextCell, if_pos hhalt]
    rw [Machine.nextID_of_halt program.toMachine _ (by
      simpa [MachineInput.initialID] using hhalt)]
    exact initialCell_eq program input position
  · cases move <;>
      simp [nextCell, nextHead, nextSymbol, action, inputAt,
        Machine.nextID, MachineInput.initialID, MachineInput.tape,
        TableProgram.toMachine, TableMachine.toMachine,
        -TableProgram.toTableMachine_step, -TableMachine.toMachine_step,
        ID.cellAt, Move.apply, htmBlank, htmStart, htmHalt, hhalt]

theorem nextLeft_eq (program : TableProgram) (input : List Nat)
    (position : Nat) :
    nextLeft program input position =
      (program.toMachine.nextID
        (MachineInput.initialID program.toMachine input)).cellAtLeft position := by
  cases position with
  | zero => simp [nextLeft]
  | succ position =>
      simp only [nextLeft, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        ID.cellAtLeft_succ]
      rw [show position + 1 - 1 = position by omega]
      rw [nextCell_eq]

theorem historyTile_eq (program : TableProgram) (input : List Nat)
    (position : Nat) :
    historyTile program input position =
      MachineInput.historyTile program.toMachine input 0 position := by
  unfold historyTile MachineInput.historyTile MachineInput.runCell
    MachineInput.runCellLeft
  simp only [MachineInput.run_zero, MachineInput.run_succ]
  rw [initialLeft_eq, initialCell_eq, initialCell_eq,
    nextLeft_eq, nextCell_eq, nextCell_eq]

def initialTiles (program : TableProgram) (input : List Nat) : TileSet :=
  ((List.range (input.length + 3)).map fun position =>
      toWangTile position (position + 1) initialRowTag normalRowTag
        (historyTile program input position)) ++
    [toWangTile (input.length + 3) (input.length + 3)
      initialRowTag normalRowTag
      (historyTile program input (input.length + 3))]

def normalTiles (program : TableProgram) : TileSet :=
  (tableProgramMachineHistoryTilesData program).map
    (toWangTile 0 0 normalRowTag normalRowTag)

def tiles (program : TableProgram) (input : List Nat) : TileSet :=
  initialTiles program input ++ normalTiles program

def seed (program : TableProgram) (input : List Nat) : WangTile :=
  toWangTile 0 1 initialRowTag normalRowTag (historyTile program input 0)

theorem initialTiles_primrec :
    Primrec (fun p : TableProgram × List Nat => initialTiles p.1 p.2) := by
  unfold initialTiles
  have hlength : Primrec (fun p : TableProgram × List Nat => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hbound := Primrec.nat_add.comp hlength (Primrec.const 3)
  have hrange := Primrec.list_range.comp hbound
  have hmap : Primrec₂ (fun p : TableProgram × List Nat => fun position =>
      toWangTile position (position + 1) initialRowTag normalRowTag
        (historyTile p.1 p.2 position)) := by
    apply Primrec₂.mk
    exact MachineInputTiles.toWangTile_primrec.comp
      (Primrec.pair Primrec.snd
        (Primrec.pair (Primrec.succ.comp Primrec.snd)
          (Primrec.pair (Primrec.const initialRowTag)
            (Primrec.pair (Primrec.const normalRowTag)
              (historyTile_primrec.comp
                (Primrec.pair (Primrec.fst.comp Primrec.fst)
                  (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))))))
  have hinitial := Primrec.list_map hrange hmap
  have htailHistory := historyTile_primrec.comp
    (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd hbound))
  have htail := MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair hbound
      (Primrec.pair hbound
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag) htailHistory))))
  exact Primrec.list_append.comp hinitial
    (Primrec.list_cons.comp htail (Primrec.const []))

theorem normalTiles_primrec : Primrec normalTiles := by
  unfold normalTiles
  refine Primrec.list_map tableProgramMachineHistoryTilesData_primrec ?_
  apply Primrec₂.mk
  exact MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const normalRowTag)
          (Primrec.pair (Primrec.const normalRowTag) Primrec.snd))))

theorem tiles_primrec :
    Primrec (fun p : TableProgram × List Nat => tiles p.1 p.2) := by
  unfold tiles
  exact Primrec.list_append.comp initialTiles_primrec
    (normalTiles_primrec.comp Primrec.fst)

theorem seed_primrec :
    Primrec (fun p : TableProgram × List Nat => seed p.1 p.2) := by
  unfold seed
  exact MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const 1)
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag)
            (historyTile_primrec.comp
              (Primrec.pair Primrec.fst
                (Primrec.pair Primrec.snd (Primrec.const 0))))))))

theorem tiles_computable :
    Computable (fun p : TableProgram × List Nat => tiles p.1 p.2) :=
  tiles_primrec.to_comp

theorem seed_computable :
    Computable (fun p : TableProgram × List Nat => seed p.1 p.2) :=
  seed_primrec.to_comp

theorem initialTiles_eq (program : TableProgram) (input : List Nat) :
    initialTiles program input =
      MachineInputTiles.initialTiles program.toMachine input := by
  simp [initialTiles, MachineInputTiles.initialTiles,
    MachineInputTiles.tailPosition, historyTile_eq]

theorem mem_normalTiles_iff (program : TableProgram) (tile : WangTile) :
    tile ∈ normalTiles program ↔
      tile ∈ MachineInputTiles.normalTiles program.toMachine := by
  simp [normalTiles, MachineInputTiles.normalTiles, List.mem_map,
    mem_tableProgramMachineHistoryTilesData_iff_machineHistoryTiles]

theorem mem_tiles_iff (program : TableProgram) (input : List Nat)
    (tile : WangTile) :
    tile ∈ tiles program input ↔
      tile ∈ MachineInputTiles.tiles program.toMachine input := by
  simp [tiles, MachineInputTiles.tiles, initialTiles_eq,
    mem_normalTiles_iff]

theorem seed_eq (program : TableProgram) (input : List Nat) :
    seed program input = MachineInputTiles.seed program.toMachine input := by
  simp [seed, MachineInputTiles.seed, MachineInputTiles.initialTile,
    MachineInputTiles.tailPosition, historyTile_eq]

end MachineInputTilesData
end LeanWang
