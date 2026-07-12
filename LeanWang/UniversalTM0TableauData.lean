/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauDecode

/-!
# Executable data for the direct TM0 tableau reduction

Only the first two folded cells can change during the first TM0 step.  They
are finite lookup tables; all later cells merely read the input list.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

private def plainData (symbol : Symbol) : MachineCell :=
  ({ left := default, right := symbol, head := none } : Cell).toMachineCell

private def initialZeroData (symbol : Symbol) : MachineCell :=
  (Cell.mk default symbol (some (.right, default))).toMachineCell

private def nextZeroData (symbol : Symbol) : MachineCell :=
  match tm0 default symbol with
  | none => initialZeroData symbol
  | some (q, .write written) =>
      (Cell.mk default written (some (.right, q))).toMachineCell
  | some (q, .move .left) =>
      (Cell.mk default symbol (some (.left, q))).toMachineCell
  | some (_, .move .right) => plainData symbol

private def nextOneData (first second : Symbol) : MachineCell :=
  match tm0 default first with
  | some (q, .move .right) =>
      (Cell.mk default second (some (.right, q))).toMachineCell
  | _ => plainData second

def initialMachineCellData (input : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then initialZeroData (input.getI 0)
  else plainData (input.getI position)

def nextMachineCellData (input : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then nextZeroData (input.getI 0)
  else if position = 1 then nextOneData (input.getI 0) (input.getI 1)
  else plainData (input.getI position)

def initialMachineLeftData (input : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then .boundary else initialMachineCellData input (position - 1)

def nextMachineLeftData (input : List Symbol) (position : Nat) : MachineCell :=
  if position = 0 then .boundary else nextMachineCellData input (position - 1)

def historyMachineTileData (input : List Symbol) (position : Nat) : MachineHistoryTile where
  prevLeft := initialMachineLeftData input position
  prevCenter := initialMachineCellData input position
  prevRight := initialMachineCellData input (position + 1)
  nextLeft := nextMachineLeftData input position
  nextCenter := nextMachineCellData input position
  nextRight := nextMachineCellData input (position + 1)

private theorem initial_head_symbol (input : List Symbol) :
    (Config.initial input).source.Tape.head = input.getI 0 := by
  simp [Config.initial, Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
    Turing.Tape.mk', List.getI_zero_eq_headI]

private theorem initial_cellAt_data (input : List Symbol) (position : Nat) :
    (Config.initial input).cellAt position =
      Cell.mk default (input.getI position)
        (if position = 0 then some (.right, default) else none) := by
  rw [Config.initial_cellAt]
  rfl

theorem initialMachineCellData_eq (input : List Symbol) (position : Nat) :
    initialMachineCellData input position =
      ((Config.initial input).cellAt position).toMachineCell := by
  rw [Config.initial_cellAt]
  change initialMachineCellData input position =
    (Cell.mk default (input.getI position)
      (if position = 0 then some (.right, default) else none)).toMachineCell
  by_cases hposition : position = 0
  · subst position
    simp [initialMachineCellData, initialZeroData, Cell.toMachineCell]
  · simp [initialMachineCellData, plainData, hposition, Cell.toMachineCell]

theorem nextMachineCellData_eq (input : List Symbol) (position : Nat) :
    nextMachineCellData input position =
      ((Config.initial input).next.cellAt position).toMachineCell := by
  unfold Config.next
  cases hstep : (Config.initial input).step with
  | none =>
      simp only [Option.getD_none]
      rw [← initialMachineCellData_eq]
      unfold Config.step at hstep
      rw [show (Config.initial input).source.q = default from rfl,
        initial_head_symbol] at hstep
      have hinstruction : tm0 default (input.getI 0) = none := by
        cases hm : tm0 default (input.getI 0) with
        | none => exact rfl
        | some result =>
            rcases result with ⟨q, stmt⟩
            cases stmt <;> simp [hm] at hstep
      by_cases hposition : position = 0
      · subst position
        simp [nextMachineCellData, initialMachineCellData, nextZeroData,
          initialZeroData, hinstruction]
      · by_cases hone : position = 1
        · subst position
          simp [nextMachineCellData, initialMachineCellData, nextOneData,
            plainData, hinstruction]
        · simp [nextMachineCellData, initialMachineCellData, plainData,
            hposition, hone]
  | some next =>
      simp only [Option.getD_some]
      unfold Config.step at hstep
      rw [show (Config.initial input).source.q = default from rfl,
        initial_head_symbol] at hstep
      cases hm : tm0 default (input.getI 0) with
      | none => simp [hm] at hstep
      | some result =>
          rcases result with ⟨q, stmt⟩
          cases stmt with
          | write written =>
              simp [hm] at hstep
              cases hstep
              rw [Config.cellAt_afterWrite]
              rw [initial_cellAt_data]
              by_cases hposition : position = 0
              · subst position
                simp [nextMachineCellData, nextZeroData, hm, Config.initial,
                  Cell.writeActive, Cell.withHead, Cell.toMachineCell]
              · rw [if_neg (by simp [Config.initial, hposition])]
                by_cases hone : position = 1
                · subst position
                  simp_all [nextMachineCellData, initialMachineCellData, nextOneData,
                    plainData, hm]
                · simp_all [nextMachineCellData, initialMachineCellData, plainData,
                    hposition, hone]
          | move dir =>
              simp [hm] at hstep
              cases hstep
              rw [Config.cellAt_afterMove]
              rw [initial_cellAt_data]
              cases dir <;> by_cases hzero : position = 0 <;>
                by_cases hone : position = 1 <;> subst_vars <;>
                simp_all [nextMachineCellData, nextZeroData, nextOneData, plainData,
                  hm, Config.initial, moveHead, nextSide, Side.isInward,
                  Side.isOutward, Side.opposite, Cell.withHead, Cell.toMachineCell,
                  initialMachineCellData_eq]

theorem historyMachineTileData_eq (input : List Symbol) (position : Nat) :
    historyMachineTileData input position =
      (runHistoryTile input 0 position).toMachineHistoryTile := by
  have hrunOne : Config.run input 1 = (Config.initial input).next := by
    rw [show 1 = 0 + 1 by omega, Config.run_succ, Config.run_zero]
  cases position <;>
    simp [historyMachineTileData, runHistoryTile,
      HistoryTile.toMachineHistoryTile, HistoryTile.leftMachineCell,
      initialMachineLeftData, nextMachineLeftData,
      initialMachineCellData_eq, nextMachineCellData_eq, hrunOne,
      Config.cellAtLeft]

private theorem plainData_primrec : Primrec plainData := Primrec.dom_finite plainData

private theorem initialZeroData_primrec : Primrec initialZeroData :=
  Primrec.dom_finite initialZeroData

private theorem nextZeroData_primrec : Primrec nextZeroData :=
  Primrec.dom_finite nextZeroData

private theorem nextOneData_primrec :
    Primrec (fun p : Symbol × Symbol => nextOneData p.1 p.2) :=
  Primrec.dom_finite _

theorem initialMachineCellData_primrec :
    Primrec (fun p : List Symbol × Nat =>
      initialMachineCellData p.1 p.2) := by
  unfold initialMachineCellData
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hget : Primrec (fun p : List Symbol × Nat => p.1.getI p.2) :=
    Primrec.list_getI.comp Primrec.fst Primrec.snd
  have hgetZero : Primrec (fun p : List Symbol × Nat => p.1.getI 0) :=
    Primrec.list_getI.comp Primrec.fst (Primrec.const 0)
  exact Primrec.ite hzero
    (initialZeroData_primrec.comp hgetZero) (plainData_primrec.comp hget)

theorem nextMachineCellData_primrec :
    Primrec (fun p : List Symbol × Nat => nextMachineCellData p.1 p.2) := by
  unfold nextMachineCellData
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hone : PrimrecPred (fun p : List Symbol × Nat => p.2 = 1) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hget : Primrec (fun p : List Symbol × Nat => p.1.getI p.2) :=
    Primrec.list_getI.comp Primrec.fst Primrec.snd
  have hgetZero : Primrec (fun p : List Symbol × Nat => p.1.getI 0) :=
    Primrec.list_getI.comp Primrec.fst (Primrec.const 0)
  have hgetOne : Primrec (fun p : List Symbol × Nat => p.1.getI 1) :=
    Primrec.list_getI.comp Primrec.fst (Primrec.const 1)
  exact Primrec.ite hzero (nextZeroData_primrec.comp hgetZero)
    (Primrec.ite hone
      (nextOneData_primrec.comp (Primrec.pair hgetZero hgetOne))
      (plainData_primrec.comp hget))

theorem initialMachineLeftData_primrec :
    Primrec (fun p : List Symbol × Nat =>
      initialMachineLeftData p.1 p.2) := by
  unfold initialMachineLeftData
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hpred : Primrec (fun p : List Symbol × Nat => (p.1, p.2 - 1)) :=
    Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd)
  exact Primrec.ite hzero (Primrec.const MachineCell.boundary)
    (initialMachineCellData_primrec.comp hpred)

theorem nextMachineLeftData_primrec :
    Primrec (fun p : List Symbol × Nat => nextMachineLeftData p.1 p.2) := by
  unfold nextMachineLeftData
  have hzero : PrimrecPred (fun p : List Symbol × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hpred : Primrec (fun p : List Symbol × Nat => (p.1, p.2 - 1)) :=
    Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd)
  exact Primrec.ite hzero (Primrec.const MachineCell.boundary)
    (nextMachineCellData_primrec.comp hpred)

theorem historyMachineTileData_primrec :
    Primrec (fun p : List Symbol × Nat => historyMachineTileData p.1 p.2) := by
  unfold historyMachineTileData
  have hsucc : Primrec (fun p : List Symbol × Nat => (p.1, p.2 + 1)) :=
    Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd)
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair initialMachineLeftData_primrec
      (Primrec.pair initialMachineCellData_primrec
        (Primrec.pair (initialMachineCellData_primrec.comp hsucc)
          (Primrec.pair nextMachineLeftData_primrec
            (Primrec.pair nextMachineCellData_primrec
              (nextMachineCellData_primrec.comp hsucc))))))

def initialTilesData (input : List Symbol) : TileSet :=
  ((List.range (input.length + 3)).map fun position =>
      MachineInputTiles.toWangTile position (position + 1)
        initialRowTag normalRowTag (historyMachineTileData input position)) ++
    [MachineInputTiles.toWangTile (input.length + 3) (input.length + 3)
      initialRowTag normalRowTag (historyMachineTileData input (input.length + 3))]

def tilesData (input : List Symbol) : TileSet := initialTilesData input ++ normalTiles

def seedData (input : List Symbol) : WangTile :=
  MachineInputTiles.toWangTile 0 1 initialRowTag normalRowTag
    (historyMachineTileData input 0)

theorem initialTilesData_eq (input : List Symbol) :
    initialTilesData input = initialTiles input := by
  simp [initialTilesData, initialTiles, tailPosition, historyMachineTileData_eq]

theorem tilesData_eq (input : List Symbol) : tilesData input = tiles input := by
  simp [tilesData, tiles, initialTilesData_eq]

theorem seedData_eq (input : List Symbol) : seedData input = seed input := by
  simp [seedData, seed, initialWangTile, tailPosition, historyMachineTileData_eq]

theorem initialTilesData_primrec : Primrec initialTilesData := by
  unfold initialTilesData
  have hlength : Primrec (fun input : List Symbol => input.length) :=
    Primrec.list_length
  have hbound := Primrec.nat_add.comp hlength (Primrec.const 3)
  have hrange := Primrec.list_range.comp hbound
  have hmap : Primrec₂ (fun input : List Symbol => fun position =>
      MachineInputTiles.toWangTile position (position + 1)
        initialRowTag normalRowTag (historyMachineTileData input position)) := by
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
    (Primrec.pair Primrec.id hbound)
  have htail := MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair hbound
      (Primrec.pair hbound
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag) htailHistory))))
  exact Primrec.list_append.comp hinitial
    (Primrec.list_cons.comp htail (Primrec.const []))

theorem tilesData_primrec : Primrec tilesData := by
  unfold tilesData
  exact Primrec.list_append.comp initialTilesData_primrec (Primrec.const normalTiles)

theorem seedData_primrec : Primrec seedData := by
  unfold seedData
  exact MachineInputTiles.toWangTile_primrec.comp
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const 1)
        (Primrec.pair (Primrec.const initialRowTag)
          (Primrec.pair (Primrec.const normalRowTag)
            (historyMachineTileData_primrec.comp
              (Primrec.pair Primrec.id (Primrec.const 0)))))))

theorem tiles_computable : Computable tiles :=
  tilesData_primrec.to_comp.of_eq tilesData_eq

theorem seed_computable : Computable seed :=
  seedData_primrec.to_comp.of_eq seedData_eq

def fixedDominoData (input : List Symbol) : TileSet × WangTile :=
  (tiles input, seed input)

theorem fixedDominoData_computable : Computable fixedDominoData := by
  exact tiles_computable.pair seed_computable

end UniversalTM0Tableau
end LeanWang
