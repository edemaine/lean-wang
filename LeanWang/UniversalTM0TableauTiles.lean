/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauLocalCorrect

/-!
# Finite Wang history tiles for the direct TM0 tableau
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

local instance : DecidableEq Cell := Classical.decEq Cell

/-- A typed local block from two consecutive folded tableau rows. -/
structure HistoryTile where
  atOrigin : Bool
  prevLeft : Cell
  prevCenter : Cell
  prevRight : Cell
  nextLeft : Cell
  nextCenter : Cell
  nextRight : Cell

namespace HistoryTile

def Valid (tile : HistoryTile) : Prop :=
  tile.prevLeft.Mem ∧ tile.prevCenter.Mem ∧ tile.prevRight.Mem ∧
    tile.nextLeft.Mem ∧ tile.nextCenter.Mem ∧ tile.nextRight.Mem ∧
    (tile.atOrigin = true →
      tile.prevLeft = blankCell ∧ tile.nextLeft = blankCell) ∧
    localNextCell? tile.atOrigin tile.prevLeft tile.prevCenter tile.prevRight =
      some tile.nextCenter

instance (tile : HistoryTile) : Decidable tile.Valid := by
  unfold Valid
  infer_instance

def leftMachineCell (atOrigin : Bool) (cell : Cell) : MachineCell :=
  if atOrigin then .boundary else cell.toMachineCell

def toMachineHistoryTile (tile : HistoryTile) : MachineHistoryTile where
  prevLeft := leftMachineCell tile.atOrigin tile.prevLeft
  prevCenter := tile.prevCenter.toMachineCell
  prevRight := tile.prevRight.toMachineCell
  nextLeft := leftMachineCell tile.atOrigin tile.nextLeft
  nextCenter := tile.nextCenter.toMachineCell
  nextRight := tile.nextRight.toMachineCell

def toWangTile (tile : HistoryTile) (rowTag nextRowTag : Nat) : WangTile :=
  tile.toMachineHistoryTile.toTaggedWangTile rowTag nextRowTag

theorem hMatches_toWangTile_iff (left right : HistoryTile)
    (rowTag nextRowTag rightRowTag rightNextRowTag : Nat) :
    WangTile.HMatches (left.toWangTile rowTag nextRowTag)
        (right.toWangTile rightRowTag rightNextRowTag) ↔
      rowTag = rightRowTag ∧
        left.prevCenter.toMachineCell =
          leftMachineCell right.atOrigin right.prevLeft ∧
        left.prevRight.toMachineCell = right.prevCenter.toMachineCell ∧
        left.nextCenter.toMachineCell =
          leftMachineCell right.atOrigin right.nextLeft ∧
        left.nextRight.toMachineCell = right.nextCenter.toMachineCell := by
  exact MachineHistoryTile.hMatches_toTaggedWangTile_iff_cells
    rowTag nextRowTag rightRowTag rightNextRowTag
    left.toMachineHistoryTile right.toMachineHistoryTile

theorem vMatches_toWangTile_iff (lower upper : HistoryTile)
    (rowTag nextRowTag upperRowTag upperNextRowTag : Nat) :
    WangTile.VMatches (lower.toWangTile rowTag nextRowTag)
        (upper.toWangTile upperRowTag upperNextRowTag) ↔
      nextRowTag = upperRowTag ∧
        leftMachineCell lower.atOrigin lower.nextLeft =
          leftMachineCell upper.atOrigin upper.prevLeft ∧
        lower.nextCenter.toMachineCell = upper.prevCenter.toMachineCell ∧
        lower.nextRight.toMachineCell = upper.prevRight.toMachineCell := by
  exact MachineHistoryTile.vMatches_toTaggedWangTile_iff_cells
    rowTag nextRowTag upperRowTag upperNextRowTag
    lower.toMachineHistoryTile upper.toMachineHistoryTile

end HistoryTile

abbrev HistoryTuple :=
  Bool × Cell × Cell × Cell × Cell × Cell × Cell

def HistoryTile.ofTuple (tuple : HistoryTuple) : HistoryTile where
  atOrigin := tuple.1
  prevLeft := tuple.2.1
  prevCenter := tuple.2.2.1
  prevRight := tuple.2.2.2.1
  nextLeft := tuple.2.2.2.2.1
  nextCenter := tuple.2.2.2.2.2.1
  nextRight := tuple.2.2.2.2.2.2

def historyTuples : List HistoryTuple :=
  [false, true].product
    (cells.product (cells.product (cells.product
      (cells.product (cells.product cells)))))

def historyTileCandidates : List HistoryTile :=
  historyTuples.map HistoryTile.ofTuple

theorem mem_historyTileCandidates_iff (tile : HistoryTile) :
    tile ∈ historyTileCandidates ↔
      tile.prevLeft.Mem ∧ tile.prevCenter.Mem ∧ tile.prevRight.Mem ∧
        tile.nextLeft.Mem ∧ tile.nextCenter.Mem ∧ tile.nextRight.Mem := by
  rcases tile with ⟨atOrigin, prevLeft, prevCenter, prevRight,
    nextLeft, nextCenter, nextRight⟩
  simp [historyTileCandidates, historyTuples, HistoryTile.ofTuple,
    mem_cells_iff]

def historyTiles : List HistoryTile :=
  historyTileCandidates.filter fun tile => decide tile.Valid

theorem mem_historyTiles_iff (tile : HistoryTile) :
    tile ∈ historyTiles ↔ tile.Valid := by
  rw [historyTiles, List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hvalid
    exact ⟨(mem_historyTileCandidates_iff tile).2
      ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
        hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1⟩, hvalid⟩

def normalTiles : TileSet :=
  historyTiles.map fun tile => tile.toWangTile normalRowTag normalRowTag

theorem historyTile_mem_normalTiles {tile : HistoryTile} (hvalid : tile.Valid) :
    tile.toWangTile normalRowTag normalRowTag ∈ normalTiles := by
  exact List.mem_map.2 ⟨tile, (mem_historyTiles_iff tile).2 hvalid, rfl⟩

end UniversalTM0Tableau
end LeanWang
