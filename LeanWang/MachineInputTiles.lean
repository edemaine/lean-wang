/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.MachineInputHistory

/-!
# Wang histories with a finite input on the bottom row

Horizontal position tags force the finite input history from the distinguished
corner.  Beyond a computable bound, the bottom history is constant and uses
one self-looping tail tile.  Normal rows use the same finite local-history
language as the empty-input construction.
-/

namespace LeanWang
namespace MachineInputTiles

open MachineInput

def horizontalColor (positionTag rowTag : Nat)
    (prevLeft prevRight nextLeft nextRight : MachineCell) : Nat :=
  Nat.pair positionTag
    (taggedOverlapCellColor rowTag prevLeft prevRight nextLeft nextRight)

def toWangTile (westTag eastTag rowTag nextRowTag : Nat)
    (tile : MachineHistoryTile) : WangTile where
  n := taggedTripleCellColor nextRowTag
    tile.nextLeft tile.nextCenter tile.nextRight
  s := taggedTripleCellColor rowTag
    tile.prevLeft tile.prevCenter tile.prevRight
  e := horizontalColor eastTag rowTag
    tile.prevCenter tile.prevRight tile.nextCenter tile.nextRight
  w := horizontalColor westTag rowTag
    tile.prevLeft tile.prevCenter tile.nextLeft tile.nextCenter

theorem hMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (left right : MachineHistoryTile) :
    WangTile.HMatches
        (toWangTile westTag eastTag rowTag nextRowTag left)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' right) ↔
      eastTag = westTag' ∧ rowTag = rowTag' ∧
        left.prevCenter = right.prevLeft ∧
        left.prevRight = right.prevCenter ∧
        left.nextCenter = right.nextLeft ∧
        left.nextRight = right.nextCenter := by
  simp [WangTile.HMatches, toWangTile, horizontalColor,
    taggedOverlapCellColor_eq_iff]

theorem vMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (lower upper : MachineHistoryTile) :
    WangTile.VMatches
        (toWangTile westTag eastTag rowTag nextRowTag lower)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' upper) ↔
      nextRowTag = rowTag' ∧
        lower.nextLeft = upper.prevLeft ∧
        lower.nextCenter = upper.prevCenter ∧
        lower.nextRight = upper.prevRight := by
  simp [WangTile.VMatches, toWangTile, taggedTripleCellColor_eq_iff]

/-- Past this position, the time-zero local history is a constant blank tail. -/
def tailPosition (input : List Nat) : Nat :=
  input.length + 3

theorem run_zero_cell_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length ≤ position) (hpositive : 0 < position) :
    (run M input 0).cellAt position = MachineCell.plain M.blank := by
  simp [run_zero, initialID, ID.cellAt, tape,
    List.getElem?_eq_none_iff.mpr hlength, Nat.ne_of_gt hpositive]

theorem run_zero_cellLeft_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length < position) (htwo : 2 ≤ position) :
    (run M input 0).cellAtLeft position = MachineCell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [ID.cellAtLeft_succ]
  exact run_zero_cell_eq_plain_blank M input (by omega) (by omega)

theorem run_one_cell_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length ≤ position) (htwo : 2 ≤ position) :
    (run M input 1).cellAt position = MachineCell.plain M.blank := by
  by_cases hhalt : M.start = M.halt
  · have hinitial : (initialID M input).state = M.halt := by
      simpa [initialID] using hhalt
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
      Machine.nextID_of_halt M _ hinitial]
    exact run_zero_cell_eq_plain_blank M input hlength (by omega)
  · have hstate : (initialID M input).state ≠ M.halt := by
      simpa [initialID] using hhalt
    have hhead : (M.nextID (initialID M input)).head ≤ 1 := by
      rw [Machine.nextID_head_of_ne_halt hstate]
      rcases hstep : M.step M.start (tape M.blank input 0) with
        ⟨write, state, move⟩
      change (M.step M.start (tape M.blank input 0)).2.2.apply 0 ≤ 1
      rw [hstep]
      cases move <;> simp [Move.apply]
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero]
    rw [ID.cellAt_of_ne (by omega : position ≠ (M.nextID (initialID M input)).head)]
    congr 1
    rw [Machine.nextID_tape_of_ne_head (by simp [initialID]; omega)]
    exact tape_eq_blank_of_length_le hlength

theorem run_one_cellLeft_eq_plain_blank
    (M : Machine) (input : List Nat) {position : Nat}
    (hlength : input.length + 1 < position) (hthree : 3 ≤ position) :
    (run M input 1).cellAtLeft position = MachineCell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [ID.cellAtLeft_succ]
  exact run_one_cell_eq_plain_blank M input (by omega) (by omega)

def blankHistoryTile (M : Machine) : MachineHistoryTile where
  prevLeft := .plain M.blank
  prevCenter := .plain M.blank
  prevRight := .plain M.blank
  nextLeft := .plain M.blank
  nextCenter := .plain M.blank
  nextRight := .plain M.blank

theorem historyTile_zero_eq_blank_of_tailPosition_le
    (M : Machine) (input : List Nat) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position = blankHistoryTile M := by
  have hp : input.length + 3 ≤ position := by
    simpa [tailPosition] using hposition
  unfold historyTile runCell runCellLeft blankHistoryTile
  simp only [Nat.zero_add]
  rw [run_zero_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]

theorem historyTile_zero_eq_tail_of_tailPosition_le
    (M : Machine) (input : List Nat) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position =
      historyTile M input 0 (tailPosition input) := by
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input hposition]
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]

def initialTile (M : Machine) (input : List Nat) (position : Nat) : WangTile :=
  let tail := tailPosition input
  if position < tail then
    toWangTile position (position + 1) initialRowTag normalRowTag
      (historyTile M input 0 position)
  else
    toWangTile tail tail initialRowTag normalRowTag
      (historyTile M input 0 tail)

def initialTiles (M : Machine) (input : List Nat) : TileSet :=
  ((List.range (tailPosition input)).map fun position =>
      toWangTile position (position + 1) initialRowTag normalRowTag
        (historyTile M input 0 position)) ++
    [toWangTile (tailPosition input) (tailPosition input)
      initialRowTag normalRowTag
      (historyTile M input 0 (tailPosition input))]

def normalTiles (M : Machine) : TileSet :=
  (machineHistoryTiles M).map
    (toWangTile 0 0 normalRowTag normalRowTag)

def tiles (M : Machine) (input : List Nat) : TileSet :=
  initialTiles M input ++ normalTiles M

def seed (M : Machine) (input : List Nat) : WangTile :=
  initialTile M input 0

theorem initialTile_mem (M : Machine) (input : List Nat) (position : Nat) :
    initialTile M input position ∈ initialTiles M input := by
  rw [initialTile]
  split_ifs with hposition
  · rw [initialTiles, List.mem_append]
    left
    rw [List.mem_map]
    exact ⟨position, by simp [hposition], rfl⟩
  · rw [initialTiles, List.mem_append]
    right
    simp

theorem initialTile_history (M : Machine) (input : List Nat) (position : Nat) :
    let tail := tailPosition input
    initialTile M input position =
      if position < tail then
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position)
      else
        toWangTile tail tail initialRowTag normalRowTag
          (historyTile M input 0 position) := by
  dsimp
  rw [initialTile]
  split_ifs with hposition
  · rfl
  · congr 1
    exact (historyTile_zero_eq_tail_of_tailPosition_le M input (by omega)).symm

set_option linter.flexible false in
theorem initialTile_hMatches (M : Machine) (input : List Nat) (position : Nat) :
    WangTile.HMatches (initialTile M input position)
      (initialTile M input (position + 1)) := by
  rw [initialTile_history, initialTile_history]
  by_cases hposition : position + 1 < tailPosition input
  · simp [hposition, show position < tailPosition input by omega,
      hMatches_toWangTile_iff]
    simpa only [MachineHistoryTile.hMatches_toWangTile_iff_cells] using
      historyTile_hMatches M input 0 position
  · have htail : tailPosition input ≤ position + 1 := by omega
    by_cases hbefore : position < tailPosition input
    · have heq : position + 1 = tailPosition input := by omega
      simp [hbefore, heq, hMatches_toWangTile_iff]
      rw [← heq]
      simpa only [MachineHistoryTile.hMatches_toWangTile_iff_cells] using
        historyTile_hMatches M input 0 position
    · simp [hbefore, hposition, hMatches_toWangTile_iff]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input (by omega :
        tailPosition input ≤ position)]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input htail]
      rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]
      simp [blankHistoryTile]

def runTile (M : Machine) (input : List Nat) (time position : Nat) : WangTile :=
  if time = 0 then initialTile M input position
  else toWangTile 0 0 normalRowTag normalRowTag
    (historyTile M input time position)

theorem runTile_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input)
    (time position : Nat) :
    runTile M input time position ∈ tiles M input := by
  cases time with
  | zero => simp [runTile, tiles, initialTile_mem]
  | succ time =>
      rw [runTile, if_neg (by omega)]
      simp only [tiles, List.mem_append]
      right
      rw [normalTiles, List.mem_map]
      exact ⟨historyTile M input (time + 1) position,
        historyTile_mem_machineHistoryTiles supported notHalts
          (time + 1) position, rfl⟩

theorem runTile_hMatches (M : Machine) (input : List Nat)
    (time position : Nat) :
    WangTile.HMatches (runTile M input time position)
      (runTile M input time (position + 1)) := by
  cases time with
  | zero => simpa [runTile] using initialTile_hMatches M input position
  | succ time =>
      simp [runTile, hMatches_toWangTile_iff]
      simpa only [MachineHistoryTile.hMatches_toWangTile_iff_cells] using
        historyTile_hMatches M input (time + 1) position

theorem runTile_vMatches (M : Machine) (input : List Nat)
    (time position : Nat) :
    WangTile.VMatches (runTile M input time position)
      (runTile M input (time + 1) position) := by
  cases time with
  | zero =>
      rw [runTile, if_pos rfl, runTile, if_neg (by omega)]
      rw [initialTile_history]
      split_ifs <;> simp [vMatches_toWangTile_iff, historyTile]
  | succ time =>
      simp [runTile, vMatches_toWangTile_iff, historyTile]

theorem tilesQuarterWithSeed_of_not_halts
    {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input) :
    TilesQuarterWithSeed (tiles M input) (seed M input) := by
  let plane : Nat × Nat → TileIn (tiles M input) := fun point =>
    ⟨runTile M input point.2 point.1,
      runTile_mem supported notHalts point.2 point.1⟩
  refine ⟨plane, ?_, ?_⟩
  · constructor
    · intro point
      exact runTile_hMatches M input point.2 point.1
    · intro point
      exact runTile_vMatches M input point.2 point.1
  · rfl

end MachineInputTiles
end LeanWang
