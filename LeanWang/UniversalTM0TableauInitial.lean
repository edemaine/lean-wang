/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauHistory
import LeanWang.MachineInputTiles

/-!
# Finite forced initial rows for the direct TM0 tableau
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

private def inputAt (input : List Symbol) (position : Nat) : Symbol :=
  input.getI position

theorem symbolsAt_initial (input : List Symbol) (position : Nat) :
    symbolsAt (Config.initial input).source.Tape .right 0 position =
      (default, inputAt input position) := by
  cases position with
  | zero =>
      have hleft : sourceOffset .right 0 (leftAbs 0) = Int.negSucc 0 := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
      have hright : sourceOffset .right 0 (rightAbs 0) = 0 := by
        simp [sourceOffset, activeAbs, rightAbs]
      rw [symbolsAt, hleft, hright]
      have hget : input.headI = input.getI 0 :=
        (List.getI_zero_eq_headI (l := input)).symm
      simp [Config.initial, Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.nth, inputAt, hget]
  | succ position =>
      have hleft : sourceOffset .right 0 (leftAbs (position + 1)) =
          Int.negSucc (position + 1) := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
        omega
      have hright : sourceOffset .right 0 (rightAbs (position + 1)) =
          Int.ofNat (position + 1) := by
        simp [sourceOffset, activeAbs, rightAbs]
      rw [symbolsAt, hleft, hright]
      have hget : input.tail.getI position = input.getI (position + 1) := by
        cases input <;> rfl
      simp [Config.initial, Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.nth, inputAt, hget]

theorem Config.initial_cellAt (input : List Symbol) (position : Nat) :
    (Config.initial input).cellAt position =
      { left := default
        right := inputAt input position
        head := if position = 0 then some (.right, default) else none } := by
  change
    Cell.mk (symbolsAt (Config.initial input).source.Tape .right 0 position).1
      (symbolsAt (Config.initial input).source.Tape .right 0 position).2
      (if position = 0 then some (.right, default) else none) = _
  rw [symbolsAt_initial]

theorem Config.initial_cellAt_eq_blank {input : List Symbol} {position : Nat}
    (hlength : input.length ≤ position) (hpositive : position ≠ 0) :
    (Config.initial input).cellAt position = blankCell := by
  rw [Config.initial_cellAt]
  have hdefault : inputAt input position = default :=
    List.getI_eq_default (l := input) hlength
  simp [hpositive, hdefault, blankCell]

theorem Config.initial_next_cellAt_eq_blank {input : List Symbol} {position : Nat}
    (hlength : input.length ≤ position) (htwo : 2 ≤ position) :
    (Config.initial input).next.cellAt position = blankCell := by
  unfold Config.next
  cases hstep : (Config.initial input).step with
  | none =>
      simp only [hstep, Option.getD_none]
      exact Config.initial_cellAt_eq_blank hlength (by omega)
  | some next =>
      simp only [hstep, Option.getD_some]
      unfold Config.step at hstep
      cases hm : tm0 (Config.initial input).source.q
          (Config.initial input).source.Tape.head with
      | none => simp [hm] at hstep
      | some result =>
          rcases result with ⟨q', stmt⟩
          cases stmt with
          | write symbol =>
              simp [hm] at hstep
              cases hstep
              rw [Config.cellAt_afterWrite]
              rw [if_neg (by simp [Config.initial]; omega)]
              exact Config.initial_cellAt_eq_blank hlength (by omega)
          | move dir =>
              simp [hm] at hstep
              cases hstep
              rw [Config.cellAt_afterMove]
              have hhead : moveHead .right true 0 dir ≤ 1 := by
                cases dir <;> simp [moveHead, Side.isInward, Side.isOutward]
              rw [if_neg (by simpa [Config.initial] using
                (show position ≠ moveHead .right true 0 dir by omega))]
              rw [Config.initial_cellAt_eq_blank hlength (by omega)]
              rfl

theorem Config.initial_cellAtLeft_eq_blank {input : List Symbol} {position : Nat}
    (hlength : input.length + 1 ≤ position) (htwo : 2 ≤ position) :
    (Config.initial input).cellAtLeft position = blankCell := by
  cases position with
  | zero => omega
  | succ position =>
      change (Config.initial input).cellAt position = blankCell
      exact Config.initial_cellAt_eq_blank (by omega) (by omega)

theorem Config.initial_next_cellAtLeft_eq_blank
    {input : List Symbol} {position : Nat}
    (hlength : input.length + 1 ≤ position) (hthree : 3 ≤ position) :
    (Config.initial input).next.cellAtLeft position = blankCell := by
  cases position with
  | zero => omega
  | succ position =>
      change (Config.initial input).next.cellAt position = blankCell
      exact Config.initial_next_cellAt_eq_blank (by omega) (by omega)

def tailPosition (input : List Symbol) : Nat := input.length + 3

def blankHistoryTile : HistoryTile where
  atOrigin := false
  prevLeft := blankCell
  prevCenter := blankCell
  prevRight := blankCell
  nextLeft := blankCell
  nextCenter := blankCell
  nextRight := blankCell

theorem runHistoryTile_zero_eq_blank_of_tailPosition_le
    (input : List Symbol) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    runHistoryTile input 0 position = blankHistoryTile := by
  have htail : input.length + 3 ≤ position := by
    simpa [tailPosition] using hposition
  have hlength : input.length ≤ position - 1 := by
    omega
  have hpositive : position ≠ 0 := by
    omega
  unfold runHistoryTile blankHistoryTile
  simp only [Config.run_zero, Config.run_succ]
  rw [Config.initial_cellAtLeft_eq_blank (by omega) (by omega)]
  rw [Config.initial_cellAt_eq_blank (by omega) hpositive]
  rw [Config.initial_cellAt_eq_blank (by omega) (by omega)]
  rw [Config.initial_next_cellAtLeft_eq_blank
    (by omega) (by omega)]
  rw [Config.initial_next_cellAt_eq_blank
    (by omega) (by omega)]
  rw [Config.initial_next_cellAt_eq_blank
    (by omega) (by omega)]
  simp [hpositive]

theorem runHistoryTile_zero_eq_tail_of_tailPosition_le
    (input : List Symbol) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    runHistoryTile input 0 position =
      runHistoryTile input 0 (tailPosition input) := by
  rw [runHistoryTile_zero_eq_blank_of_tailPosition_le input hposition]
  rw [runHistoryTile_zero_eq_blank_of_tailPosition_le input (le_refl _)]

def initialWangTile (input : List Symbol) (position : Nat) : WangTile :=
  let tail := tailPosition input
  if position < tail then
    MachineInputTiles.toWangTile position (position + 1)
      initialRowTag normalRowTag
      (runHistoryTile input 0 position).toMachineHistoryTile
  else
    MachineInputTiles.toWangTile tail tail initialRowTag normalRowTag
      (runHistoryTile input 0 tail).toMachineHistoryTile

def initialTiles (input : List Symbol) : TileSet :=
  ((List.range (tailPosition input)).map fun position =>
      MachineInputTiles.toWangTile position (position + 1)
        initialRowTag normalRowTag
        (runHistoryTile input 0 position).toMachineHistoryTile) ++
    [MachineInputTiles.toWangTile (tailPosition input) (tailPosition input)
      initialRowTag normalRowTag
      (runHistoryTile input 0 (tailPosition input)).toMachineHistoryTile]

def tiles (input : List Symbol) : TileSet := initialTiles input ++ normalTiles

def seed (input : List Symbol) : WangTile := initialWangTile input 0

theorem initialWangTile_mem (input : List Symbol) (position : Nat) :
    initialWangTile input position ∈ initialTiles input := by
  rw [initialWangTile]
  split
  next hposition =>
    apply List.mem_append_left
    exact List.mem_map.2 ⟨position, by simp [hposition], rfl⟩
  next _ =>
    apply List.mem_append_right
    simp

theorem initialWangTile_history (input : List Symbol) (position : Nat) :
    initialWangTile input position =
      if position < tailPosition input then
        MachineInputTiles.toWangTile position (position + 1)
          initialRowTag normalRowTag
          (runHistoryTile input 0 position).toMachineHistoryTile
      else
        MachineInputTiles.toWangTile (tailPosition input) (tailPosition input)
          initialRowTag normalRowTag
          (runHistoryTile input 0 position).toMachineHistoryTile := by
  rw [initialWangTile]
  split
  · rfl
  · congr 1
    exact congrArg HistoryTile.toMachineHistoryTile
      (runHistoryTile_zero_eq_tail_of_tailPosition_le input (by omega)).symm

theorem positioned_hMatches_of_overlap
    (left right : HistoryTile) (west east west' east' : Nat)
    (htag : east = west')
    (hoverlap :
      left.prevCenter.toMachineCell =
          HistoryTile.leftMachineCell right.atOrigin right.prevLeft ∧
        left.prevRight.toMachineCell = right.prevCenter.toMachineCell ∧
        left.nextCenter.toMachineCell =
          HistoryTile.leftMachineCell right.atOrigin right.nextLeft ∧
        left.nextRight.toMachineCell = right.nextCenter.toMachineCell) :
    WangTile.HMatches
      (MachineInputTiles.toWangTile west east initialRowTag normalRowTag
        left.toMachineHistoryTile)
      (MachineInputTiles.toWangTile west' east' initialRowTag normalRowTag
        right.toMachineHistoryTile) := by
  rw [MachineInputTiles.hMatches_toWangTile_iff]
  exact ⟨htag, rfl, hoverlap.1, hoverlap.2.1,
    hoverlap.2.2.1, hoverlap.2.2.2⟩

theorem initialWangTile_hMatches (input : List Symbol) (position : Nat) :
    WangTile.HMatches (initialWangTile input position)
      (initialWangTile input (position + 1)) := by
  rw [initialWangTile_history, initialWangTile_history]
  have hoverlap := runHistoryTile_hOverlap input 0 position
  by_cases hnext : position + 1 < tailPosition input
  · rw [if_pos (by omega), if_pos hnext]
    exact positioned_hMatches_of_overlap
      (runHistoryTile input 0 position)
      (runHistoryTile input 0 (position + 1))
      position (position + 1) (position + 1) (position + 2) rfl hoverlap
  · by_cases hbefore : position < tailPosition input
    · have heq : position + 1 = tailPosition input := by omega
      rw [if_pos hbefore, if_neg hnext]
      exact positioned_hMatches_of_overlap
        (runHistoryTile input 0 position)
        (runHistoryTile input 0 (position + 1))
        position (position + 1) (tailPosition input) (tailPosition input)
        heq hoverlap
    · rw [if_neg hbefore, if_neg hnext]
      exact positioned_hMatches_of_overlap
        (runHistoryTile input 0 position)
        (runHistoryTile input 0 (position + 1))
        (tailPosition input) (tailPosition input)
        (tailPosition input) (tailPosition input) rfl hoverlap

def runWangTile (input : List Symbol) : Nat → Nat → WangTile
  | 0, position => initialWangTile input position
  | time + 1, position => MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
      (runHistoryTile input (time + 1) position).toMachineHistoryTile

theorem runWangTile_mem {input : List Symbol}
    (hdom : ¬ (Turing.TM0.eval tm0 input).Dom) (time position : Nat) :
    runWangTile input time position ∈ tiles input := by
  cases time with
  | zero =>
      rw [runWangTile, tiles]
      exact List.mem_append_left _ (initialWangTile_mem input position)
  | succ time =>
      rw [runWangTile]
      apply List.mem_append_right
      exact historyTile_mem_normalTiles
        (runHistoryTile_valid hdom (time + 1) position)

theorem runWangTile_hMatches (input : List Symbol) (time position : Nat) :
    WangTile.HMatches (runWangTile input time position)
      (runWangTile input time (position + 1)) := by
  cases time with
  | zero => exact initialWangTile_hMatches input position
  | succ time =>
      exact runHistoryTile_positioned_hMatches input (time + 1) position

theorem positioned_vMatches_of_overlap
    (lower upper : HistoryTile) (west east : Nat)
    (hoverlap :
      HistoryTile.leftMachineCell lower.atOrigin lower.nextLeft =
          HistoryTile.leftMachineCell upper.atOrigin upper.prevLeft ∧
        lower.nextCenter.toMachineCell = upper.prevCenter.toMachineCell ∧
        lower.nextRight.toMachineCell = upper.prevRight.toMachineCell) :
    WangTile.VMatches
      (MachineInputTiles.toWangTile west east initialRowTag normalRowTag
        lower.toMachineHistoryTile)
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        upper.toMachineHistoryTile) := by
  rw [MachineInputTiles.vMatches_toWangTile_iff]
  exact ⟨rfl, hoverlap.1, hoverlap.2.1, hoverlap.2.2⟩

theorem normal_vMatches_of_overlap
    (lower upper : HistoryTile)
    (hoverlap :
      HistoryTile.leftMachineCell lower.atOrigin lower.nextLeft =
          HistoryTile.leftMachineCell upper.atOrigin upper.prevLeft ∧
        lower.nextCenter.toMachineCell = upper.prevCenter.toMachineCell ∧
        lower.nextRight.toMachineCell = upper.prevRight.toMachineCell) :
    WangTile.VMatches
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        lower.toMachineHistoryTile)
      (MachineInputTiles.toWangTile 0 0 normalRowTag normalRowTag
        upper.toMachineHistoryTile) := by
  rw [MachineInputTiles.vMatches_toWangTile_iff]
  exact ⟨rfl, hoverlap.1, hoverlap.2.1, hoverlap.2.2⟩

theorem runWangTile_vMatches (input : List Symbol) (time position : Nat) :
    WangTile.VMatches (runWangTile input time position)
      (runWangTile input (time + 1) position) := by
  cases time with
  | zero =>
      have hoverlap := runHistoryTile_vOverlap input 0 position
      rw [runWangTile, runWangTile]
      rw [initialWangTile_history]
      split
      · exact positioned_vMatches_of_overlap
          (runHistoryTile input 0 position) (runHistoryTile input 1 position)
          position (position + 1) hoverlap
      · exact positioned_vMatches_of_overlap
          (runHistoryTile input 0 position) (runHistoryTile input 1 position)
          (tailPosition input) (tailPosition input) hoverlap
  | succ time =>
      exact normal_vMatches_of_overlap
        (runHistoryTile input (time + 1) position)
        (runHistoryTile input (time + 2) position)
        (runHistoryTile_vOverlap input (time + 1) position)

theorem tilesQuarterWithSeed_of_not_dom {input : List Symbol}
    (hdom : ¬ (Turing.TM0.eval tm0 input).Dom) :
    TilesQuarterWithSeed (tiles input) (seed input) := by
  let plane : Nat × Nat → TileIn (tiles input) := fun point =>
    ⟨runWangTile input point.2 point.1,
      runWangTile_mem hdom point.2 point.1⟩
  refine ⟨plane, ?_, rfl⟩
  constructor
  · intro point
    exact runWangTile_hMatches input point.2 point.1
  · intro point
    exact runWangTile_vMatches input point.2 point.1

end UniversalTM0Tableau
end LeanWang
