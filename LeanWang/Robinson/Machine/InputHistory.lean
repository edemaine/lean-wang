/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Machine.Input
import LeanWang.Robinson.Machine.History

/-!
# Space-time histories from finite machine inputs

The finite local-history language is independent of the input. Only the bottom
row of the eventual Wang construction depends on the input word.
-/

namespace LeanWang
namespace MachineInput

theorem initialID_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) :
    (initialID M input).Mem M := by
  constructor
  · exact M.start_mem
  · intro position
    cases hsymbol : input[position]? with
    | none => simp [initialID, tape, hsymbol, M.blank_mem]
    | some symbol =>
        simp only [initialID, tape, hsymbol, Option.getD_some]
        exact supported symbol (List.mem_iff_getElem?.2 ⟨position, hsymbol⟩)

theorem run_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (steps : Nat) :
    (run M input steps).Mem M := by
  induction steps with
  | zero => simpa using initialID_mem supported
  | succ steps ih =>
      rw [run_succ]
      exact M.nextID_mem ih

/-- Cell in the space-time history of a finite-input computation. -/
def runCell (M : Machine) (input : List Nat) (time position : Nat) :
    MachineCell :=
  (run M input time).cellAt position

/-- Left neighbor, with the one-sided tape boundary at position zero. -/
def runCellLeft (M : Machine) (input : List Nat) (time position : Nat) :
    MachineCell :=
  (run M input time).cellAtLeft position

theorem runCell_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input)
    (time position : Nat) :
    (runCell M input time position).Mem M := by
  exact ID.cellAt_mem (run_mem supported time)
    (run_state_ne_halt_of_not_halts notHalts time) position

theorem runCellLeft_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input)
    (time position : Nat) :
    (runCellLeft M input time position).Mem M := by
  exact ID.cellAtLeft_mem (run_mem supported time)
    (run_state_ne_halt_of_not_halts notHalts time) position

/-- A local history block cut from two rows of a finite-input run. -/
def historyTile (M : Machine) (input : List Nat) (time position : Nat) :
    MachineHistoryTile where
  prevLeft := runCellLeft M input time position
  prevCenter := runCell M input time position
  prevRight := runCell M input time (position + 1)
  nextLeft := runCellLeft M input (time + 1) position
  nextCenter := runCell M input (time + 1) position
  nextRight := runCell M input (time + 1) (position + 1)

theorem historyTile_hMatches (M : Machine) (input : List Nat)
    (time position : Nat) :
    WangTile.HMatches (historyTile M input time position).toWangTile
      (historyTile M input time (position + 1)).toWangTile := by
  simp [WangTile.HMatches, MachineHistoryTile.toWangTile,
    historyTile, runCellLeft, runCell, run_succ]

theorem historyTile_vMatches (M : Machine) (input : List Nat)
    (time position : Nat) :
    WangTile.VMatches (historyTile M input time position).toWangTile
      (historyTile M input (time + 1) position).toWangTile := by
  simp [WangTile.VMatches, MachineHistoryTile.toWangTile, historyTile]

theorem historyTile_cells_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input)
    (time position : Nat) :
    (historyTile M input time position).prevLeft.Mem M ∧
      (historyTile M input time position).prevCenter.Mem M ∧
      (historyTile M input time position).prevRight.Mem M ∧
      (historyTile M input time position).nextLeft.Mem M ∧
      (historyTile M input time position).nextCenter.Mem M ∧
      (historyTile M input time position).nextRight.Mem M := by
  simp [historyTile, runCellLeft_mem supported notHalts,
    runCell_mem supported notHalts]

theorem historyTile_local_of_state_ne_halt {M : Machine} {input : List Nat}
    {time : Nat}
    (hstate : (run M input time).state ≠ M.halt)
    (hnext : (run M input (time + 1)).state ≠ M.halt)
    (position : Nat) :
    localNextCell? M (historyTile M input time position).prevLeft
        (historyTile M input time position).prevCenter
        (historyTile M input time position).prevRight =
      some (historyTile M input time position).nextCenter := by
  let c := run M input time
  have hstate' : c.state ≠ M.halt := by simpa [c] using hstate
  have hnextState : (M.step c.state (c.tape c.head)).2.1 ≠ M.halt := by
    rw [← Machine.nextID_state_of_ne_halt hstate']
    simpa [c, run_succ] using hnext
  simpa [historyTile, runCell, runCellLeft, c, run_succ] using
    Machine.localNextCell?_cellAt
      (M := M) (c := c) (pos := position) hstate' hnextState

theorem historyTile_local {M : Machine} {input : List Nat}
    (notHalts : ¬ Halts M input) (time position : Nat) :
    localNextCell? M (historyTile M input time position).prevLeft
        (historyTile M input time position).prevCenter
        (historyTile M input time position).prevRight =
      some (historyTile M input time position).nextCenter := by
  exact historyTile_local_of_state_ne_halt
    (run_state_ne_halt_of_not_halts notHalts time)
    (run_state_ne_halt_of_not_halts notHalts (time + 1)) position

theorem historyTile_boundaryOK (M : Machine) (input : List Nat)
    (time position : Nat) :
    (historyTile M input time position).prevLeft = MachineCell.boundary →
      (historyTile M input time position).nextLeft = MachineCell.boundary := by
  cases position with
  | zero => simp [historyTile, runCellLeft]
  | succ position =>
      intro hprev
      have hnot : (run M input time).cellAt position ≠ MachineCell.boundary :=
        ID.cellAt_ne_boundary (run M input time) position
      exact False.elim (hnot (by
        simpa [historyTile, runCellLeft] using hprev))

theorem historyTile_mem_machineHistoryTiles {M : Machine} {input : List Nat}
    (supported : Supported M input) (notHalts : ¬ Halts M input)
    (time position : Nat) :
    historyTile M input time position ∈ machineHistoryTiles M := by
  rcases historyTile_cells_mem supported notHalts time position with
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight⟩
  exact mem_machineHistoryTiles_of_supported hprevLeft hprevCenter hprevRight
    hnextLeft hnextCenter hnextRight
    (historyTile_local notHalts time position)
    (historyTile_boundaryOK M input time position)

end MachineInput
end LeanWang
