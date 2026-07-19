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
    (historyTile M input time position).prevCenter =
        (historyTile M input time (position + 1)).prevLeft ∧
      (historyTile M input time position).prevRight =
        (historyTile M input time (position + 1)).prevCenter ∧
      (historyTile M input time position).nextCenter =
        (historyTile M input time (position + 1)).nextLeft ∧
      (historyTile M input time position).nextRight =
        (historyTile M input time (position + 1)).nextCenter := by
  simp [historyTile, runCellLeft, runCell, run_succ]

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

namespace InitialHistoryData

variable {Input : Type}

/-- Tape contents after the first step, represented by executable input data. -/
def nextTape (tapeData : Input -> Nat -> Nat) (firstWrite : Input -> Nat)
    (source : Input) (position : Nat) : Nat :=
  if position = 0 then firstWrite source else tapeData source position

/-- Cell representation of the initial configuration. -/
def initialCell (M : Machine) (tapeData : Input -> Nat -> Nat)
    (source : Input) (position : Nat) : MachineCell :=
  if position = 0 then .head M.start (tapeData source position)
  else .plain (tapeData source position)

/-- Cell representation after the first machine step. -/
def nextCell (tapeData : Input -> Nat -> Nat) (firstWrite firstState firstHead : Input -> Nat)
    (source : Input) (position : Nat) : MachineCell :=
  let tape := nextTape tapeData firstWrite source position
  if position = firstHead source then .head (firstState source) tape else .plain tape

def leftCell (cells : Input -> Nat -> MachineCell)
    (source : Input) (position : Nat) : MachineCell :=
  if position = 0 then .boundary else cells source (position - 1)

/-- The bottom history tile obtained from executable initial and first-step data. -/
def historyTile (M : Machine) (tapeData : Input -> Nat -> Nat)
    (firstWrite firstState firstHead : Input -> Nat)
    (source : Input) (position : Nat) : MachineHistoryTile where
  prevLeft := leftCell (initialCell M tapeData) source position
  prevCenter := initialCell M tapeData source position
  prevRight := initialCell M tapeData source (position + 1)
  nextLeft := leftCell (nextCell tapeData firstWrite firstState firstHead) source position
  nextCenter := nextCell tapeData firstWrite firstState firstHead source position
  nextRight := nextCell tapeData firstWrite firstState firstHead source (position + 1)

theorem historyTile_eq (M : Machine) (encodeInput : Input -> List Nat)
    (source : Input) (position : Nat)
    (tapeData : Input -> Nat -> Nat) (firstWrite firstState firstHead : Input -> Nat)
    (startNeHalt : M.start ≠ M.halt)
    (tape_eq : forall position,
      tapeData source position = tape M.blank (encodeInput source) position)
    (write_eq : firstWrite source =
      (M.step M.start (tapeData source 0)).1)
    (state_eq : firstState source =
      (M.step M.start (tapeData source 0)).2.1)
    (head_eq : firstHead source =
      (M.step M.start (tapeData source 0)).2.2.apply 0) :
    historyTile M tapeData firstWrite firstState firstHead source position =
      MachineInput.historyTile M (encodeInput source) 0 position := by
  let initial := MachineInput.initialID M (encodeInput source)
  have initialNe : initial.state ≠ M.halt := by
    simpa [initial, MachineInput.initialID] using startNeHalt
  have initialCellEq (position : Nat) :
      initialCell M tapeData source position = initial.cellAt position := by
    by_cases atHead : position = 0 <;>
      simp [initialCell, initial, MachineInput.initialID, ID.cellAt, atHead, tape_eq]
  have runTapeEq (position : Nat) :
      (MachineInput.run M (encodeInput source) 1).tape position =
        nextTape tapeData firstWrite source position := by
    rw [show 1 = 0 + 1 by omega, MachineInput.run_succ, MachineInput.run_zero]
    by_cases atHead : position = 0
    · subst position
      change (M.nextID initial).tape initial.head = _
      rw [Machine.nextID_tape_head_of_ne_halt initialNe]
      simpa [initial, MachineInput.initialID, nextTape, tape_eq] using write_eq.symm
    · rw [Machine.nextID_tape_of_ne_head (by
          simpa [initial, MachineInput.initialID] using atHead)]
      simp [MachineInput.initialID, nextTape, atHead, tape_eq]
  have runHeadEq :
      (MachineInput.run M (encodeInput source) 1).head = firstHead source := by
    rw [show 1 = 0 + 1 by omega, MachineInput.run_succ, MachineInput.run_zero,
      Machine.nextID_head_of_ne_halt initialNe]
    simpa [initial, MachineInput.initialID, tape_eq] using head_eq.symm
  have runStateEq :
      (MachineInput.run M (encodeInput source) 1).state = firstState source := by
    rw [show 1 = 0 + 1 by omega, MachineInput.run_succ, MachineInput.run_zero,
      Machine.nextID_state_of_ne_halt initialNe]
    simpa [initial, MachineInput.initialID, tape_eq] using state_eq.symm
  have nextCellEq (position : Nat) :
      nextCell tapeData firstWrite firstState firstHead source position =
        (MachineInput.run M (encodeInput source) 1).cellAt position := by
    unfold nextCell ID.cellAt
    rw [runHeadEq, runStateEq, runTapeEq]
  cases position <;>
    simp [historyTile, MachineInput.historyTile, MachineInput.runCell,
      MachineInput.runCellLeft, leftCell, initial, initialCellEq, nextCellEq,
      ID.cellAtLeft]

theorem historyTile_primrec
    [Primcodable Input] (M : Machine) (tapeData : Input -> Nat -> Nat)
    (firstWrite firstState firstHead : Input -> Nat)
    (tapePrimrec : Primrec (fun p : Input × Nat => tapeData p.1 p.2))
    (writePrimrec : Primrec firstWrite) (statePrimrec : Primrec firstState)
    (headPrimrec : Primrec firstHead) :
    Primrec (fun p : Input × Nat =>
      historyTile M tapeData firstWrite firstState firstHead p.1 p.2) := by
  have zero : PrimrecPred (fun p : Input × Nat => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have nextTapePrimrec : Primrec (fun p : Input × Nat =>
      nextTape tapeData firstWrite p.1 p.2) :=
    Primrec.ite zero (writePrimrec.comp Primrec.fst) tapePrimrec
  have initialCellPrimrec : Primrec (fun p : Input × Nat =>
      initialCell M tapeData p.1 p.2) :=
    Primrec.ite zero
      (MachineCell.head_primrec.comp
        (Primrec.pair (Primrec.const M.start) tapePrimrec))
      (MachineCell.plain_primrec.comp tapePrimrec)
  have atNextHead : PrimrecPred (fun p : Input × Nat =>
      p.2 = firstHead p.1) :=
    Primrec.eq.comp Primrec.snd (headPrimrec.comp Primrec.fst)
  have nextCellPrimrec : Primrec (fun p : Input × Nat =>
      nextCell tapeData firstWrite firstState firstHead p.1 p.2) :=
    Primrec.ite atNextHead
      (MachineCell.head_primrec.comp
        (Primrec.pair (statePrimrec.comp Primrec.fst) nextTapePrimrec))
      (MachineCell.plain_primrec.comp nextTapePrimrec)
  have predecessor : Primrec (fun p : Input × Nat => (p.1, p.2 - 1)) :=
    Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd)
  have initialLeftPrimrec : Primrec (fun p : Input × Nat =>
      leftCell (initialCell M tapeData) p.1 p.2) :=
    Primrec.ite zero (Primrec.const MachineCell.boundary)
      (initialCellPrimrec.comp predecessor)
  have nextLeftPrimrec : Primrec (fun p : Input × Nat =>
      leftCell (nextCell tapeData firstWrite firstState firstHead) p.1 p.2) :=
    Primrec.ite zero (Primrec.const MachineCell.boundary)
      (nextCellPrimrec.comp predecessor)
  have successor : Primrec (fun p : Input × Nat => (p.1, p.2 + 1)) :=
    Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd)
  exact MachineHistoryTile.mk_primrec.comp
    (Primrec.pair initialLeftPrimrec
      (Primrec.pair initialCellPrimrec
        (Primrec.pair (initialCellPrimrec.comp successor)
          (Primrec.pair nextLeftPrimrec
            (Primrec.pair nextCellPrimrec
              (nextCellPrimrec.comp successor))))))

end InitialHistoryData

end MachineInput
end LeanWang
