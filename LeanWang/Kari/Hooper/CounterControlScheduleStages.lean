/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlScheduleSemantics

/-!
# Register-update schedule stages

This module isolates the representation-independent order and geometry of the
increment prefixes and positive-decrement suffixes used by both finite-frame
and open-core instruction semantics.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlScheduleSemantics

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlShiftSemantics

noncomputable section

/- The increment schedule visits boundaries 4, 3, 2, and 1 in order.
These equations isolate its fixed geometry from the execution proof. -/
theorem incrementSchedule_clock_start (registers : Registers) :
    layoutEnd registers =
      lastGapOffset (registers.increment .clock) 3 := by
  simp [lastGapOffset, CounterLayout.boundaryPos, layoutEnd,
    RegisterLayout.clockBoundary_eq, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]
  omega

theorem incrementSchedule_clock_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .temp) 2 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

theorem incrementSchedule_temp_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      lastGapOffset (registers.increment .right) 1 := by
  simp [lastGapOffset, boundaryOffset, CounterLayout.boundaryPos,
    RegisterLayout.values, Registers.increment, Registers.set, Registers.get]
  omega

theorem incrementSchedule_finish_temp (registers : Registers) :
    boundaryOffset (registers.increment .clock) ((3 : Fin 4).castSucc) =
      boundaryOffset registers 3 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

theorem incrementSchedule_finish_right (registers : Registers) :
    boundaryOffset (registers.increment .temp) ((2 : Fin 4).castSucc) =
      boundaryOffset registers 2 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

theorem incrementSchedule_finish_left (registers : Registers) :
    boundaryOffset (registers.increment .right) ((1 : Fin 4).castSucc) =
      boundaryOffset registers 1 := by
  simp [boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
    Registers.increment, Registers.set, Registers.get]

/-! ## Generic increment prefixes -/

/-- Consecutive stages in the fixed clock-to-left increment order. -/
inductive IncrementStageNext : Register → Register → Prop
  | clock : IncrementStageNext .clock .temp
  | temp : IncrementStageNext .temp .right
  | right : IncrementStageNext .right .left

/-- The internal boundary index used to install a non-clock stage. -/
def incrementStageIndex : Register → Fin 4
  | .clock => 3
  | .temp => 3
  | .right => 2
  | .left => 1

/-- The stages following the mandatory clock shift, through the selected
target register. -/
def incrementStages : Register → List Register
  | .clock => []
  | .temp => [.temp]
  | .right => [.temp, .right]
  | .left => [.temp, .right, .left]

/-- A tail follows the fixed increment order and ends at its target. -/
inductive IncrementStageChain : Register → Register →
    List Register → Prop
  | done (stage : Register) : IncrementStageChain stage stage []
  | cons {current next target : Register} {tail : List Register}
      (hnext : IncrementStageNext current next)
      (hrest : IncrementStageChain next target tail) :
      IncrementStageChain current target (next :: tail)

theorem incrementStages_chain (register : Register) :
    IncrementStageChain .clock register (incrementStages register) := by
  cases register with
  | clock => exact .done .clock
  | temp => exact .cons .clock (.done .temp)
  | right => exact .cons .clock (.cons .temp (.done .right))
  | left =>
      exact .cons .clock (.cons .temp (.cons .right (.done .left)))

theorem incrementStages_labels (register : Register) :
    4 :: (incrementStages register).map
        (fun stage => (incrementStageIndex stage).castSucc) =
      MarkerShift.incrementOrder register := by
  cases register <;> rfl

theorem incrementStage_positive (registers : Registers)
    {current next : Register} (hnext : IncrementStageNext current next) :
    0 < RegisterLayout.values (registers.increment current)
      (incrementStageIndex next) := by
  cases hnext <;>
    simp [incrementStageIndex, RegisterLayout.values, Registers.increment,
      Registers.set, Registers.get]

theorem incrementStage_move (registers : Registers)
    {current next : Register} (hnext : IncrementStageNext current next) :
    MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape (registers.increment current))
        (MarkerTape.boundaryPosition (registers.increment current)
          (incrementStageIndex next).castSucc)
        (incrementStageIndex next).castSucc =
      MarkerTape.canonicalTape (registers.increment next) := by
  cases hnext with
  | clock => exact MarkerSchedule.moveTempBoundary_after_clock registers
  | temp => exact MarkerSchedule.moveRightBoundary_after_temp registers
  | right => exact MarkerSchedule.moveLeftBoundary_after_right registers

theorem incrementStage_head (registers : Registers)
    {current next after : Register}
    (hnext : IncrementStageNext current next)
    (hafter : IncrementStageNext next after) :
    boundaryOffset (registers.increment current)
        (incrementStageIndex next).castSucc =
      lastGapOffset (registers.increment next) (incrementStageIndex after) := by
  cases hnext <;> cases hafter
  · exact incrementSchedule_clock_temp registers
  · exact incrementSchedule_temp_right registers

theorem incrementStage_finish (registers : Registers)
    {current next : Register} (hnext : IncrementStageNext current next) :
    boundaryOffset (registers.increment current)
        (incrementStageIndex next).castSucc =
      boundaryOffset registers
        (MarkerSchedule.decrementStartBoundary next) := by
  cases hnext with
  | clock => exact incrementSchedule_finish_temp registers
  | temp => exact incrementSchedule_finish_right registers
  | right => exact incrementSchedule_finish_left registers


/-! ## Generic positive-decrement stage chains -/

/-- Gap index shifted at one stage of a positive-decrement suffix. -/
def decrementStageIndex : Register → Fin 4
  | .left => 0
  | .right => 1
  | .temp => 2
  | .clock => 3

/-- Intermediate layout: the final tuple with the current suffix register
still one cell longer. -/
def decrementStageRegisters
    (final : Registers) (stage : Register) : Registers :=
  final.increment stage

/-- Consecutive registers in the left-to-right decrement suffix. -/
inductive DecrementStageNext : Register → Register → Prop
  | left : DecrementStageNext .left .right
  | right : DecrementStageNext .right .temp
  | temp : DecrementStageNext .temp .clock

/-- The suffix of register boundaries shifted by one named decrement. -/
def decrementStages : Register → List Register
  | .left => [.left, .right, .temp, .clock]
  | .right => [.right, .temp, .clock]
  | .temp => [.temp, .clock]
  | .clock => [.clock]

/-- A list follows the fixed left-to-right register order and ends at clock. -/
inductive DecrementStageChain : Register → List Register → Prop
  | clock : DecrementStageChain .clock [.clock]
  | cons {stage next : Register} {tail : List Register}
      (hnext : DecrementStageNext stage next)
      (hrest : DecrementStageChain next (next :: tail)) :
      DecrementStageChain stage (stage :: next :: tail)

theorem decrementStages_chain (register : Register) :
    DecrementStageChain register (decrementStages register) := by
  cases register with
  | clock => exact .clock
  | temp => exact .cons .temp .clock
  | right => exact .cons .right (.cons .temp .clock)
  | left => exact .cons .left (.cons .right (.cons .temp .clock))

theorem decrementStages_labels (register : Register) :
    (decrementStages register).map
        (fun stage => (decrementStageIndex stage).succ) =
      MarkerShift.decrementOrder register := by
  cases register <;>
    rfl

theorem decrementStage_layoutEnd
    (final : Registers) (stage : Register) :
    layoutEnd (decrementStageRegisters final stage) = layoutEnd final + 1 := by
  simp [decrementStageRegisters]

theorem decrementStage_positive (final : Registers) (stage : Register) :
    0 < RegisterLayout.values (decrementStageRegisters final stage)
      (decrementStageIndex stage) := by
  cases stage <;>
    simp [decrementStageRegisters, decrementStageIndex,
      RegisterLayout.values, Registers.increment, Registers.set,
      Registers.get]

theorem decrementStage_move {final : Registers} {stage next : Register}
    (hnext : DecrementStageNext stage next) :
    MarkerMachine.moveAt .left
        (MarkerTape.canonicalTape (decrementStageRegisters final stage))
        (MarkerTape.boundaryPosition (decrementStageRegisters final stage)
          (decrementStageIndex stage).succ)
        (decrementStageIndex stage).succ =
      MarkerTape.canonicalTape (decrementStageRegisters final next) := by
  cases hnext with
  | left => exact MarkerSchedule.moveLeftBoundary_before_right final
  | right => exact MarkerSchedule.moveRightBoundary_before_temp final
  | temp => exact MarkerSchedule.moveTempBoundary_before_clock final

theorem decrementStage_head {final : Registers} {stage next : Register}
    (hnext : DecrementStageNext stage next) :
    boundaryOffset (decrementStageRegisters final stage)
        (decrementStageIndex stage).succ =
      firstGapOffset (decrementStageRegisters final next)
        (decrementStageIndex next) := by
  cases hnext <;>
    simp [decrementStageRegisters, decrementStageIndex, boundaryOffset,
      firstGapOffset, CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.set, Registers.get] <;>
    omega


end

end CounterControlScheduleSemantics
end Hooper
end Kari
end LeanWang
