/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.MarkerChain

/-!
# Executable collision-free marker schedules

This file connects the head-relative tapes used by the finite marker programs
to the absolute-coordinate suffix shifts of `MarkerShift`.  In particular, a
marker may be found in one direction, shifted in the other direction, and then
left by moving the head back onto its old (now blank) source cell.  This is the
geometry needed to execute the right-to-left increment and left-to-right
positive-decrement schedules without overwriting an unmoved boundary.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerSchedule

open Turing CounterMachine

/-- Reverse one head direction. -/
def reverse : Turing.Dir → Turing.Dir
  | .left => .right
  | .right => .left

@[simp] theorem reverse_left : reverse .left = .right := rfl
@[simp] theorem reverse_right : reverse .right = .left := rfl

/-! ## Absolute-coordinate meaning of one independent move -/

/-- Generalization of `MarkerMachine.moveAt_recenter` in which the direction
used to find a marker is independent of the direction used to shift it. -/
theorem independentMove_recenter (search shift : Turing.Dir)
    (T : FullTM0.Tape MarkerTape.Symbol) (origin : Int)
    (distance : Nat) (label : Fin 5) :
    ((((MarkerMachine.encodeTape (MarkerMachine.recenter T origin)).moveN
          search distance).write MarkerMachine.blankSymbol).move shift).write
        (MarkerMachine.boundarySymbol label) =
      MarkerMachine.encodeTape (MarkerMachine.recenter
        (MarkerMachine.moveAt shift T
          (origin + FullTM0.Tape.offset search distance) label)
        (origin + FullTM0.Tape.offset search distance +
          FullTM0.Tape.delta shift)) := by
  calc
    _ = MarkerMachine.encodeTape
        (((((MarkerMachine.recenter T origin).moveN search distance).write
          (.blank : MarkerTape.Symbol)).move shift).write
            (.boundary label)) := by
      symm
      simp only [MarkerMachine.encodeTape_write,
        MarkerMachine.encodeTape_move, MarkerMachine.encodeTape_moveN,
        MarkerMachine.encodeSymbol_blank,
        MarkerMachine.encodeSymbol_boundary]
    _ = _ := by
      apply congrArg MarkerMachine.encodeTape
      rw [MarkerMachine.recenter_moveN]
      rw [← MarkerMachine.recenter_writeAt]
      rw [MarkerMachine.recenter_move]
      rw [← MarkerMachine.recenter_writeAt]
      rfl

/-- If a command departs opposite to its shift, its final head position is
the old source cell of the moved boundary. -/
theorem resultTape_recenter_source (expected : Fin 5)
    (search shift : Turing.Dir) (T : FullTM0.Tape MarkerTape.Symbol)
    (origin : Int) (distance : Nat) :
    MarkerChain.resultTape
        ⟨⟨expected, search, shift⟩, reverse shift⟩ distance
        (MarkerMachine.encodeTape (MarkerMachine.recenter T origin)) =
      MarkerMachine.encodeTape (MarkerMachine.recenter
        (MarkerMachine.moveAt shift T
          (origin + FullTM0.Tape.offset search distance) expected)
        (origin + FullTM0.Tape.offset search distance)) := by
  unfold MarkerChain.resultTape MarkerProgram.resultTape
  rw [independentMove_recenter]
  rw [← MarkerMachine.encodeTape_move]
  rw [MarkerMachine.recenter_move]
  apply congrArg MarkerMachine.encodeTape
  apply congrArg (MarkerMachine.recenter
    (MarkerMachine.moveAt shift T
      (origin + FullTM0.Tape.offset search distance) expected))
  cases shift <;>
    simp [reverse, FullTM0.Tape.delta]

/-! ## Concrete command lists -/

/-- Increment moves the required suffix right-to-left.  Each command leaves
the newly written boundary to the left, returning the head to the marker's old
source cell before the next leftward search begins. -/
def incrementCommands (register : Register) : List MarkerChain.Command :=
  (MarkerShift.incrementOrder register).map fun expected =>
    ⟨⟨expected, .left, .right⟩, .left⟩

/-- A positive decrement moves the required suffix left-to-right.  Each
command returns right to the old source cell before the next rightward search.
-/
def decrementCommands (register : Register) : List MarkerChain.Command :=
  (MarkerShift.decrementOrder register).map fun expected =>
    ⟨⟨expected, .right, .left⟩, .right⟩

@[simp]
theorem incrementCommands_expected (register : Register) :
    (incrementCommands register).map
        (fun command => command.move.expected) =
      MarkerShift.incrementOrder register := by
  simp [incrementCommands, Function.comp_def]

@[simp]
theorem decrementCommands_expected (register : Register) :
    (decrementCommands register).map
        (fun command => command.move.expected) =
      MarkerShift.decrementOrder register := by
  simp [decrementCommands, Function.comp_def]

/-! ## First exact executable schedule -/

/-- Canonical marker tape with the head centered on labelled boundary `j`. -/
noncomputable def boundaryTape (registers : Registers) (j : Fin 5) :
    FullTM0.Tape MarkerMachine.Symbol :=
  MarkerMachine.encodeTape (MarkerMachine.recenter
    (MarkerTape.canonicalTape registers)
    (MarkerTape.boundaryPosition registers j))

/-- After an increment schedule, the head is back on the old source cell of
the last boundary moved by the schedule. -/
noncomputable def incrementResultTape (registers : Registers) (j : Fin 5) :
    FullTM0.Tape MarkerMachine.Symbol :=
  MarkerMachine.encodeTape (MarkerMachine.recenter
    (MarkerTape.canonicalTape (registers.increment .clock))
    (MarkerTape.boundaryPosition registers j))

/-- The singleton clock schedule is already an exact executable realization
of `Registers.increment .clock`.  This is the base case for the longer suffix
schedules. -/
theorem incrementClock_executes (registers : Registers) :
    MarkerChain.Executes (incrementCommands .clock)
      (boundaryTape registers 4) (incrementResultTape registers 4) := by
  rw [show incrementCommands .clock =
      [⟨⟨4, .left, .right⟩, .left⟩] by
    rfl]
  refine MarkerChain.Executes.cons
    (command := ⟨⟨4, .left, .right⟩, .left⟩)
    (commands := []) (T := boundaryTape registers 4)
    (U := incrementResultTape registers 4) 0 ?_ ?_ ?_
  · constructor
    · intro i hi
      omega
    · simp [boundaryTape, MarkerMachine.recenter,
        FullTM0.Tape.offset]
  · change
      ((((boundaryTape registers 4).moveN .left 0).write
          MarkerMachine.blankSymbol).move .right).read =
        MarkerMachine.blankSymbol
    rw [FullTM0.Tape.moveN_zero]
    rw [FullTM0.Tape.read_eq, FullTM0.Tape.move_right_apply]
    rw [FullTM0.Tape.write_apply_of_ne MarkerMachine.blankSymbol _
      (by norm_num : (0 + 1 : Int) ≠ 0)]
    change MarkerMachine.encodeSymbol
        (MarkerTape.canonicalTape registers
          (MarkerTape.boundaryPosition registers 4 + 1)) =
      MarkerMachine.blankSymbol
    rw [MarkerMachine.encodeSymbol_eq_blank_iff]
    rw [MarkerTape.canonicalTape_eq_blank_iff]
    intro j hj
    have hstrict := MarkerTape.boundaryPosition_injective registers
    fin_cases j <;>
      simp [MarkerTape.boundaryPosition,
        RegisterLayout.startBoundary_eq,
        RegisterLayout.leftBoundary_eq,
        RegisterLayout.rightBoundary_eq,
        RegisterLayout.tempBoundary_eq,
        RegisterLayout.clockBoundary_eq] at hj <;>
      omega
  · unfold boundaryTape incrementResultTape
    change MarkerChain.Executes []
      (MarkerChain.resultTape
        ⟨⟨4, .left, .right⟩, reverse .right⟩ 0
        (MarkerMachine.encodeTape (MarkerMachine.recenter
          (MarkerTape.canonicalTape registers)
          (MarkerTape.boundaryPosition registers 4))))
      (MarkerMachine.encodeTape (MarkerMachine.recenter
        (MarkerTape.canonicalTape (registers.increment .clock))
        (MarkerTape.boundaryPosition registers 4)))
    rw [resultTape_recenter_source]
    simp only [FullTM0.Tape.offset_left, Nat.cast_zero, neg_zero, add_zero]
    rw [MarkerMachine.moveAt_clock_eq_incrementTape]
    rw [MarkerShift.incrementTape_canonical]
    exact MarkerChain.Executes.nil _

/-! Moving the remaining suffix boundaries turns the successive intermediate
canonical layouts into the next named-register increment. -/

theorem moveTempBoundary_after_clock (registers : Registers) :
    MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape (registers.increment .clock))
        (MarkerTape.boundaryPosition (registers.increment .clock) 3) 3 =
      MarkerTape.canonicalTape (registers.increment .temp) := by
  rw [MarkerMachine.moveAt_right]
  apply MarkerShift.tape_ext_boundary
  intro position label
  rw [MarkerShift.moveRightAt_eq_boundary_iff]
  simp only [MarkerTape.canonicalTape_eq_boundary_iff]
  fin_cases label <;>
    simp [MarkerTape.boundaryPosition,
      RegisterLayout.startBoundary_eq,
      RegisterLayout.leftBoundary_eq,
      RegisterLayout.rightBoundary_eq,
      RegisterLayout.tempBoundary_eq,
      RegisterLayout.clockBoundary_eq,
      Registers.increment, Registers.set, Registers.get] <;>
    omega

theorem moveRightBoundary_after_temp (registers : Registers) :
    MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape (registers.increment .temp))
        (MarkerTape.boundaryPosition (registers.increment .temp) 2) 2 =
      MarkerTape.canonicalTape (registers.increment .right) := by
  rw [MarkerMachine.moveAt_right]
  apply MarkerShift.tape_ext_boundary
  intro position label
  rw [MarkerShift.moveRightAt_eq_boundary_iff]
  simp only [MarkerTape.canonicalTape_eq_boundary_iff]
  fin_cases label <;>
    simp [MarkerTape.boundaryPosition,
      RegisterLayout.startBoundary_eq,
      RegisterLayout.leftBoundary_eq,
      RegisterLayout.rightBoundary_eq,
      RegisterLayout.tempBoundary_eq,
      RegisterLayout.clockBoundary_eq,
      Registers.increment, Registers.set, Registers.get] <;>
    omega

theorem moveLeftBoundary_after_right (registers : Registers) :
    MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape (registers.increment .right))
        (MarkerTape.boundaryPosition (registers.increment .right) 1) 1 =
      MarkerTape.canonicalTape (registers.increment .left) := by
  rw [MarkerMachine.moveAt_right]
  apply MarkerShift.tape_ext_boundary
  intro position label
  rw [MarkerShift.moveRightAt_eq_boundary_iff]
  simp only [MarkerTape.canonicalTape_eq_boundary_iff]
  fin_cases label <;>
    simp [MarkerTape.boundaryPosition,
      RegisterLayout.startBoundary_eq,
      RegisterLayout.leftBoundary_eq,
      RegisterLayout.rightBoundary_eq,
      RegisterLayout.tempBoundary_eq,
      RegisterLayout.clockBoundary_eq,
      Registers.increment, Registers.set, Registers.get] <;>
    omega

/-! ## One generic right shift from the far end of a positive gap -/

/-- Encoded canonical tape centered at the last cell of gap `i`. -/
noncomputable def lastGapTape (registers : Registers) (i : Fin 4) :
    FullTM0.Tape MarkerMachine.Symbol :=
  MarkerMachine.encodeTape (MarkerTape.lastGapCellTape registers i)

/-- Result of shifting the left boundary of gap `i`, with the final head back
at that boundary's old source coordinate. -/
noncomputable def shiftedBoundaryTape (current next : Registers) (i : Fin 4) :
    FullTM0.Tape MarkerMachine.Symbol :=
  MarkerMachine.encodeTape (MarkerMachine.recenter
    (MarkerTape.canonicalTape next)
    (MarkerTape.boundaryPosition current i.castSucc))

/-- Starting at the last cell of a nonempty gap, search left for its labelled
left boundary, shift that boundary right, and return to its old source cell.
The caller supplies the absolute tape identity produced by that shift. -/
theorem positiveGapShift_executes (current next : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values current i)
    (hmove : MarkerMachine.moveAt .right
        (MarkerTape.canonicalTape current)
        (MarkerTape.boundaryPosition current i.castSucc) i.castSucc =
      MarkerTape.canonicalTape next) :
    MarkerChain.Executes
      [⟨⟨i.castSucc, .left, .right⟩, .left⟩]
      (lastGapTape current i) (shiftedBoundaryTape current next i) := by
  refine MarkerChain.Executes.cons
    (command := ⟨⟨i.castSucc, .left, .right⟩, .left⟩)
    (commands := []) (T := lastGapTape current i)
    (U := shiftedBoundaryTape current next i)
    (RegisterLayout.values current i) ?_ ?_ ?_
  · have hgap := MarkerMachine.encodeTape_searchGap
      (MarkerTape.searchGap_left_label current i)
    simpa [lastGapTape] using hgap
  · change
      (((((lastGapTape current i).moveN .left
          (RegisterLayout.values current i)).write
            MarkerMachine.blankSymbol).move .right).read =
        MarkerMachine.blankSymbol)
    rw [FullTM0.Tape.read_eq, FullTM0.Tape.move_right_apply]
    rw [FullTM0.Tape.write_apply_of_ne MarkerMachine.blankSymbol _
      (by norm_num : (0 + 1 : Int) ≠ 0)]
    change MarkerMachine.encodeSymbol
        (MarkerTape.lastGapCellTape current i
          (1 + FullTM0.Tape.offset .left
            (RegisterLayout.values current i))) =
      MarkerMachine.blankSymbol
    rw [MarkerMachine.encodeSymbol_eq_blank_iff]
    have hinterior := MarkerTape.canonicalTape_gapInterior current i 0 hpositive
    change MarkerTape.canonicalTape current
      (CounterLayout.lastGapCellTape (RegisterLayout.values current) i
        (1 + FullTM0.Tape.offset .left
          (RegisterLayout.values current i))) = .blank
    have hsucc :
        (CounterLayout.boundaryPos (RegisterLayout.values current)
            (i + 1) : Int) =
          CounterLayout.boundaryPos (RegisterLayout.values current) i +
            RegisterLayout.values current i + 1 := by
      exact_mod_cast CounterLayout.boundaryPos_succ
        (RegisterLayout.values current) i
    have hcoord :
        CounterLayout.lastGapCellTape (RegisterLayout.values current) i
            (1 + FullTM0.Tape.offset .left
              (RegisterLayout.values current i)) =
          (CounterLayout.boundaryPos (RegisterLayout.values current) i : Int) +
            1 := by
      simp [CounterLayout.lastGapCellTape, FullTM0.Tape.offset_left,
        hsucc]
      ring
    rw [hcoord]
    simpa using hinterior
  · unfold lastGapTape shiftedBoundaryTape
    change MarkerChain.Executes []
      (MarkerChain.resultTape
        ⟨⟨i.castSucc, .left, .right⟩, reverse .right⟩
        (RegisterLayout.values current i)
        (MarkerMachine.encodeTape (MarkerMachine.recenter
          (MarkerTape.canonicalTape current)
          ((CounterLayout.boundaryPos (RegisterLayout.values current)
            (i + 1) : Int) - 1))))
      (MarkerMachine.encodeTape (MarkerMachine.recenter
        (MarkerTape.canonicalTape next)
        (MarkerTape.boundaryPosition current i.castSucc)))
    rw [resultTape_recenter_source]
    have htarget :
        (CounterLayout.boundaryPos (RegisterLayout.values current)
            (i + 1) : Int) - 1 +
            FullTM0.Tape.offset .left
              (RegisterLayout.values current i) =
          MarkerTape.boundaryPosition current i.castSucc := by
      have hsucc :
          (CounterLayout.boundaryPos (RegisterLayout.values current)
              (i + 1) : Int) =
            CounterLayout.boundaryPos (RegisterLayout.values current) i +
              RegisterLayout.values current i + 1 := by
        exact_mod_cast CounterLayout.boundaryPos_succ
          (RegisterLayout.values current) i
      rw [hsucc]
      simp [FullTM0.Tape.offset_left, MarkerTape.boundaryPosition]
    rw [htarget, hmove]
    exact MarkerChain.Executes.nil _

/-! ## Complete increment schedules -/

/-- Guarded command executions compose under list concatenation. -/
theorem executes_append {first second : List MarkerChain.Command}
    {T U V : FullTM0.Tape MarkerMachine.Symbol}
    (hfirst : MarkerChain.Executes first T U)
    (hsecond : MarkerChain.Executes second U V) :
    MarkerChain.Executes (first ++ second) T V := by
  induction hfirst with
  | nil T => simpa using hsecond
  | cons command commands T U distance hgap hdestination hrest ih =>
      exact MarkerChain.Executes.cons command (commands ++ second) T V
        distance hgap hdestination (ih hsecond)

theorem incrementClock_toLastGap (registers : Registers) :
    MarkerChain.Executes [⟨⟨4, .left, .right⟩, .left⟩]
      (boundaryTape registers 4)
      (lastGapTape (registers.increment .clock) 3) := by
  have h := incrementClock_executes registers
  change MarkerChain.Executes [⟨⟨4, .left, .right⟩, .left⟩]
    (boundaryTape registers 4) (incrementResultTape registers 4) at h
  convert h using 1
  funext position
  simp [incrementResultTape, lastGapTape, MarkerTape.lastGapCellTape,
    CounterLayout.lastGapCellTape, MarkerMachine.recenter,
    MarkerTape.boundaryPosition,
    RegisterLayout.clockBoundary_eq,
    Registers.increment, Registers.set, Registers.get]
  congr 2 <;> ring

theorem incrementTemp_step (registers : Registers) :
    MarkerChain.Executes [⟨⟨3, .left, .right⟩, .left⟩]
      (lastGapTape (registers.increment .clock) 3)
      (lastGapTape (registers.increment .temp) 2) := by
  have h := positiveGapShift_executes
    (registers.increment .clock) (registers.increment .temp) (3 : Fin 4)
    (by simp [RegisterLayout.values, Registers.increment,
      Registers.set, Registers.get])
    (moveTempBoundary_after_clock registers)
  have hlabel : (3 : Fin 4).castSucc = (3 : Fin 5) := by rfl
  rw [hlabel] at h
  have hout : shiftedBoundaryTape (registers.increment .clock)
      (registers.increment .temp) 3 =
      lastGapTape (registers.increment .temp) 2 := by
    funext position
    simp [shiftedBoundaryTape, lastGapTape,
      MarkerTape.lastGapCellTape, CounterLayout.lastGapCellTape,
      MarkerMachine.recenter, MarkerTape.boundaryPosition,
      RegisterLayout.tempBoundary_eq,
      Registers.increment, Registers.set, Registers.get]
    congr 2 <;> ring
  rw [hout] at h
  exact h

theorem incrementRight_step (registers : Registers) :
    MarkerChain.Executes [⟨⟨2, .left, .right⟩, .left⟩]
      (lastGapTape (registers.increment .temp) 2)
      (lastGapTape (registers.increment .right) 1) := by
  have h := positiveGapShift_executes
    (registers.increment .temp) (registers.increment .right) (2 : Fin 4)
    (by simp [RegisterLayout.values, Registers.increment,
      Registers.set, Registers.get])
    (moveRightBoundary_after_temp registers)
  have hlabel : (2 : Fin 4).castSucc = (2 : Fin 5) := by rfl
  rw [hlabel] at h
  have hout : shiftedBoundaryTape (registers.increment .temp)
      (registers.increment .right) 2 =
      lastGapTape (registers.increment .right) 1 := by
    funext position
    simp [shiftedBoundaryTape, lastGapTape,
      MarkerTape.lastGapCellTape, CounterLayout.lastGapCellTape,
      MarkerMachine.recenter, MarkerTape.boundaryPosition,
      RegisterLayout.rightBoundary_eq,
      Registers.increment, Registers.set, Registers.get]
    congr 2 <;> ring
  rw [hout] at h
  exact h

theorem incrementLeft_step (registers : Registers) :
    MarkerChain.Executes [⟨⟨1, .left, .right⟩, .left⟩]
      (lastGapTape (registers.increment .right) 1)
      (lastGapTape (registers.increment .left) 0) := by
  have h := positiveGapShift_executes
    (registers.increment .right) (registers.increment .left) (1 : Fin 4)
    (by simp [RegisterLayout.values, Registers.increment,
      Registers.set, Registers.get])
    (moveLeftBoundary_after_right registers)
  have hlabel : (1 : Fin 4).castSucc = (1 : Fin 5) := by rfl
  rw [hlabel] at h
  have hout : shiftedBoundaryTape (registers.increment .right)
      (registers.increment .left) 1 =
      lastGapTape (registers.increment .left) 0 := by
    funext position
    simp [shiftedBoundaryTape, lastGapTape,
      MarkerTape.lastGapCellTape, CounterLayout.lastGapCellTape,
      MarkerMachine.recenter, MarkerTape.boundaryPosition,
      RegisterLayout.leftBoundary_eq,
      Registers.increment, Registers.set, Registers.get]
  rw [hout] at h
  exact h

/-- Canonical exit head position of a complete named-register increment. -/
noncomputable def incrementFinishTape (registers : Registers) : Register →
    FullTM0.Tape MarkerMachine.Symbol
  | .left => lastGapTape (registers.increment .left) 0
  | .right => lastGapTape (registers.increment .right) 1
  | .temp => lastGapTape (registers.increment .temp) 2
  | .clock => lastGapTape (registers.increment .clock) 3

/-- Every collision-free increment schedule executes exactly on a canonical
five-boundary layout. -/
theorem increment_executes (registers : Registers) (register : Register) :
    MarkerChain.Executes (incrementCommands register)
      (boundaryTape registers 4) (incrementFinishTape registers register) := by
  have hclock := incrementClock_toLastGap registers
  have htemp := incrementTemp_step registers
  have hright := incrementRight_step registers
  have hleft := incrementLeft_step registers
  cases register with
  | clock => exact hclock
  | temp =>
      simpa [incrementCommands, incrementFinishTape,
        MarkerShift.incrementOrder] using
        executes_append hclock htemp
  | right =>
      simpa [incrementCommands, incrementFinishTape,
        MarkerShift.incrementOrder] using
        executes_append (executes_append hclock htemp) hright
  | left =>
      simpa [incrementCommands, incrementFinishTape,
        MarkerShift.incrementOrder] using
        executes_append
          (executes_append (executes_append hclock htemp) hright) hleft

end MarkerSchedule
end Hooper
end Kari
end LeanWang
