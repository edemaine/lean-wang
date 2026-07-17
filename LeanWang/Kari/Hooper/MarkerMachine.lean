/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FiniteTM0
import LeanWang.Kari.Hooper.MarkerShift

/-!
# A finite TM0 primitive for moving a labelled marker

This file is the first concrete transition-table layer of Hooper's marker
machine.  The generated program searches through blanks for one expected
labelled boundary, clears it, moves one cell farther in the same direction,
checks that this destination is blank, and writes the boundary there.  Any
unexpected label or occupied destination has no rule and therefore halts.

The program has four states and four rules.  Its correctness theorem is stated
for an arbitrary full tape and search distance.  Thus later counter-program
compilation can reuse the same primitive for each boundary in the
collision-free orders from `MarkerShift`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerMachine

open Turing
open CounterMachine

/-- Six symbols suffice for the blank and five labelled boundaries. -/
abbrev AlphabetSize := 6

/-- The explicit finite alphabet accepted by `FiniteTM0`. -/
abbrev Symbol := FiniteTM0.Symbol AlphabetSize

/-- Numeric encoding of the core marker alphabet. -/
def encodeSymbol : MarkerTape.Symbol → Symbol
  | .blank => 0
  | .boundary j => ⟨j.val + 1, by
      change j.val + 1 < 6
      omega⟩

/-- The encoded blank symbol. -/
def blankSymbol : Symbol :=
  encodeSymbol .blank

/-- The encoded form of boundary label `j`. -/
def boundarySymbol (j : Fin 5) : Symbol :=
  encodeSymbol (.boundary j)

@[simp] theorem encodeSymbol_blank : encodeSymbol .blank = blankSymbol :=
  rfl

@[simp] theorem encodeSymbol_boundary (j : Fin 5) :
    encodeSymbol (.boundary j) = boundarySymbol j :=
  rfl

theorem blankSymbol_ne_boundarySymbol (j : Fin 5) :
    blankSymbol ≠ boundarySymbol j := by
  intro h
  have := congrArg Fin.val h
  simp [blankSymbol, boundarySymbol, encodeSymbol] at this

theorem boundarySymbol_injective :
    Function.Injective boundarySymbol := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [boundarySymbol, encodeSymbol] using this

@[simp] theorem boundarySymbol_eq_boundarySymbol_iff (i j : Fin 5) :
    boundarySymbol i = boundarySymbol j ↔ i = j :=
  boundarySymbol_injective.eq_iff

@[simp] theorem encodeSymbol_eq_blank_iff (a : MarkerTape.Symbol) :
    encodeSymbol a = blankSymbol ↔ a = .blank := by
  cases a with
  | blank => simp
  | boundary j =>
      constructor
      · intro h
        exact (Ne.symm (blankSymbol_ne_boundarySymbol j)
          (by simpa only [encodeSymbol_boundary] using h)).elim
      · intro h
        cases h

@[simp] theorem encodeSymbol_eq_boundary_iff
    (a : MarkerTape.Symbol) (j : Fin 5) :
    encodeSymbol a = boundarySymbol j ↔ a = .boundary j := by
  cases a with
  | blank =>
      simp [blankSymbol_ne_boundarySymbol j]
  | boundary i =>
      simp

/-- Pointwise encoding of a marker tape into the explicit six-symbol
alphabet. -/
def encodeTape (T : FullTM0.Tape MarkerTape.Symbol) :
    FullTM0.Tape Symbol :=
  fun i => encodeSymbol (T i)

@[simp] theorem encodeTape_apply
    (T : FullTM0.Tape MarkerTape.Symbol) (i : Int) :
    encodeTape T i = encodeSymbol (T i) :=
  rfl

/-- Tape recentering: absolute position `position` becomes the head cell. -/
def recenter {A : Type} (T : FullTM0.Tape A) (position : Int) :
    FullTM0.Tape A :=
  fun i => T (position + i)

@[simp] theorem recenter_apply {A : Type} (T : FullTM0.Tape A)
    (position i : Int) :
    recenter T position i = T (position + i) :=
  rfl

@[simp] theorem encodeTape_write (T : FullTM0.Tape MarkerTape.Symbol)
    (a : MarkerTape.Symbol) :
    encodeTape (T.write a) = (encodeTape T).write (encodeSymbol a) := by
  funext i
  by_cases hi : i = 0
  · simp [encodeTape, FullTM0.Tape.write, hi]
  · simp [encodeTape, FullTM0.Tape.write, hi]

@[simp] theorem encodeTape_move (T : FullTM0.Tape MarkerTape.Symbol)
    (direction : Turing.Dir) :
    encodeTape (T.move direction) = (encodeTape T).move direction := by
  funext i
  cases direction <;> rfl

@[simp] theorem encodeTape_moveN (T : FullTM0.Tape MarkerTape.Symbol)
    (direction : Turing.Dir) (distance : Nat) :
    encodeTape (T.moveN direction distance) =
      (encodeTape T).moveN direction distance := by
  funext i
  rfl

/-- Recentering and then moving the head `distance` cells is the same as
recentering once at the resulting absolute position. -/
theorem recenter_moveN {A : Type} (T : FullTM0.Tape A) (origin : Int)
    (direction : Turing.Dir) (distance : Nat) :
    (recenter T origin).moveN direction distance =
      recenter T (origin + FullTM0.Tape.offset direction distance) := by
  funext i
  simp only [FullTM0.Tape.moveN_apply, recenter_apply]
  congr 1
  ring

/-- An absolute write at the recentering position becomes a head write. -/
theorem recenter_writeAt (T : FullTM0.Tape MarkerTape.Symbol) (position : Int)
    (a : MarkerTape.Symbol) :
    recenter (MarkerShift.writeAt T position a) position =
      (recenter T position).write a := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [recenter, MarkerShift.writeAt, FullTM0.Tape.write]
  · have hposition : position + i ≠ position := by omega
    simp [recenter, MarkerShift.writeAt, FullTM0.Tape.write, hi, hposition]

/-- One head move translates the absolute recentering coordinate by its
signed displacement. -/
theorem recenter_move {A : Type} (T : FullTM0.Tape A) (position : Int)
    (direction : Turing.Dir) :
    (recenter T position).move direction =
      recenter T (position + FullTM0.Tape.delta direction) := by
  funext i
  cases direction <;>
    simp only [recenter, FullTM0.Tape.move, FullTM0.Tape.delta]
  · congr 1
    ring
  · congr 1
    ring

/-- Encoding preserves a labelled search gap exactly. -/
theorem encodeTape_searchGap {T : FullTM0.Tape MarkerTape.Symbol}
    {direction : Turing.Dir} {distance : Nat} {expected : Fin 5}
    (hgap : SearchGap MarkerTape.IsBlank
      (MarkerTape.IsBoundaryLabel expected) T direction distance) :
    SearchGap (fun a => a = blankSymbol)
      (fun a => a = boundarySymbol expected)
      (encodeTape T) direction distance := by
  constructor
  · intro i hi
    rw [encodeTape_apply, encodeSymbol_eq_blank_iff]
    exact (MarkerTape.isBlank_iff_eq_blank _).mp (hgap.blank hi)
  · change encodeSymbol (T (FullTM0.Tape.offset direction distance)) =
        boundarySymbol expected
    rw [encodeSymbol_eq_boundary_iff]
    have hmark := hgap.marked
    cases hsymbol : T (FullTM0.Tape.offset direction distance) with
    | blank => simp [hsymbol, MarkerTape.IsBoundaryLabel] at hmark
    | boundary j =>
        simp only [hsymbol, MarkerTape.isBoundaryLabel_boundary] at hmark
        simpa [hsymbol, hmark]

/-- Direction-generic form of the abstract one-cell marker move. -/
def moveAt (direction : Turing.Dir) (T : FullTM0.Tape MarkerTape.Symbol)
    (position : Int) (label : Fin 5) : FullTM0.Tape MarkerTape.Symbol :=
  MarkerShift.writeAt (MarkerShift.writeAt T position .blank)
    (position + FullTM0.Tape.delta direction) (.boundary label)

@[simp] theorem moveAt_left (T : FullTM0.Tape MarkerTape.Symbol)
    (position : Int) (label : Fin 5) :
    moveAt .left T position label = MarkerShift.moveLeftAt T position label := by
  simp only [moveAt, FullTM0.Tape.delta_left, MarkerShift.moveLeftAt]
  congr 2

@[simp] theorem moveAt_right (T : FullTM0.Tape MarkerTape.Symbol)
    (position : Int) (label : Fin 5) :
    moveAt .right T position label = MarkerShift.moveRightAt T position label := by
  simp only [moveAt, FullTM0.Tape.delta_right, MarkerShift.moveRightAt]

/-- The head-relative tape produced by the primitive is exactly the encoded
abstract marker move, recentered at the marker's new position. -/
theorem moveAt_recenter (direction : Turing.Dir)
    (T : FullTM0.Tape MarkerTape.Symbol) (origin : Int)
    (distance : Nat) (label : Fin 5) :
    ((((encodeTape (recenter T origin)).moveN direction distance).write
        blankSymbol).move direction).write (boundarySymbol label) =
      encodeTape (recenter
        (moveAt direction T
          (origin + FullTM0.Tape.offset direction distance) label)
        (origin + FullTM0.Tape.offset direction distance +
          FullTM0.Tape.delta direction)) := by
  calc
    _ = encodeTape (((((recenter T origin).moveN direction distance).write
          (.blank : MarkerTape.Symbol)).move direction).write
            (.boundary label)) := by
        symm
        simp only [encodeTape_write, encodeTape_move, encodeTape_moveN,
          encodeSymbol_blank, encodeSymbol_boundary]
    _ = _ := by
      apply congrArg encodeTape
      rw [recenter_moveN]
      rw [← recenter_writeAt]
      rw [recenter_move]
      rw [← recenter_writeAt]
      rfl

/-- Search-loop state. -/
def searchState : FiniteTM0.State := 0

/-- The expected marker has just been cleared. -/
def moveState : FiniteTM0.State := 1

/-- The head has moved to the destination, which must be blank. -/
def verifyState : FiniteTM0.State := 2

/-- Successful terminal state.  It deliberately has no outgoing rule. -/
def doneState : FiniteTM0.State := 3

/-- Explicit action corresponding to a head direction. -/
def moveAction : Turing.Dir → FiniteTM0.Action AlphabetSize
  | .left => .moveLeft
  | .right => .moveRight

@[simp] theorem moveAction_toStmt (d : Turing.Dir) :
    (moveAction d).toStmt = .move d := by
  cases d <;> rfl

/-- Generate the guarded four-rule program for one expected label and one
direction.

* blank in `searchState`: continue searching;
* expected label in `searchState`: clear it;
* blank in `moveState`: move one cell farther;
* blank in `verifyState`: write the expected label and finish.

No rule accepts another boundary label or a nonblank destination.
-/
def program (expected : Fin 5) (direction : Turing.Dir) :
    FiniteTM0.Table AlphabetSize :=
  [ FiniteTM0.Rule.mk searchState blankSymbol
      searchState (moveAction direction)
  , FiniteTM0.Rule.mk searchState (boundarySymbol expected)
      moveState (.write blankSymbol)
  , FiniteTM0.Rule.mk moveState blankSymbol
      verifyState (moveAction direction)
  , FiniteTM0.Rule.mk verifyState blankSymbol
      doneState (.write (boundarySymbol expected))
  ]

/-- Semantic TM0 machine generated by `program`. -/
def machine (expected : Fin 5) (direction : Turing.Dir) :
    Turing.TM0.Machine Symbol FiniteTM0.State :=
  FiniteTM0.machine (program expected direction)

/-- The four generated rule keys are pairwise distinct. -/
theorem program_deterministic (expected : Fin 5) (direction : Turing.Dir) :
    FiniteTM0.Deterministic (program expected direction) := by
  simp [FiniteTM0.Deterministic, program, FiniteTM0.Rule.mk,
    searchState, moveState, verifyState,
    blankSymbol_ne_boundarySymbol]

/-- Lookup in every generated table is computable.  Together with the
four-element list definition, this is the executable finiteness interface used
by later compilers. -/
theorem program_lookup_computable (expected : Fin 5) (direction : Turing.Dir) :
    Computable fun input :
        FiniteTM0.Key AlphabetSize =>
      FiniteTM0.lookupAction (program expected direction)
        input.1 input.2 :=
  (FiniteTM0.lookupAction_computable (numSymbols := AlphabetSize)).comp
    ((Computable.const (program expected direction)).pair Computable.id)

@[simp] theorem step_search_blank (expected : Fin 5) (direction : Turing.Dir)
    (T : FullTM0.Tape Symbol) (hread : T.read = blankSymbol) :
    FullTM0.step (machine expected direction) ⟨searchState, T⟩ =
      some ⟨searchState, T.move direction⟩ := by
  change T 0 = blankSymbol at hread
  cases direction <;>
    simp [FullTM0.step, machine, FiniteTM0.machine, program,
      FiniteTM0.lookupAction, FiniteTM0.Rule.mk, searchState,
      FullTM0.Tape.read, hread, moveAction]

@[simp] theorem step_search_boundary (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape Symbol)
    (hread : T.read = boundarySymbol expected) :
    FullTM0.step (machine expected direction) ⟨searchState, T⟩ =
      some ⟨moveState, T.write blankSymbol⟩ := by
  change T 0 = boundarySymbol expected at hread
  have hne : boundarySymbol expected ≠ blankSymbol :=
    (blankSymbol_ne_boundarySymbol expected).symm
  cases direction <;>
    simp [FullTM0.step, machine, FiniteTM0.machine, program,
      FiniteTM0.lookupAction, FiniteTM0.Rule.mk, searchState, moveState,
      FullTM0.Tape.read, hread, hne, moveAction]

@[simp] theorem step_move (expected : Fin 5) (direction : Turing.Dir)
    (T : FullTM0.Tape Symbol) (hread : T.read = blankSymbol) :
    FullTM0.step (machine expected direction) ⟨moveState, T⟩ =
      some ⟨verifyState, T.move direction⟩ := by
  change T 0 = blankSymbol at hread
  cases direction <;>
    simp [FullTM0.step, machine, FiniteTM0.machine, program,
      FiniteTM0.lookupAction, FiniteTM0.Rule.mk, searchState, moveState,
      verifyState, FullTM0.Tape.read, hread, moveAction]

@[simp] theorem step_verify (expected : Fin 5) (direction : Turing.Dir)
    (T : FullTM0.Tape Symbol) (hread : T.read = blankSymbol) :
    FullTM0.step (machine expected direction) ⟨verifyState, T⟩ =
      some ⟨doneState, T.write (boundarySymbol expected)⟩ := by
  change T 0 = blankSymbol at hread
  cases direction <;>
    simp [FullTM0.step, machine, FiniteTM0.machine, program,
      FiniteTM0.lookupAction, FiniteTM0.Rule.mk, searchState, moveState,
      verifyState, doneState, FullTM0.Tape.read, hread,
      moveAction]

/-- One successful semantic step gives full-tape reachability. -/
private theorem reaches_of_step {expected : Fin 5} {direction : Turing.Dir}
    {c d : FullTM0.Cfg Symbol FiniteTM0.State}
    (h : FullTM0.step (machine expected direction) c = some d) :
    FullTM0.Reaches (machine expected direction) c d := by
  apply Relation.ReflTransGen.single
  simpa [h]

/-- The search loop reaches and clears an expected boundary after crossing
exactly `distance` blank cells. -/
theorem search_reaches_clear (expected : Fin 5) (direction : Turing.Dir)
    (T : FullTM0.Tape Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol)
      (fun a => a = boundarySymbol expected) T direction distance) :
    FullTM0.Reaches (machine expected direction)
      ⟨searchState, T⟩
      ⟨moveState, (T.moveN direction distance).write blankSymbol⟩ := by
  induction distance generalizing T with
  | zero =>
      have hread : T.read = boundarySymbol expected := by
        simpa [SearchGap, FullTM0.Tape.read] using hgap.2
      simpa using reaches_of_step
        (step_search_boundary expected direction T hread)
  | succ distance ih =>
      have hread : T.read = blankSymbol := by
        simpa [FullTM0.Tape.read] using hgap.blank (Nat.zero_lt_succ distance)
      have hfirst := reaches_of_step
        (step_search_blank expected direction T hread)
      have htail : SearchGap (fun a => a = blankSymbol)
          (fun a => a = boundarySymbol expected) (T.move direction)
          direction distance := by
        simpa [Nat.succ_eq_add_one] using hgap.tail
      have hrest := ih (T.move direction) htail
      have hall := hfirst.trans hrest
      simpa [FullTM0.Reaches, StateTransition.Reaches,
        FullTM0.Tape.move_moveN,
        Nat.succ_eq_add_one] using hall

/-- Exact final tape of the guarded primitive, expressed in head-relative
coordinates.  The destination-blank hypothesis is the guard checked by the
third rule. -/
theorem moveMarker_reaches (expected : Fin 5) (direction : Turing.Dir)
    (T : FullTM0.Tape Symbol) (distance : Nat)
    (hgap : SearchGap (fun a => a = blankSymbol)
      (fun a => a = boundarySymbol expected) T direction distance)
    (hdestination :
      (((T.moveN direction distance).write blankSymbol).move direction).read =
        blankSymbol) :
    FullTM0.Reaches (machine expected direction)
      ⟨searchState, T⟩
      ⟨doneState,
        (((T.moveN direction distance).write blankSymbol).move direction).write
          (boundarySymbol expected)⟩ := by
  have hsearch := search_reaches_clear expected direction T distance hgap
  have hmove := reaches_of_step
    (step_move expected direction
      ((T.moveN direction distance).write blankSymbol) (by simp))
  have hwrite := reaches_of_step
    (step_verify expected direction
      (((T.moveN direction distance).write blankSymbol).move direction)
      hdestination)
  exact hsearch.trans (hmove.trans hwrite)

/-! ## A concrete named-register operation -/

/-- The clock-gap search tape is the canonical marker tape recentered at the
first cell after boundary 3. -/
theorem firstClockGap_eq_recenter (v : Registers) :
    MarkerTape.firstGapCellTape v 3 =
      recenter (MarkerTape.canonicalTape v)
        (MarkerTape.boundaryPosition v 3 + 1) := by
  funext i
  rfl

/-- The clock boundary is found `v.clock` cells from the first cell of its
gap. -/
theorem clock_search_source (v : Registers) :
    MarkerTape.boundaryPosition v 3 + 1 +
        FullTM0.Tape.offset .right v.clock =
      MarkerTape.boundaryPosition v 4 := by
  simp [MarkerTape.boundaryPosition, RegisterLayout.tempBoundary_eq,
    RegisterLayout.clockBoundary_eq]
  omega

/-- The cell immediately right of the final canonical boundary is blank. -/
theorem clock_destination_blank (v : Registers) :
    MarkerTape.firstGapCellTape v 3
        (FullTM0.Tape.offset .right (v.clock + 1)) = .blank := by
  unfold MarkerTape.firstGapCellTape
  rw [MarkerTape.canonicalTape_eq_blank_iff]
  intro j
  fin_cases j <;>
    simp [CounterLayout.firstGapCellTape, FullTM0.Tape.offset_right,
      MarkerTape.boundaryPosition, RegisterLayout.startBoundary_eq,
      RegisterLayout.leftBoundary_eq, RegisterLayout.rightBoundary_eq,
      RegisterLayout.tempBoundary_eq, RegisterLayout.clockBoundary_eq] <;>
    omega

/-- For the clock register, the generic right move is exactly the singleton
suffix shift prescribed by `MarkerShift.incrementTape`. -/
theorem moveAt_clock_eq_incrementTape (v : Registers) :
    moveAt .right (MarkerTape.canonicalTape v)
        (MarkerTape.boundaryPosition v 4) 4 =
      MarkerShift.incrementTape v .clock (MarkerTape.canonicalTape v) := by
  simp [MarkerShift.incrementTape, MarkerShift.incrementOrder,
    MarkerShift.moveCanonicalRight]

/-- The concrete four-rule finite TM0 program performs one exact increment of
the clock register on its canonical marker tape.  The final tape is recentered
at the newly moved boundary, because `FullTM0` uses head-relative coordinates.
-/
theorem incrementClock_reaches (v : Registers) :
    FullTM0.Reaches (machine 4 .right)
      ⟨searchState,
        encodeTape (MarkerTape.firstGapCellTape v 3)⟩
      ⟨doneState,
        encodeTape (recenter
          (MarkerShift.incrementTape v .clock (MarkerTape.canonicalTape v))
          (MarkerTape.boundaryPosition v 4 + 1))⟩ := by
  have hgap := encodeTape_searchGap (MarkerTape.searchGap_clock_right v)
  have hdestination :
      ((((encodeTape (MarkerTape.firstGapCellTape v 3)).moveN .right
          v.clock).write blankSymbol).move .right).read = blankSymbol := by
    rw [FullTM0.Tape.read_eq, FullTM0.Tape.move_right_apply]
    rw [FullTM0.Tape.write_apply_of_ne blankSymbol
      ((encodeTape (MarkerTape.firstGapCellTape v 3)).moveN .right v.clock)
      (by norm_num : (0 + 1 : Int) ≠ 0)]
    change encodeSymbol
        (MarkerTape.firstGapCellTape v 3
          (1 + FullTM0.Tape.offset .right v.clock)) = blankSymbol
    simpa [FullTM0.Tape.offset_right, add_comm] using
      congrArg encodeSymbol (clock_destination_blank v)
  have hreach := moveMarker_reaches 4 .right
    (encodeTape (MarkerTape.firstGapCellTape v 3)) v.clock hgap hdestination
  have hbridge := moveAt_recenter .right (MarkerTape.canonicalTape v)
    (MarkerTape.boundaryPosition v 3 + 1) v.clock 4
  rw [← firstClockGap_eq_recenter] at hbridge
  rw [hbridge] at hreach
  rw [clock_search_source, moveAt_clock_eq_incrementTape] at hreach
  simpa [FullTM0.Tape.delta_right] using hreach

end MarkerMachine
end Hooper
end Kari
end LeanWang
