/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerProgram
import LeanWang.Kari.Hooper.CanonicalInitializer
import LeanWang.Kari.Hooper.FiniteTM0Path

/-!
# Finite program for the canonical nested initializer

A failed bounded search enters the shared core with its physical return tag
under the head at the far end of the exhausted prefix.  The initializer first
clears that copy, walks back across the prefix, writes the same tag at the
original search head, and installs the five canonical boundaries toward the
suspended target.  It finishes on boundary `4`, one blank cell before the old
far endpoint.

Every return tag gets a private straight-line path because the finite control
must remember which symbol to relocate.  All paths have the same effective,
code-dependent length and converge to one common counter-program entry.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CanonicalInitializerProgram

open Turing CounterMachine
open BoundedMarkerProgram

noncomputable section

abbrev Instruction (numTags : Nat) :=
  FiniteTM0Path.Instruction (AlphabetSize numTags)

/-- Explicit finite-table action for one physical head move. -/
def moveAction {numTags : Nat} : Turing.Dir →
    FiniteTM0.Action (AlphabetSize numTags)
  | .left => .moveLeft
  | .right => .moveRight

@[simp]
theorem applyAction_moveAction {numTags : Nat} (direction : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) :
    FiniteTM0Path.applyAction (moveAction direction) T =
      T.move direction := by
  cases direction <;> rfl

/-- A guarded physical head move. -/
def moveInstruction {numTags : Nat} (expected : Symbol numTags)
    (direction : Turing.Dir) : Instruction numTags :=
  ⟨expected, moveAction direction⟩

/-- A guarded rewrite at the current head position. -/
def writeInstruction {numTags : Nat} (expected written : Symbol numTags) :
    Instruction numTags :=
  ⟨expected, .write written⟩

/-- Move from a known nonblank symbol across `gap` blank cells to the next
cell.  Thus the physical distance travelled is `gap + 1`. -/
def advance {numTags : Nat} (expected : Symbol numTags)
    (direction : Turing.Dir) (gap : Nat) : List (Instruction numTags) :=
  moveInstruction expected direction ::
    List.replicate gap (moveInstruction blankSymbol direction)

/-- The only nonzero register in the designated initial counter
configuration. -/
def inputGap (c : Nat.Partrec.Code) : Nat :=
  (StackEncoding.sourceInitialRegisters c).right

/-- Tag relocation followed by the five boundary writes, starting at the
original outer-search head. -/
def placementInstructions {numTags : Nat} (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags) :
    List (Instruction numTags) :=
  [writeInstruction blankSymbol (tagSymbol tag)] ++
    advance (tagSymbol tag) growth 0 ++
    [writeInstruction blankSymbol (boundarySymbol 0)] ++
    advance (boundarySymbol 0) growth 0 ++
    [writeInstruction blankSymbol (boundarySymbol 1)] ++
    advance (boundarySymbol 1) growth (inputGap c) ++
    [writeInstruction blankSymbol (boundarySymbol 2)] ++
    advance (boundarySymbol 2) growth 0 ++
    [writeInstruction blankSymbol (boundarySymbol 3)] ++
    advance (boundarySymbol 3) growth 0 ++
    [writeInstruction blankSymbol (boundarySymbol 4)]

/-- Straight-line initializer entered immediately after the far copy of the
tag has been cleared. -/
def instructions {numTags : Nat} (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags) :
    List (Instruction numTags) :=
  List.replicate (NestingMachine.bound (CanonicalInitializer.radius c))
      (moveInstruction blankSymbol (NestingMachine.opposite growth)) ++
    placementInstructions c growth tag

/-- Number of source states in one tag-specific initializer path. -/
def pathWidth (c : Nat.Partrec.Code) : Nat :=
  2 * CanonicalInitializer.span c + 7

@[simp]
theorem advance_length {numTags : Nat} (expected : Symbol numTags)
    (direction : Turing.Dir) (gap : Nat) :
    (advance expected direction gap).length = gap + 1 := by
  simp [advance]

@[simp]
theorem instructions_length {numTags : Nat} (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags) :
    (instructions c growth tag).length = pathWidth c := by
  simp [instructions, pathWidth, CanonicalInitializer.span,
    placementInstructions, CanonicalInitializer.radius,
    NestingMachine.bound, inputGap]
  omega

/-- One extra source state dispatches the completed path to the common
counter-program entry. -/
def tagBlockWidth (c : Nat.Partrec.Code) : Nat :=
  pathWidth c + 1

/-- First source state of one tag-specific path. -/
def pathOffset (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    {numTags : Nat} (tag : Fin numTags) : FiniteTM0.State :=
  sharedEntry + 1 + tag.val * tagBlockWidth c

/-- Source state that follows the last boundary write of one private path. -/
def pathExit (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    {numTags : Nat} (tag : Fin numTags) : FiniteTM0.State :=
  pathOffset sharedEntry c tag + pathWidth c

/-- Common entry of the anchored counter program after every tag-specific
initializer path. -/
def exitState (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (numTags : Nat) : FiniteTM0.State :=
  sharedEntry + 1 + numTags * tagBlockWidth c

/-- At the shared core entry, reading a physical return tag clears its far
copy and selects the corresponding private initializer path. -/
def dispatchTable (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (numTags : Nat) : FiniteTM0.Table (AlphabetSize numTags) :=
  (List.finRange numTags).map fun tag =>
    FiniteTM0.Rule.mk sharedEntry (tagSymbol tag)
      (pathOffset sharedEntry c tag) (.write blankSymbol)

/-- One private path and its final jump to the common anchored-program
entry. -/
def tagBlock (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    {numTags : Nat} (growth : Turing.Dir) (tag : Fin numTags) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  FiniteTM0Path.table (pathOffset sharedEntry c tag)
      (instructions c growth tag) ++
    [FiniteTM0.Rule.mk (pathExit sharedEntry c tag) (boundarySymbol 4)
      (exitState sharedEntry c numTags) (.write (boundarySymbol 4))]

/-- Complete shared initializer in one physical growth orientation. -/
def table (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (numTags : Nat) (growth : Turing.Dir) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  dispatchTable sharedEntry c numTags ++
    (List.finRange numTags).flatMap fun tag =>
      tagBlock sharedEntry c growth tag

/-! ## Exact tape semantics -/

/-- Head-relative tape after installing the tag and five boundaries.  The
head finishes on boundary `4`. -/
def resultTape {numTags : Nat} (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags)) : FullTM0.Tape (Symbol numTags) :=
  let T := T.write (tagSymbol tag)
  let T := (T.moveN growth 1).write (boundarySymbol 0)
  let T := (T.moveN growth 1).write (boundarySymbol 1)
  let T := (T.moveN growth (inputGap c + 1)).write (boundarySymbol 2)
  let T := (T.moveN growth 1).write (boundarySymbol 3)
  (T.moveN growth 1).write (boundarySymbol 4)

/-- Guarded path executions compose under list concatenation. -/
theorem executes_append {numTags : Nat}
    {first second : List (Instruction numTags)}
    {T U V : FullTM0.Tape (Symbol numTags)}
    (hfirst : FiniteTM0Path.Executes first T U)
    (hsecond : FiniteTM0Path.Executes second U V) :
    FiniteTM0Path.Executes (first ++ second) T V := by
  induction hfirst with
  | nil T => simpa using hsecond
  | cons instruction instructions T U hread hrest ih =>
      exact FiniteTM0Path.Executes.cons instruction
        (instructions ++ second) T V hread (ih hsecond)

/-- Repeating a guarded blank move executes as the corresponding finite head
translation. -/
theorem blankMoves_executes {numTags : Nat} (direction : Turing.Dir)
    (distance : Nat) (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ i < distance,
      (T.moveN direction i).read = blankSymbol) :
    FiniteTM0Path.Executes
      (List.replicate distance (moveInstruction blankSymbol direction))
      T (T.moveN direction distance) := by
  induction distance generalizing T with
  | zero =>
      simpa using FiniteTM0Path.Executes.nil T
  | succ distance ih =>
      rw [List.replicate_succ]
      apply FiniteTM0Path.Executes.cons
      · change T.read = blankSymbol
        simpa only [FullTM0.Tape.moveN_zero] using
          hblank 0 (Nat.zero_lt_succ distance)
      · have htail : ∀ i < distance,
            ((T.move direction).moveN direction i).read = blankSymbol := by
          intro i hi
          rw [FullTM0.Tape.move_moveN]
          exact hblank (i + 1) (Nat.succ_lt_succ hi)
        have htailExec := ih (T.move direction) htail
        rw [FullTM0.Tape.move_moveN] at htailExec
        change FiniteTM0Path.Executes
          (List.replicate distance
            (moveInstruction blankSymbol direction))
          (FiniteTM0Path.applyAction (moveAction direction) T)
          (T.moveN direction (distance + 1))
        rw [applyAction_moveAction]
        exact htailExec

/-- Move from a known symbol across a guarded blank gap. -/
theorem advance_executes {numTags : Nat} (expected : Symbol numTags)
    (direction : Turing.Dir) (gap : Nat)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = expected)
    (hblank : ∀ i < gap,
      ((T.move direction).moveN direction i).read = blankSymbol) :
    FiniteTM0Path.Executes (advance expected direction gap)
      T (T.moveN direction (gap + 1)) := by
  apply FiniteTM0Path.Executes.cons
  · exact hread
  · have htail := blankMoves_executes direction gap (T.move direction)
      hblank
    simpa [advance, moveInstruction,
      FullTM0.Tape.move_moveN] using htail

/-- One guarded rewrite is an exact one-instruction path. -/
theorem write_executes {numTags : Nat} (expected written : Symbol numTags)
    (T : FullTM0.Tape (Symbol numTags)) (hread : T.read = expected) :
    FiniteTM0Path.Executes [writeInstruction expected written]
      T (T.write written) := by
  apply FiniteTM0Path.Executes.cons
  · exact hread
  · exact FiniteTM0Path.Executes.nil _

/-- A write at the current head cannot affect a strictly positive move in
either direction. -/
theorem read_moveN_write_of_pos {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) (written : Symbol numTags)
    (direction : Turing.Dir) (distance : Nat) (hpositive : 0 < distance) :
    ((T.write written).moveN direction distance).read =
      (T.moveN direction distance).read := by
  rw [FullTM0.Tape.read_moveN, FullTM0.Tape.read_moveN]
  apply FullTM0.Tape.write_apply_of_ne
  cases direction <;>
    simp [FullTM0.Tape.offset] <;> omega

/-- On a blank canonical prefix, the placement suffix installs exactly the
tag and five labelled boundaries and finishes on boundary `4`. -/
theorem placement_executes {numTags : Nat} (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hblank : ∀ position ≤ CanonicalInitializer.span c,
      (T.moveN growth position).read = blankSymbol) :
    FiniteTM0Path.Executes (placementInstructions c growth tag)
      T (resultTape c growth tag T) := by
  let Ttag := T.write (tagSymbol tag)
  let T0 := (Ttag.moveN growth 1).write (boundarySymbol 0)
  let T1 := (T0.moveN growth 1).write (boundarySymbol 1)
  let T2 := (T1.moveN growth (inputGap c + 1)).write (boundarySymbol 2)
  let T3 := (T2.moveN growth 1).write (boundarySymbol 3)
  let T4 := (T3.moveN growth 1).write (boundarySymbol 4)
  have hreadStart : T.read = blankSymbol := by
    simpa only [FullTM0.Tape.moveN_zero] using
      hblank 0 (Nat.zero_le _)
  have htag : FiniteTM0Path.Executes
      [writeInstruction blankSymbol (tagSymbol tag)] T Ttag := by
    simpa [Ttag] using
      write_executes blankSymbol (tagSymbol tag) T hreadStart
  have hto0 : FiniteTM0Path.Executes
      (advance (tagSymbol tag) growth 0) Ttag (Ttag.moveN growth 1) := by
    apply advance_executes
    · simp [Ttag]
    · intro i hi
      omega
  have hread0 : (Ttag.moveN growth 1).read = blankSymbol := by
    rw [read_moveN_write_of_pos T (tagSymbol tag) growth 1 (by omega)]
    exact hblank 1 (by
      change 1 ≤ inputGap c + 5
      omega)
  have hwrite0 : FiniteTM0Path.Executes
      [writeInstruction blankSymbol (boundarySymbol 0)]
      (Ttag.moveN growth 1) T0 := by
    simpa [T0] using write_executes blankSymbol (boundarySymbol 0)
      (Ttag.moveN growth 1) hread0
  have hto1 : FiniteTM0Path.Executes
      (advance (boundarySymbol 0) growth 0) T0 (T0.moveN growth 1) := by
    apply advance_executes
    · simp [T0]
    · intro i hi
      omega
  have hread1 : (T0.moveN growth 1).read = blankSymbol := by
    rw [read_moveN_write_of_pos (Ttag.moveN growth 1)
      (boundarySymbol 0) growth 1 (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [read_moveN_write_of_pos T (tagSymbol tag) growth 2 (by omega)]
    exact hblank 2 (by
      change 2 ≤ inputGap c + 5
      omega)
  have hwrite1 : FiniteTM0Path.Executes
      [writeInstruction blankSymbol (boundarySymbol 1)]
      (T0.moveN growth 1) T1 := by
    simpa [T1] using write_executes blankSymbol (boundarySymbol 1)
      (T0.moveN growth 1) hread1
  have hto2 : FiniteTM0Path.Executes
      (advance (boundarySymbol 1) growth (inputGap c)) T1
      (T1.moveN growth (inputGap c + 1)) := by
    apply advance_executes
    · simp [T1]
    · intro i hi
      rw [FullTM0.Tape.move_moveN]
      rw [read_moveN_write_of_pos (T0.moveN growth 1)
        (boundarySymbol 1) growth (i + 1) (by omega)]
      rw [FullTM0.Tape.moveN_add]
      rw [show 1 + (i + 1) = i + 2 by omega]
      rw [read_moveN_write_of_pos (Ttag.moveN growth 1)
        (boundarySymbol 0) growth (i + 2) (by omega)]
      rw [FullTM0.Tape.moveN_add]
      rw [show 1 + (i + 2) = i + 3 by omega]
      rw [read_moveN_write_of_pos T (tagSymbol tag) growth (i + 3)
        (by omega)]
      exact hblank (i + 3) (by
        change i + 3 ≤ inputGap c + 5
        omega)
  have hread2 : (T1.moveN growth (inputGap c + 1)).read =
      blankSymbol := by
    rw [read_moveN_write_of_pos (T0.moveN growth 1)
      (boundarySymbol 1) growth (inputGap c + 1) (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show 1 + (inputGap c + 1) = inputGap c + 2 by omega]
    rw [read_moveN_write_of_pos (Ttag.moveN growth 1)
      (boundarySymbol 0) growth (inputGap c + 2) (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show 1 + (inputGap c + 2) = inputGap c + 3 by omega]
    rw [read_moveN_write_of_pos T (tagSymbol tag) growth
      (inputGap c + 3) (by omega)]
    exact hblank (inputGap c + 3) (by
      change inputGap c + 3 ≤ inputGap c + 5
      omega)
  have hwrite2 : FiniteTM0Path.Executes
      [writeInstruction blankSymbol (boundarySymbol 2)]
      (T1.moveN growth (inputGap c + 1)) T2 := by
    simpa [T2] using write_executes blankSymbol (boundarySymbol 2)
      (T1.moveN growth (inputGap c + 1)) hread2
  have hto3 : FiniteTM0Path.Executes
      (advance (boundarySymbol 2) growth 0) T2 (T2.moveN growth 1) := by
    apply advance_executes
    · simp [T2]
    · intro i hi
      omega
  have hread3 : (T2.moveN growth 1).read = blankSymbol := by
    rw [read_moveN_write_of_pos (T1.moveN growth (inputGap c + 1))
      (boundarySymbol 2) growth 1 (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show inputGap c + 1 + 1 = inputGap c + 2 by omega]
    rw [read_moveN_write_of_pos (T0.moveN growth 1)
      (boundarySymbol 1) growth (inputGap c + 2) (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show 1 + (inputGap c + 2) = inputGap c + 3 by omega]
    rw [read_moveN_write_of_pos (Ttag.moveN growth 1)
      (boundarySymbol 0) growth (inputGap c + 3) (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show 1 + (inputGap c + 3) = inputGap c + 4 by omega]
    rw [read_moveN_write_of_pos T (tagSymbol tag) growth
      (inputGap c + 4) (by omega)]
    exact hblank (inputGap c + 4) (by
      change inputGap c + 4 ≤ inputGap c + 5
      omega)
  have hwrite3 : FiniteTM0Path.Executes
      [writeInstruction blankSymbol (boundarySymbol 3)]
      (T2.moveN growth 1) T3 := by
    simpa [T3] using write_executes blankSymbol (boundarySymbol 3)
      (T2.moveN growth 1) hread3
  have hto4 : FiniteTM0Path.Executes
      (advance (boundarySymbol 3) growth 0) T3 (T3.moveN growth 1) := by
    apply advance_executes
    · simp [T3]
    · intro i hi
      omega
  have hread4 : (T3.moveN growth 1).read = blankSymbol := by
    rw [read_moveN_write_of_pos (T2.moveN growth 1)
      (boundarySymbol 3) growth 1 (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [read_moveN_write_of_pos (T1.moveN growth (inputGap c + 1))
      (boundarySymbol 2) growth 2 (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show inputGap c + 1 + 2 = inputGap c + 3 by omega]
    rw [read_moveN_write_of_pos (T0.moveN growth 1)
      (boundarySymbol 1) growth (inputGap c + 3) (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show 1 + (inputGap c + 3) = inputGap c + 4 by omega]
    rw [read_moveN_write_of_pos (Ttag.moveN growth 1)
      (boundarySymbol 0) growth (inputGap c + 4) (by omega)]
    rw [FullTM0.Tape.moveN_add]
    rw [show 1 + (inputGap c + 4) = inputGap c + 5 by omega]
    rw [read_moveN_write_of_pos T (tagSymbol tag) growth
      (inputGap c + 5) (by omega)]
    exact hblank (inputGap c + 5) (by
      change inputGap c + 5 ≤ inputGap c + 5
      exact Nat.le_refl _)
  have hwrite4 : FiniteTM0Path.Executes
      [writeInstruction blankSymbol (boundarySymbol 4)]
      (T3.moveN growth 1) T4 := by
    simpa [T4] using write_executes blankSymbol (boundarySymbol 4)
      (T3.moveN growth 1) hread4
  have hall := executes_append htag
    (executes_append hto0
      (executes_append hwrite0
        (executes_append hto1
          (executes_append hwrite1
            (executes_append hto2
              (executes_append hwrite2
                (executes_append hto3
                  (executes_append hwrite3
                    (executes_append hto4 hwrite4)))))))))
  simpa [placementInstructions, resultTape, Ttag, T0, T1, T2, T3, T4]
    using hall

/-- Equal-distance moves in opposite directions restore a full tape. -/
theorem moveN_opposite {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags))
    (direction : Turing.Dir) (distance : Nat) :
    (T.moveN direction distance).moveN
        (NestingMachine.opposite direction) distance = T := by
  funext position
  cases direction <;>
    simp [FullTM0.Tape.moveN, FullTM0.Tape.offset,
      NestingMachine.opposite]

/-- Rewriting the symbol already under the head leaves a full tape
unchanged. -/
theorem write_eq_self_of_read_eq {numTags : Nat}
    (T : FullTM0.Tape (Symbol numTags)) (symbol : Symbol numTags)
    (hread : T.read = symbol) : T.write symbol = T := by
  funext position
  by_cases hposition : position = 0
  · subst position
    simpa [FullTM0.Tape.read] using hread.symm
  · exact FullTM0.Tape.write_apply_of_ne symbol T hposition

/-- The complete private path clears the far tag, restores the outer-search
head, relocates the tag there, and installs the canonical marker core. -/
theorem instructions_executes_after_clear {numTags : Nat}
    (c : Nat.Partrec.Code) (command : Command numTags)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      command.target.Matches outer command.searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    FiniteTM0Path.Executes
      (instructions c command.searchDirection command.returnTag)
      ((taggedFrameTapeNative (CanonicalInitializer.radius c) command
        outer).write blankSymbol)
      (resultTape c command.searchDirection command.returnTag outer) := by
  let prefixLength := NestingMachine.bound (CanonicalInitializer.radius c)
  have hfarBlank :
      (outer.moveN command.searchDirection prefixLength).read = blankSymbol := by
    simpa [FullTM0.Tape.read] using hgap.blank hfar
  have hcleared :
      (taggedFrameTapeNative (CanonicalInitializer.radius c) command
        outer).write blankSymbol =
      outer.moveN command.searchDirection prefixLength := by
    change ((outer.moveN command.searchDirection prefixLength).write
      (tagSymbol command.returnTag)).write blankSymbol = _
    rw [show ((outer.moveN command.searchDirection prefixLength).write
        (tagSymbol command.returnTag)).write blankSymbol =
      (outer.moveN command.searchDirection prefixLength).write
        blankSymbol by
      funext position
      by_cases hposition : position = 0 <;>
        simp [FullTM0.Tape.write, hposition]]
    exact write_eq_self_of_read_eq
      (outer.moveN command.searchDirection prefixLength) blankSymbol hfarBlank
  have hretreatBlank : ∀ i < prefixLength,
      ((outer.moveN command.searchDirection prefixLength).moveN
        (NestingMachine.opposite command.searchDirection) i).read =
        blankSymbol := by
    intro i hi
    have hle : i ≤ prefixLength := Nat.le_of_lt hi
    have hremaining : prefixLength - i < distance := by omega
    have hblank := hgap.blank hremaining
    cases hdirection : command.searchDirection with
    | left =>
        rw [hdirection] at hblank
        simp only [NestingMachine.opposite_left, FullTM0.Tape.read_eq,
          FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_right, zero_add,
          FullTM0.Tape.offset_left] at hblank ⊢
        rw [Nat.cast_sub hle] at hblank
        convert hblank using 1
        all_goals ring_nf
    | right =>
        rw [hdirection] at hblank
        simp only [NestingMachine.opposite_right, FullTM0.Tape.read_eq,
          FullTM0.Tape.moveN_apply, FullTM0.Tape.offset_left, zero_add,
          FullTM0.Tape.offset_right] at hblank ⊢
        rw [Nat.cast_sub hle] at hblank
        convert hblank using 1
        all_goals ring_nf
  have hretreat := blankMoves_executes
    (NestingMachine.opposite command.searchDirection) prefixLength
    (outer.moveN command.searchDirection prefixLength) hretreatBlank
  rw [moveN_opposite] at hretreat
  have hprefixBlank : ∀ position ≤ CanonicalInitializer.span c,
      (outer.moveN command.searchDirection position).read = blankSymbol := by
    intro position hposition
    have hlt : position < distance := by
      have hspan : CanonicalInitializer.span c < prefixLength := by
        simp [prefixLength, CanonicalInitializer.radius, NestingMachine.bound]
      omega
    simpa [FullTM0.Tape.read] using hgap.blank hlt
  have hplace := placement_executes c command.searchDirection
    command.returnTag outer hprefixBlank
  rw [hcleared]
  simpa [instructions, prefixLength] using executes_append hretreat hplace

end

end CanonicalInitializerProgram
end Hooper
end Kari
end LeanWang
