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
code-dependent length and may jump to tag-specific continuations.
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

/-- One extra source state dispatches a completed path to its selected
continuation state. -/
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

/-- First fresh state after all initializer source states.  Tag-specific exit
targets may be allocated at or after this state. -/
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

/-- One private path and its final jump to a tag-specific continuation. -/
def tagBlock (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    {numTags : Nat} (growth : Turing.Dir) (tag : Fin numTags)
    (target : FiniteTM0.State) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  FiniteTM0Path.table (pathOffset sharedEntry c tag)
      (instructions c growth tag) ++
    [FiniteTM0.Rule.mk (pathExit sharedEntry c tag) (boundarySymbol 4)
      target (.write (boundarySymbol 4))]

/-- Complete shared initializer, retaining both its physical orientation and
its continuation state in the selected tag's finite-control block. -/
def table (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (numTags : Nat) (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State) :
    FiniteTM0.Table (AlphabetSize numTags) :=
  dispatchTable sharedEntry c numTags ++
    (List.finRange numTags).flatMap fun tag =>
      tagBlock sharedEntry c (growth tag) tag (exitFor tag)

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

private theorem reaches_of_step {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols}
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hstep : FullTM0.step (FiniteTM0.machine rules) start = some finish) :
    FullTM0.Reaches (FiniteTM0.machine rules) start finish :=
  Relation.ReflTransGen.single hstep

/-- The shared dispatcher has one distinct key for every physical return tag. -/
theorem dispatchTable_deterministic (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) (numTags : Nat) :
    FiniteTM0.Deterministic (dispatchTable sharedEntry c numTags) := by
  let dispatchKey := fun tag : Fin numTags =>
    (sharedEntry, tagSymbol tag)
  have hinjective : Function.Injective dispatchKey := by
    intro first second heq
    apply tagSymbol_injective
    exact congrArg Prod.snd heq
  have hmapped := (List.nodup_finRange numTags).map hinjective
  simpa [FiniteTM0.Deterministic, dispatchTable, FiniteTM0.Rule.mk,
    dispatchKey, List.map_map, Function.comp_def] using hmapped

/-- The dispatch rule for a selected tag occurs in the shared dispatcher. -/
theorem dispatchRule_mem (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) {numTags : Nat} (tag : Fin numTags) :
    FiniteTM0.Rule.mk sharedEntry (tagSymbol tag)
        (pathOffset sharedEntry c tag) (.write blankSymbol) ∈
      dispatchTable sharedEntry c numTags := by
  simp [dispatchTable]

/-- Reading a physical return tag clears it and selects its private path. -/
theorem dispatchTable_reaches_path (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) {numTags : Nat} (tag : Fin numTags)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = tagSymbol tag) :
    FullTM0.Reaches
      (FiniteTM0.machine (dispatchTable sharedEntry c numTags))
      ⟨sharedEntry, T⟩
      ⟨pathOffset sharedEntry c tag, T.write blankSymbol⟩ := by
  have hlookup :
      FiniteTM0.lookupAction (dispatchTable sharedEntry c numTags)
          sharedEntry (tagSymbol tag) =
        some (pathOffset sharedEntry c tag, .write blankSymbol) := by
    rw [FiniteTM0.lookupAction_eq_some_iff_of_deterministic
      (dispatchTable_deterministic sharedEntry c numTags)]
    exact dispatchRule_mem sharedEntry c tag
  apply reaches_of_step
  simp only [FullTM0.step]
  rw [hread]
  simp only [FiniteTM0.machine_apply, hlookup, Option.map_some,
    FiniteTM0.Action.toStmt_write]

/-- Every source state of one private block lies in its allocated half-open
state interval. -/
theorem source_mem_tagBlock {numTags : Nat}
    {sharedEntry source : FiniteTM0.State} {c : Nat.Partrec.Code}
    {growth : Turing.Dir} {tag : Fin numTags}
    {target : FiniteTM0.State}
    (hsource : source ∈ FiniteTM0.sourceStates
      (tagBlock sharedEntry c growth tag target)) :
    pathOffset sharedEntry c tag ≤ source ∧
      source < pathOffset sharedEntry c tag + tagBlockWidth c := by
  simp only [tagBlock, FiniteTM0.sourceStates, List.map_append,
    List.mem_append, List.map_singleton, List.mem_singleton,
    FiniteTM0.Rule.mk] at hsource
  rcases hsource with hpath | hfinish
  · have hbounds := FiniteTM0Path.source_mem_table hpath
    constructor
    · exact hbounds.1
    · have hupper := hbounds.2
      simp only [FiniteTM0Path.exitState, FiniteTM0Path.width,
        instructions_length] at hupper
      simp only [tagBlockWidth]
      exact hupper.trans
        (Nat.add_lt_add_left (Nat.lt_succ_self (pathWidth c)) _)
  · subst source
    constructor
    · simp [pathExit, pathWidth]
    · simp [pathExit, tagBlockWidth]

/-- The final source state of a private block is not owned by its compiled
straight-line prefix. -/
theorem path_final_source_disjoint {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (target : FiniteTM0.State) :
    List.Disjoint
      (FiniteTM0.sourceStates
        (FiniteTM0Path.table (pathOffset sharedEntry c tag)
          (instructions c growth tag)))
      (FiniteTM0.sourceStates
        [FiniteTM0.Rule.mk (pathExit sharedEntry c tag)
          (boundarySymbol (numTags := numTags) 4)
          target
          (.write (boundarySymbol (numTags := numTags) 4))]) := by
  rw [List.disjoint_iff_ne]
  intro first hfirst second hsecond heq
  have hbounds := FiniteTM0Path.source_mem_table hfirst
  have hsecondEq : second = pathExit sharedEntry c tag := by
    simpa [FiniteTM0.sourceStates, FiniteTM0.Rule.mk] using hsecond
  have hupper : first < pathExit sharedEntry c tag := by
    simpa [FiniteTM0Path.exitState, FiniteTM0Path.width,
      pathExit, instructions_length] using hbounds.2
  exact (Nat.ne_of_lt hupper) (heq.trans hsecondEq)

/-- One private initializer block is deterministic. -/
theorem tagBlock_deterministic {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (target : FiniteTM0.State) :
    FiniteTM0.Deterministic (tagBlock sharedEntry c growth tag target) := by
  simp only [tagBlock, FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append
    (FiniteTM0Path.table_deterministic _ _) (by simp)
  rw [List.disjoint_iff_ne]
  intro first hfirst second hsecond heq
  have hsourceFirst : first.1 ∈ FiniteTM0.sourceStates
      (FiniteTM0Path.table (pathOffset sharedEntry c tag)
        (instructions c growth tag)) := by
    rcases List.mem_map.mp hfirst with ⟨rule, hrule, hkey⟩
    exact List.mem_map.mpr ⟨rule, hrule, congrArg Prod.fst hkey⟩
  have hsourceSecond : second.1 ∈ FiniteTM0.sourceStates
      [FiniteTM0.Rule.mk (pathExit sharedEntry c tag)
        (boundarySymbol (numTags := numTags) 4)
        target
        (.write (boundarySymbol (numTags := numTags) 4))] := by
    rcases List.mem_map.mp hsecond with ⟨rule, hrule, hkey⟩
    exact List.mem_map.mpr ⟨rule, hrule, congrArg Prod.fst hkey⟩
  exact (List.disjoint_iff_ne.mp
    (path_final_source_disjoint sharedEntry c growth tag target))
      first.1 hsourceFirst second.1 hsourceSecond (congrArg Prod.fst heq)

/-- Private blocks for distinct tags occupy disjoint state intervals. -/
theorem tagBlock_sourceStates_disjoint_of_ne {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (firstGrowth secondGrowth : Turing.Dir)
    (firstTarget secondTarget : FiniteTM0.State)
    {first second : Fin numTags}
    (hne : first ≠ second) :
    List.Disjoint
      (FiniteTM0.sourceStates
        (tagBlock sharedEntry c firstGrowth first firstTarget))
      (FiniteTM0.sourceStates
        (tagBlock sharedEntry c secondGrowth second secondTarget)) := by
  rw [List.disjoint_iff_ne]
  intro firstState hfirst secondState hsecond heq
  have hfirstBounds := source_mem_tagBlock hfirst
  have hsecondBounds := source_mem_tagBlock hsecond
  have hval : first.val ≠ second.val := by
    intro h
    apply hne
    exact Fin.ext h
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · have hmul := Nat.mul_le_mul_right (tagBlockWidth c)
        (Nat.succ_le_of_lt hlt)
    have hseparate :
        pathOffset sharedEntry c first + tagBlockWidth c ≤
          pathOffset sharedEntry c second := by
      simpa [pathOffset, Nat.succ_mul, Nat.add_assoc] using
        Nat.add_le_add_left hmul (sharedEntry + 1)
    subst secondState
    exact (Nat.not_lt_of_ge (hseparate.trans hsecondBounds.1))
      hfirstBounds.2
  · have hmul := Nat.mul_le_mul_right (tagBlockWidth c)
        (Nat.succ_le_of_lt hgt)
    have hseparate :
        pathOffset sharedEntry c second + tagBlockWidth c ≤
          pathOffset sharedEntry c first := by
      simpa [pathOffset, Nat.succ_mul, Nat.add_assoc] using
        Nat.add_le_add_left hmul (sharedEntry + 1)
    subst secondState
    exact (Nat.not_lt_of_ge (hseparate.trans hfirstBounds.1))
      hsecondBounds.2

/-- The shared dispatch state precedes every private block. -/
theorem dispatch_tagBlock_sourceStates_disjoint {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (target : FiniteTM0.State) :
    List.Disjoint
      (FiniteTM0.sourceStates (dispatchTable sharedEntry c numTags))
      (FiniteTM0.sourceStates
        (tagBlock sharedEntry c growth tag target)) := by
  rw [List.disjoint_iff_ne]
  intro dispatchState hdispatch blockState hblock heq
  have hdispatchEq : dispatchState = sharedEntry := by
    simp only [dispatchTable, FiniteTM0.sourceStates, List.map_map,
      List.mem_map, FiniteTM0.Rule.mk, Function.comp_apply] at hdispatch
    rcases hdispatch with ⟨returnTag, -, hstate⟩
    exact hstate.symm
  have hblockBounds := source_mem_tagBlock hblock
  rw [hdispatchEq] at heq
  subst blockState
  have hlower : sharedEntry + 1 ≤
      pathOffset sharedEntry c tag := by
    simp [pathOffset]
  exact (Nat.not_succ_le_self sharedEntry)
    (hlower.trans hblockBounds.1)

private theorem key_mem_sourceStates {numSymbols : Nat}
    {rules : FiniteTM0.Table numSymbols} {key : FiniteTM0.Key numSymbols}
    (hkey : key ∈ rules.map Prod.fst) :
    key.1 ∈ FiniteTM0.sourceStates rules := by
  rcases List.mem_map.mp hkey with ⟨rule, hrule, hkey⟩
  exact List.mem_map.mpr ⟨rule, hrule, congrArg Prod.fst hkey⟩

private theorem deterministic_append_of_source_disjoint {numSymbols : Nat}
    {first second : FiniteTM0.Table numSymbols}
    (hfirst : FiniteTM0.Deterministic first)
    (hsecond : FiniteTM0.Deterministic second)
    (hdisjoint : List.Disjoint (FiniteTM0.sourceStates first)
      (FiniteTM0.sourceStates second)) :
    FiniteTM0.Deterministic (first ++ second) := by
  simp only [FiniteTM0.Deterministic, List.map_append]
  apply List.Nodup.append hfirst hsecond
  rw [List.disjoint_iff_ne]
  intro firstKey hfirstKey secondKey hsecondKey heq
  exact (List.disjoint_iff_ne.mp hdisjoint)
    firstKey.1 (key_mem_sourceStates hfirstKey)
    secondKey.1 (key_mem_sourceStates hsecondKey)
    (congrArg Prod.fst heq)

private theorem sourceStates_flatMap {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (tags : List (Fin numTags)) :
    FiniteTM0.sourceStates
        (tags.flatMap fun tag =>
          tagBlock sharedEntry c (growth tag) tag (exitFor tag)) =
      tags.flatMap fun tag =>
        FiniteTM0.sourceStates
          (tagBlock sharedEntry c (growth tag) tag (exitFor tag)) := by
  simp only [FiniteTM0.sourceStates, List.map_flatMap]

/-- Any list of distinct tags compiles to pairwise state-disjoint private
blocks. -/
theorem tagBlocks_deterministic {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (tags : List (Fin numTags))
    (htags : tags.Nodup) :
    FiniteTM0.Deterministic
      (tags.flatMap fun tag =>
        tagBlock sharedEntry c (growth tag) tag (exitFor tag)) := by
  induction tags with
  | nil => simp [FiniteTM0.Deterministic]
  | cons tag tags ih =>
      simp only [List.nodup_cons] at htags
      simp only [List.flatMap_cons]
      apply deterministic_append_of_source_disjoint
        (tagBlock_deterministic sharedEntry c (growth tag) tag (exitFor tag))
        (ih htags.2)
      rw [List.disjoint_iff_ne]
      intro firstState hfirst secondState hsecond heq
      rw [sourceStates_flatMap sharedEntry c growth exitFor tags] at hsecond
      rcases List.mem_flatMap.mp hsecond with
        ⟨secondTag, hsecondTag, hsecondSource⟩
      have hne : tag ≠ secondTag := by
        intro h
        apply htags.1
        simpa [h] using hsecondTag
      exact (List.disjoint_iff_ne.mp
        (tagBlock_sourceStates_disjoint_of_ne sharedEntry c
          (growth tag) (growth secondTag)
          (exitFor tag) (exitFor secondTag) hne))
          firstState hfirst secondState hsecondSource heq

/-- The dispatcher is source-disjoint from a concatenation of private
blocks. -/
theorem dispatch_tagBlocks_sourceStates_disjoint {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (tags : List (Fin numTags)) :
    List.Disjoint
      (FiniteTM0.sourceStates (dispatchTable sharedEntry c numTags))
      (FiniteTM0.sourceStates
        (tags.flatMap fun tag =>
          tagBlock sharedEntry c (growth tag) tag (exitFor tag))) := by
  rw [List.disjoint_iff_ne]
  intro dispatchState hdispatch blockState hblock heq
  rw [sourceStates_flatMap sharedEntry c growth exitFor tags] at hblock
  rcases List.mem_flatMap.mp hblock with ⟨tag, -, htag⟩
  exact (List.disjoint_iff_ne.mp
    (dispatch_tagBlock_sourceStates_disjoint sharedEntry c
      (growth tag) tag (exitFor tag)))
      dispatchState hdispatch blockState htag heq

/-- The complete shared initializer has no duplicate transition keys. -/
theorem table_deterministic (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) (numTags : Nat)
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State) :
    FiniteTM0.Deterministic
      (table sharedEntry c numTags growth exitFor) := by
  apply deterministic_append_of_source_disjoint
    (dispatchTable_deterministic sharedEntry c numTags)
    (tagBlocks_deterministic sharedEntry c growth exitFor
      (List.finRange numTags) (List.nodup_finRange numTags))
  exact dispatch_tagBlocks_sourceStates_disjoint sharedEntry c
    growth exitFor _

/-- Every source state of the complete initializer lies in the half-open
interval from the shared dispatcher to the first fresh state. -/
theorem source_mem_table {sharedEntry source : FiniteTM0.State}
    {c : Nat.Partrec.Code} {numTags : Nat}
    {growth : Fin numTags → Turing.Dir}
    {exitFor : Fin numTags → FiniteTM0.State}
    (hsource : source ∈ FiniteTM0.sourceStates
      (table sharedEntry c numTags growth exitFor)) :
    sharedEntry ≤ source ∧ source < exitState sharedEntry c numTags := by
  simp only [table, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hsource
  rcases hsource with hdispatch | hblocks
  · have hsourceEq : source = sharedEntry := by
      simp only [dispatchTable, List.map_map,
        List.mem_map, FiniteTM0.Rule.mk, Function.comp_apply] at hdispatch
      rcases hdispatch with ⟨tag, -, heq⟩
      exact heq.symm
    subst source
    constructor
    · exact Nat.le_refl _
    · simpa [exitState] using
        (Nat.lt_succ_self sharedEntry).trans_le
          (Nat.le_add_right (sharedEntry + 1)
            (numTags * tagBlockWidth c))
  · change source ∈ FiniteTM0.sourceStates
        ((List.finRange numTags).flatMap fun tag =>
          tagBlock sharedEntry c (growth tag) tag (exitFor tag)) at hblocks
    rw [sourceStates_flatMap sharedEntry c growth exitFor
        (List.finRange numTags)] at hblocks
    rcases List.mem_flatMap.mp hblocks with
      ⟨tag, -, htag⟩
    have hbounds := source_mem_tagBlock htag
    constructor
    · have hlower : sharedEntry ≤ pathOffset sharedEntry c tag := by
        rw [pathOffset]
        exact (Nat.le_add_right sharedEntry 1).trans
          (Nat.le_add_right (sharedEntry + 1)
            (tag.val * tagBlockWidth c))
      exact hlower.trans hbounds.1
    · have hmul := Nat.mul_le_mul_right (tagBlockWidth c)
          (Nat.succ_le_of_lt tag.isLt)
      have hseparate :
          pathOffset sharedEntry c tag + tagBlockWidth c ≤
            exitState sharedEntry c numTags := by
        simpa [pathOffset, exitState, Nat.succ_mul, Nat.add_assoc] using
          Nat.add_le_add_left hmul (sharedEntry + 1)
      exact hbounds.2.trans_le hseparate

/-- Lookup in a fixed generated initializer table is computable. -/
theorem table_lookup_computable (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) (numTags : Nat)
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State) :
    Computable fun input : FiniteTM0.Key (AlphabetSize numTags) =>
      FiniteTM0.lookupAction (table sharedEntry c numTags growth exitFor)
        input.1 input.2 :=
  (FiniteTM0.lookupAction_computable
    (numSymbols := AlphabetSize numTags)).comp
    ((Computable.const (table sharedEntry c numTags growth exitFor)).pair
      Computable.id)

private theorem step_mono_of_deterministic_superset {numSymbols : Nat}
    {small large : FiniteTM0.Table numSymbols}
    (hdet : FiniteTM0.Deterministic large)
    (hsubset : ∀ rule ∈ small, rule ∈ large)
    {current next :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hstep : FullTM0.step (FiniteTM0.machine small) current = some next) :
    FullTM0.step (FiniteTM0.machine large) current = some next := by
  simp only [FullTM0.step, FiniteTM0.machine,
    FullTM0.Tape.read_eq] at hstep ⊢
  cases hlookup : FiniteTM0.lookupAction small current.q (current.tape 0) with
  | none => simp [hlookup] at hstep
  | some result =>
      rcases result with ⟨target, action⟩
      have hrule := FiniteTM0.rule_mem_of_lookupAction_eq_some hlookup
      have hlarge : FiniteTM0.lookupAction large current.q (current.tape 0) =
          some (target, action) := by
        rw [FiniteTM0.lookupAction_eq_some_iff_of_deterministic hdet]
        exact hsubset _ hrule
      rw [hlarge]
      simpa [hlookup] using hstep

private theorem reaches_mono_of_deterministic_superset {numSymbols : Nat}
    {small large : FiniteTM0.Table numSymbols}
    (hdet : FiniteTM0.Deterministic large)
    (hsubset : ∀ rule ∈ small, rule ∈ large)
    {start finish :
      FullTM0.Cfg (FiniteTM0.Symbol numSymbols) FiniteTM0.State}
    (hreach : FullTM0.Reaches (FiniteTM0.machine small) start finish) :
    FullTM0.Reaches (FiniteTM0.machine large) start finish := by
  apply Relation.ReflTransGen.mono ?_ hreach
  intro current next hstep
  exact step_mono_of_deterministic_superset hdet hsubset hstep

/-- The dispatch execution embeds in the complete initializer table. -/
theorem table_reaches_path (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) {numTags : Nat}
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (tag : Fin numTags) (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = tagSymbol tag) :
    FullTM0.Reaches
      (FiniteTM0.machine (table sharedEntry c numTags growth exitFor))
      ⟨sharedEntry, T⟩
      ⟨pathOffset sharedEntry c tag, T.write blankSymbol⟩ := by
  apply reaches_mono_of_deterministic_superset
    (table_deterministic sharedEntry c numTags growth exitFor) ?_
    (dispatchTable_reaches_path sharedEntry c tag T hread)
  intro rule hrule
  exact List.mem_append_left _ hrule

/-- A successful guarded initializer path, followed by its final preserving
jump, reaches its selected continuation state. -/
theorem tagBlock_reaches_exit {numTags : Nat}
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (tag : Fin numTags)
    (target : FiniteTM0.State)
    {T U : FullTM0.Tape (Symbol numTags)}
    (hexec : FiniteTM0Path.Executes (instructions c growth tag) T U)
    (hread : U.read = boundarySymbol 4) :
    FullTM0.Reaches
      (FiniteTM0.machine (tagBlock sharedEntry c growth tag target))
      ⟨pathOffset sharedEntry c tag, T⟩
      ⟨target, U⟩ := by
  let pathRules := FiniteTM0Path.table (pathOffset sharedEntry c tag)
    (instructions c growth tag)
  let finish : FiniteTM0.Table (AlphabetSize numTags) :=
    [FiniteTM0.Rule.mk (pathExit sharedEntry c tag) (boundarySymbol 4)
      target (.write (boundarySymbol 4))]
  have hprefixLocal :=
    FiniteTM0Path.executes_reaches (pathOffset sharedEntry c tag) hexec
  have hprefix : FullTM0.Reaches (FiniteTM0.machine (pathRules ++ finish))
      ⟨pathOffset sharedEntry c tag, T⟩
      ⟨pathExit sharedEntry c tag, U⟩ := by
    apply FiniteTM0Path.reaches_append_left
    simpa [pathRules, FiniteTM0Path.exitState, FiniteTM0Path.width,
      pathExit, instructions_length] using hprefixLocal
  have hfinishLocal : FullTM0.Reaches (FiniteTM0.machine finish)
      ⟨pathExit sharedEntry c tag, U⟩
      ⟨target, U.write (boundarySymbol 4)⟩ := by
    have hread0 : U 0 = boundarySymbol 4 := by
      simpa [FullTM0.Tape.read] using hread
    apply reaches_of_step
    simp [finish, FullTM0.step, FiniteTM0.machine,
      FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
      FullTM0.Tape.read_eq, hread0]
  have hfinish : FullTM0.Reaches (FiniteTM0.machine (pathRules ++ finish))
      ⟨pathExit sharedEntry c tag, U⟩
      ⟨target, U.write (boundarySymbol 4)⟩ := by
    apply FiniteTM0Path.reaches_append_right_of_source_disjoint
    · simpa [pathRules, finish] using
        path_final_source_disjoint sharedEntry c growth tag target
    · exact hfinishLocal
  have hall := hprefix.trans hfinish
  rw [write_eq_self_of_read_eq U (boundarySymbol 4) hread] at hall
  change Relation.ReflTransGen
    (fun current next =>
      next ∈ FullTM0.step
        (FiniteTM0.machine (tagBlock sharedEntry c growth tag target)) current)
    ⟨pathOffset sharedEntry c tag, T⟩
    ⟨target, U⟩
  simpa only [tagBlock, pathRules, finish] using hall

/-- A selected private block execution embeds in the complete initializer
table. -/
theorem table_reaches_exit_of_executes (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) {numTags : Nat}
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (tag : Fin numTags) {T U : FullTM0.Tape (Symbol numTags)}
    (hexec : FiniteTM0Path.Executes
      (instructions c (growth tag) tag) T U)
    (hread : U.read = boundarySymbol 4) :
    FullTM0.Reaches
      (FiniteTM0.machine (table sharedEntry c numTags growth exitFor))
      ⟨pathOffset sharedEntry c tag, T⟩
      ⟨exitFor tag, U⟩ := by
  apply reaches_mono_of_deterministic_superset
    (table_deterministic sharedEntry c numTags growth exitFor) ?_
    (tagBlock_reaches_exit sharedEntry c (growth tag) tag
      (exitFor tag) hexec hread)
  intro rule hrule
  apply List.mem_append_right
  exact List.mem_flatMap.mpr
    ⟨tag, List.mem_finRange tag, hrule⟩

/-- Dispatch and a successful selected private path compose inside the same
complete initializer table. -/
theorem table_reaches_exit (sharedEntry : FiniteTM0.State)
    (c : Nat.Partrec.Code) {numTags : Nat}
    (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (tag : Fin numTags) {T U : FullTM0.Tape (Symbol numTags)}
    (htag : T.read = tagSymbol tag)
    (hexec : FiniteTM0Path.Executes (instructions c (growth tag) tag)
      (T.write blankSymbol) U)
    (hboundary : U.read = boundarySymbol 4) :
    FullTM0.Reaches
      (FiniteTM0.machine (table sharedEntry c numTags growth exitFor))
      ⟨sharedEntry, T⟩
      ⟨exitFor tag, U⟩ := by
  exact (table_reaches_path sharedEntry c growth exitFor tag T htag).trans
    (table_reaches_exit_of_executes sharedEntry c growth exitFor tag
      hexec hboundary)

/-- A failed bounded search can enter the complete initializer at its shared
tag dispatcher and reach the exact canonical initialized tape at the selected
continuation state. -/
theorem table_reaches_resultTape_after_failed_search
    (sharedEntry : FiniteTM0.State) (c : Nat.Partrec.Code)
    {numTags : Nat} (growth : Fin numTags → Turing.Dir)
    (exitFor : Fin numTags → FiniteTM0.State)
    (command : Command numTags)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgrowth : growth command.returnTag = command.searchDirection)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      command.target.Matches outer command.searchDirection distance)
    (hfar : NestingMachine.bound (CanonicalInitializer.radius c) < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine
        (table sharedEntry c numTags growth exitFor))
      ⟨sharedEntry,
        taggedFrameTapeNative (CanonicalInitializer.radius c) command outer⟩
      ⟨exitFor command.returnTag,
        resultTape c command.searchDirection command.returnTag outer⟩ := by
  apply table_reaches_exit sharedEntry c growth exitFor command.returnTag
  · simp [taggedFrameTapeNative]
  · simpa [hgrowth] using
      instructions_executes_after_clear c command outer distance hgap hfar
  · simp [resultTape]

end

end CanonicalInitializerProgram
end Hooper
end Kari
end LeanWang
