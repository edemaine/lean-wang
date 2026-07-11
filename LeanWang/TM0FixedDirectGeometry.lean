/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FixedDirectProgram

/-!
# Folded-tape geometry for the direct fixed-TM0 simulation

This module contains only the semantic relation between Mathlib's two-sided
TM0 tape and the one-sided folded Post tape.  It deliberately has no dependency
on the generated position-coded compiler.
-/

namespace LeanWang
namespace TM0FixedDirectGeometry

open TM0Route TM0FoldedCompiler

def rightAbs (i : Nat) : Int := i

def leftAbs (i : Nat) : Int := -((i : Int) + 1)

def activeAbs : FoldSide → Nat → Int
  | FoldSide.right, h => rightAbs h
  | FoldSide.left, h => leftAbs h

def sourceOffset (side : FoldSide) (head : Nat) (abs : Int) : Int :=
  abs - activeAbs side head

def foldedCellOfTapeAt (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head i : Nat) : Nat :=
  foldedSymbolCode (decide (i = 0))
    (T.nth (sourceOffset side head (leftAbs i)))
    (T.nth (sourceOffset side head (rightAbs i)))

def FoldedTapeRel (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) (tape : Nat → Nat) : Prop :=
  ∀ i, tape i = foldedCellOfTapeAt T side head i

def FoldedConfigRel (tc : Turing.ToPartrec.Code)
    (cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)) (id : PostID) : Prop :=
  ∃ side : FoldSide,
    cfg.q ∈ partrecStartedTM0LabelList tc ∧
      id.state = some (foldedSimStateCode tc side cfg.q) ∧
      FoldedTapeRel cfg.Tape side id.head id.tape

@[simp] theorem sourceOffset_right_head (h : Nat) :
    sourceOffset FoldSide.right h (rightAbs h) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp] theorem sourceOffset_left_head (h : Nat) :
    sourceOffset FoldSide.left h (leftAbs h) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

theorem foldedRead_active_cell (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) :
    foldedRead side
        (T.nth (sourceOffset side head (leftAbs head)))
        (T.nth (sourceOffset side head (rightAbs head))) = T.head := by
  cases side <;> simp [foldedRead, Turing.Tape.nth_zero]

theorem sourceOffset_right_left_head_ne_zero (head : Nat) :
    sourceOffset FoldSide.right head (leftAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem sourceOffset_left_right_head_ne_zero (head : Nat) :
    sourceOffset FoldSide.left head (rightAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
theorem foldedCellOfTapeAt_write_active (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head : Nat) (new : SourceSymbol) :
    foldedCellOfTapeAt (T.write new) side head head =
      foldedWriteForStmt side (decide (head = 0)) new
        (T.nth (sourceOffset side head (leftAbs head)))
        (T.nth (sourceOffset side head (rightAbs head))) := by
  cases side
  · by_cases h : head = 0
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_left_head, sourceOffset_left_right_head_ne_zero, h]
      rfl
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_left_head, sourceOffset_left_right_head_ne_zero, h]
      rfl
  · by_cases h : head = 0
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_right_head, sourceOffset_right_left_head_ne_zero, h]
      rfl
    · simp [foldedCellOfTapeAt, foldedWriteForStmt, foldedWrite, foldedWriteMarked,
        sourceOffset_right_head, sourceOffset_right_left_head_ne_zero, h]
      rfl

theorem sourceOffset_left_ne_zero_of_ne_head
    (side : FoldSide) {head i : Nat} (h : i ≠ head) :
    sourceOffset side head (leftAbs i) ≠ 0 := by
  cases side
  · simp [sourceOffset, activeAbs, leftAbs]
    omega
  · simp [sourceOffset, activeAbs, leftAbs, rightAbs]
    omega

theorem sourceOffset_right_ne_zero_of_ne_head
    (side : FoldSide) {head i : Nat} (h : i ≠ head) :
    sourceOffset side head (rightAbs i) ≠ 0 := by
  cases side
  · simp [sourceOffset, activeAbs, rightAbs, leftAbs]
    omega
  · simp [sourceOffset, activeAbs, rightAbs]
    omega

theorem foldedCellOfTapeAt_write_inactive (T : Turing.Tape SourceSymbol)
    (side : FoldSide) {head i : Nat} (new : SourceSymbol) (h : i ≠ head) :
    foldedCellOfTapeAt (T.write new) side head i =
      foldedCellOfTapeAt T side head i := by
  have hleft := sourceOffset_left_ne_zero_of_ne_head side h
  have hright := sourceOffset_right_ne_zero_of_ne_head side h
  simp [foldedCellOfTapeAt, hleft, hright]

theorem FoldedTapeRel_write
    {T : Turing.Tape SourceSymbol} {side : FoldSide} {head : Nat} {tape : Nat → Nat}
    (new : SourceSymbol) (hrel : FoldedTapeRel T side head tape) :
    FoldedTapeRel (T.write new) side head
      (Function.update tape head
        (foldedWriteForStmt side (decide (head = 0)) new
          (T.nth (sourceOffset side head (leftAbs head)))
          (T.nth (sourceOffset side head (rightAbs head))))) := by
  intro i
  by_cases hi : i = head
  · subst i
    simp [Function.update_self, foldedCellOfTapeAt_write_active]
  · rw [Function.update_of_ne hi, hrel i]
    exact (foldedCellOfTapeAt_write_inactive T side new hi).symm

theorem activeAbs_foldedMoveHead
    (side : FoldSide) (head : Nat) (dir : Turing.Dir) :
    activeAbs (foldedMoveNextSide side (decide (head = 0)) dir)
        (foldedMoveHead side (decide (head = 0)) head dir) =
      activeAbs side head + match dir with
        | Turing.Dir.left => -1
        | Turing.Dir.right => 1 := by
  cases side <;> cases dir <;> by_cases h : head = 0
  all_goals
    subst_vars
    simp_all [foldedMoveNextSide, foldedMoveHead, activeAbs, leftAbs, rightAbs]
    try omega

theorem sourceOffset_foldedMoveHead
    (side : FoldSide) (head : Nat) (dir : Turing.Dir) (abs : Int) :
    sourceOffset (foldedMoveNextSide side (decide (head = 0)) dir)
        (foldedMoveHead side (decide (head = 0)) head dir) abs =
      sourceOffset side head abs - match dir with
        | Turing.Dir.left => -1
        | Turing.Dir.right => 1 := by
  unfold sourceOffset
  rw [activeAbs_foldedMoveHead]
  cases dir <;> omega

theorem foldedCellOfTapeAt_move (T : Turing.Tape SourceSymbol)
    (side : FoldSide) (head i : Nat) (dir : Turing.Dir) :
    foldedCellOfTapeAt (T.move dir)
        (foldedMoveNextSide side (decide (head = 0)) dir)
        (foldedMoveHead side (decide (head = 0)) head dir) i =
      foldedCellOfTapeAt T side head i := by
  cases dir <;> simp [foldedCellOfTapeAt, sourceOffset_foldedMoveHead]

theorem FoldedTapeRel_move
    {T : Turing.Tape SourceSymbol} {side : FoldSide} {head : Nat} {tape : Nat → Nat}
    (dir : Turing.Dir) (hrel : FoldedTapeRel T side head tape) :
    FoldedTapeRel (T.move dir)
      (foldedMoveNextSide side (decide (head = 0)) dir)
      (foldedMoveHead side (decide (head = 0)) head dir) tape := by
  intro i
  rw [hrel i, foldedCellOfTapeAt_move]

theorem foldedMoveStmt_applyStmt_head
    (side : FoldSide) (marked : Bool) (cell : Nat) (dir : Turing.Dir)
    (tape : Nat → Nat) (head : Nat) :
    (PostProgram.applyStmt (foldedMoveStmt side marked cell dir) tape head).2 =
      foldedMoveHead side marked head dir := by
  cases side <;> cases marked <;> cases dir <;>
    simp [foldedMoveStmt, foldedMoveHead, PostProgram.applyStmt, Move.apply]

theorem foldedMoveStmt_applyStmt_tape
    (side : FoldSide) (marked : Bool) (cell : Nat) (dir : Turing.Dir)
    {tape : Nat → Nat} {head : Nat} (hcell : tape head = cell) :
    (PostProgram.applyStmt (foldedMoveStmt side marked cell dir) tape head).1 = tape := by
  cases side <;> cases marked <;> cases dir <;>
    simp [foldedMoveStmt, PostProgram.applyStmt, hcell]

end TM0FixedDirectGeometry
end LeanWang
