/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.UniversalTM0TableauDynamics

/-!
# Semantic folded rows for the direct TM0 tableau
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Tableau

open UniversalTM0Semantic

def rightAbs (i : Nat) : Int := i

def leftAbs (i : Nat) : Int := -((i : Int) + 1)

def activeAbs : Side → Nat → Int
  | .right, head => rightAbs head
  | .left, head => leftAbs head

def sourceOffset (side : Side) (head : Nat) (absolute : Int) : Int :=
  absolute - activeAbs side head

def nextSide (side : Side) (atOrigin : Bool) (dir : Turing.Dir) : Side :=
  if atOrigin && side.isInward dir then side.opposite else side

def moveHead (side : Side) (atOrigin : Bool) (head : Nat)
    (dir : Turing.Dir) : Nat :=
  if atOrigin && side.isInward dir then head
  else if side.isOutward dir then head + 1
  else head.pred

theorem nextSide_of_head_ne_zero (side : Side) {head : Nat}
    (hhead : head ≠ 0) (dir : Turing.Dir) :
    nextSide side (decide (head = 0)) dir = side := by
  simp [nextSide, hhead]

theorem moveHead_eq_zero_iff_of_head_ne_zero (side : Side) {head : Nat}
    (hhead : head ≠ 0) (dir : Turing.Dir) :
    moveHead side (decide (head = 0)) head dir = 0 ↔
      side.isInward dir ∧ head = 1 := by
  cases side <;> cases dir <;>
    simp [moveHead, Side.isInward, Side.isOutward, hhead] <;> omega

theorem zero_eq_moveHead_iff_of_head_ne_zero (side : Side) {head : Nat}
    (hhead : head ≠ 0) (dir : Turing.Dir) :
    0 = moveHead side (decide (head = 0)) head dir ↔
      side.isInward dir ∧ head = 1 := by
  rw [eq_comm, moveHead_eq_zero_iff_of_head_ne_zero side hhead dir]

structure Config where
  source : Turing.TM0.Cfg Symbol Label
  side : Side
  head : Nat

def Config.afterWrite (config : Config) (q' : Label) (symbol : Symbol) : Config :=
  { source := { q := q', Tape := config.source.Tape.write symbol }
    side := config.side
    head := config.head }

def Config.afterMove (config : Config) (q' : Label) (dir : Turing.Dir) : Config :=
  { source := { q := q', Tape := config.source.Tape.move dir }
    side := nextSide config.side (decide (config.head = 0)) dir
    head := moveHead config.side (decide (config.head = 0)) config.head dir }

def Config.step (config : Config) : Option Config :=
  match tm0 config.source.q config.source.Tape.head with
  | none => none
  | some (q', .write symbol) => some (config.afterWrite q' symbol)
  | some (q', .move dir) => some (config.afterMove q' dir)

def Config.initial (input : List Symbol) : Config where
  source := Turing.TM0.init input
  side := .right
  head := 0

def symbolsAt (tape : Turing.Tape Symbol) (side : Side)
    (head position : Nat) : Symbol × Symbol :=
  (tape.nth (sourceOffset side head (leftAbs position)),
    tape.nth (sourceOffset side head (rightAbs position)))

def Config.cellAt (config : Config) (position : Nat) : Cell :=
  let symbols := symbolsAt config.source.Tape config.side config.head position
  { left := symbols.1
    right := symbols.2
    head := if position = config.head then some (config.side, config.source.q) else none }

def Config.cellAtLeft (config : Config) (position : Nat) : Cell :=
  match position with
  | 0 => blankCell
  | position + 1 => config.cellAt position

@[simp] theorem sourceOffset_right_head (head : Nat) :
    sourceOffset .right head (rightAbs head) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp] theorem sourceOffset_left_head (head : Nat) :
    sourceOffset .left head (leftAbs head) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

theorem cellAt_activeSymbol (config : Config) :
    (config.cellAt config.head).activeSymbol config.side = config.source.Tape.head := by
  rcases config with ⟨source, side, head⟩
  cases side <;> simp [Config.cellAt, symbolsAt, Cell.activeSymbol]

@[simp] theorem cellAt_head (config : Config) :
    (config.cellAt config.head).head = some (config.side, config.source.q) := by
  simp [Config.cellAt]

theorem cellAt_head_eq_none {config : Config} {position : Nat}
    (h : position ≠ config.head) : (config.cellAt position).head = none := by
  simp [Config.cellAt, h]

theorem cellAt_withHead_none_of_ne {config : Config} {position : Nat}
    (h : position ≠ config.head) :
    (config.cellAt position).withHead none = config.cellAt position := by
  cases hcell : config.cellAt position with
  | mk left right head =>
      have hhead : head = none := by
        simpa [hcell] using cellAt_head_eq_none h
      subst head
      rfl

theorem activeAbs_moveHead (side : Side) (head : Nat) (dir : Turing.Dir) :
    activeAbs (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) =
      activeAbs side head + match dir with
      | .left => -1
      | .right => 1 := by
  cases side <;> cases dir <;> by_cases h : head = 0
  all_goals subst_vars
  all_goals simp_all [nextSide, moveHead, Side.isInward, Side.isOutward,
    Side.opposite, activeAbs, leftAbs, rightAbs]
  all_goals try omega

theorem sourceOffset_moveHead (side : Side) (head : Nat) (dir : Turing.Dir)
    (absolute : Int) :
    sourceOffset (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) absolute =
      sourceOffset side head absolute - match dir with
      | .left => -1
      | .right => 1 := by
  unfold sourceOffset
  rw [activeAbs_moveHead]
  cases dir <;> omega

theorem symbolsAt_move (tape : Turing.Tape Symbol) (side : Side)
    (head position : Nat) (dir : Turing.Dir) :
    symbolsAt (tape.move dir)
        (nextSide side (decide (head = 0)) dir)
        (moveHead side (decide (head = 0)) head dir) position =
      symbolsAt tape side head position := by
  cases dir <;> simp [symbolsAt, sourceOffset_moveHead]

theorem sourceOffset_left_ne_zero_of_ne_head
    (side : Side) {head position : Nat} (h : position ≠ head) :
    sourceOffset side head (leftAbs position) ≠ 0 := by
  cases side <;> simp [sourceOffset, activeAbs, leftAbs, rightAbs] <;> omega

theorem sourceOffset_right_ne_zero_of_ne_head
    (side : Side) {head position : Nat} (h : position ≠ head) :
    sourceOffset side head (rightAbs position) ≠ 0 := by
  cases side <;> simp [sourceOffset, activeAbs, leftAbs, rightAbs] <;> omega

theorem symbolsAt_write_inactive (tape : Turing.Tape Symbol) (side : Side)
    {head position : Nat} (symbol : Symbol) (h : position ≠ head) :
    symbolsAt (tape.write symbol) side head position =
      symbolsAt tape side head position := by
  simp [symbolsAt, sourceOffset_left_ne_zero_of_ne_head side h,
    sourceOffset_right_ne_zero_of_ne_head side h]

theorem sourceOffset_right_left_head_ne_zero (head : Nat) :
    sourceOffset .right head (leftAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem sourceOffset_left_right_head_ne_zero (head : Nat) :
    sourceOffset .left head (rightAbs head) ≠ 0 := by
  simp [sourceOffset, activeAbs, rightAbs, leftAbs]
  omega

theorem symbolsAt_write_active (tape : Turing.Tape Symbol) (side : Side)
    (head : Nat) (symbol : Symbol) :
    symbolsAt (tape.write symbol) side head head =
      match side with
      | .left => (symbol, (symbolsAt tape side head head).2)
      | .right => ((symbolsAt tape side head head).1, symbol) := by
  cases side with
  | left =>
      simp only [symbolsAt, sourceOffset_left_head, Turing.Tape.write_nth,
        if_pos, Prod.mk.injEq, true_and]
      rw [if_neg (sourceOffset_left_right_head_ne_zero head)]
  | right =>
      simp only [symbolsAt, sourceOffset_right_head, Turing.Tape.write_nth,
        if_pos, Prod.mk.injEq, and_true]
      rw [if_neg (sourceOffset_right_left_head_ne_zero head)]

theorem Config.cellAt_afterWrite (config : Config) (q' : Label)
    (symbol : Symbol) (position : Nat) :
    (config.afterWrite q' symbol).cellAt position =
      if position = config.head then
        ((config.cellAt position).writeActive config.side symbol).withHead
          (some (config.side, q'))
      else config.cellAt position := by
  by_cases hposition : position = config.head
  · subst position
    simp only [if_pos, Config.cellAt, Config.afterWrite]
    rw [symbolsAt_write_active]
    cases config.side <;> rfl
  · simp only [if_neg hposition, Config.cellAt, Config.afterWrite]
    rw [symbolsAt_write_inactive _ _ _ hposition]

theorem Config.cellAt_afterMove (config : Config) (q' : Label)
    (dir : Turing.Dir) (position : Nat) :
    (config.afterMove q' dir).cellAt position =
      (config.cellAt position).withHead
        (if position = moveHead config.side (decide (config.head = 0)) config.head dir then
          some (nextSide config.side (decide (config.head = 0)) dir, q')
        else none) := by
  unfold Config.cellAt Config.afterMove
  rw [symbolsAt_move]
  rfl

theorem Config.step_source {config next : Config}
    (hstep : config.step = some next) :
    Turing.TM0.step tm0 config.source = some next.source := by
  unfold Config.step at hstep
  cases hm : tm0 config.source.q config.source.Tape.head with
  | none => simp [hm] at hstep
  | some result =>
      rcases result with ⟨q', stmt⟩
      cases stmt <;> simp [hm] at hstep <;> cases hstep <;>
        simp [Turing.TM0.step, Config.afterWrite, Config.afterMove, hm]

end UniversalTM0Tableau
end LeanWang
