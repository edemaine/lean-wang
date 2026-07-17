/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Machine.UniversalTM0.Semantic

/-!
# Folded coordinates for the fixed universal TM0 machine

A two-sided TM0 tape is represented on a one-sided tape by pairing source
positions `-(i + 1)` and `i` at target position `i`.  This module contains only
the coordinate bookkeeping and source semantics used by the fixed-machine
simulation.
-/

noncomputable section

namespace LeanWang
namespace UniversalTM0Folded

open UniversalTM0Semantic

abbrev Symbol := Turing.TM2to1.Γ' Stack StackSymbol
abbrev Label := Turing.TM1to0.Λ' tm1

private instance : DecidableEq Symbol := Classical.decEq Symbol

def symbols : List Symbol := Finset.univ.toList

theorem mem_symbols (symbol : Symbol) : symbol ∈ symbols := by
  simp [symbols]

inductive Side where
  | left
  | right
deriving DecidableEq, Repr

def sides : List Side := [.left, .right]

theorem mem_sides (side : Side) : side ∈ sides := by
  cases side <;> simp [sides]

def Side.opposite : Side → Side
  | .left => .right
  | .right => .left

def Side.isOutward : Side → Turing.Dir → Bool
  | .left, .left | .right, .right => true
  | _, _ => false

def Side.isInward (side : Side) (dir : Turing.Dir) : Bool :=
  !(side.isOutward dir)

def rightAbs (position : Nat) : Int := position

def leftAbs (position : Nat) : Int := -((position : Int) + 1)

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

@[simp] theorem sourceOffset_right_head (head : Nat) :
    sourceOffset .right head (rightAbs head) = 0 := by
  simp [sourceOffset, activeAbs, rightAbs]

@[simp] theorem sourceOffset_left_head (head : Nat) :
    sourceOffset .left head (leftAbs head) = 0 := by
  simp [sourceOffset, activeAbs, leftAbs]

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

end UniversalTM0Folded
end LeanWang
