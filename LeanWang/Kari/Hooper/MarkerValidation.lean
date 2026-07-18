/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.MarkerNavigation

/-!
# Canonical marker-layout validation

An arbitrary entry into the eventual counter controller must not be able to
skip the sparse-layout checks.  Before each logical counter instruction, the
controller therefore traverses all five labelled boundaries from its common
anchor at boundary `4` to boundary `0` and back again.  Each leg first steps
off the current boundary and then performs one labelled search across the
adjacent register gap.

This file records that finite route independently of the bounded-search
implementation.  Its execution relation exposes the exact `SearchGap` needed
by every leg, so a later compiler can replace each of them by Hooper's bounded
controller.  The proof includes zero-valued registers: in that case the first
cell after departure is already the next boundary and the search distance is
zero.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerValidation

open Turing CounterMachine
open MarkerSchedule

/-- One validation leg: depart from the current boundary in `direction`, then
search for `target`. -/
structure Leg where
  target : Fin 5
  direction : Turing.Dir
  deriving DecidableEq

/-- Exact tape semantics of one validation leg. -/
def Leg.Executes (leg : Leg)
    (start finish : FullTM0.Tape MarkerMachine.Symbol) : Prop :=
  ∃ distance,
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol leg.target)
      (start.move leg.direction) leg.direction distance ∧
    finish = (start.move leg.direction).moveN leg.direction distance

/-- Sequential execution of a finite validation route. -/
inductive Executes : List Leg →
    FullTM0.Tape MarkerMachine.Symbol →
    FullTM0.Tape MarkerMachine.Symbol → Prop
  | nil (T) : Executes [] T T
  | cons (leg) (legs) (T U V)
      (first : leg.Executes T U)
      (rest : Executes legs U V) :
      Executes (leg :: legs) T V

/-- One leftward leg crosses gap `i` from boundary `i+1` to boundary `i`. -/
theorem leftLeg_executes (registers : Registers) (i : Fin 4) :
    (Leg.mk i.castSucc .left).Executes
      (boundaryTape registers i.succ)
      (boundaryTape registers i.castSucc) := by
  refine ⟨RegisterLayout.values registers i,
    MarkerNavigation.boundaryTape_search_left registers i, ?_⟩
  rw [MarkerNavigation.boundaryTape_move_left]
  exact (MarkerNavigation.lastGapTape_moveN_left registers i).symm

/-- One rightward leg crosses gap `i` from boundary `i` to boundary `i+1`. -/
theorem rightLeg_executes (registers : Registers) (i : Fin 4) :
    (Leg.mk i.succ .right).Executes
      (boundaryTape registers i.castSucc)
      (boundaryTape registers i.succ) := by
  refine ⟨RegisterLayout.values registers i,
    MarkerNavigation.boundaryTape_search_right registers i, ?_⟩
  rw [MarkerNavigation.boundaryTape_move_right]
  exact (MarkerNavigation.firstGapTape_moveN_right registers i).symm

/-- Fixed eight-leg validation sweep from boundary `4` to `0` and back. -/
def sweep : List Leg :=
  [ ⟨3, .left⟩
  , ⟨2, .left⟩
  , ⟨1, .left⟩
  , ⟨0, .left⟩
  , ⟨1, .right⟩
  , ⟨2, .right⟩
  , ⟨3, .right⟩
  , ⟨4, .right⟩
  ]

@[simp]
theorem sweep_length : sweep.length = 8 :=
  rfl

/-- The complete validation route succeeds on every canonical five-boundary
layout and returns to the common boundary-`4` instruction anchor. -/
theorem sweep_executes (registers : Registers) :
    Executes sweep (boundaryTape registers 4) (boundaryTape registers 4) := by
  apply Executes.cons _ _ _ (boundaryTape registers 3) _
    (leftLeg_executes registers (3 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 2) _
    (leftLeg_executes registers (2 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 1) _
    (leftLeg_executes registers (1 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 0) _
    (leftLeg_executes registers (0 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 1) _
    (rightLeg_executes registers (0 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 2) _
    (rightLeg_executes registers (1 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 3) _
    (rightLeg_executes registers (2 : Fin 4))
  apply Executes.cons _ _ _ (boundaryTape registers 4) _
    (rightLeg_executes registers (3 : Fin 4))
  exact Executes.nil _

end MarkerValidation
end Hooper
end Kari
end LeanWang
