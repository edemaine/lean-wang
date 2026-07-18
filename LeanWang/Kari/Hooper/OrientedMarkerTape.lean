/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.FiniteTM0Mirror
import LeanWang.Kari.Hooper.MarkerValidation

/-!
# Oriented canonical marker tapes

A failed rightward search launches the ordinary right-growing canonical core;
a failed leftward search launches its reflected copy.  This file packages the
shared geometry.  `orientTape growth` is the identity when `growth = .right`
and reflection through the head when `growth = .left`.  Logical directions
are transported in the same way, so writes, moves, finite moves, search gaps,
and the complete marker-validation sweep all commute with orientation.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace OrientedMarkerTape

open Turing

universe u

/-- Transport a direction from the ordinary right-growing core into a core
whose positive growth direction is `growth`. -/
def orientDirection (growth logical : Turing.Dir) : Turing.Dir :=
  match growth with
  | .right => logical
  | .left => FiniteTM0Mirror.mirrorDir logical

@[simp]
theorem orientDirection_right (logical : Turing.Dir) :
    orientDirection .right logical = logical :=
  rfl

@[simp]
theorem orientDirection_left (logical : Turing.Dir) :
    orientDirection .left logical = FiniteTM0Mirror.mirrorDir logical :=
  rfl

@[simp]
theorem orientDirection_growth_right (growth : Turing.Dir) :
    orientDirection growth .right = growth := by
  cases growth <;> rfl

@[simp]
theorem orientDirection_growth_left (growth : Turing.Dir) :
    orientDirection growth .left = FiniteTM0Mirror.mirrorDir growth := by
  cases growth <;> rfl

/-- Identity-or-reflection of a head-relative tape according to its growth
direction. -/
def orientTape {Γ : Type u} (growth : Turing.Dir)
    (T : FullTM0.Tape Γ) : FullTM0.Tape Γ :=
  match growth with
  | .right => T
  | .left => FiniteTM0Mirror.Tape.mirror T

@[simp]
theorem orientTape_right {Γ : Type u} (T : FullTM0.Tape Γ) :
    orientTape .right T = T :=
  rfl

@[simp]
theorem orientTape_left {Γ : Type u} (T : FullTM0.Tape Γ) :
    orientTape .left T = FiniteTM0Mirror.Tape.mirror T :=
  rfl

@[simp]
theorem orientTape_read {Γ : Type u} (growth : Turing.Dir)
    (T : FullTM0.Tape Γ) :
    (orientTape growth T).read = T.read := by
  cases growth <;> simp [orientTape]

@[simp]
theorem orientTape_write {Γ : Type u} (growth : Turing.Dir)
    (T : FullTM0.Tape Γ) (symbol : Γ) :
    orientTape growth (T.write symbol) =
      (orientTape growth T).write symbol := by
  cases growth <;> simp [orientTape]

@[simp]
theorem orientTape_move {Γ : Type u} (growth logical : Turing.Dir)
    (T : FullTM0.Tape Γ) :
    orientTape growth (T.move logical) =
      (orientTape growth T).move (orientDirection growth logical) := by
  cases growth <;> simp [orientTape, orientDirection]

@[simp]
theorem orientTape_moveN {Γ : Type u} (growth logical : Turing.Dir)
    (T : FullTM0.Tape Γ) (distance : Nat) :
    orientTape growth (T.moveN logical distance) =
      (orientTape growth T).moveN
        (orientDirection growth logical) distance := by
  cases growth <;> simp [orientTape, orientDirection]

/-- Search geometry transports exactly to either physical orientation. -/
theorem searchGap_orient_iff {Γ : Type u}
    {IsBlank IsMark : Γ → Prop} (growth logical : Turing.Dir)
    (T : FullTM0.Tape Γ) (distance : Nat) :
    SearchGap IsBlank IsMark (orientTape growth T)
        (orientDirection growth logical) distance ↔
      SearchGap IsBlank IsMark T logical distance := by
  cases growth with
  | left =>
      exact FiniteTM0Mirror.searchGap_mirror_iff T logical distance
  | right => rfl

/-- One validation leg transported into the chosen physical orientation. -/
def orientLeg (growth : Turing.Dir) (leg : MarkerValidation.Leg) :
    MarkerValidation.Leg :=
  ⟨leg.target, orientDirection growth leg.direction⟩

theorem leg_executes_orient (growth : Turing.Dir)
    {leg : MarkerValidation.Leg}
    {start finish : FullTM0.Tape MarkerMachine.Symbol}
    (h : leg.Executes start finish) :
    (orientLeg growth leg).Executes
      (orientTape growth start) (orientTape growth finish) := by
  rcases h with ⟨distance, hgap, rfl⟩
  refine ⟨distance, ?_, ?_⟩
  · simp only [orientLeg]
    rw [← orientTape_move]
    exact (searchGap_orient_iff growth leg.direction
      (start.move leg.direction) distance).2 hgap
  · simp [orientLeg]

/-- A whole finite validation route transports pointwise to its reflected
left-growing copy. -/
theorem executes_orient (growth : Turing.Dir)
    {legs : List MarkerValidation.Leg}
    {start finish : FullTM0.Tape MarkerMachine.Symbol}
    (h : MarkerValidation.Executes legs start finish) :
    MarkerValidation.Executes (legs.map (orientLeg growth))
      (orientTape growth start) (orientTape growth finish) := by
  induction h with
  | nil T => exact MarkerValidation.Executes.nil _
  | cons leg legs T U V first rest ih =>
      exact MarkerValidation.Executes.cons _ _ _ _ _
        (leg_executes_orient growth first) ih

/-- The canonical eight-leg sweep is valid in both growth orientations and
returns to the correspondingly oriented boundary-`4` anchor. -/
theorem sweep_executes (growth : Turing.Dir)
    (registers : CounterMachine.Registers) :
    MarkerValidation.Executes
      (MarkerValidation.sweep.map (orientLeg growth))
      (orientTape growth (MarkerSchedule.boundaryTape registers 4))
      (orientTape growth (MarkerSchedule.boundaryTape registers 4)) :=
  executes_orient growth (MarkerValidation.sweep_executes registers)

end OrientedMarkerTape
end Hooper
end Kari
end LeanWang
