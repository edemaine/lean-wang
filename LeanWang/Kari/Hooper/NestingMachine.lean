/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.BasicLemma
import LeanWang.Kari.Hooper.MarkerProgram

/-!
# A finite controller for Hooper's bounded nested searches

Appendix VII of Hooper's paper replaces each unbounded search by a finite
search prefix.  A nearby target returns immediately.  Exhausting the prefix
enters a launch state for a nested canonical computation.  Once that
computation has reached the far frame boundary and restored the suspended
tape, a finite unwind routine returns to the original search exactly one cell
closer to its target.

This file makes those three finite pieces completely explicit.  The generated
`FiniteTM0.Table` contains both the left- and right-moving copies of the
controller.  The only remaining semantic input is `CoreGrows`: the statement
that an immortal canonical computation carries the exact launch configuration
to the exact restored-boundary configuration.  From that single hypothesis we
construct all four fields of `NestingLaws`, so `NestingLaws.basicLemma` applies
without any further transition-table reasoning.

The parameter called `radius` below leaves at least one cell for unwinding:
the actual directly inspected prefix has length `radius + 1`.  This avoids a
special zero-radius controller while retaining an arbitrary finite bound.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace NestingMachine

open Turing

/-! ## Local state allocation -/

/-- The direction opposite to a suspended search. -/
def opposite : Turing.Dir → Turing.Dir
  | .left => .right
  | .right => .left

@[simp] theorem opposite_left : opposite .left = .right := rfl
@[simp] theorem opposite_right : opposite .right = .left := rfl

/-- Number of blank cells inspected before a nested computation is launched. -/
def bound (radius : Nat) : Nat := radius + 1

/-- Successful exit of one local directional controller. -/
def localSuccessState (radius : Nat) : FiniteTM0.State :=
  bound radius + 1

/-- Handoff state for the nested canonical computation. -/
def localLaunchState (radius : Nat) : FiniteTM0.State :=
  bound radius + 2

/-- Entry of the fixed finite routine that unwinds a restored frame. -/
def localUnwindState (radius : Nat) : FiniteTM0.State :=
  bound radius + 3

/-- Half-open state interval reserved for one directional controller. -/
def localWidth (radius : Nat) : Nat :=
  2 * bound radius + 3

/-- Numeric offset of the left- or right-moving controller. -/
def directionOffset (radius : Nat) : Turing.Dir → FiniteTM0.State
  | .left => 0
  | .right => localWidth radius

/-- Entry state of a directional search. -/
def searchState (radius : Nat) (direction : Turing.Dir) : FiniteTM0.State :=
  directionOffset radius direction

/-- Successful exit state of a directional search. -/
def successState (radius : Nat) (direction : Turing.Dir) : FiniteTM0.State :=
  directionOffset radius direction + localSuccessState radius

/-- Concrete launch state of a directional search. -/
def launchState (radius : Nat) (direction : Turing.Dir) : FiniteTM0.State :=
  directionOffset radius direction + localLaunchState radius

/-- Concrete restored-boundary state from which finite unwinding begins. -/
def unwindState (radius : Nat) (direction : Turing.Dir) : FiniteTM0.State :=
  directionOffset radius direction + localUnwindState radius

/-! ## Explicit one-direction table -/

/-- Unroll a bounded scan.  `remaining` counts blank-moving rules still to be
emitted; the final state recognizes the target or hands off on a blank. -/
def scanTableAux (expected : Fin 5) (direction : Turing.Dir)
    (success launch : FiniteTM0.State) :
    Nat → FiniteTM0.State → FiniteTM0.Table MarkerMachine.AlphabetSize
  | 0, state =>
      [ FiniteTM0.Rule.mk state (MarkerMachine.boundarySymbol expected)
          success (.write (MarkerMachine.boundarySymbol expected))
      , FiniteTM0.Rule.mk state MarkerMachine.blankSymbol
          launch (.write MarkerMachine.blankSymbol)
      ]
  | remaining + 1, state =>
      FiniteTM0.Rule.mk state (MarkerMachine.boundarySymbol expected)
          success (.write (MarkerMachine.boundarySymbol expected)) ::
      FiniteTM0.Rule.mk state MarkerMachine.blankSymbol
          (state + 1) (MarkerMachine.moveAction direction) ::
      scanTableAux expected direction success launch remaining (state + 1)

/-- The bounded scan prefix for one direction, in local states. -/
def scanTable (radius : Nat) (expected : Fin 5) (direction : Turing.Dir) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  scanTableAux expected direction (localSuccessState radius)
    (localLaunchState radius) (bound radius) 0

/-- Unroll the fixed return path.  It moves opposite to the outer search
`remaining` times and finally changes control state by rewriting the known
blank under the head. -/
def unwindTableAux (direction : Turing.Dir) (search : FiniteTM0.State) :
    Nat → FiniteTM0.State → FiniteTM0.Table MarkerMachine.AlphabetSize
  | 0, state =>
      [FiniteTM0.Rule.mk state MarkerMachine.blankSymbol search
        (.write MarkerMachine.blankSymbol)]
  | remaining + 1, state =>
      FiniteTM0.Rule.mk state MarkerMachine.blankSymbol (state + 1)
          (MarkerMachine.moveAction (opposite direction)) ::
        unwindTableAux direction search remaining (state + 1)

/-- The local finite unwind routine. -/
def unwindTable (radius : Nat) (direction : Turing.Dir) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  unwindTableAux direction 0 radius (localUnwindState radius)

/-- One complete local directional controller. -/
def localTable (radius : Nat) (expected : Fin 5) (direction : Turing.Dir) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  scanTable radius expected direction ++ unwindTable radius direction

/-! ## Exact lookup equations -/

@[simp]
theorem lookup_scanTableAux_target_current (expected : Fin 5)
    (direction : Turing.Dir) (success launch state remaining : Nat) :
    FiniteTM0.lookupAction
        (scanTableAux expected direction success launch remaining state)
        state (MarkerMachine.boundarySymbol expected) =
      some (success,
        .write (MarkerMachine.boundarySymbol expected)) := by
  cases remaining <;>
    simp [scanTableAux, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]

@[simp]
theorem lookup_scanTableAux_blank_current (expected : Fin 5)
    (direction : Turing.Dir) (success launch state : Nat) :
    FiniteTM0.lookupAction
        (scanTableAux expected direction success launch 0 state)
        state MarkerMachine.blankSymbol =
      some (launch, .write MarkerMachine.blankSymbol) := by
  simp [scanTableAux, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
    MarkerMachine.blankSymbol_ne_boundarySymbol]

@[simp]
theorem lookup_scanTableAux_blank_step (expected : Fin 5)
    (direction : Turing.Dir) (success launch state remaining : Nat) :
    FiniteTM0.lookupAction
        (scanTableAux expected direction success launch (remaining + 1) state)
        state MarkerMachine.blankSymbol =
      some (state + 1, MarkerMachine.moveAction direction) := by
  simp [scanTableAux, FiniteTM0.lookupAction, FiniteTM0.Rule.mk,
    MarkerMachine.blankSymbol_ne_boundarySymbol]

@[simp]
theorem lookup_unwindTableAux_final (direction : Turing.Dir)
    (search state : Nat) :
    FiniteTM0.lookupAction (unwindTableAux direction search 0 state)
        state MarkerMachine.blankSymbol =
      some (search, .write MarkerMachine.blankSymbol) := by
  simp [unwindTableAux, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]

@[simp]
theorem lookup_unwindTableAux_step (direction : Turing.Dir)
    (search state remaining : Nat) :
    FiniteTM0.lookupAction
        (unwindTableAux direction search (remaining + 1) state)
        state MarkerMachine.blankSymbol =
      some (state + 1, MarkerMachine.moveAction (opposite direction)) := by
  simp [unwindTableAux, FiniteTM0.lookupAction, FiniteTM0.Rule.mk]

/-- Target lookup at every state of an unrolled scan. -/
theorem lookup_scanTableAux_target_at (expected : Fin 5)
    (direction : Turing.Dir) (success launch state remaining i : Nat)
    (hi : i ≤ remaining) :
    FiniteTM0.lookupAction
        (scanTableAux expected direction success launch remaining state)
        (state + i) (MarkerMachine.boundarySymbol expected) =
      some (success,
        .write (MarkerMachine.boundarySymbol expected)) := by
  induction i generalizing remaining state with
  | zero =>
      simpa using lookup_scanTableAux_target_current expected direction
        success launch state remaining
  | succ i ih =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          have hstate : state + (i + 1) ≠ state := by omega
          simp only [scanTableAux]
          simp only [FiniteTM0.lookupAction, FiniteTM0.Rule.mk, hstate,
            Prod.mk.injEq, false_and, and_false, if_false]
          have htail := ih (state := state + 1) (remaining := remaining)
            (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Blank lookup at every proper-prefix state of an unrolled scan. -/
theorem lookup_scanTableAux_blank_at (expected : Fin 5)
    (direction : Turing.Dir) (success launch state remaining i : Nat)
    (hi : i < remaining) :
    FiniteTM0.lookupAction
        (scanTableAux expected direction success launch remaining state)
        (state + i) MarkerMachine.blankSymbol =
      some (state + i + 1, MarkerMachine.moveAction direction) := by
  induction i generalizing remaining state with
  | zero =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          simpa using lookup_scanTableAux_blank_step expected direction
            success launch state remaining
  | succ i ih =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          have hstate : state + (i + 1) ≠ state := by omega
          simp only [scanTableAux]
          simp only [FiniteTM0.lookupAction, FiniteTM0.Rule.mk, hstate,
            Prod.mk.injEq, false_and, and_false, if_false]
          have htail := ih (state := state + 1) (remaining := remaining)
            (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Exhausting all unrolled blank moves reaches the launch transition. -/
theorem lookup_scanTableAux_launch_at (expected : Fin 5)
    (direction : Turing.Dir) (success launch state remaining : Nat) :
    FiniteTM0.lookupAction
        (scanTableAux expected direction success launch remaining state)
        (state + remaining) MarkerMachine.blankSymbol =
      some (launch, .write MarkerMachine.blankSymbol) := by
  induction remaining generalizing state with
  | zero =>
      simpa using lookup_scanTableAux_blank_current expected direction
        success launch state
  | succ remaining ih =>
      have hstate : state + (remaining + 1) ≠ state := by omega
      simp only [scanTableAux]
      simp only [FiniteTM0.lookupAction, FiniteTM0.Rule.mk, hstate,
        Prod.mk.injEq, false_and, and_false, if_false]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (state + 1)

/-! ## Exact bounded-scan executions -/

@[simp]
theorem tape_write_read (T : FullTM0.Tape MarkerMachine.Symbol) :
    T.write T.read = T := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [FullTM0.Tape.read, FullTM0.Tape.write]
  · simp [FullTM0.Tape.write, hi]

/-- A successful semantic step gives full-tape reachability. -/
private theorem reaches_of_step {M : Turing.TM0.Machine
    MarkerMachine.Symbol FiniteTM0.State}
    {c d : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State}
    (h : FullTM0.step M c = some d) : FullTM0.Reaches M c d := by
  apply Relation.ReflTransGen.single
  simpa [h]

@[simp]
theorem step_scan_blank_at (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (i : Nat) (hi : i < bound radius)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (FiniteTM0.machine (scanTable radius expected direction))
        ⟨i, T⟩ =
      some ⟨i + 1, T.move direction⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, scanTable]
  rw [hread]
  have hlookup := lookup_scanTableAux_blank_at expected direction
    (localSuccessState radius) (localLaunchState radius) 0
    (bound radius) i hi
  simp only [Nat.zero_add] at hlookup
  rw [hlookup]
  cases direction <;> rfl

@[simp]
theorem step_scan_target_at (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (i : Nat) (hi : i ≤ bound radius)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.boundarySymbol expected) :
    FullTM0.step (FiniteTM0.machine (scanTable radius expected direction))
        ⟨i, T⟩ =
      some ⟨localSuccessState radius, T⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, scanTable]
  rw [hread]
  have hlookup := lookup_scanTableAux_target_at expected direction
    (localSuccessState radius) (localLaunchState radius) 0
    (bound radius) i hi
  simp only [Nat.zero_add] at hlookup
  rw [hlookup]
  have htape : T.write (MarkerMachine.boundarySymbol expected) = T := by
    rw [← hread]
    exact tape_write_read T
  simp [htape]

@[simp]
theorem step_scan_launch (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (FiniteTM0.machine (scanTable radius expected direction))
        ⟨bound radius, T⟩ =
      some ⟨localLaunchState radius, T⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, scanTable]
  rw [hread]
  have hlookup := lookup_scanTableAux_launch_at expected direction
    (localSuccessState radius) (localLaunchState radius) 0
    (bound radius)
  simp only [Nat.zero_add] at hlookup
  rw [hlookup]
  have htape : T.write MarkerMachine.blankSymbol = T := by
    rw [← hread]
    exact tape_write_read T
  simp [htape]

/-- Cross a guarded blank prefix while retaining the scan program's absolute
progress state. -/
theorem scan_moves_reaches (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (progress distance : Nat)
    (hbound : progress + distance ≤ bound radius)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i < distance,
      T (FullTM0.Tape.offset direction i) = MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (scanTable radius expected direction))
      ⟨progress, T⟩
      ⟨progress + distance, T.moveN direction distance⟩ := by
  induction distance generalizing progress T with
  | zero =>
      simp only [Nat.add_zero, FullTM0.Tape.moveN_zero]
      exact Relation.ReflTransGen.refl
  | succ distance ih =>
      have hprogress : progress < bound radius := by omega
      have hread : T.read = MarkerMachine.blankSymbol := by
        simpa [FullTM0.Tape.read] using hblank 0 (Nat.zero_lt_succ distance)
      have hfirst := reaches_of_step
        (step_scan_blank_at radius expected direction progress hprogress T hread)
      have htailBlank : ∀ i < distance,
          (T.move direction) (FullTM0.Tape.offset direction i) =
            MarkerMachine.blankSymbol := by
        intro i hi
        simpa using hblank (i + 1) (Nat.succ_lt_succ hi)
      have hrest := ih (progress + 1) (by omega) (T.move direction)
        htailBlank
      have hall := hfirst.trans hrest
      simpa [FullTM0.Reaches, StateTransition.Reaches,
        FullTM0.Tape.move_moveN, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

/-- A target inside the finite prefix is found with no tape-content change. -/
theorem scan_reaches_success (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hnear : distance ≤ bound radius) :
    FullTM0.Reaches (FiniteTM0.machine (scanTable radius expected direction))
      ⟨0, T⟩
      ⟨localSuccessState radius, T.moveN direction distance⟩ := by
  have hmoves := scan_moves_reaches radius expected direction 0 distance
    (by simpa using hnear) T (fun i hi => hgap.blank hi)
  have hread : (T.moveN direction distance).read =
      MarkerMachine.boundarySymbol expected := by
    simpa using hgap.marked
  have hfinish := reaches_of_step
    (step_scan_target_at radius expected direction distance hnear
      (T.moveN direction distance) hread)
  have hmoves' : FullTM0.Reaches
      (FiniteTM0.machine (scanTable radius expected direction))
      ⟨0, T⟩ ⟨distance, T.moveN direction distance⟩ := by
    simpa using hmoves
  exact hmoves'.trans hfinish

/-- A target beyond the finite prefix produces the exact launch
configuration, with the head recentered at the prefix boundary. -/
theorem scan_reaches_launch (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hfar : bound radius < distance) :
    FullTM0.Reaches (FiniteTM0.machine (scanTable radius expected direction))
      ⟨0, T⟩
      ⟨localLaunchState radius, T.moveN direction (bound radius)⟩ := by
  have hmoves := scan_moves_reaches radius expected direction 0 (bound radius)
    (by simp) T (fun i hi => hgap.blank (Nat.lt_trans hi hfar))
  have hread : (T.moveN direction (bound radius)).read =
      MarkerMachine.blankSymbol := by
    simpa using hgap.blank hfar
  have hfinish := reaches_of_step
    (step_scan_launch radius expected direction
      (T.moveN direction (bound radius)) hread)
  have hmoves' : FullTM0.Reaches
      (FiniteTM0.machine (scanTable radius expected direction))
      ⟨0, T⟩
      ⟨bound radius, T.moveN direction (bound radius)⟩ := by
    simpa using hmoves
  exact hmoves'.trans hfinish

/-! ## Exact finite unwinding -/

/-- Movement lookup at every proper-prefix state of an unwind routine. -/
theorem lookup_unwindTableAux_move_at (direction : Turing.Dir)
    (search state remaining i : Nat) (hi : i < remaining) :
    FiniteTM0.lookupAction (unwindTableAux direction search remaining state)
        (state + i) MarkerMachine.blankSymbol =
      some (state + i + 1,
        MarkerMachine.moveAction (opposite direction)) := by
  induction i generalizing remaining state with
  | zero =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          simpa using lookup_unwindTableAux_step direction search state remaining
  | succ i ih =>
      cases remaining with
      | zero => omega
      | succ remaining =>
          have hstate : state + (i + 1) ≠ state := by omega
          simp only [unwindTableAux, FiniteTM0.lookupAction,
            FiniteTM0.Rule.mk, hstate, Prod.mk.injEq, false_and, if_false]
          have htail := ih (state := state + 1) (remaining := remaining)
            (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Final no-op lookup after all unwind moves. -/
theorem lookup_unwindTableAux_finish_at (direction : Turing.Dir)
    (search state remaining : Nat) :
    FiniteTM0.lookupAction (unwindTableAux direction search remaining state)
        (state + remaining) MarkerMachine.blankSymbol =
      some (search, .write MarkerMachine.blankSymbol) := by
  induction remaining generalizing state with
  | zero => simpa using lookup_unwindTableAux_final direction search state
  | succ remaining ih =>
      have hstate : state + (remaining + 1) ≠ state := by omega
      simp only [unwindTableAux, FiniteTM0.lookupAction,
        FiniteTM0.Rule.mk, hstate, Prod.mk.injEq, false_and, if_false]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (state + 1)

@[simp]
theorem step_unwind_move_at (radius : Nat) (direction : Turing.Dir)
    (i : Nat) (hi : i < radius)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (FiniteTM0.machine (unwindTable radius direction))
        ⟨localUnwindState radius + i, T⟩ =
      some ⟨localUnwindState radius + i + 1,
        T.move (opposite direction)⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, unwindTable]
  rw [hread]
  rw [lookup_unwindTableAux_move_at direction 0
    (localUnwindState radius) radius i hi]
  cases direction <;> rfl

@[simp]
theorem step_unwind_finish (radius : Nat) (direction : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hread : T.read = MarkerMachine.blankSymbol) :
    FullTM0.step (FiniteTM0.machine (unwindTable radius direction))
        ⟨localUnwindState radius + radius, T⟩ =
      some ⟨0, T⟩ := by
  simp only [FullTM0.step, FiniteTM0.machine, unwindTable]
  rw [hread]
  rw [lookup_unwindTableAux_finish_at direction 0
    (localUnwindState radius) radius]
  have htape : T.write MarkerMachine.blankSymbol = T := by
    rw [← hread]
    exact tape_write_read T
  simp [htape]

/-- Cross a guarded blank prefix inside the fixed unwind routine. -/
theorem unwind_moves_reaches (radius : Nat) (direction : Turing.Dir)
    (progress distance : Nat) (hbound : progress + distance ≤ radius)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i < distance,
      T (FullTM0.Tape.offset (opposite direction) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (unwindTable radius direction))
      ⟨localUnwindState radius + progress, T⟩
      ⟨localUnwindState radius + progress + distance,
        T.moveN (opposite direction) distance⟩ := by
  induction distance generalizing progress T with
  | zero =>
      simp only [Nat.add_zero, FullTM0.Tape.moveN_zero]
      exact Relation.ReflTransGen.refl
  | succ distance ih =>
      have hprogress : progress < radius := by omega
      have hread : T.read = MarkerMachine.blankSymbol := by
        simpa [FullTM0.Tape.read] using hblank 0 (Nat.zero_lt_succ distance)
      have hfirst := reaches_of_step
        (step_unwind_move_at radius direction progress hprogress T hread)
      have htailBlank : ∀ i < distance,
          (T.move (opposite direction))
              (FullTM0.Tape.offset (opposite direction) i) =
            MarkerMachine.blankSymbol := by
        intro i hi
        simpa using hblank (i + 1) (Nat.succ_lt_succ hi)
      have hrest := ih (progress + 1) (by omega)
        (T.move (opposite direction)) htailBlank
      have hall := hfirst.trans hrest
      simpa [FullTM0.Reaches, StateTransition.Reaches,
        FullTM0.Tape.move_moveN, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

/-- Moving back `radius` cells from the launch boundary leaves the head one
cell in the original search direction. -/
theorem moveN_bound_opposite (T : FullTM0.Tape MarkerMachine.Symbol)
    (radius : Nat) (direction : Turing.Dir) :
    (T.moveN direction (bound radius)).moveN (opposite direction) radius =
      T.move direction := by
  funext i
  cases direction <;>
    simp [FullTM0.Tape.moveN, FullTM0.Tape.offset, bound,
      opposite, FullTM0.Tape.move] <;> ring

/-- The restored boundary configuration follows the fixed return path and
resumes the outer search exactly one cell closer. -/
theorem unwind_reaches (radius : Nat) (direction : Turing.Dir)
    (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN direction (bound radius))
          (FullTM0.Tape.offset (opposite direction) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (unwindTable radius direction))
      ⟨localUnwindState radius, T.moveN direction (bound radius)⟩
      ⟨0, T.move direction⟩ := by
  have hmoves := unwind_moves_reaches radius direction 0 radius (by simp)
    (T.moveN direction (bound radius))
    (fun i hi => hblank i (Nat.le_of_lt hi))
  have hmoves' : FullTM0.Reaches
      (FiniteTM0.machine (unwindTable radius direction))
      ⟨localUnwindState radius, T.moveN direction (bound radius)⟩
      ⟨localUnwindState radius + radius, T.move direction⟩ := by
    simpa [moveN_bound_opposite] using hmoves
  have hfinal : (T.move direction).read = MarkerMachine.blankSymbol := by
    have h := hblank radius (Nat.le_refl radius)
    rw [← moveN_bound_opposite T radius direction]
    simpa [FullTM0.Tape.read] using h
  have hfinish := reaches_of_step
    (step_unwind_finish radius direction (T.move direction) hfinal)
  exact hmoves'.trans hfinish

/-! ## Linking scan and unwind into one directional block -/

/-- Source states of a scan unrolling occupy exactly its advertised interval. -/
theorem source_mem_scanTableAux {expected : Fin 5}
    {direction : Turing.Dir} {success launch state remaining q : Nat}
    (hq : q ∈ FiniteTM0.sourceStates
      (scanTableAux expected direction success launch remaining state)) :
    state ≤ q ∧ q ≤ state + remaining := by
  induction remaining generalizing state with
  | zero =>
      simp [FiniteTM0.sourceStates, scanTableAux] at hq
      subst q
      simp
  | succ remaining ih =>
      simp only [scanTableAux, FiniteTM0.sourceStates, List.map_cons,
        List.mem_cons] at hq
      rcases hq with rfl | rfl | htail
      · omega
      · omega
      · have hb := ih htail
        omega

/-- Source states of an unwind unrolling occupy exactly its advertised interval. -/
theorem source_mem_unwindTableAux {direction : Turing.Dir}
    {search state remaining q : Nat}
    (hq : q ∈ FiniteTM0.sourceStates
      (unwindTableAux direction search remaining state)) :
    state ≤ q ∧ q ≤ state + remaining := by
  induction remaining generalizing state with
  | zero =>
      simp [FiniteTM0.sourceStates, unwindTableAux] at hq
      subst q
      simp
  | succ remaining ih =>
      simp only [unwindTableAux, FiniteTM0.sourceStates, List.map_cons,
        List.mem_cons] at hq
      rcases hq with rfl | htail
      · omega
      · have hb := ih htail
        omega

/-- No unwind source state is a scan source state. -/
theorem scan_unwind_source_disjoint (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) :
    ∀ state,
      state ∈ FiniteTM0.sourceStates (unwindTable radius direction) →
      state ∉ FiniteTM0.sourceStates (scanTable radius expected direction) := by
  intro state hunwind hscan
  have hs := source_mem_scanTableAux hscan
  have hu := source_mem_unwindTableAux hunwind
  simp only [bound] at hs
  simp only [localUnwindState, bound] at hu
  omega

/-- Nearby search correctness for the complete local directional block. -/
theorem local_reaches_success (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hnear : distance ≤ bound radius) :
    FullTM0.Reaches (FiniteTM0.machine (localTable radius expected direction))
      ⟨0, T⟩
      ⟨localSuccessState radius, T.moveN direction distance⟩ := by
  exact FiniteTM0Program.reaches_append_left _ _
    (scan_reaches_success radius expected direction T distance hgap hnear)

/-- Exact launch correctness for the complete local directional block. -/
theorem local_reaches_launch (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hfar : bound radius < distance) :
    FullTM0.Reaches (FiniteTM0.machine (localTable radius expected direction))
      ⟨0, T⟩
      ⟨localLaunchState radius, T.moveN direction (bound radius)⟩ := by
  exact FiniteTM0Program.reaches_append_left _ _
    (scan_reaches_launch radius expected direction T distance hgap hfar)

/-- Exact unwind correctness for the complete local directional block. -/
theorem local_unwind_reaches (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN direction (bound radius))
          (FullTM0.Tape.offset (opposite direction) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (localTable radius expected direction))
      ⟨localUnwindState radius, T.moveN direction (bound radius)⟩
      ⟨0, T.move direction⟩ := by
  exact MarkerProgram.reaches_append_right_of_source_disjoint _ _
    (scan_unwind_source_disjoint radius expected direction)
    (unwind_reaches radius direction T hblank)

/-! ## Linking the two directional copies -/

/-- Every source state of a local controller lies in its allocated interval. -/
theorem source_mem_localTable {radius : Nat} {expected : Fin 5}
    {direction : Turing.Dir} {state : Nat}
    (hstate : state ∈ FiniteTM0.sourceStates
      (localTable radius expected direction)) :
    state < localWidth radius := by
  simp only [localTable, FiniteTM0.sourceStates, List.map_append,
    List.mem_append] at hstate
  rcases hstate with hscan | hunwind
  · have hs := source_mem_scanTableAux hscan
    simp only [localWidth, bound]
    simp only [bound] at hs
    omega
  · have hu := source_mem_unwindTableAux hunwind
    simp only [localWidth, localUnwindState, bound]
    simp only [localUnwindState, bound] at hu
    omega

/-- Relocate one directional controller into its reserved state interval. -/
def directionalTable (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  FiniteTM0Program.relocate (directionOffset radius direction)
    (localTable radius expected direction)

/-- Relocated source states stay inside their directional interval. -/
theorem source_mem_directionalTable {radius : Nat} {expected : Fin 5}
    {direction : Turing.Dir} {state : Nat}
    (hstate : state ∈ FiniteTM0.sourceStates
      (directionalTable radius expected direction)) :
    directionOffset radius direction ≤ state ∧
      state < directionOffset radius direction + localWidth radius := by
  simp only [directionalTable, FiniteTM0Program.relocate,
    FiniteTM0.sourceStates, List.map_map, List.mem_map] at hstate
  rcases hstate with ⟨rule, hrule, rfl⟩
  have hlocal : rule.1.1 ∈ FiniteTM0.sourceStates
      (localTable radius expected direction) :=
    List.mem_map.mpr ⟨rule, hrule, rfl⟩
  have hbound := source_mem_localTable hlocal
  change directionOffset radius direction ≤
      directionOffset radius direction + rule.1.1 ∧
    directionOffset radius direction + rule.1.1 <
      directionOffset radius direction + localWidth radius
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hbound _⟩

/-- Left and right copies of the controller. -/
def controllerTable (radius : Nat) (expected : Fin 5) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  directionalTable radius expected .left ++
    directionalTable radius expected .right

/-- The relocated directional blocks have disjoint source-state intervals. -/
theorem left_right_source_disjoint (radius : Nat) (expected : Fin 5) :
    ∀ state,
      state ∈ FiniteTM0.sourceStates
        (directionalTable radius expected .right) →
      state ∉ FiniteTM0.sourceStates
        (directionalTable radius expected .left) := by
  intro state hright hleft
  have hr := source_mem_directionalTable hright
  have hl := source_mem_directionalTable hleft
  have hrLower : localWidth radius ≤ state := by
    simpa [directionOffset] using hr.1
  have hlUpper : state < localWidth radius := by
    simpa [directionOffset] using hl.2
  exact (Nat.not_lt_of_ge hrLower) hlUpper

/-- Relocated direct-success theorem for one directional block. -/
theorem directional_reaches_success (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hnear : distance ≤ bound radius) :
    FullTM0.Reaches
      (FiniteTM0.machine (directionalTable radius expected direction))
      ⟨searchState radius direction, T⟩
      ⟨successState radius direction, T.moveN direction distance⟩ := by
  have h := FiniteTM0Program.reaches_relocate
    (directionOffset radius direction)
    (localTable radius expected direction)
    (local_reaches_success radius expected direction T distance hgap hnear)
  simpa [directionalTable, FiniteTM0Program.liftCfg, searchState,
    successState] using h

/-- Relocated launch theorem for one directional block. -/
theorem directional_reaches_launch (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hfar : bound radius < distance) :
    FullTM0.Reaches
      (FiniteTM0.machine (directionalTable radius expected direction))
      ⟨searchState radius direction, T⟩
      ⟨launchState radius direction, T.moveN direction (bound radius)⟩ := by
  have h := FiniteTM0Program.reaches_relocate
    (directionOffset radius direction)
    (localTable radius expected direction)
    (local_reaches_launch radius expected direction T distance hgap hfar)
  simpa [directionalTable, FiniteTM0Program.liftCfg, searchState,
    launchState] using h

/-- Relocated unwind theorem for one directional block. -/
theorem directional_unwind_reaches (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN direction (bound radius))
          (FullTM0.Tape.offset (opposite direction) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches
      (FiniteTM0.machine (directionalTable radius expected direction))
      ⟨unwindState radius direction, T.moveN direction (bound radius)⟩
      ⟨searchState radius direction, T.move direction⟩ := by
  have h := FiniteTM0Program.reaches_relocate
    (directionOffset radius direction)
    (localTable radius expected direction)
    (local_unwind_reaches radius expected direction T hblank)
  simpa [directionalTable, FiniteTM0Program.liftCfg, searchState,
    unwindState] using h

/-- Direct success after linking both directions into one controller. -/
theorem controller_reaches_success (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hnear : distance ≤ bound radius) :
    FullTM0.Reaches (FiniteTM0.machine (controllerTable radius expected))
      ⟨searchState radius direction, T⟩
      ⟨successState radius direction, T.moveN direction distance⟩ := by
  have h := directional_reaches_success radius expected direction T distance
    hgap hnear
  cases direction with
  | left =>
      exact FiniteTM0Program.reaches_append_left _ _ h
  | right =>
      exact MarkerProgram.reaches_append_right_of_source_disjoint _ _
        (left_right_source_disjoint radius expected) h

/-- Exact launch after linking both directions into one controller. -/
theorem controller_reaches_launch (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hfar : bound radius < distance) :
    FullTM0.Reaches (FiniteTM0.machine (controllerTable radius expected))
      ⟨searchState radius direction, T⟩
      ⟨launchState radius direction, T.moveN direction (bound radius)⟩ := by
  have h := directional_reaches_launch radius expected direction T distance
    hgap hfar
  cases direction with
  | left =>
      exact FiniteTM0Program.reaches_append_left _ _ h
  | right =>
      exact MarkerProgram.reaches_append_right_of_source_disjoint _ _
        (left_right_source_disjoint radius expected) h

/-- Exact unwind after linking both directions into one controller. -/
theorem controller_unwind_reaches (radius : Nat) (expected : Fin 5)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN direction (bound radius))
          (FullTM0.Tape.offset (opposite direction) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (FiniteTM0.machine (controllerTable radius expected))
      ⟨unwindState radius direction, T.moveN direction (bound radius)⟩
      ⟨searchState radius direction, T.move direction⟩ := by
  have h := directional_unwind_reaches radius expected direction T hblank
  cases direction with
  | left =>
      exact FiniteTM0Program.reaches_append_left _ _ h
  | right =>
      exact MarkerProgram.reaches_append_right_of_source_disjoint _ _
        (left_right_source_disjoint radius expected) h

/-! ## Appending the nested core -/

/-- Complete finite program: the bounded controller followed by an arbitrary
finite nested-core table.  The core may own the reserved launch states. -/
def table (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize) :
    FiniteTM0.Table MarkerMachine.AlphabetSize :=
  controllerTable radius expected ++ core

/-- Semantic full-tape machine of the complete finite program. -/
def machine (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize) :
    Turing.TM0.Machine MarkerMachine.Symbol FiniteTM0.State :=
  FiniteTM0.machine (table radius expected core)

theorem machine_reaches_success (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hnear : distance ≤ bound radius) :
    FullTM0.Reaches (machine radius expected core)
      ⟨searchState radius direction, T⟩
      ⟨successState radius direction, T.moveN direction distance⟩ := by
  exact FiniteTM0Program.reaches_append_left _ _
    (controller_reaches_success radius expected direction T distance
      hgap hnear)

theorem machine_reaches_launch (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (distance : Nat)
    (hgap : SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      T direction distance)
    (hfar : bound radius < distance) :
    FullTM0.Reaches (machine radius expected core)
      ⟨searchState radius direction, T⟩
      ⟨launchState radius direction, T.moveN direction (bound radius)⟩ := by
  exact FiniteTM0Program.reaches_append_left _ _
    (controller_reaches_launch radius expected direction T distance
      hgap hfar)

theorem machine_unwind_reaches (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (direction : Turing.Dir) (T : FullTM0.Tape MarkerMachine.Symbol)
    (hblank : ∀ i ≤ radius,
      (T.moveN direction (bound radius))
          (FullTM0.Tape.offset (opposite direction) i) =
        MarkerMachine.blankSymbol) :
    FullTM0.Reaches (machine radius expected core)
      ⟨unwindState radius direction, T.moveN direction (bound radius)⟩
      ⟨searchState radius direction, T.move direction⟩ := by
  exact FiniteTM0Program.reaches_append_left _ _
    (controller_unwind_reaches radius expected direction T hblank)

/-! ## The exact suspended-frame invariant -/

/-- A launched frame remembers a genuine outer search gap whose target lies
beyond the finite prefix. -/
def FrameWellFormed (radius : Nat) (expected : Fin 5)
    (frame : Frame MarkerMachine.Symbol Turing.Dir) : Prop :=
  SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol expected)
      frame.outer frame.saved frame.distance ∧
    bound radius < frame.distance

/-- Concrete launch invariant: exact outer frame plus exact recentering at the
finite-prefix boundary. -/
def NestedAt (radius : Nat) (expected : Fin 5)
    (frame : Frame MarkerMachine.Symbol Turing.Dir)
    (cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State) : Prop :=
  FrameWellFormed radius expected frame ∧
    cfg = ⟨launchState radius frame.saved,
      frame.outer.moveN frame.saved (bound radius)⟩

/-- Concrete restored-boundary invariant.  In particular, the nested core has
restored the complete outer tape before handing control to finite unwinding. -/
def BoundaryAt (radius : Nat) (expected : Fin 5)
    (frame : Frame MarkerMachine.Symbol Turing.Dir)
    (cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State) : Prop :=
  FrameWellFormed radius expected frame ∧
    cfg = ⟨unwindState radius frame.saved,
      frame.outer.moveN frame.saved (bound radius)⟩

/-- The outer search gap supplies every blank traversed by finite unwinding. -/
theorem FrameWellFormed.returnBlank {radius : Nat} {expected : Fin 5}
    {frame : Frame MarkerMachine.Symbol Turing.Dir}
    (hframe : FrameWellFormed radius expected frame) :
    ∀ i ≤ radius,
      (frame.outer.moveN frame.saved (bound radius))
          (FullTM0.Tape.offset (opposite frame.saved) i) =
        MarkerMachine.blankSymbol := by
  intro i hi
  have hibound : i ≤ bound radius := by
    simp only [bound]
    omega
  have hindex : bound radius - i < frame.distance :=
    lt_of_le_of_lt (Nat.sub_le _ _) hframe.2
  have hblank := hframe.1.blank hindex
  have hcoord :
      FullTM0.Tape.offset (opposite frame.saved) i +
          FullTM0.Tape.offset frame.saved (bound radius) =
        FullTM0.Tape.offset frame.saved (bound radius - i) := by
    cases frame.saved <;>
      simp [FullTM0.Tape.offset, opposite, Nat.cast_sub hibound] <;> ring
  rw [FullTM0.Tape.moveN_apply, hcoord]
  exact hblank

/-- Search-system interface exported to Hooper's abstract Basic Lemma. -/
def searchSystem (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize) :
    SearchSystem MarkerMachine.Symbol FiniteTM0.State Turing.Dir where
  machine := machine radius expected core
  searchState := searchState radius
  successState := successState radius
  direction := id
  radius := fun _ => bound radius
  isBlank := fun a => a = MarkerMachine.blankSymbol
  isMark := fun a => a = MarkerMachine.boundarySymbol expected
  nestedAt := NestedAt radius expected
  boundaryAt := BoundaryAt radius expected

/-! ## The sole remaining nested-core obligation -/

/-- Exact growth/restoration property required of the appended nested core.

The premise about all shorter searches is the simultaneous induction
hypothesis from Hooper's Appendix VII.  Everything before and after this
interval has already been compiled into `table` and proved correct above. -/
def CoreGrows (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (CoreImmortal : Prop) : Prop :=
  ∀ {frame : Frame MarkerMachine.Symbol Turing.Dir}
      {cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State},
    CoreImmortal →
      (∀ j < frame.distance,
        (searchSystem radius expected core).Solves j) →
      NestedAt radius expected frame cfg →
      ∃ boundary,
        FullTM0.Reaches (machine radius expected core) cfg boundary ∧
          BoundaryAt radius expected frame boundary

/-- The explicit finite controller discharges `direct`, `launch`, and
`unwind`; a proof of `CoreGrows` supplies exactly the remaining `grow` field. -/
theorem nestingLaws (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (CoreImmortal : Prop)
    (hgrows : CoreGrows radius expected core CoreImmortal) :
    NestingLaws (searchSystem radius expected core) CoreImmortal where
  direct := by
    intro direction T distance hgap hnear
    simpa [searchSystem, SearchSystem.startCfg,
      SearchSystem.successCfg] using
      machine_reaches_success radius expected core direction T distance
        hgap hnear
  launch := by
    intro direction T distance hgap hfar
    let cfg : FullTM0.Cfg MarkerMachine.Symbol FiniteTM0.State :=
      ⟨launchState radius direction,
        T.moveN direction (bound radius)⟩
    refine ⟨cfg, ?_, ?_⟩
    · simpa [cfg, searchSystem, SearchSystem.startCfg] using
        machine_reaches_launch radius expected core direction T distance
          hgap hfar
    · exact ⟨⟨hgap, hfar⟩, rfl⟩
  grow := by
    intro frame cfg hcore hshort hnested
    exact hgrows hcore hshort hnested
  unwind := by
    intro frame boundary hboundary
    rcases hboundary with ⟨hframe, rfl⟩
    simpa [searchSystem, SearchSystem.startCfg] using
      machine_unwind_reaches radius expected core frame.saved frame.outer
        hframe.returnBlank

/-- Concrete form of Hooper's Basic Lemma for the generated finite table. -/
theorem solves_all (radius : Nat) (expected : Fin 5)
    (core : FiniteTM0.Table MarkerMachine.AlphabetSize)
    (CoreImmortal : Prop)
    (hgrows : CoreGrows radius expected core CoreImmortal)
    (hcore : CoreImmortal) :
    ∀ distance, (searchSystem radius expected core).Solves distance :=
  (nestingLaws radius expected core CoreImmortal hgrows).basicLemma hcore

end NestingMachine
end Hooper
end Kari
end LeanWang
