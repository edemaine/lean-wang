/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGlobalUnnesting
import LeanWang.Kari.Hooper.CounterControlArbitrarySearch

/-!
# Generated searches with one cleared cell behind them

Every search resumed by the shared return dispatcher starts one cell after
the erased return tag.  Thus, in addition to its ordinary finite target gap,
the cell immediately behind its entry head is blank.

This one-cell guard is the stable nesting-level invariant needed by Hooper's
global converse.  Moving the head back over the guard recovers a genuine
parent gap of length `distance + 1`.  It is deliberately weaker than a
represented child counter frame, and is therefore retained by every shared
return, including returns from a cleanup suffix.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedSearch

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- A genuine generated search whose preceding cell has already been
cleared.  `guard` is stated in the direction opposite the generated search,
so the definition is independent of the controller orientation which
created it. -/
structure GuardedSearch (base : Nat) (c : Nat.Partrec.Code) where
  current : GenuineSearch base c
  guard :
    (current.outer.move
      (NestingMachine.opposite
        (command base c current.search).searchDirection)).read =
      blankSymbol

namespace GuardedSearch

variable {base : Nat} {c : Nat.Partrec.Code}

/-- Physical direction of the guarded generated search. -/
def direction (current : GuardedSearch base c) : Turing.Dir :=
  (command base c current.current.search).searchDirection

/-- Tape before the one-cell departure which entered the guarded search. -/
def parentOuter (current : GuardedSearch base c) :
    FullTM0.Tape (Symbol numTags) :=
  current.current.outer.move (NestingMachine.opposite current.direction)

@[simp] theorem parentOuter_read (current : GuardedSearch base c) :
    current.parentOuter.read = blankSymbol := by
  exact current.guard

/-- Departing again in the search direction restores the packaged outer
tape exactly. -/
theorem parentOuter_move (current : GuardedSearch base c) :
    current.parentOuter.move current.direction = current.current.outer := by
  funext position
  cases hdirection : current.direction <;>
    simp [parentOuter, hdirection, NestingMachine.opposite,
      FullTM0.Tape.move]

/-- One move is the same as `moveN 1`, in the form used to prepend the guard
to the packaged search gap. -/
theorem parentOuter_moveN_one (current : GuardedSearch base c) :
    current.parentOuter.moveN current.direction 1 = current.current.outer := by
  rw [← current.parentOuter_move]
  simpa using
    (FullTM0.Tape.move_moveN current.parentOuter current.direction 0).symm

/-- The erased guard and the current genuine gap form an exact parent gap
which is one cell longer. -/
theorem parentGap (current : GuardedSearch base c) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (command base c current.current.search).target.Matches
      current.parentOuter current.direction
      (current.current.distance + 1) := by
  have hprefix : ∀ i < 1,
      current.parentOuter (FullTM0.Tape.offset current.direction i) =
        blankSymbol := by
    intro i hi
    have hiZero : i = 0 := by omega
    subst i
    simpa [FullTM0.Tape.read] using current.parentOuter_read
  have htail : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c current.current.search).target.Matches
      (current.parentOuter.moveN current.direction 1) current.direction
      current.current.distance := by
    rw [current.parentOuter_moveN_one]
    exact current.current.gap
  have hfull :=
    CounterControlArbitrarySearch.SearchGap.prepend_moveN hprefix htail
  simpa [Nat.add_comm] using hfull

/-- The found tape of the guarded search is equivalently the found tape of
its one-cell-longer parent gap. -/
theorem moveN_distance_eq_parentMoveN (current : GuardedSearch base c) :
    current.current.outer.moveN current.direction current.current.distance =
      current.parentOuter.moveN current.direction
        (current.current.distance + 1) := by
  rw [← current.parentOuter_moveN_one,
    FullTM0.Tape.moveN_add]
  congr 1
  omega

/-- The guarded gap is strictly shorter than its recovered parent gap. -/
theorem distance_lt_parentDistance (current : GuardedSearch base c) :
    current.current.distance < current.current.distance + 1 := by
  omega

end GuardedSearch

end

end CounterControlGuardedSearch
end Hooper
end Kari
end LeanWang
