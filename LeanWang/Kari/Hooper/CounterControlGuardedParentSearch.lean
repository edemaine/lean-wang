/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedCoordinates
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlGenuineCoordinates

/-!
# Viewing a guarded search from its parent cell

The blank guard immediately behind a generated search can be included as the
first cell of an ordinary genuine search.  This increases its measured gap by
one without changing the exact found configuration.  Consequently, a weak
monotone continuation of the parent view is a strict guarded escape for the
original search.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedParentSearch

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Include the erased guard as the first blank cell of a genuine search. -/
def parentSearch
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) : GenuineSearch base c where
  search := current.current.search
  outer := current.parentOuter
  distance := current.current.distance + 1
  gap := current.parentGap

@[simp] theorem parentSearch_search
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) :
    (parentSearch current).search = current.current.search := rfl

@[simp] theorem parentSearch_distance
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) :
    (parentSearch current).distance = current.current.distance + 1 := rfl

/-- The parent view selects exactly the same generated raw command. -/
@[simp] theorem parentSearch_selectedRaw
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) :
    (parentSearch current).selectedRaw = current.selectedRaw := rfl

/-- Adding the guard changes the entry coordinate, but not the found target
configuration. -/
@[simp] theorem foundCfg_parentSearch
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c) :
    foundCfg (parentSearch current) = foundCfg current.current := by
  change
    (⟨(searchSystem base c).successState current.current.search,
      current.parentOuter.moveN current.direction
        (current.current.distance + 1)⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) =
    ⟨(searchSystem base c).successState current.current.search,
      current.current.outer.moveN current.direction
        current.current.distance⟩
  congr 1
  exact current.moveN_distance_eq_parentMoveN.symm

/-- Weak progress measured from the one-cell-longer parent view is strict
progress measured from the original guarded search. -/
def escape_of_parentMonotone
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (outcome : FoundMonotoneGuardedEntryOutcome (parentSearch current)) :
    FoundGuardedEscapeOutcome current := by
  cases outcome with
  | logical core reaches hinside =>
      exact .parent (.logical core (by simpa using reaches) (by
        rw [parentSearch_distance] at hinside
        omega))
  | nextSearch next reaches hdistance =>
      exact .parent (.nextSearch next (by simpa using reaches) (by
        rw [parentSearch_distance] at hdistance
        omega))

/-- Consumer-facing nonempty form of `escape_of_parentMonotone`. -/
theorem foundGuardedEscapeOutcome_of_parentMonotone
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (outcome : Nonempty
      (FoundMonotoneGuardedEntryOutcome (parentSearch current))) :
    Nonempty (FoundGuardedEscapeOutcome current) := by
  rcases outcome with ⟨outcome⟩
  exact ⟨escape_of_parentMonotone current outcome⟩

end

end CounterControlGuardedParentSearch
end Hooper
end Kari
end LeanWang
