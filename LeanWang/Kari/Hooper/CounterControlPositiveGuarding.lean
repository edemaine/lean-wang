/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlGenuineCoordinates

/-!
# Turning a positive genuine gap into a guarded gap

If an arbitrary genuine search has positive distance, moving its entry head
one cell toward the target consumes one known blank cell.  The resulting
search has the same exact found configuration and its consumed cell is the
one-cell guard.  Strict guarded progress from distance `d - 1` therefore
becomes weak monotone progress from the original distance `d`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPositiveGuarding

open Turing
open BoundedMarkerProgram CounterControlPlan
open CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlParentContinuation
open CounterControlGuardedParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Consume the first blank cell of a positive genuine search gap. -/
def tailSearch
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance) :
    GenuineSearch base c where
  search := current.search
  outer := current.outer.move current.direction
  distance := current.distance - 1
  gap := by
    have hdistance : current.distance = current.distance - 1 + 1 := by
      omega
    have hgap := current.gap
    rw [hdistance] at hgap
    exact hgap.tail

/-- The consumed first cell is blank, so the tail search is guarded. -/
def guardedTail
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance) :
    GuardedSearch base c where
  current := tailSearch current hpositive
  guard := by
    have hblank := current.gap.blank (show 0 < current.distance by
      exact hpositive)
    change ((current.outer.move current.direction).move
      (NestingMachine.opposite current.direction)).read = blankSymbol
    have hinverse : (current.outer.move current.direction).move
        (NestingMachine.opposite current.direction) = current.outer := by
      funext position
      cases current.direction <;>
        simp [NestingMachine.opposite, FullTM0.Tape.move]
    rw [hinverse]
    simpa [FullTM0.Tape.read, FullTM0.Tape.offset] using hblank

@[simp] theorem tailSearch_search
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance) :
    (tailSearch current hpositive).search = current.search := rfl

@[simp] theorem guardedTail_distance
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance) :
    (guardedTail current hpositive).current.distance = current.distance - 1 :=
  rfl

/-- Consuming one blank cell changes the entry coordinates but not the exact
found target configuration. -/
theorem foundCfg_guardedTail
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance) :
    foundCfg (guardedTail current hpositive).current = foundCfg current := by
  have hdistance : current.distance - 1 + 1 = current.distance := by
    omega
  change
    (⟨(searchSystem base c).successState current.search,
      (current.outer.move current.direction).moveN current.direction
        (current.distance - 1)⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) =
    ⟨(searchSystem base c).successState current.search,
      current.outer.moveN current.direction current.distance⟩
  apply congrArg (fun tape =>
    (⟨(searchSystem base c).successState current.search, tape⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State))
  rw [FullTM0.Tape.move_moveN, hdistance]

/-- A strict guarded parent outcome for the consumed tail is exactly a weak
monotone entry outcome for the original positive genuine gap. -/
def monotone_of_guardedTail_parent
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance)
    (outcome : FoundGuardedParentOutcome
      (guardedTail current hpositive)) :
    FoundMonotoneGuardedEntryOutcome current := by
  have hfound := foundCfg_guardedTail current hpositive
  cases outcome with
  | logical core reaches hinside =>
      exact .logical core (by simpa [hfound] using reaches) (by
        rw [guardedTail_distance] at hinside
        omega)
  | nextSearch next reaches hdistance =>
      exact .nextSearch next (by simpa [hfound] using reaches) (by
        rw [guardedTail_distance] at hdistance
        omega)

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- If a strict guarded escape temporarily stops at a larger unguarded
search, any monotone continuation of that replay search completes the
conversion for the original positive gap. -/
theorem monotone_of_guardedTail_escape
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c) (hpositive : 0 < current.distance)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (outcome : FoundGuardedEscapeOutcome
      (guardedTail current hpositive))
    (hcontinue : ∀ next : GenuineSearch base c,
      FullTM0.ImmortalFrom (CounterControlNestingBridge.machine base c)
          (foundCfg next) →
        Nonempty (FoundMonotoneGuardedEntryOutcome next)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome current) := by
  cases outcome with
  | parent parent => exact ⟨monotone_of_guardedTail_parent current
      hpositive parent⟩
  | nextSearch next reaches hdistance =>
      have hfound := foundCfg_guardedTail current hpositive
      have hreachesNext : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (foundCfg current) next.cfg := by
        simpa [hfound] using reaches
      have himmortalNext := immortalFrom_of_reaches base c himmortal
        hreachesNext
      have hnextFound := reaches_foundCfg_of_immortal next himmortalNext
      have himmortalNextFound := immortalFrom_foundCfg next himmortalNext
      rcases hcontinue next himmortalNextFound with ⟨continued⟩
      have hle : current.distance ≤ next.distance := by
        rw [guardedTail_distance] at hdistance
        omega
      cases continued with
      | logical core hreach hinside =>
          exact ⟨.logical core
            (hreachesNext.trans (hnextFound.trans hreach))
            (hle.trans hinside)⟩
      | nextSearch guarded hreach hdistance =>
          exact ⟨.nextSearch guarded
            (hreachesNext.trans (hnextFound.trans hreach))
            (hle.trans hdistance)⟩

end

end CounterControlPositiveGuarding
end Hooper
end Kari
end LeanWang
