/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Find

/-!
# One-dimensional nearest-boundary search

This file contains the axis-independent order argument used to extract the
nearest selected boundary on either side of a coordinate.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightBoundarySearch

/-- A finite run of zero-weight steps leaves an integer potential unchanged. -/
theorem potential_eq_of_zero_steps
    {potential weight : Nat -> Int} {start finish : Nat}
    (startLeFinish : start <= finish)
    (step : forall position, start < position -> position <= finish ->
      potential position = potential (position - 1) + weight position)
    (zero : forall position, start < position -> position <= finish ->
      weight position = 0) :
    potential finish = potential start := by
  induction finish, startLeFinish using Nat.le_induction with
  | base => rfl
  | succ finish _ inductionHypothesis =>
      rw [step (finish + 1) (by omega) le_rfl,
        zero (finish + 1) (by omega) le_rfl]
      have previous : finish + 1 - 1 = finish := by omega
      rw [previous, inductionHypothesis
        (fun position lower upper => step position lower (by omega))
        (fun position lower upper => zero position lower (by omega))]
      omega

/-- A nearest `-1` step above a unit-height point contradicts positivity. -/
theorem negative_step_after_false
    {potential weight : Nat -> Int} {start boundary : Nat}
    (startBoundary : start < boundary)
    (startHeight : potential start = 1)
    (step : forall position, start < position -> position <= boundary ->
      potential position = potential (position - 1) + weight position)
    (zero : forall position, start < position -> position < boundary ->
      weight position = 0)
    (negative : weight boundary = -1)
    (positive : 1 <= potential boundary) : False := by
  have stable := potential_eq_of_zero_steps
    (potential := potential) (weight := weight)
    (start := start) (finish := boundary - 1) (by omega)
    (fun position lower upper => step position lower (by omega))
    (fun position lower upper => zero position lower (by omega))
  have boundaryStep := step boundary startBoundary le_rfl
  rw [stable, startHeight, negative] at boundaryStep
  omega

/-- A nearest `+1` step below a unit-height point contradicts positivity at
the preceding point. -/
theorem positive_step_before_false
    {potential weight : Nat -> Int} {boundary finish : Nat}
    (boundaryFinish : boundary <= finish)
    (finishHeight : potential finish = 1)
    (boundaryStep :
      potential boundary = potential (boundary - 1) + weight boundary)
    (stepAfter : forall position, boundary < position -> position <= finish ->
      potential position = potential (position - 1) + weight position)
    (zero : forall position, boundary < position -> position <= finish ->
      weight position = 0)
    (positiveWeight : weight boundary = 1)
    (positiveBefore : 1 <= potential (boundary - 1)) : False := by
  have stable := potential_eq_of_zero_steps
    (potential := potential) (weight := weight)
    (start := boundary) (finish := finish) boundaryFinish stepAfter zero
  rw [finishHeight] at stable
  rw [stable.symm, positiveWeight] at boundaryStep
  omega

theorem exists_first_after
    {P : Nat -> Prop} {start finish : Nat}
    (hstart : start < finish) (hfinish : P finish) :
    exists first, start < first /\ first <= finish /\ P first /\
      forall value, start < value -> value < first -> Not (P value) := by
  classical
  let Q : Nat -> Prop := fun distance =>
    0 < distance /\ start + distance <= finish /\ P (start + distance)
  have existsQ : exists distance, Q distance := by
    refine ⟨finish - start, ?_⟩
    dsimp [Q]
    have hsum : start + (finish - start) = finish := by omega
    exact ⟨by omega, by omega, by simpa [hsum] using hfinish⟩
  let distance := Nat.find existsQ
  have found : Q distance := Nat.find_spec existsQ
  refine ⟨start + distance, by simpa [Q] using found.1,
    found.2.1, found.2.2, ?_⟩
  intro value hvalueStart hvalueFirst hvalue
  have candidate : Q (value - start) := by
    dsimp [Q]
    have hsum : start + (value - start) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsum] using hvalue⟩
  have minimal := Nat.find_min' existsQ candidate
  dsimp [distance] at hvalueFirst
  omega

theorem exists_last_before
    {P : Nat -> Prop} {first finish : Nat}
    (hfirst : first < finish) (hfirstP : P first) :
    exists last, first <= last /\ last < finish /\ P last /\
      forall value, last < value -> value < finish -> Not (P value) := by
  classical
  let Q : Nat -> Prop := fun distance =>
    0 < distance /\ distance <= finish - first /\ P (finish - distance)
  have existsQ : exists distance, Q distance := by
    refine ⟨finish - first, ?_⟩
    dsimp [Q]
    have hsub : finish - (finish - first) = first := by omega
    exact ⟨by omega, le_rfl, by simpa [hsub] using hfirstP⟩
  let distance := Nat.find existsQ
  have found : Q distance := Nat.find_spec existsQ
  refine ⟨finish - distance, by omega, by omega, found.2.2, ?_⟩
  intro value hlastValue hvalueFinish hvalue
  have candidate : Q (finish - value) := by
    dsimp [Q]
    have hsub : finish - (finish - value) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsub] using hvalue⟩
  have minimal := Nat.find_min' existsQ candidate
  dsimp [distance] at hlastValue
  omega

/-- Given any selected point in an open interval, expose the current point or
the nearest selected point on one side.  The two callbacks provide the
domain-specific orientation of those nearest points. -/
theorem boundary_of_exists_selected
    {Direction : Type} {selected : Nat -> Option Direction}
    {lower coordinate upper : Nat} {after before : Direction}
    (witness : exists boundary, lower < boundary /\ boundary < upper /\
      selected boundary ≠ none)
    (orientAfter : forall boundary, coordinate < boundary -> boundary < upper ->
      selected boundary ≠ none ->
      (forall value, coordinate < value -> value < boundary ->
        selected value = none) ->
      selected boundary = some after)
    (orientBefore : forall boundary, lower < boundary -> boundary < coordinate ->
      selected boundary ≠ none ->
      (forall value, boundary < value -> value < coordinate ->
        selected value = none) ->
      selected coordinate = none ->
      selected boundary = some before) :
    selected coordinate ≠ none \/
      (exists boundary, coordinate < boundary /\ boundary < upper /\
        selected boundary = some after /\
        forall value, coordinate < value -> value < boundary ->
          selected value = none) \/
      (exists boundary, lower < boundary /\ boundary < coordinate /\
        selected boundary = some before /\
        forall value, boundary < value -> value < coordinate ->
          selected value = none) := by
  by_cases atCoordinate : selected coordinate ≠ none
  · exact Or.inl atCoordinate
  have coordinateClear : selected coordinate = none := not_ne_iff.mp atCoordinate
  rcases witness with ⟨boundary, boundaryLower, boundaryUpper, boundarySelected⟩
  rcases lt_trichotomy coordinate boundary with afterCoordinate | equal | beforeCoordinate
  · rcases exists_first_after (P := fun value => selected value ≠ none)
        afterCoordinate boundarySelected with
      ⟨first, coordinateFirst, firstBoundary, firstSelected, between⟩
    have firstUpper : first < upper := by omega
    have oriented := orientAfter first coordinateFirst firstUpper firstSelected
      (fun value coordinateValue valueFirst =>
        not_ne_iff.mp (between value coordinateValue valueFirst))
    exact Or.inr (Or.inl ⟨first, coordinateFirst, firstUpper, oriented,
      fun value coordinateValue valueFirst =>
        not_ne_iff.mp (between value coordinateValue valueFirst)⟩)
  · subst boundary
    exact (boundarySelected coordinateClear).elim
  · rcases exists_last_before (P := fun value => selected value ≠ none)
        beforeCoordinate boundarySelected with
      ⟨last, boundaryLast, lastCoordinate, lastSelected, between⟩
    have lastLower : lower < last := by omega
    have oriented := orientBefore last lastLower lastCoordinate lastSelected
      (fun value lastValue valueCoordinate =>
        not_ne_iff.mp (between value lastValue valueCoordinate)) coordinateClear
    exact Or.inr (Or.inr ⟨last, lastLower, lastCoordinate, oriented,
      fun value lastValue valueCoordinate =>
        not_ne_iff.mp (between value lastValue valueCoordinate)⟩)

end OrientedLightBoundarySearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
