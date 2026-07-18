/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignals
import LeanWang.Robinson.Closed104.RedShadeGraphColoring

/-!
# Finite obstruction-signal rectangles

The horizontal and vertical signal constraints are independent one-dimensional
path problems.  Every finite sequence of selected-border orientations admits a
matching flow path.  Consequently every finite valid shaded rectangle can be
decorated by a valid obstruction-signal layer.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedSignalRectangle

open RedCycles RedShadeGraphColoring Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- The common one-dimensional signal rule.  `true` means that the interior is
on the positive side of the selected border. -/
def flowAllowed (interior : Option Bool)
    (before after : Signals.Flow) : Bool :=
  match interior with
  | none => decide (before = after)
  | some true => decide (before ≠ .none ∧ after ≠ .forward)
  | some false => decide (after ≠ .none ∧ before ≠ .backward)

def horizontalInteriorCode : Option Signals.HorizontalInterior → Option Bool
  | none => none
  | some .west => some false
  | some .east => some true

def verticalInteriorCode : Option Signals.VerticalInterior → Option Bool
  | none => none
  | some .south => some false
  | some .north => some true

@[simp] theorem flowAllowed_horizontal
    (interior : Option Signals.HorizontalInterior)
    (before after : Signals.Flow) :
    flowAllowed (horizontalInteriorCode interior) before after =
      Signals.horizontalAllowed interior
        { west := before, east := after, south := .none, north := .none } := by
  rcases interior with _ | interior
  · rfl
  · cases interior <;> rfl

@[simp] theorem flowAllowed_vertical
    (interior : Option Signals.VerticalInterior)
    (before after : Signals.Flow) :
    flowAllowed (verticalInteriorCode interior) before after =
      Signals.verticalAllowed interior
        { west := .none, east := .none, south := before, north := after } := by
  rcases interior with _ | interior
  · rfl
  · cases interior <;> rfl

theorem horizontalAllowed_ignore_vertical
    (interior : Option Signals.HorizontalInterior)
    (west east south north : Signals.Flow) :
    Signals.horizontalAllowed interior
        { west := west, east := east, south := south, north := north } =
      Signals.horizontalAllowed interior
        { west := west, east := east, south := .none, north := .none } := by
  rcases interior with _ | interior
  · rfl
  · cases interior <;> rfl

theorem verticalAllowed_ignore_horizontal
    (interior : Option Signals.VerticalInterior)
    (west east south north : Signals.Flow) :
    Signals.verticalAllowed interior
        { west := west, east := east, south := south, north := north } =
      Signals.verticalAllowed interior
        { west := .none, east := .none, south := south, north := north } := by
  rcases interior with _ | interior
  · rfl
  · cases interior <;> rfl

theorem horizontalAllowed_only_horizontal
    (interior : Option Signals.HorizontalInterior) (state : Signals.State) :
    Signals.horizontalAllowed interior state =
      Signals.horizontalAllowed interior
        { west := state.west, east := state.east,
          south := .none, north := .none } := by
  rcases interior with _ | interior
  · rfl
  · cases interior <;> rfl

theorem verticalAllowed_only_vertical
    (interior : Option Signals.VerticalInterior) (state : Signals.State) :
    Signals.verticalAllowed interior state =
      Signals.verticalAllowed interior
        { west := .none, east := .none,
          south := state.south, north := state.north } := by
  rcases interior with _ | interior
  · rfl
  · cases interior <;> rfl

/-- A matching edge-flow path through `length` consecutive cells. -/
structure FlowPath (interior : Nat → Option Bool) (length : Nat) where
  edge : Nat → Signals.Flow
  allowed : ∀ i, i < length →
    flowAllowed (interior i) (edge i) (edge (i + 1)) = true

/-- Orientation of the last selected border strictly before an edge. -/
def previousInterior (interior : Nat → Option Bool) : Nat → Option Bool
  | 0 => none
  | position + 1 =>
      match interior position with
      | some positive => some positive
      | none => previousInterior interior position

/-- Position of the last selected border strictly before an edge. -/
def previousInteriorPosition (interior : Nat → Option Bool) : Nat → Option Nat
  | 0 => none
  | position + 1 =>
      match interior position with
      | some _ => some position
      | none => previousInteriorPosition interior position

/-- First cell coordinate after the last selected border before an edge. -/
def intervalStart (interior : Nat → Option Bool) (position : Nat) : Nat :=
  match previousInteriorPosition interior position with
  | none => 0
  | some previous => previous + 1

@[simp] theorem intervalStart_succ_of_none
    (interior : Nat → Option Bool) (position : Nat)
    (hnone : interior position = none) :
    intervalStart interior (position + 1) = intervalStart interior position := by
  simp [intervalStart, previousInteriorPosition, hnone]

/-- Signed coordinate of an edge inside its current selected-border interval. -/
def intervalCoordinate (interior : Nat → Option Bool) (position : Nat) : Int :=
  (position : Int) - intervalStart interior position

/-- Orientation of the first selected border in a bounded suffix. -/
def nextInterior (interior : Nat → Option Bool) : Nat → Nat → Option Bool
  | _, 0 => none
  | position, fuel + 1 =>
      match interior position with
      | some positive => some positive
      | none => nextInterior interior (position + 1) fuel

/-- A selected border remains the previous one until another border occurs. -/
theorem previousInterior_eq_of_none_between
    {interior : Nat → Option Bool} {border position : Nat}
    {orientation : Bool}
    (selected : interior border = some orientation)
    (between : ∀ candidate, border < candidate → candidate < position →
      interior candidate = none)
    (afterBorder : border < position) :
    previousInterior interior position = some orientation := by
  have startLe : border + 1 ≤ position := by omega
  induction position, startLe using Nat.le_induction with
  | base => simp [previousInterior, selected]
  | succ position _ inductionHypothesis =>
      have positionBetween : border < position ∧ position < position + 1 := by
        omega
      have previous := inductionHypothesis
        (fun candidate lower upper => between candidate lower (by omega))
        positionBetween.1
      simp [previousInterior,
        between position positionBetween.1 positionBetween.2, previous]

/-- The first selected border in a bounded suffix has its prescribed
orientation if no oppositely oriented border occurs before it. -/
theorem nextInterior_eq_of_no_opposite_before
    {interior : Nat → Option Bool} {position border length : Nat}
    {orientation : Bool}
    (selected : interior border = some orientation)
    (noOpposite : ∀ candidate, position ≤ candidate → candidate < border →
      interior candidate ≠ some (!orientation))
    (atMostBorder : position ≤ border) (borderBeforeEnd : border < length) :
    nextInterior interior position (length - position) = some orientation := by
  induction distance : border - position generalizing position with
  | zero =>
      have positionEq : position = border := by omega
      subst position
      have fuelPositive : 0 < length - border := by omega
      obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero fuelPositive.ne'
      rw [fuelEq]
      simp [nextInterior, selected]
  | succ distance inductionHypothesis =>
      have positionBefore : position < border := by omega
      have fuelEq : length - position = length - (position + 1) + 1 := by omega
      rw [fuelEq]
      cases current : interior position with
      | none =>
          simp only [nextInterior, current]
          apply inductionHypothesis (position := position + 1)
          · intro candidate lower upper
            exact noOpposite candidate (by omega) upper
          · omega
          · omega
      | some currentOrientation =>
          cases orientation <;> cases currentOrientation
          · simp [nextInterior, current]
          · exact (noOpposite position le_rfl positionBefore current).elim
          · exact (noOpposite position le_rfl positionBefore current).elim
          · simp [nextInterior, current]

/-- A successful bounded suffix scan witnesses the selected border it found. -/
theorem exists_interior_of_nextInterior_eq_some
    {interior : Nat → Option Bool} {position fuel : Nat}
    {orientation : Bool}
    (next : nextInterior interior position fuel = some orientation) :
    ∃ candidate, position ≤ candidate ∧ candidate < position + fuel ∧
      interior candidate = some orientation := by
  induction fuel generalizing position with
  | zero => simp [nextInterior] at next
  | succ fuel inductionHypothesis =>
      cases current : interior position with
      | none =>
          simp only [nextInterior, current] at next
          obtain ⟨candidate, lower, upper, selected⟩ := inductionHypothesis next
          exact ⟨candidate, by omega, by omega, selected⟩
      | some currentOrientation =>
          simp only [nextInterior, current] at next
          cases next
          exact ⟨position, le_rfl, by omega, current⟩

/-- Canonical edge flow determined by the nearest selected borders.  The
clear case is the interval after an opening border and before a closing one. -/
def intervalEdge (interior : Nat → Option Bool) (length position : Nat) :
    Signals.Flow :=
  match nextInterior interior position (length - position) with
  | none => .backward
  | some false =>
      if previousInterior interior position = some false then .forward else .none
  | some true =>
      if previousInterior interior position = some true then .backward else .forward

@[simp] theorem intervalEdge_eq_none_iff
    (interior : Nat → Option Bool) (length position : Nat) :
    intervalEdge interior length position = .none ↔
      nextInterior interior position (length - position) = some false ∧
        previousInterior interior position ≠ some false := by
  unfold intervalEdge
  cases hnext : nextInterior interior position (length - position) with
  | none => simp
  | some next =>
      cases next with
      | false =>
          cases hprevious : previousInterior interior position with
          | none => simp
          | some previous => cases previous <;> simp
      | true =>
          cases hprevious : previousInterior interior position with
          | none => simp
          | some previous => cases previous <;> simp

/-- The nearest-border formula satisfies every one-dimensional local signal
rule. -/
def intervalPath (interior : Nat → Option Bool) (length : Nat) :
    FlowPath interior length where
  edge := intervalEdge interior length
  allowed := by
    intro position hposition
    have hlength : length - position = (length - (position + 1)) + 1 := by
      omega
    cases hcurrent : interior position with
    | none =>
        have hprevious : previousInterior interior (position + 1) =
            previousInterior interior position := by
          simp [previousInterior, hcurrent]
        have hnext : nextInterior interior position (length - position) =
            nextInterior interior (position + 1) (length - (position + 1)) := by
          rw [hlength]
          simp [nextInterior, hcurrent]
        simp [flowAllowed, intervalEdge, hprevious, hnext]
    | some current =>
        cases current with
        | false =>
            cases hprevious : previousInterior interior position with
            | none =>
                cases hnext : nextInterior interior (position + 1)
                    (length - (position + 1)) with
                | none => simp [flowAllowed, intervalEdge, hcurrent,
                    hprevious, hnext, hlength, nextInterior]
                | some next => cases next <;>
                    simp [flowAllowed, intervalEdge, hcurrent,
                      hprevious, hnext, hlength, previousInterior, nextInterior]
            | some previous =>
                cases previous <;>
                  cases hnext : nextInterior interior (position + 1)
                    (length - (position + 1)) with
                  | none => simp [flowAllowed, intervalEdge, hcurrent,
                      hprevious, hnext, hlength, nextInterior]
                  | some next => cases next <;>
                      simp [flowAllowed, intervalEdge, hcurrent,
                        hprevious, hnext, hlength, previousInterior, nextInterior]
        | true =>
            cases hprevious : previousInterior interior position with
            | none =>
                cases hnext : nextInterior interior (position + 1)
                    (length - (position + 1)) with
                | none => simp [flowAllowed, intervalEdge, hcurrent,
                    hprevious, hnext, hlength, nextInterior]
                | some next => cases next <;>
                    simp [flowAllowed, intervalEdge, hcurrent,
                      hprevious, hnext, hlength, previousInterior, nextInterior]
            | some previous =>
                cases previous <;>
                  cases hnext : nextInterior interior (position + 1)
                    (length - (position + 1)) with
                  | none => simp [flowAllowed, intervalEdge, hcurrent,
                      hprevious, hnext, hlength, nextInterior]
                  | some next => cases next <;>
                      simp [flowAllowed, intervalEdge, hcurrent,
                        hprevious, hnext, hlength, previousInterior, nextInterior]

/-- A selected border cannot have clear canonical signal edges on both sides. -/
theorem interior_eq_none_of_adjacent_clear
    (interior : Nat → Option Bool) {length position : Nat}
    (hposition : position < length)
    (hleft : intervalEdge interior length position = .none)
    (hright : intervalEdge interior length (position + 1) = .none) :
    interior position = none := by
  have allowed := (intervalPath interior length).allowed position hposition
  change flowAllowed (interior position)
    (intervalEdge interior length position)
    (intervalEdge interior length (position + 1)) = true at allowed
  rw [hleft, hright] at allowed
  cases hcurrent : interior position with
  | none => rfl
  | some current =>
      cases current <;> simp [flowAllowed, hcurrent] at allowed

/-- The selected-border interval origin is constant across a clear cell. -/
theorem intervalStart_succ_of_adjacent_clear
    (interior : Nat → Option Bool) {length position : Nat}
    (hposition : position < length)
    (hleft : intervalEdge interior length position = .none)
    (hright : intervalEdge interior length (position + 1) = .none) :
    intervalStart interior (position + 1) = intervalStart interior position := by
  apply intervalStart_succ_of_none
  exact interior_eq_none_of_adjacent_clear interior hposition hleft hright

/-- Interval coordinates increase by one along a clear canonical signal run. -/
theorem intervalCoordinate_succ_of_adjacent_clear
    (interior : Nat → Option Bool) {length position : Nat}
    (hposition : position < length)
    (hleft : intervalEdge interior length position = .none)
    (hright : intervalEdge interior length (position + 1) = .none) :
    intervalCoordinate interior (position + 1) =
      intervalCoordinate interior position + 1 := by
  rw [intervalCoordinate, intervalCoordinate,
    intervalStart_succ_of_adjacent_clear interior hposition hleft hright]
  omega

/-- Canonical obstruction path given by the nearest-border formula. -/
def canonicalPath (interior : Nat → Option Bool) (length : Nat) :
    FlowPath interior length :=
  intervalPath interior length

/-- Finite analogue of the compatible shaded plane signal grid. -/
structure ValidSignalRectangle (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (signalGrid : Nat → Nat → Signals.State)
    (width height : Nat) : Prop where
  shadeValid : ValidShadeRectangle indexGrid shadeGrid width height
  signalAllowed : ∀ x y, x < width → y < height →
    ShadedSignals.locallyAllowed
      ((indexGrid (x / 2) (y / 2), quadrantAt x y), shadeGrid x y)
      (signalGrid x y) = true
  hmatch : ∀ x y, x + 1 < width → y < height →
    (signalGrid x y).east = (signalGrid (x + 1) y).west
  vmatch : ∀ x y, x < width → y + 1 < height →
    (signalGrid x y).north = (signalGrid x (y + 1)).south

variable (indexGrid : Nat → Nat → Index)
  (shadeGrid : Nat → Nat → RedShades.State) (width height : Nat)

def horizontalInterior (x y : Nat) : Option Bool :=
  horizontalInteriorCode
    (ShadedSignals.selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (shadeGrid x y))

def verticalInterior (x y : Nat) : Option Bool :=
  verticalInteriorCode
    (ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (shadeGrid x y))

def horizontalPath (y : Nat) :
    FlowPath (fun x => horizontalInterior indexGrid shadeGrid x y) width :=
  canonicalPath (fun x => horizontalInterior indexGrid shadeGrid x y) width

def verticalPath (x : Nat) :
    FlowPath (fun y => verticalInterior indexGrid shadeGrid x y) height :=
  canonicalPath (fun y => verticalInterior indexGrid shadeGrid x y) height

/-- Combine the independent row and column edge paths into signal states. -/
def signalGrid : Nat → Nat → Signals.State := fun x y =>
  { west := (horizontalPath indexGrid shadeGrid width y).edge x
    east := (horizontalPath indexGrid shadeGrid width y).edge (x + 1)
    south := (verticalPath indexGrid shadeGrid height x).edge y
    north := (verticalPath indexGrid shadeGrid height x).edge (y + 1) }

@[simp] theorem signalGrid_west (x y : Nat) :
    (signalGrid indexGrid shadeGrid width height x y).west =
      (horizontalPath indexGrid shadeGrid width y).edge x := rfl

@[simp] theorem signalGrid_east (x y : Nat) :
    (signalGrid indexGrid shadeGrid width height x y).east =
      (horizontalPath indexGrid shadeGrid width y).edge (x + 1) := rfl

@[simp] theorem signalGrid_south (x y : Nat) :
    (signalGrid indexGrid shadeGrid width height x y).south =
      (verticalPath indexGrid shadeGrid height x).edge y := rfl

@[simp] theorem signalGrid_north (x y : Nat) :
    (signalGrid indexGrid shadeGrid width height x y).north =
      (verticalPath indexGrid shadeGrid height x).edge (y + 1) := rfl

theorem signalGrid_allowed (x y : Nat) (hx : x < width) (hy : y < height) :
    ShadedSignals.locallyAllowed
      ((indexGrid (x / 2) (y / 2), quadrantAt x y), shadeGrid x y)
      (signalGrid indexGrid shadeGrid width height x y) = true := by
  have hh := (horizontalPath indexGrid shadeGrid width y).allowed x hx
  have hv := (verticalPath indexGrid shadeGrid height x).allowed y hy
  simp only [horizontalInterior, flowAllowed_horizontal] at hh
  simp only [verticalInterior, flowAllowed_vertical] at hv
  rw [ShadedSignals.locallyAllowed, Bool.and_eq_true]
  simp only [ShadedSignals.selectedVerticalInterior?,
    ShadedSignals.selectedHorizontalInterior?]
  constructor
  · rw [horizontalAllowed_only_horizontal, signalGrid_west, signalGrid_east]
    exact hh
  · rw [verticalAllowed_only_vertical, signalGrid_south, signalGrid_north]
    exact hv

/-- Every finite valid shaded rectangle admits a matching signal decoration. -/
theorem validSignalRectangle
    (shadeValid : ValidShadeRectangle indexGrid shadeGrid width height) :
    ValidSignalRectangle indexGrid shadeGrid
      (signalGrid indexGrid shadeGrid width height) width height := by
  constructor
  · exact shadeValid
  · exact signalGrid_allowed indexGrid shadeGrid width height
  · intro x y _ _
    rfl
  · intro x y _ _
    rfl

theorem exists_validSignalRectangle
    (shadeValid : ValidShadeRectangle indexGrid shadeGrid width height) :
    ∃ signalGrid : Nat → Nat → Signals.State,
      ValidSignalRectangle indexGrid shadeGrid signalGrid width height :=
  ⟨signalGrid indexGrid shadeGrid width height,
    validSignalRectangle indexGrid shadeGrid width height shadeValid⟩

end ShadedSignalRectangle
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
