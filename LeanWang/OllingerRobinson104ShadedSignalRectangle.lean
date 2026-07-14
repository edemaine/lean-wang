/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedSignals
import LeanWang.OllingerRobinson104RedShadeGraphColoring

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

namespace FlowPath

/-- Append one prescribed edge to a finite flow path. -/
def snoc {interior : Nat → Option Bool} {length : Nat}
    (path : FlowPath interior length) (last : Signals.Flow)
    (allowedLast : flowAllowed (interior length) (path.edge length) last = true) :
    FlowPath interior (length + 1) where
  edge := fun i => if i = length + 1 then last else path.edge i
  allowed := by
    intro i hi
    by_cases hprefix : i < length
    · have hiNe : i ≠ length + 1 := by omega
      have hiNextNe : i + 1 ≠ length + 1 := by omega
      change flowAllowed (interior i)
        (if i = length + 1 then last else path.edge i)
        (if i + 1 = length + 1 then last else path.edge (i + 1)) = true
      rw [if_neg hiNe, if_neg hiNextNe]
      exact path.allowed i hprefix
    · have hiEq : i = length := by omega
      subst i
      have hlengthNe : length ≠ length + 1 := by omega
      change flowAllowed (interior length)
        (if length = length + 1 then last else path.edge length)
        (if length + 1 = length + 1 then last else path.edge (length + 1)) = true
      rw [if_neg hlengthNe, if_pos rfl]
      exact allowedLast

@[simp] theorem snoc_last {interior : Nat → Option Bool} {length : Nat}
    (path : FlowPath interior length) (last : Signals.Flow)
    (allowedLast : flowAllowed (interior length) (path.edge length) last = true) :
    (path.snoc last allowedLast).edge (length + 1) = last := by
  simp [snoc]

end FlowPath

/-- Every finite orientation sequence has paths ending in each of the three
endpoint classes needed to extend across another selected border. -/
theorem exists_flowPaths (interior : Nat → Option Bool) (length : Nat) :
    (∃ path : FlowPath interior length,
        path.edge length = .backward) ∧
      (∃ path : FlowPath interior length,
        path.edge length ≠ .backward) ∧
      (∃ path : FlowPath interior length,
        path.edge length ≠ .none) := by
  induction length with
  | zero =>
      refine ⟨⟨{ edge := fun _ => .backward, allowed := by omega }, rfl⟩,
        ⟨{ edge := fun _ => .none, allowed := by omega }, by simp⟩,
        ⟨{ edge := fun _ => .forward, allowed := by omega }, by simp⟩⟩
  | succ length ih =>
      rcases ih with ⟨⟨backwardPath, hbackward⟩,
        ⟨notBackwardPath, hnotBackward⟩,
        ⟨nonemptyPath, hnonempty⟩⟩
      cases hlast : interior length with
      | none =>
          let backwardNext := backwardPath.snoc (backwardPath.edge length) (by
            simp [flowAllowed, hlast])
          let notBackwardNext := notBackwardPath.snoc (notBackwardPath.edge length) (by
            simp [flowAllowed, hlast])
          let nonemptyNext := nonemptyPath.snoc (nonemptyPath.edge length) (by
            simp [flowAllowed, hlast])
          refine ⟨⟨backwardNext, ?_⟩,
            ⟨notBackwardNext, ?_⟩, ⟨nonemptyNext, ?_⟩⟩
          · simp [backwardNext, hbackward]
          · simpa [notBackwardNext] using hnotBackward
          · simpa [nonemptyNext] using hnonempty
      | some positive =>
          cases positive with
          | false =>
              have hallowedBackward : flowAllowed (interior length)
                  (notBackwardPath.edge length) .backward = true := by
                simp [flowAllowed, hlast, hnotBackward]
              have hallowedForward : flowAllowed (interior length)
                  (notBackwardPath.edge length) .forward = true := by
                simp [flowAllowed, hlast, hnotBackward]
              refine ⟨⟨notBackwardPath.snoc .backward hallowedBackward, by simp⟩,
                ⟨notBackwardPath.snoc .forward hallowedForward, by simp⟩,
                ⟨notBackwardPath.snoc .forward hallowedForward, by simp⟩⟩
          | true =>
              have hallowedBackward : flowAllowed (interior length)
                  (nonemptyPath.edge length) .backward = true := by
                simp [flowAllowed, hlast, hnonempty]
              have hallowedNone : flowAllowed (interior length)
                  (nonemptyPath.edge length) .none = true := by
                simp [flowAllowed, hlast, hnonempty]
              refine ⟨⟨nonemptyPath.snoc .backward hallowedBackward, by simp⟩,
                ⟨nonemptyPath.snoc .none hallowedNone, by simp⟩,
                ⟨nonemptyPath.snoc .backward hallowedBackward, by simp⟩⟩

theorem exists_flowPath (interior : Nat → Option Bool) (length : Nat) :
    Nonempty (FlowPath interior length) := by
  rcases exists_flowPaths interior length with ⟨⟨path, _⟩, _⟩
  exact ⟨path⟩

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

noncomputable def horizontalPath (y : Nat) :
    FlowPath (fun x => horizontalInterior indexGrid shadeGrid x y) width :=
  Classical.choice (exists_flowPath
    (fun x => horizontalInterior indexGrid shadeGrid x y) width)

noncomputable def verticalPath (x : Nat) :
    FlowPath (fun y => verticalInterior indexGrid shadeGrid x y) height :=
  Classical.choice (exists_flowPath
    (fun y => verticalInterior indexGrid shadeGrid x y) height)

/-- Combine the independent row and column edge paths into signal states. -/
noncomputable def signalGrid : Nat → Nat → Signals.State := fun x y =>
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
