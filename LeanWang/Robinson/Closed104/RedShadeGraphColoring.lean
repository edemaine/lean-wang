/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphBoundedPath

/-!
# Finite red-shade rectangles

This module records the local allowance and edge-matching conditions used by
finite shaded supertiles.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphColoring

open Signals.FreeCellLocal RedShadeGraph RedShadeGraphBoundedPath

/-- The finite analogue of `ValidShadeGrid`. -/
structure ValidShadeRectangle (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → RedShades.State) (width height : Nat) : Prop where
  allowed : ∀ x y, x < width → y < height →
    RedShades.locallyAllowed
      (indexGrid (x / 2) (y / 2), quadrantAt x y) (stateGrid x y) = true
  hmatch : ∀ x y, x + 1 < width → y < height →
    (stateGrid x y).east = (stateGrid (x + 1) y).west
  vmatch : ∀ x y, x < width → y + 1 < height →
    (stateGrid x y).north = (stateGrid x (y + 1)).south

theorem link_soundOnRectangle
    {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State} {width height : Nat}
    (valid : ValidShadeRectangle indexGrid stateGrid width height)
    {first second : Port} {parity : Bool}
    (link : Link indexGrid first second parity)
    (firstBounds : PortInBounds first width height)
    (secondBounds : PortInBounds second width height) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction link with
  | horizontalMatch x y =>
      exact valid.hmatch x y secondBounds.1 secondBounds.2
  | verticalMatch x y =>
      exact valid.vmatch x y secondBounds.1 secondBounds.2
  | horizontal x y hpath =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at hpath
      exact RedShades.horizontal_eq_of_allowedFor allowed hpath
  | vertical x y hpath =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at hpath
      exact RedShades.vertical_eq_of_allowedFor allowed hpath
  | westNorth x y hwest hnorth =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at hwest hnorth
      exact RedShades.west_north_corner_eq_of_allowedFor allowed hwest hnorth
  | westSouth x y hwest hsouth =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at hwest hsouth
      exact RedShades.west_south_corner_eq_of_allowedFor allowed hwest hsouth
  | eastNorth x y heast hnorth =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at heast hnorth
      exact RedShades.east_north_corner_eq_of_allowedFor allowed heast hnorth
  | eastSouth x y heast hsouth =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at heast hsouth
      exact RedShadeGraph.east_south_corner_eq_of_allowedFor
        allowed heast hsouth
  | crossing x y hhorizontal hvertical =>
      have allowed := valid.allowed x y firstBounds.1 firstBounds.2
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      unfold componentAt at hhorizontal hvertical
      apply related_true_of_ne_of_present
      · exact RedShades.west_present_of_allowedFor allowed (by
          simp [RedShades.hasWest, hhorizontal])
      · exact RedShades.south_present_of_allowedFor allowed (by
          simp [RedShades.hasSouth, hvertical])
      · exact RedShades.crossing_opposite_of_allowedFor
          allowed hhorizontal hvertical
  | symm link ih =>
      exact (ih secondBounds firstBounds).symm

theorem boundedPath_soundOnRectangle
    {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State} {width height : Nat}
    (valid : ValidShadeRectangle indexGrid stateGrid width height)
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction path with
  | refl port _ => exact Related.refl _
  | ofLink link firstBounds secondBounds =>
      exact link_soundOnRectangle valid link firstBounds secondBounds
  | trans firstPath secondPath firstIH secondIH =>
      exact Related.trans firstIH secondIH

/-- A finite valid assignment carries a shade exactly on the ports present in
the underlying unshaded geometry. -/
theorem value_isSome_eq_portPresent
    {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State} {width height : Nat}
    (valid : ValidShadeRectangle indexGrid stateGrid width height)
    (port : Port) (bounds : PortInBounds port width height) :
    (value stateGrid port).isSome = portPresent indexGrid port := by
  rcases port with ⟨x, y, side⟩
  have allowed := valid.allowed x y bounds.1 bounds.2
  unfold RedShades.locallyAllowed at allowed
  change RedShades.allowedFor (componentAt indexGrid x y) (quadrantAt x y)
    (stateGrid x y) = true at allowed
  simp only [RedShades.allowedFor, Bool.and_eq_true, decide_eq_true_eq,
    RedShades.optionPresent] at allowed
  cases side <;> simp only [value, portPresent] <;> aesop

end RedShadeGraphColoring
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
