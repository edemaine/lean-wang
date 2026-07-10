/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShades
import LeanWang.OllingerRobinson104SignalFreeCellLocal

/-!
Path-level propagation for the light/dark red-wire layer.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadePaths

open RedCycles Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A locally allowed, edge-matching shade assignment over a quarter grid. -/
structure ValidShadeGrid (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → RedShades.State) : Prop where
  allowed : ∀ x y,
    RedShades.locallyAllowed
      (indexGrid (x / 2) (y / 2), quadrantAt x y) (stateGrid x y) = true
  hmatch : ∀ x y, (stateGrid x y).east = (stateGrid (x + 1) y).west
  vmatch : ∀ x y, (stateGrid x y).north = (stateGrid x (y + 1)).south

theorem ValidShadeGrid.horizontal_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasHorizontal
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).east := by
  have hallowed := valid.allowed x y
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  unfold componentAt at hpath
  exact RedShades.horizontal_eq_of_allowedFor hallowed hpath

theorem ValidShadeGrid.vertical_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasVertical
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).south = (stateGrid x y).north := by
  have hallowed := valid.allowed x y
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  unfold componentAt at hpath
  exact RedShades.vertical_eq_of_allowedFor hallowed hpath

theorem ValidShadeGrid.west_north_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hwest : RedShades.cornerWest
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hnorth : RedShades.cornerNorth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).north := by
  have hallowed := valid.allowed x y
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  unfold componentAt at hwest hnorth
  exact RedShades.west_north_corner_eq_of_allowedFor hallowed hwest hnorth

theorem ValidShadeGrid.west_south_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hwest : RedShades.cornerWest
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hsouth : RedShades.cornerSouth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).south := by
  have hallowed := valid.allowed x y
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  unfold componentAt at hwest hsouth
  exact RedShades.west_south_corner_eq_of_allowedFor hallowed hwest hsouth

/-- Equality of horizontal shade across a sequence of path quarters. -/
theorem horizontal_shade_across
    (state : Nat → RedShades.State) (start count : Nat)
    (hmatch : ∀ i, i ≤ count →
      (state (start + i)).east = (state (start + i + 1)).west)
    (htransmit : ∀ i, i < count →
      (state (start + i + 1)).west = (state (start + i + 1)).east) :
    (state start).east = (state (start + count + 1)).west := by
  induction count with
  | zero => simpa using hmatch 0 (by omega)
  | succ count ih =>
      have hprefix := ih
        (fun i hi => hmatch i (by omega))
        (fun i hi => htransmit i (by omega))
      calc
        (state start).east = (state (start + count + 1)).west := hprefix
        _ = (state (start + count + 1)).east := htransmit count (by omega)
        _ = (state (start + (count + 1) + 1)).west := by
          simpa [Nat.add_assoc] using hmatch (count + 1) (by omega)

/-- Equality of vertical shade across a sequence of path quarters. -/
theorem vertical_shade_across
    (state : Nat → RedShades.State) (start count : Nat)
    (hmatch : ∀ i, i ≤ count →
      (state (start + i)).north = (state (start + i + 1)).south)
    (htransmit : ∀ i, i < count →
      (state (start + i + 1)).south = (state (start + i + 1)).north) :
    (state start).north = (state (start + count + 1)).south := by
  induction count with
  | zero => simpa using hmatch 0 (by omega)
  | succ count ih =>
      have hprefix := ih
        (fun i hi => hmatch i (by omega))
        (fun i hi => htransmit i (by omega))
      calc
        (state start).north = (state (start + count + 1)).south := hprefix
        _ = (state (start + count + 1)).north := htransmit count (by omega)
        _ = (state (start + (count + 1) + 1)).south := by
          simpa [Nat.add_assoc] using hmatch (count + 1) (by omega)

end RedShadePaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
