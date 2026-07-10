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
