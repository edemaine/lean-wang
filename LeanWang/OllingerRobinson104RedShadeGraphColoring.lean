/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraph

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

open Signals.FreeCellLocal

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

end RedShadeGraphColoring
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
