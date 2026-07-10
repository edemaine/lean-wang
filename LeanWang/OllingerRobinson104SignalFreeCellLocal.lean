/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SignalQuarterEmbedding

/-!
The finite free-cell gadget repeated inside Robinson boards.

Below every parent and each of its four children, a depth-two supertile contains
an `8 x 8` quarter block. Its red boundaries are at local coordinates `3` and
`6`; coordinates `4` and `5` between them carry no perpendicular red boundary.
The child quadrant selects `4` or `5` as the canonical free coordinate.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace Signals
namespace FreeCellLocal

open Figure16 QuarterGeometry QuarterEmbedding RedCycles

set_option maxRecDepth 20000

def quadrantAt (x y : Nat) : Quadrant :=
  Quadrant.ofBits (x % 2 == 1, y % 2 == 1)

def componentAt (grid : Nat → Nat → Index) (x y : Nat) : Thick :=
  (components (grid (x / 2) (y / 2))).2.1

def verticalInteriorAt (grid : Nat → Nat → Index) (x y : Nat) :
    Option HorizontalInterior :=
  verticalInterior? (componentAt grid x y) (quadrantAt x y)

def horizontalInteriorAt (grid : Nat → Nat → Index) (x y : Nat) :
    Option VerticalInterior :=
  horizontalInterior? (componentAt grid x y) (quadrantAt x y)

def localGrid (parent : Index) (ix iy : Fin 2) : Nat → Nat → Index :=
  iterateRefine 2 (fun _ _ => childBlock parent ix iy)

/-- Named form of the finite local free-cell geometry. -/
structure Geometry (parent : Index) (ix iy : Fin 2) : Prop where
  westBoundary :
    verticalInteriorAt (localGrid parent ix iy) 3 (4 + iy.val) = some .east
  eastBoundary :
    verticalInteriorAt (localGrid parent ix iy) 6 (4 + iy.val) = some .west
  verticalClear4 :
    verticalInteriorAt (localGrid parent ix iy) 4 (4 + iy.val) = none
  verticalClear5 :
    verticalInteriorAt (localGrid parent ix iy) 5 (4 + iy.val) = none
  southBoundary :
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 3 = some .north
  northBoundary :
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 6 = some .south
  horizontalClear4 :
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 4 = none
  horizontalClear5 :
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 5 = none

/- One native audit covers all 416 parent/child-quadrant cases. -/
set_option linter.style.nativeDecide false in
theorem geometryFacts (parent : Index) (ix iy : Fin 2) :
    verticalInteriorAt (localGrid parent ix iy) 3 (4 + iy.val) = some .east ∧
    verticalInteriorAt (localGrid parent ix iy) 6 (4 + iy.val) = some .west ∧
    verticalInteriorAt (localGrid parent ix iy) 4 (4 + iy.val) = none ∧
    verticalInteriorAt (localGrid parent ix iy) 5 (4 + iy.val) = none ∧
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 3 = some .north ∧
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 6 = some .south ∧
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 4 = none ∧
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) 5 = none := by
  revert parent ix iy
  native_decide

theorem geometry (parent : Index) (ix iy : Fin 2) : Geometry parent ix iy := by
  have h := geometryFacts parent ix iy
  exact {
    westBoundary := h.1
    eastBoundary := h.2.1
    verticalClear4 := h.2.2.1
    verticalClear5 := h.2.2.2.1
    southBoundary := h.2.2.2.2.1
    northBoundary := h.2.2.2.2.2.1
    horizontalClear4 := h.2.2.2.2.2.2.1
    horizontalClear5 := h.2.2.2.2.2.2.2
  }

theorem Geometry.verticalClearSelected {parent : Index} {ix iy : Fin 2}
    (geometry : Geometry parent ix iy) :
    verticalInteriorAt (localGrid parent ix iy) (4 + ix.val) (4 + iy.val) = none := by
  fin_cases ix
  · simpa using geometry.verticalClear4
  · simpa using geometry.verticalClear5

theorem Geometry.horizontalClearSelected {parent : Index} {ix iy : Fin 2}
    (geometry : Geometry parent ix iy) :
    horizontalInteriorAt (localGrid parent ix iy) (4 + ix.val) (4 + iy.val) = none := by
  fin_cases iy
  · simpa using geometry.horizontalClear4
  · simpa using geometry.horizontalClear5

end FreeCellLocal
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
