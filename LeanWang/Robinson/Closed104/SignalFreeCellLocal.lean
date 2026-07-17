/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.Signals

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

open Figure16 QuarterGeometry RedCycles

set_option maxRecDepth 20000

def quadrantAt (x y : Nat) : Quadrant :=
  Quadrant.ofBits (x % 2 == 1, y % 2 == 1)

def componentAt (grid : Nat → Nat → Index) (x y : Nat) : Thick :=
  (components (grid (x / 2) (y / 2))).2.1


end FreeCellLocal
end Signals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
