/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraph

/-! Executable red-port selectors shared by seam search and shade semantics. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamShadePaths

open RedCycles RedShadeGraph Signals.FreeCellLocal

def horizontalPort (grid : Nat → Nat → Index) (x y : Nat) : Port :=
  if RedShades.hasWest (componentAt grid x y) (quadrantAt x y) then
    ⟨x, y, .west⟩
  else ⟨x, y, .east⟩

def verticalPort (grid : Nat → Nat → Index) (x y : Nat) : Port :=
  if RedShades.hasSouth (componentAt grid x y) (quadrantAt x y) then
    ⟨x, y, .south⟩
  else ⟨x, y, .north⟩

end PairCoverSeamShadePaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
