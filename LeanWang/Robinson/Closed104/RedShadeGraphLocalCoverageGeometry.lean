/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphRefinementGeometry
import LeanWang.Robinson.Closed104.RedShadeCycles

/-! Sources and targets for local red-graph coverage. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphLocalCoverage

open RedShadeCycles RedShadeGraph RedShadeGraphRefinement

def portsIn (width height : Nat) : List Port :=
  (List.range height).flatMap fun y =>
    (List.range width).flatMap fun x =>
      [.mk x y .west, .mk x y .east, .mk x y .south, .mk x y .north]

/-- One strict side port of the cell cycle created in the southwest depth-two
subtile. -/
def cycleSource : Port :=
  .mk (quarterWest 1 + 1) (quarterSouth 1) .west

def inheritedSources (parent : Index) : List Port :=
  ((portsIn 2 2).filter
    (portPresent (coarseGrid parent))).map sparsePort

def sources (parent : Index) : List Port :=
  cycleSource :: inheritedSources parent

end RedShadeGraphLocalCoverage
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
