/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageData

/-! Executable finite connectivity check for the odd comparison base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeBase

open RedCycles RedShadeGraph RedShadeGraphLocalCoverage RedShadeGraphSearch
  RedShadeCycles

def indexGrid : Nat → Nat → Index :=
  iterateRefine 4 (fun _ _ => (0 : Index))

def cyclePorts : List Port :=
  [⟨5, 5, .east⟩, ⟨12, 5, .west⟩,
    ⟨12, 12, .west⟩, ⟨5, 12, .east⟩]

def nodes : List Node :=
  exploreFast indexGrid 16 16 4000 cyclePorts

def targetCovered (target : Port) : Bool :=
  if 4 ≤ target.x && target.x < 12 && 4 ≤ target.y && target.y < 12 &&
      portPresent indexGrid target then
    nodes.any fun node => decide (node.current = target)
  else true

def complete : Bool :=
  (portsIn 16 16).all targetCovered

end CanonicalOddShadeBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
