/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeBaseCheck
import LeanWang.Robinson.Closed104.RedShadeGraphStaticCertificate

/-! Soundness interface for the finite odd comparison base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeBase

open RedCycles RedShadePaths RedShadeCycles RedShadeGraph
  RedShadeGraphBoundedPath RedShadeGraphLocalCoverage
  RedShadeGraphStaticCertificate

/-- Every live port in the central base square has a bounded path from the
odd root cycle, with a certificate-selected parity. -/
theorem exists_boundedPath {target : Port}
    (targetMem : target ∈ portsIn 16 16)
    (targetWest : 4 ≤ target.x) (targetEast : target.x < 12)
    (targetSouth : 4 ≤ target.y) (targetNorth : target.y < 12)
    (targetPresent : portPresent indexGrid target = true) :
    ∃ start parity,
      start ∈ cyclePorts ∧
        BoundedPath indexGrid 16 16 start target parity := by
  have covered := List.all_eq_true.1 complete_eq_true target targetMem
  simp only [targetCovered, targetWest, targetEast, targetSouth, targetNorth,
    targetPresent, decide_true, Bool.true_and, if_true,
    Option.isSome_iff_exists]
      at covered
  rcases covered with ⟨⟨index, state⟩, route⟩
  have routeMem : (index, state) ∈ routes := by
    unfold baseRoute? at route
    exact List.mem_of_find?_eq_some route
  have current := List.find?_some route
  simp only [decide_eq_true_eq] at current
  have evaluated := evaluate_of_mem_evaluated routeMem
  have sourceMem := origin_mem_sources_of_evaluate evaluated
  have path := boundedPath_of_evaluate evaluated
  refine ⟨state.origin, state.parity, sourceMem, ?_⟩
  simpa only [current] using path

end CanonicalOddShadeBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
