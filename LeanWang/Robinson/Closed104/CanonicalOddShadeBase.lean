/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeBaseCheck
import LeanWang.Robinson.Closed104.RedShadeGraphSearchSoundness

/-! Soundness interface for the finite odd comparison base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeBase

open RedCycles RedShadePaths RedShadeCycles RedShadeGraph
  RedShadeGraphLocalCoverage RedShadeGraphSearch RedShadeGraphSearchSoundness

theorem cyclePorts_inBounds {port : Port} (hport : port ∈ cyclePorts) :
    PortInBounds port 16 16 := by
  rw [cyclePorts] at hport
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl <;> constructor <;> simp

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
    targetPresent, decide_true, Bool.true_and, if_true, List.any_eq_true]
      at covered
  rcases covered with ⟨node, hnode, current⟩
  have sound := exploreFast_bounded_sound
    (fun port hport => cyclePorts_inBounds hport) hnode
  refine ⟨node.origin, node.parity, sound.1, ?_⟩
  have currentEq : node.current = target := of_decide_eq_true current
  have path := sound.2
  rw [currentEq] at path
  exact path

end CanonicalOddShadeBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
