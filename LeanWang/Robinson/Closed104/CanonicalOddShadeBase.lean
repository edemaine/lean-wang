/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddShadeBaseCheck
import LeanWang.Robinson.Closed104.RedShadeCrossingBoards
import LeanWang.Robinson.Closed104.RedShadeGraphBoards
import LeanWang.Robinson.Closed104.RedShadeGraphSearchSoundness

/-! Soundness interface for the finite odd comparison base. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeBase

open OrientedRedCycles RedCycles RedShadePaths RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphLocalCoverage RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeCrossingBoards

theorem onCycle_of_mem {port : Port} (hport : port ∈ cyclePorts) :
    OnCycle 2 6 2 6 port := by
  rw [cyclePorts, List.mem_flatMap] at hport
  rcases hport with ⟨offset, hoffset, hport⟩
  simp only [List.mem_range] at hoffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OnCycle.southWest _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.southEast _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.northWest _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.northEast _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.westSouth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)
  · exact OnCycle.westNorth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)
  · exact OnCycle.eastSouth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)
  · exact OnCycle.eastNorth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)

theorem cyclePorts_inBounds {port : Port} (hport : port ∈ cyclePorts) :
    PortInBounds port 16 16 := by
  rw [cyclePorts, List.mem_flatMap] at hport
  rcases hport with ⟨offset, hoffset, hport⟩
  simp only [List.mem_range] at hoffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PortInBounds] <;> omega

theorem cycle : CycleOn indexGrid 2 6 2 6 := by
  simpa [indexGrid] using
    (RedShadeCrossingBoards.smallCycle (fun _ _ => (0 : Index))
      (level := 2) (by decide))

/-- Every live port in the central base square has a bounded path from the
odd root cycle, with a certificate-selected parity. -/
theorem exists_boundedPath {target : Port}
    (targetMem : target ∈ portsIn 16 16)
    (targetWest : 4 ≤ target.x) (targetEast : target.x < 12)
    (targetSouth : 4 ≤ target.y) (targetNorth : target.y < 12)
    (targetPresent : portPresent indexGrid target = true) :
    ∃ start parity,
      OnCycle 2 6 2 6 start ∧
        BoundedPath indexGrid 16 16 start target parity := by
  have covered := List.all_eq_true.1 complete_eq_true target targetMem
  simp only [targetCovered, targetWest, targetEast, targetSouth, targetNorth,
    targetPresent, decide_true, Bool.true_and, if_true, List.any_eq_true]
      at covered
  rcases covered with ⟨node, hnode, current⟩
  have sound := exploreFast_bounded_sound
    (fun port hport => cyclePorts_inBounds hport) hnode
  refine ⟨node.origin, node.parity, onCycle_of_mem sound.1, ?_⟩
  have currentEq : node.current = target := of_decide_eq_true current
  have path := sound.2
  rw [currentEq] at path
  exact path

end CanonicalOddShadeBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
