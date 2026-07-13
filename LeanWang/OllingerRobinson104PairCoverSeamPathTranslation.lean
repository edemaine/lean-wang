/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamPathBoundedBase
import LeanWang.OllingerRobinson104RefinementTranslation
import LeanWang.OllingerRobinson104SparseFreeLinePlaneBase

/-!
# Translation of bounded seam paths into arbitrary parent blocks

The finite checker runs on a constant-parent refinement.  Its bounded path can
be moved first to the shifted refinement of an arbitrary coarse grid and then
translated to global quarter coordinates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathTranslation

open RedCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphTranslation RefinementTranslation
  PairCoverSeamPathBaseAudit PairCoverSeamPathBoundedBase
  ShadedFreeLineRecurrence Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem fineGrid_eq_total (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    fineGrid phase depth grid =
      iterateRefine (refinementDepth phase depth + 2) grid := by
  simpa [fineGrid, Nat.add_comm] using
    (PlaneRedBoards.iterateRefine_add 2 (refinementDepth phase depth) grid)

theorem globalGrid_eq_total (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid) =
      iterateRefine (refinementDepth phase depth + 2) grid := by
  simpa [SparseFreeLinePlaneBase.refinedGrid, Nat.add_comm] using
    (PlaneRedBoards.iterateRefine_add 2 (refinementDepth phase depth) grid)

theorem searchSize_eq_totalQuarterWidth (phase : Phase) (depth : Nat) :
    searchSize phase depth =
      2 ^ ((refinementDepth phase depth + 2) + 1) := by
  simp [searchSize]

/-- A bounded path certified on one constant parent translates into the
corresponding block of an arbitrary coarse grid. -/
theorem boundedPath_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {first target : Port} {parity : Bool}
    (path : BoundedPath
      (fineGrid phase depth (fun _ _ => grid blockX blockY))
      (searchSize phase depth) (searchSize phase depth)
      first target parity) :
    Path (iterateRefine 2
        (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
      (translatePort first
        (2 ^ ((refinementDepth phase depth + 2) + 1) * blockX)
        (2 ^ ((refinementDepth phase depth + 2) + 1) * blockY))
      (translatePort target
        (2 ^ ((refinementDepth phase depth + 2) + 1) * blockX)
        (2 ^ ((refinementDepth phase depth + 2) + 1) * blockY)) parity := by
  let totalDepth := refinementDepth phase depth + 2
  have localEq : fineGrid phase depth (fun _ _ => grid blockX blockY) =
      iterateRefine totalDepth (fun _ _ => grid blockX blockY) := by
    exact fineGrid_eq_total phase depth _
  have componentsEq : ∀ x y,
      x < searchSize phase depth → y < searchSize phase depth →
      componentAt (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        componentAt
          (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    rw [localEq]
    have hx' : x < 2 ^ (totalDepth + 1) := by
      simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hx
    have hy' : y < 2 ^ (totalDepth + 1) := by
      simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hy
    exact (componentAt_shift_eq_constant totalDepth grid blockX blockY x y
      hx' hy').symm
  have shifted :=
    (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
      componentsEq path).path
  have translated := path_translate (depth := totalDepth) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted
  rw [globalGrid_eq_total phase depth grid]
  simpa [totalDepth] using translated

end PairCoverSeamPathTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
