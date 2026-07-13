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
  PairCoverSeamShadePaths ShadedFreeLineRecurrence Signals.FreeCellLocal

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

theorem horizontalPort_translate (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat) :
    translatePort
        (horizontalPort (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY) =
      horizontalPort (iterateRefine depth grid)
        (2 ^ (depth + 1) * blockX + x)
        (2 ^ (depth + 1) * blockY + y) := by
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  simp only [horizontalPort]
  rw [componentAt_iterateRefine_shift,
    quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
  split <;> rfl

theorem verticalPort_translate (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat) :
    translatePort
        (verticalPort (iterateRefine depth (shiftGrid grid blockX blockY)) x y)
        (2 ^ (depth + 1) * blockX) (2 ^ (depth + 1) * blockY) =
      verticalPort (iterateRefine depth grid)
        (2 ^ (depth + 1) * blockX + x)
        (2 ^ (depth + 1) * blockY + y) := by
  have hscale : 2 ∣ 2 ^ (depth + 1) := dvd_pow_self 2 (by omega)
  simp only [verticalPort]
  rw [componentAt_iterateRefine_shift,
    quadrantAt_shift (2 ^ (depth + 1)) blockX blockY x y hscale]
  split <;> rfl

theorem horizontalPort_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat)
    (hx : x < searchSize phase depth) (hy : y < searchSize phase depth) :
    translatePort
        (horizontalPort
          (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y)
        (searchSize phase depth * blockX) (searchSize phase depth * blockY) =
      horizontalPort
        (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
        (searchSize phase depth * blockX + x)
        (searchSize phase depth * blockY + y) := by
  let totalDepth := refinementDepth phase depth + 2
  have localEq := fineGrid_eq_total phase depth
    (fun _ _ => grid blockX blockY)
  have hx' : x < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hx
  have hy' : y < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hy
  have componentEq :
      componentAt (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        componentAt (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    rw [localEq]
    exact (componentAt_shift_eq_constant totalDepth grid blockX blockY x y
      hx' hy').symm
  have portEq :
      horizontalPort (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        horizontalPort
          (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    unfold horizontalPort
    rw [componentEq]
  rw [portEq]
  rw [globalGrid_eq_total phase depth grid]
  simpa [totalDepth, searchSize_eq_totalQuarterWidth] using
    horizontalPort_translate totalDepth grid blockX blockY x y

theorem verticalPort_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat)
    (hx : x < searchSize phase depth) (hy : y < searchSize phase depth) :
    translatePort
        (verticalPort
          (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y)
        (searchSize phase depth * blockX) (searchSize phase depth * blockY) =
      verticalPort
        (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
        (searchSize phase depth * blockX + x)
        (searchSize phase depth * blockY + y) := by
  let totalDepth := refinementDepth phase depth + 2
  have localEq := fineGrid_eq_total phase depth
    (fun _ _ => grid blockX blockY)
  have hx' : x < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hx
  have hy' : y < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hy
  have componentEq :
      componentAt (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        componentAt (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    rw [localEq]
    exact (componentAt_shift_eq_constant totalDepth grid blockX blockY x y
      hx' hy').symm
  have portEq :
      verticalPort (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        verticalPort
          (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    unfold verticalPort
    rw [componentEq]
  rw [portEq]
  rw [globalGrid_eq_total phase depth grid]
  simpa [totalDepth, searchSize_eq_totalQuarterWidth] using
    verticalPort_translate totalDepth grid blockX blockY x y

theorem verticalInterior_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat)
    (hx : x < searchSize phase depth) (hy : y < searchSize phase depth) :
    Signals.verticalInterior?
        (componentAt
          (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y)
        (quadrantAt x y) =
      Signals.verticalInterior?
        (componentAt
          (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
          (searchSize phase depth * blockX + x)
          (searchSize phase depth * blockY + y))
        (quadrantAt (searchSize phase depth * blockX + x)
          (searchSize phase depth * blockY + y)) := by
  let totalDepth := refinementDepth phase depth + 2
  have localEq := fineGrid_eq_total phase depth
    (fun _ _ => grid blockX blockY)
  have hx' : x < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hx
  have hy' : y < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hy
  have componentEq :
      componentAt (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        componentAt (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    rw [localEq]
    exact (componentAt_shift_eq_constant totalDepth grid blockX blockY x y
      hx' hy').symm
  rw [componentEq, globalGrid_eq_total phase depth grid]
  simpa [totalDepth, searchSize_eq_totalQuarterWidth] using
    verticalInterior_iterateRefine_shift totalDepth grid blockX blockY x y

theorem horizontalInterior_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat)
    (hx : x < searchSize phase depth) (hy : y < searchSize phase depth) :
    Signals.horizontalInterior?
        (componentAt
          (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y)
        (quadrantAt x y) =
      Signals.horizontalInterior?
        (componentAt
          (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
          (searchSize phase depth * blockX + x)
          (searchSize phase depth * blockY + y))
        (quadrantAt (searchSize phase depth * blockX + x)
          (searchSize phase depth * blockY + y)) := by
  let totalDepth := refinementDepth phase depth + 2
  have localEq := fineGrid_eq_total phase depth
    (fun _ _ => grid blockX blockY)
  have hx' : x < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hx
  have hy' : y < 2 ^ (totalDepth + 1) := by
    simpa [totalDepth, searchSize_eq_totalQuarterWidth] using hy
  have componentEq :
      componentAt (fineGrid phase depth (fun _ _ => grid blockX blockY)) x y =
        componentAt (iterateRefine totalDepth (shiftGrid grid blockX blockY)) x y := by
    rw [localEq]
    exact (componentAt_shift_eq_constant totalDepth grid blockX blockY x y
      hx' hy').symm
  rw [componentEq, globalGrid_eq_total phase depth grid]
  simpa [totalDepth, searchSize_eq_totalQuarterWidth] using
    horizontalInterior_iterateRefine_shift totalDepth grid blockX blockY x y

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
        (searchSize phase depth * blockX)
        (searchSize phase depth * blockY))
      (translatePort target
        (searchSize phase depth * blockX)
        (searchSize phase depth * blockY)) parity := by
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
  simpa [totalDepth, searchSize_eq_totalQuarterWidth] using translated

end PairCoverSeamPathTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
