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

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphTranslation RefinementTranslation
  PairCoverSeamArithmetic
  PairCoverSeamPathSearch PairCoverSeamPathBaseAudit PairCoverSeamPathBoundedBase
  PairCoverSeamShadePaths ShadedFreeLineRecurrence Signals.FreeCellLocal
  ShadedObstructionPairCoverRecurrence

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

theorem searchSize_mul_eq_parentQuarterOffset
    (phase : Phase) (depth block : Nat) :
    searchSize phase depth * block =
      2 * (2 ^ refinementDepth phase (depth + 1) * block) := by
  have hpow := PairCoverSeamArithmetic.two_pow_refinementDepth_succ phase depth
  simp only [searchSize, pow_add, hpow]
  ring

theorem quarterOffset_add_west (phase : Phase) (depth block : Nat) :
    searchSize phase depth * block +
        quarterWest (successorWest phase depth 0) =
      quarterWest (successorWest phase depth block) := by
  rw [searchSize_mul_eq_parentQuarterOffset]
  simp [successorWest, quarterWest]
  ring

theorem quarterOffset_add_east (phase : Phase) (depth block : Nat) :
    searchSize phase depth * block +
        quarterEast (successorEast phase depth 0) =
      quarterEast (successorEast phase depth block) := by
  rw [searchSize_mul_eq_parentQuarterOffset]
  simp [successorEast, quarterEast]
  ring

theorem quarterOffset_add_south (phase : Phase) (depth block : Nat) :
    searchSize phase depth * block +
        quarterSouth (successorWest phase depth 0) =
      quarterSouth (successorWest phase depth block) := by
  simpa [quarterSouth, quarterWest] using quarterOffset_add_west phase depth block

theorem quarterOffset_add_north (phase : Phase) (depth block : Nat) :
    searchSize phase depth * block +
        quarterNorth (successorEast phase depth 0) =
      quarterNorth (successorEast phase depth block) := by
  simpa [quarterNorth, quarterEast] using quarterOffset_add_east phase depth block

def localCoordinate (phase : Phase) (depth block coordinate : Nat) : Nat :=
  coordinate - searchSize phase depth * block

theorem offset_add_localCoordinate
    {phase : Phase} {depth block coordinate : Nat}
    (hlower : quarterSouth (successorWest phase depth block) < coordinate) :
    searchSize phase depth * block +
        localCoordinate phase depth block coordinate = coordinate := by
  have hboundary := quarterOffset_add_south phase depth block
  unfold localCoordinate
  omega

theorem localCoordinate_mem_coordinates
    {phase : Phase} {depth block coordinate : Nat}
    (hlower : quarterSouth (successorWest phase depth block) < coordinate)
    (hupper : coordinate < quarterNorth (successorEast phase depth block)) :
    localCoordinate phase depth block coordinate ∈ coordinates phase depth := by
  have hlowerEq := quarterOffset_add_south phase depth block
  have hupperEq := quarterOffset_add_north phase depth block
  have hcoordinate := offset_add_localCoordinate hlower
  simp only [coordinates, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor <;> omega

theorem inAbsoluteChildInterval_add_offset_iff
    (phase : Phase) (depth parent : Nat) (side : Fin 2) (coordinate : Nat) :
    InAbsoluteChildInterval phase depth parent side
        (searchSize phase depth * parent + coordinate) ↔
      InAbsoluteChildInterval phase depth 0 side coordinate := by
  unfold InAbsoluteChildInterval absoluteChildBlock
  rw [searchSize_mul_eq_parentQuarterOffset,
    two_pow_refinementDepth_succ]
  simp only [Nat.mul_zero, Nat.zero_add, quarterWest, quarterEast]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> omega

theorem fitsContainedVerticalChild_add_offsets_iff
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    FitsContainedVerticalChild phase depth parentX parentY
        (searchSize phase depth * parentX + column)
        (searchSize phase depth * parentY + row)
        (searchSize phase depth * parentY + boundary) ↔
      FitsContainedVerticalChild phase depth 0 0 column row boundary := by
  rw [fitsContainedVerticalChild_iff_regions,
    fitsContainedVerticalChild_iff_regions]
  constructor
  · rintro ⟨⟨sideX, hcolumn⟩, ⟨sideY, hrow, hboundary⟩⟩
    exact ⟨⟨sideX,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentX sideX column).1 hcolumn⟩,
      ⟨sideY,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentY sideY row).1 hrow,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentY sideY boundary).1 hboundary⟩⟩
  · rintro ⟨⟨sideX, hcolumn⟩, ⟨sideY, hrow, hboundary⟩⟩
    exact ⟨⟨sideX,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentX sideX column).2 hcolumn⟩,
      ⟨sideY,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentY sideY row).2 hrow,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentY sideY boundary).2 hboundary⟩⟩

theorem fitsContainedHorizontalChild_add_offsets_iff
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    FitsContainedHorizontalChild phase depth parentX parentY
        (searchSize phase depth * parentX + column)
        (searchSize phase depth * parentY + row)
        (searchSize phase depth * parentX + boundary) ↔
      FitsContainedHorizontalChild phase depth 0 0 column row boundary := by
  rw [fitsContainedHorizontalChild_iff_regions,
    fitsContainedHorizontalChild_iff_regions]
  constructor
  · rintro ⟨⟨sideX, hcolumn, hboundary⟩, ⟨sideY, hrow⟩⟩
    exact ⟨⟨sideX,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentX sideX column).1 hcolumn,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentX sideX boundary).1 hboundary⟩,
      ⟨sideY,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentY sideY row).1 hrow⟩⟩
  · rintro ⟨⟨sideX, hcolumn, hboundary⟩, ⟨sideY, hrow⟩⟩
    exact ⟨⟨sideX,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentX sideX column).2 hcolumn,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentX sideX boundary).2 hboundary⟩,
      ⟨sideY,
        (inAbsoluteChildInterval_add_offset_iff
          phase depth parentY sideY row).2 hrow⟩⟩

theorem containedVerticalSeamCheck_add_offsets
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    containedVerticalSeamCheck phase depth parentX parentY
        (searchSize phase depth * parentX + column)
        (searchSize phase depth * parentY + row)
        (searchSize phase depth * parentY + boundary) =
      containedVerticalSeamCheck phase depth 0 0 column row boundary := by
  rw [Bool.eq_iff_iff, containedVerticalSeamCheck_eq_true_iff,
    containedVerticalSeamCheck_eq_true_iff]
  exact not_congr (fitsContainedVerticalChild_add_offsets_iff
    phase depth parentX parentY column row boundary)

theorem containedHorizontalSeamCheck_add_offsets
    (phase : Phase) (depth parentX parentY column row boundary : Nat) :
    containedHorizontalSeamCheck phase depth parentX parentY
        (searchSize phase depth * parentX + column)
        (searchSize phase depth * parentY + row)
        (searchSize phase depth * parentX + boundary) =
      containedHorizontalSeamCheck phase depth 0 0 column row boundary := by
  rw [Bool.eq_iff_iff, containedHorizontalSeamCheck_eq_true_iff,
    containedHorizontalSeamCheck_eq_true_iff]
  exact not_congr (fitsContainedHorizontalChild_add_offsets_iff
    phase depth parentX parentY column row boundary)

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

/-- A bounded vertical seam certificate becomes a global seam path in the
corresponding successor parent. -/
theorem boundedVerticalSeamPath_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {column row boundary : Nat}
    (hcolumn : column < searchSize phase depth)
    (hrow : row < searchSize phase depth)
    (hboundary : boundary < searchSize phase depth)
    (path : BoundedVerticalSeamPath
      (fineGrid phase depth (fun _ _ => grid blockX blockY))
      (searchSize phase depth)
      (successorWest phase depth 0) (successorEast phase depth 0)
      column row boundary) :
    VerticalSeamPath
      (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
      (successorWest phase depth blockX) (successorEast phase depth blockX)
      (searchSize phase depth * blockX + column)
      (searchSize phase depth * blockY + row)
      (searchSize phase depth * blockY + boundary) := by
  rcases path with path | path
  · rcases path with ⟨targetX, hwest, heast, hinterior, path⟩
    have htargetX : targetX < searchSize phase depth := by
      have hbounds := path.second_inBounds
      unfold verticalPort at hbounds
      split at hbounds <;> exact hbounds.1
    left
    refine ⟨searchSize phase depth * blockX + targetX, ?_, ?_, ?_, ?_⟩
    · rw [← quarterOffset_add_west]
      omega
    · rw [← quarterOffset_add_east]
      omega
    · rw [← verticalInterior_parentBlock phase depth grid blockX blockY
        targetX row htargetX hrow]
      exact hinterior
    · have translated := boundedPath_parentBlock
        phase depth grid blockX blockY path
      rw [horizontalPort_parentBlock phase depth grid blockX blockY
        column boundary hcolumn hboundary] at translated
      rw [verticalPort_parentBlock phase depth grid blockX blockY
        targetX row htargetX hrow] at translated
      exact translated
  · rcases path with ⟨targetY, hbetween, hinterior, path⟩
    have htargetY : targetY < searchSize phase depth := by
      have hbounds := path.second_inBounds
      unfold horizontalPort at hbounds
      split at hbounds <;> exact hbounds.2
    right
    refine ⟨searchSize phase depth * blockY + targetY, ?_, ?_, ?_⟩
    · unfold StrictBetween at hbetween ⊢
      omega
    · rw [← horizontalInterior_parentBlock phase depth grid blockX blockY
        column targetY hcolumn htargetY]
      exact hinterior
    · have translated := boundedPath_parentBlock
        phase depth grid blockX blockY path
      rw [horizontalPort_parentBlock phase depth grid blockX blockY
        column boundary hcolumn hboundary] at translated
      rw [horizontalPort_parentBlock phase depth grid blockX blockY
        column targetY hcolumn htargetY] at translated
      exact translated

/-- A bounded horizontal seam certificate becomes a global seam path in the
corresponding successor parent. -/
theorem boundedHorizontalSeamPath_parentBlock
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {row column boundary : Nat}
    (hrow : row < searchSize phase depth)
    (hcolumn : column < searchSize phase depth)
    (hboundary : boundary < searchSize phase depth)
    (path : BoundedHorizontalSeamPath
      (fineGrid phase depth (fun _ _ => grid blockX blockY))
      (searchSize phase depth)
      (successorWest phase depth 0) (successorEast phase depth 0)
      row column boundary) :
    HorizontalSeamPath
      (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
      (successorWest phase depth blockY) (successorEast phase depth blockY)
      (searchSize phase depth * blockY + row)
      (searchSize phase depth * blockX + column)
      (searchSize phase depth * blockX + boundary) := by
  rcases path with path | path
  · rcases path with ⟨targetY, hsouth, hnorth, hinterior, path⟩
    have htargetY : targetY < searchSize phase depth := by
      have hbounds := path.second_inBounds
      unfold horizontalPort at hbounds
      split at hbounds <;> exact hbounds.2
    left
    refine ⟨searchSize phase depth * blockY + targetY, ?_, ?_, ?_, ?_⟩
    · rw [← quarterOffset_add_south]
      omega
    · rw [← quarterOffset_add_north]
      omega
    · rw [← horizontalInterior_parentBlock phase depth grid blockX blockY
        column targetY hcolumn htargetY]
      exact hinterior
    · have translated := boundedPath_parentBlock
        phase depth grid blockX blockY path
      rw [verticalPort_parentBlock phase depth grid blockX blockY
        boundary row hboundary hrow] at translated
      rw [horizontalPort_parentBlock phase depth grid blockX blockY
        column targetY hcolumn htargetY] at translated
      exact translated
  · rcases path with ⟨targetX, hbetween, hinterior, path⟩
    have htargetX : targetX < searchSize phase depth := by
      have hbounds := path.second_inBounds
      unfold verticalPort at hbounds
      split at hbounds <;> exact hbounds.1
    right
    refine ⟨searchSize phase depth * blockX + targetX, ?_, ?_, ?_⟩
    · unfold StrictBetween at hbetween ⊢
      omega
    · rw [← verticalInterior_parentBlock phase depth grid blockX blockY
        targetX row htargetX hrow]
      exact hinterior
    · have translated := boundedPath_parentBlock
        phase depth grid blockX blockY path
      rw [verticalPort_parentBlock phase depth grid blockX blockY
        boundary row hboundary hrow] at translated
      rw [verticalPort_parentBlock phase depth grid blockX blockY
        targetX row htargetX hrow] at translated
      exact translated

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent local-to-global query transport exceeds the default.
/-- The bounded finite certificate supplies a global vertical seam path for
every wrong-facing query that is not contained in one recursive child. -/
theorem BoundedPaths.verticalSeamPath
    {phase : Phase} {depth : Nat} (paths : BoundedPaths phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (hboundarySouth :
      quarterSouth (successorWest phase depth parentY) < boundary)
    (hboundaryNorth :
      boundary < quarterNorth (successorEast phase depth parentY))
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2
              (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
            column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2
              (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
            column boundary)
          (quadrantAt column boundary) = some .north))
    (notFits : ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary) :
    VerticalSeamPath
      (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
      (successorWest phase depth parentX) (successorEast phase depth parentX)
      column row boundary := by
  let localColumn := localCoordinate phase depth parentX column
  let localRow := localCoordinate phase depth parentY row
  let localBoundary := localCoordinate phase depth parentY boundary
  have hlocalColumn := localCoordinate_mem_coordinates
    hcolumnWest hcolumnEast
  have hlocalRow := localCoordinate_mem_coordinates hrowSouth hrowNorth
  have hlocalBoundary := localCoordinate_mem_coordinates
    hboundarySouth hboundaryNorth
  have hcolumnEq : searchSize phase depth * parentX + localColumn = column :=
    offset_add_localCoordinate hcolumnWest
  have hrowEq : searchSize phase depth * parentY + localRow = row :=
    offset_add_localCoordinate hrowSouth
  have hboundaryEq :
      searchSize phase depth * parentY + localBoundary = boundary :=
    offset_add_localCoordinate hboundarySouth
  dsimp only [localColumn] at hcolumnEq
  dsimp only [localRow] at hrowEq
  dsimp only [localBoundary] at hboundaryEq
  have hinteriorEq :
      Signals.horizontalInterior?
          (componentAt
            (fineGrid phase depth (fun _ _ => grid parentX parentY))
            localColumn localBoundary)
          (quadrantAt localColumn localBoundary) =
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2
              (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
            column boundary)
          (quadrantAt column boundary) := by
    have h := horizontalInterior_parentBlock phase depth grid parentX parentY
      localColumn localBoundary
      (coordinate_lt_searchSize hlocalColumn)
      (coordinate_lt_searchSize hlocalBoundary)
    dsimp only [localColumn, localBoundary] at h
    rw [hcolumnEq, hboundaryEq] at h
    exact h
  have hlocalWrongFacing :
      (localRow < localBoundary ∧
        Signals.horizontalInterior?
          (componentAt
            (fineGrid phase depth (fun _ _ => grid parentX parentY))
            localColumn localBoundary)
          (quadrantAt localColumn localBoundary) = some .south) ∨
      (localBoundary < localRow ∧
        Signals.horizontalInterior?
          (componentAt
            (fineGrid phase depth (fun _ _ => grid parentX parentY))
            localColumn localBoundary)
          (quadrantAt localColumn localBoundary) = some .north) := by
    rcases wrongFacing with wrongFacing | wrongFacing
    · left
      exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
    · right
      exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
  have hlocalNotFits : ¬FitsContainedVerticalChild phase depth 0 0
      localColumn localRow localBoundary := by
    intro fits
    apply notFits
    rw [← hcolumnEq, ← hrowEq, ← hboundaryEq]
    exact (fitsContainedVerticalChild_add_offsets_iff
      phase depth parentX parentY localColumn localRow localBoundary).2 fits
  have hlocalCheck : containedVerticalSeamCheck phase depth 0 0
      localColumn localRow localBoundary = true :=
    (containedVerticalSeamCheck_eq_true_iff
      phase depth 0 0 localColumn localRow localBoundary).2 hlocalNotFits
  have hquery : localRow ∈ verticalQueries phase depth
      (fineGrid phase depth (fun _ _ => grid parentX parentY))
      (coordinates phase depth) localColumn localBoundary := by
    simp only [verticalQueries, List.mem_filter, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨hlocalRow, hlocalWrongFacing, hlocalCheck⟩
  have localPath := (paths (grid parentX parentY)).vertical
    hlocalColumn hlocalBoundary hquery
  have globalPath := boundedVerticalSeamPath_parentBlock
    phase depth grid parentX parentY
    (coordinate_lt_searchSize hlocalColumn)
    (coordinate_lt_searchSize hlocalRow)
    (coordinate_lt_searchSize hlocalBoundary) localPath
  simpa only [hcolumnEq, hrowEq, hboundaryEq] using globalPath

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent local-to-global query transport exceeds the default.
/-- The bounded finite certificate supplies a global horizontal seam path for
every wrong-facing query that is not contained in one recursive child. -/
theorem BoundedPaths.horizontalSeamPath
    {phase : Phase} {depth : Nat} (paths : BoundedPaths phase depth)
    (grid : Nat → Nat → Index) (parentX parentY : Nat)
    {column row boundary : Nat}
    (hcolumnWest : quarterWest (successorWest phase depth parentX) < column)
    (hcolumnEast : column < quarterEast (successorEast phase depth parentX))
    (hrowSouth : quarterSouth (successorWest phase depth parentY) < row)
    (hrowNorth : row < quarterNorth (successorEast phase depth parentY))
    (hboundaryWest :
      quarterWest (successorWest phase depth parentX) < boundary)
    (hboundaryEast :
      boundary < quarterEast (successorEast phase depth parentX))
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2
              (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
            boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2
              (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
            boundary row)
          (quadrantAt boundary row) = some .east))
    (notFits : ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary) :
    HorizontalSeamPath
      (iterateRefine 2 (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
      (successorWest phase depth parentY) (successorEast phase depth parentY)
      row column boundary := by
  let localColumn := localCoordinate phase depth parentX column
  let localRow := localCoordinate phase depth parentY row
  let localBoundary := localCoordinate phase depth parentX boundary
  have hlocalColumn := localCoordinate_mem_coordinates
    hcolumnWest hcolumnEast
  have hlocalRow := localCoordinate_mem_coordinates hrowSouth hrowNorth
  have hlocalBoundary := localCoordinate_mem_coordinates
    hboundaryWest hboundaryEast
  have hcolumnEq : searchSize phase depth * parentX + localColumn = column :=
    offset_add_localCoordinate hcolumnWest
  have hrowEq : searchSize phase depth * parentY + localRow = row :=
    offset_add_localCoordinate hrowSouth
  have hboundaryEq :
      searchSize phase depth * parentX + localBoundary = boundary :=
    offset_add_localCoordinate hboundaryWest
  dsimp only [localColumn] at hcolumnEq
  dsimp only [localRow] at hrowEq
  dsimp only [localBoundary] at hboundaryEq
  have hinteriorEq :
      Signals.verticalInterior?
          (componentAt
            (fineGrid phase depth (fun _ _ => grid parentX parentY))
            localBoundary localRow)
          (quadrantAt localBoundary localRow) =
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2
              (SparseFreeLinePlaneBase.refinedGrid phase depth grid))
            boundary row)
          (quadrantAt boundary row) := by
    have h := verticalInterior_parentBlock phase depth grid parentX parentY
      localBoundary localRow
      (coordinate_lt_searchSize hlocalBoundary)
      (coordinate_lt_searchSize hlocalRow)
    dsimp only [localBoundary, localRow] at h
    rw [hboundaryEq, hrowEq] at h
    exact h
  have hlocalWrongFacing :
      (localColumn < localBoundary ∧
        Signals.verticalInterior?
          (componentAt
            (fineGrid phase depth (fun _ _ => grid parentX parentY))
            localBoundary localRow)
          (quadrantAt localBoundary localRow) = some .west) ∨
      (localBoundary < localColumn ∧
        Signals.verticalInterior?
          (componentAt
            (fineGrid phase depth (fun _ _ => grid parentX parentY))
            localBoundary localRow)
          (quadrantAt localBoundary localRow) = some .east) := by
    rcases wrongFacing with wrongFacing | wrongFacing
    · left
      exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
    · right
      exact ⟨by omega, hinteriorEq.trans wrongFacing.2⟩
  have hlocalNotFits : ¬FitsContainedHorizontalChild phase depth 0 0
      localColumn localRow localBoundary := by
    intro fits
    apply notFits
    rw [← hcolumnEq, ← hrowEq, ← hboundaryEq]
    exact (fitsContainedHorizontalChild_add_offsets_iff
      phase depth parentX parentY localColumn localRow localBoundary).2 fits
  have hlocalCheck : containedHorizontalSeamCheck phase depth 0 0
      localColumn localRow localBoundary = true :=
    (containedHorizontalSeamCheck_eq_true_iff
      phase depth 0 0 localColumn localRow localBoundary).2 hlocalNotFits
  have hquery : localColumn ∈ horizontalQueries phase depth
      (fineGrid phase depth (fun _ _ => grid parentX parentY))
      (coordinates phase depth) localRow localBoundary := by
    simp only [horizontalQueries, List.mem_filter, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨hlocalColumn, hlocalWrongFacing, hlocalCheck⟩
  have localPath := (paths (grid parentX parentY)).horizontal
    hlocalBoundary hlocalRow hquery
  have globalPath := boundedHorizontalSeamPath_parentBlock
    phase depth grid parentX parentY
    (coordinate_lt_searchSize hlocalRow)
    (coordinate_lt_searchSize hlocalColumn)
    (coordinate_lt_searchSize hlocalBoundary) localPath
  simpa only [hrowEq, hcolumnEq, hboundaryEq] using globalPath

end PairCoverSeamPathTranslation
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
