/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedBoundarySameBlock
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedSourceBoundaryAudit

/-!
# Transport created source-boundary paths

The local equality-query certificates transplant into the depth-two
macrocell containing their source and then widen to the enclosing hierarchy
collar.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedSourceBoundaryTransport

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  PairCoverSeamArithmetic PairCoverSeamShadePaths
  PairCoverSeamCreatedBoundarySameBlock PairCoverSeamCreatedLocalAuditCheck
  PairCoverSeamCreatedLocalTransport PairCoverSeamCreatedSourceBoundaryAudit
  PairCoverSeamPathSearch RefinedCoordinateProjection
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem local_created_of_not_sparse {coordinate : Nat}
    (created : ¬ IsSparseCoordinate coordinate) :
    isCreated (coordinate % 8) = true := by
  have coordinateMod : coordinate % 8 < 8 := Nat.mod_lt _ (by decide)
  have coordinateDecompose := Nat.mod_add_div coordinate 8
  simp only [isCreated, Bool.and_eq_true, bne_iff_ne]
  constructor
  · intro residue
    apply created
    refine ⟨2 * (coordinate / 8), ?_⟩
    rw [sparseCoordinate_two_mul]
    omega
  · intro residue
    apply created
    refine ⟨2 * (coordinate / 8) + 1, ?_⟩
    rw [sparseCoordinate_two_mul_add_one]
    omega

set_option maxHeartbeats 1000000 in
-- Three quotient/remainder decompositions identify the translated ports.
/-- A north-facing created horizontal source has a same-boundary row path. -/
theorem vertical
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX _parentY : Nat) {column boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) ≤ column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (north : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) = some .north)
    (createdBoundary : ¬ IsSparseCoordinate boundary) :
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX)
      column boundary boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockX := column / 8
  let blockY := boundary / 8
  let localColumn := column % 8
  let localBoundary := boundary % 8
  have localColumnLt : localColumn < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have columnEq : 8 * blockX + localColumn = column := by
    have := Nat.mod_add_div column 8
    omega
  have boundaryEq : 8 * blockY + localBoundary = boundary := by
    have := Nat.mod_add_div boundary 8
    omega
  have localNorth : Signals.horizontalInterior?
      (componentAt (fineGrid (oldGrid blockX blockY))
        localColumn localBoundary)
      (quadrantAt localColumn localBoundary) = some .north := by
    exact (horizontalInterior_twoBlock oldGrid blockX blockY
      localColumn localBoundary localColumnLt localBoundaryLt).trans (by
        simpa only [oldGrid, columnEq, boundaryEq] using north)
  have localPath := (parentPaths (oldGrid blockX blockY)).vertical
    (by
      rw [coordinates]
      exact List.mem_range.mpr localColumnLt)
    (by
      rw [coordinates]
      exact List.mem_range.mpr localBoundaryLt)
    (local_created_of_not_sparse createdBoundary) localNorth
  have path := boundedVerticalSeamPath_twoBlock oldGrid blockX blockY
    localColumnLt localBoundaryLt localBoundaryLt localPath
  have collar := localBlock_within_collar phase (depth + 1) parentX column
    columnWest columnEast
  have widened := VerticalSeamPath.widen path collar.1 collar.2
  simpa only [oldGrid, columnEq, boundaryEq] using widened

set_option maxHeartbeats 1000000 in
-- Three quotient/remainder decompositions identify the translated ports.
/-- East-facing column dual of `vertical`. -/
theorem horizontal
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (_parentX parentY : Nat) {row boundary : Nat}
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) ≤ row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (east : Signals.verticalInterior?
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) = some .east)
    (createdBoundary : ¬ IsSparseCoordinate boundary) :
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY)
      row boundary boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockX := boundary / 8
  let blockY := row / 8
  let localRow := row % 8
  let localBoundary := boundary % 8
  have localRowLt : localRow < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have rowEq : 8 * blockY + localRow = row := by
    have := Nat.mod_add_div row 8
    omega
  have boundaryEq : 8 * blockX + localBoundary = boundary := by
    have := Nat.mod_add_div boundary 8
    omega
  have localEast : Signals.verticalInterior?
      (componentAt (fineGrid (oldGrid blockX blockY))
        localBoundary localRow)
      (quadrantAt localBoundary localRow) = some .east := by
    exact (verticalInterior_twoBlock oldGrid blockX blockY
      localBoundary localRow localBoundaryLt localRowLt).trans (by
        simpa only [oldGrid, boundaryEq, rowEq] using east)
  have localPath := (parentPaths (oldGrid blockX blockY)).horizontal
    (by
      rw [coordinates]
      exact List.mem_range.mpr localRowLt)
    (by
      rw [coordinates]
      exact List.mem_range.mpr localBoundaryLt)
    (local_created_of_not_sparse createdBoundary) localEast
  have path := boundedHorizontalSeamPath_twoBlock oldGrid blockX blockY
    localRowLt localBoundaryLt localBoundaryLt localPath
  have collar := localBlock_within_collar phase (depth + 1) parentY row
    (by simpa only [quarterSouth, quarterWest] using rowSouth)
    (by simpa only [quarterNorth, quarterEast] using rowNorth)
  have widened := HorizontalSeamPath.widen path
    (by simpa only [quarterSouth, quarterWest] using collar.1)
    (by simpa only [quarterNorth, quarterEast] using collar.2)
  simpa only [oldGrid, rowEq, boundaryEq] using widened

end PairCoverSeamCreatedSourceBoundaryTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
