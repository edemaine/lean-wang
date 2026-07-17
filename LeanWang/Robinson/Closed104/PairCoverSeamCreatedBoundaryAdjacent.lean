/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentClassification
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentFullTransport
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedBoundarySameBlock

/-!
# Adjacent-macrocell created-boundary paths

The full adjacent audit supplies a path for the actual query coordinate in the
neighboring depth-two macrocell. This module classifies actual refined pairs,
transports those paths, and widens them to the enclosing hierarchy collar.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundaryAdjacent

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedAdjacentAudit
  PairCoverSeamCreatedAdjacentClassification
  PairCoverSeamCreatedAdjacentFullAudit
  PairCoverSeamCreatedAdjacentFullTransport
  PairCoverSeamCreatedBoundarySameBlock
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem local_created_of_not_sparse {coordinate : Nat}
    (created : ¬ IsSparseCoordinate coordinate) :
    coordinate % 8 ∈ createdCoordinates := by
  have hlocal : coordinate % 8 < 8 := Nat.mod_lt _ (by decide)
  have hdecompose := Nat.mod_add_div coordinate 8
  simp only [createdCoordinates, List.mem_cons, List.not_mem_nil, or_false]
  by_contra hnot
  have hsparse : coordinate % 8 = 0 ∨ coordinate % 8 = 1 := by omega
  apply created
  rcases hsparse with hzero | hone
  · refine ⟨2 * (coordinate / 8), ?_⟩
    rw [sparseCoordinate_two_mul]
    omega
  · refine ⟨2 * (coordinate / 8) + 1, ?_⟩
    rw [sparseCoordinate_two_mul_add_one]
    omega

theorem refinedGrid_verticalPair_mem
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) (x y : Nat) :
    canonicalPair
        (refinedGrid phase (depth + 1) grid x y,
          refinedGrid phase (depth + 1) grid x (y + 1)) ∈
      verticalPairs := by
  let levels := refinementDepth phase (depth + 1)
  change canonicalPair
      (iterateRefine levels grid x y,
        iterateRefine levels grid x (y + 1)) ∈ verticalPairs
  have levelsPos : 0 < levels := by
    simp only [levels, refinementDepth]
    omega
  have levelsEq : levels = levels - 1 + 1 := by omega
  rw [levelsEq]
  exact verticalPair_mem (levels - 1) grid x y

theorem refinedGrid_horizontalPair_mem
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index) (x y : Nat) :
    canonicalPair
        (refinedGrid phase (depth + 1) grid x y,
          refinedGrid phase (depth + 1) grid (x + 1) y) ∈
      horizontalPairs := by
  let levels := refinementDepth phase (depth + 1)
  change canonicalPair
      (iterateRefine levels grid x y,
        iterateRefine levels grid (x + 1) y) ∈ horizontalPairs
  have levelsPos : 0 < levels := by
    simp only [levels, refinementDepth]
    omega
  have levelsEq : levels = levels - 1 + 1 := by omega
  rw [levelsEq]
  exact horizontalPair_mem (levels - 1) grid x y

set_option maxHeartbeats 2000000 in
-- The proof normalizes five quotient/remainder decompositions in two cases.
/-- A created horizontal source and query in adjacent depth-two macrocells have
the required vertical seam path. -/
theorem vertical
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX _parentY : Nat) {column row boundary : Nat}
    (columnWest :
      quarterWest (successorWest phase (depth + 1) parentX) ≤ column)
    (columnEast :
      column < quarterEast (successorEast phase (depth + 1) parentX))
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) column boundary)
          (quadrantAt column boundary) = some .north))
    (createdBoundary : ¬IsSparseCoordinate boundary)
    (adjacent :
      row / 8 + 1 = boundary / 8 ∨ boundary / 8 + 1 = row / 8) :
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockX := column / 8
  let localColumn := column % 8
  let localRow := row % 8
  let localBoundary := boundary % 8
  have localColumnLt : localColumn < 8 := Nat.mod_lt _ (by decide)
  have localRowLt : localRow < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have columnEq : 8 * blockX + localColumn = column := by
    have := Nat.mod_add_div column 8
    omega
  have hcreated : localBoundary ∈ createdCoordinates := by
    exact local_created_of_not_sparse createdBoundary
  have collar := localBlock_within_collar phase (depth + 1) parentX column
    columnWest columnEast
  rcases wrongFacing with wrongFacing | wrongFacing
  · let blockY := row / 8
    have blockAdjacent : blockY + 1 = boundary / 8 := by
      rcases adjacent with adjacent | adjacent
      · exact adjacent
      · have rowMod := Nat.mod_lt row (by decide : 0 < 8)
        have boundaryMod := Nat.mod_lt boundary (by decide : 0 < 8)
        have rowDecompose := Nat.mod_add_div row 8
        have boundaryDecompose := Nat.mod_add_div boundary 8
        dsimp only [blockY]
        omega
    have rowEq : 8 * blockY + localRow = row := by
      have := Nat.mod_add_div row 8
      omega
    have boundaryEq : 8 * blockY + (8 + localBoundary) = boundary := by
      have := Nat.mod_add_div boundary 8
      omega
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid blockX (blockY + 1)) ∈
        verticalPairs := by
      exact refinedGrid_verticalPair_mem phase depth grid blockX blockY
    have localPath := PairCoverSeamCreatedAdjacentFullTransport.verticalUpper
      oldGrid blockX blockY hpair (column := localColumn)
      (boundary := localBoundary) (row := localRow)
      (by simpa only [List.mem_range]) hcreated
      (by simpa only [lowerQueries, List.mem_range])
      (by simpa only [oldGrid, columnEq, boundaryEq] using wrongFacing.2)
    have widened := VerticalSeamPath.widen localPath collar.1 collar.2
    simpa only [oldGrid, columnEq, rowEq, boundaryEq] using widened
  · let blockY := boundary / 8
    have blockAdjacent : blockY + 1 = row / 8 := by
      rcases adjacent with adjacent | adjacent
      · have rowMod := Nat.mod_lt row (by decide : 0 < 8)
        have boundaryMod := Nat.mod_lt boundary (by decide : 0 < 8)
        have rowDecompose := Nat.mod_add_div row 8
        have boundaryDecompose := Nat.mod_add_div boundary 8
        dsimp only [blockY]
        omega
      · exact adjacent
    have rowEq : 8 * blockY + (8 + localRow) = row := by
      have := Nat.mod_add_div row 8
      omega
    have boundaryEq : 8 * blockY + localBoundary = boundary := by
      have := Nat.mod_add_div boundary 8
      omega
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid blockX (blockY + 1)) ∈
        verticalPairs := by
      exact refinedGrid_verticalPair_mem phase depth grid blockX blockY
    have localPath := PairCoverSeamCreatedAdjacentFullTransport.verticalLower
      oldGrid blockX blockY hpair (column := localColumn)
      (boundary := localBoundary) (row := 8 + localRow)
      (by simpa only [List.mem_range]) hcreated
      (by
        simp only [upperQueries, List.mem_map]
        exact ⟨localRow, by simpa only [List.mem_range], rfl⟩)
      (by simpa only [oldGrid, columnEq, boundaryEq] using wrongFacing.2)
    have widened := VerticalSeamPath.widen localPath collar.1 collar.2
    simpa only [oldGrid, columnEq, rowEq, boundaryEq] using widened

set_option maxHeartbeats 2000000 in
-- Horizontal dual of the quotient/remainder normalization above.
/-- A created vertical source and query in adjacent depth-two macrocells have
the required horizontal seam path. -/
theorem horizontal
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (_parentX parentY : Nat) {column row boundary : Nat}
    (rowSouth :
      quarterSouth (successorWest phase (depth + 1) parentY) ≤ row)
    (rowNorth :
      row < quarterNorth (successorEast phase (depth + 1) parentY))
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2
            (refinedGrid phase (depth + 1) grid)) boundary row)
          (quadrantAt boundary row) = some .east))
    (createdBoundary : ¬IsSparseCoordinate boundary)
    (adjacent :
      column / 8 + 1 = boundary / 8 ∨ boundary / 8 + 1 = column / 8) :
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockY := row / 8
  let localColumn := column % 8
  let localRow := row % 8
  let localBoundary := boundary % 8
  have localColumnLt : localColumn < 8 := Nat.mod_lt _ (by decide)
  have localRowLt : localRow < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have rowEq : 8 * blockY + localRow = row := by
    have := Nat.mod_add_div row 8
    omega
  have hcreated : localBoundary ∈ createdCoordinates := by
    exact local_created_of_not_sparse createdBoundary
  have collar := localBlock_within_collar phase (depth + 1) parentY row
    (by simpa only [quarterSouth, quarterWest] using rowSouth)
    (by simpa only [quarterNorth, quarterEast] using rowNorth)
  rcases wrongFacing with wrongFacing | wrongFacing
  · let blockX := column / 8
    have blockAdjacent : blockX + 1 = boundary / 8 := by
      rcases adjacent with adjacent | adjacent
      · exact adjacent
      · have columnMod := Nat.mod_lt column (by decide : 0 < 8)
        have boundaryMod := Nat.mod_lt boundary (by decide : 0 < 8)
        have columnDecompose := Nat.mod_add_div column 8
        have boundaryDecompose := Nat.mod_add_div boundary 8
        dsimp only [blockX]
        omega
    have columnEq : 8 * blockX + localColumn = column := by
      have := Nat.mod_add_div column 8
      omega
    have boundaryEq : 8 * blockX + (8 + localBoundary) = boundary := by
      have := Nat.mod_add_div boundary 8
      omega
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid (blockX + 1) blockY) ∈
        horizontalPairs := by
      exact refinedGrid_horizontalPair_mem phase depth grid blockX blockY
    have localPath := PairCoverSeamCreatedAdjacentFullTransport.horizontalRight
      oldGrid blockX blockY hpair (row := localRow)
      (boundary := localBoundary) (column := localColumn)
      (by simpa only [List.mem_range]) hcreated
      (by simpa only [leftQueries, List.mem_range])
      (by simpa only [oldGrid, boundaryEq, rowEq] using wrongFacing.2)
    have widened := HorizontalSeamPath.widen localPath
      (by simpa only [quarterSouth, quarterWest] using collar.1)
      (by simpa only [quarterNorth, quarterEast] using collar.2)
    simpa only [oldGrid, columnEq, rowEq, boundaryEq] using widened
  · let blockX := boundary / 8
    have blockAdjacent : blockX + 1 = column / 8 := by
      rcases adjacent with adjacent | adjacent
      · have columnMod := Nat.mod_lt column (by decide : 0 < 8)
        have boundaryMod := Nat.mod_lt boundary (by decide : 0 < 8)
        have columnDecompose := Nat.mod_add_div column 8
        have boundaryDecompose := Nat.mod_add_div boundary 8
        dsimp only [blockX]
        omega
      · exact adjacent
    have columnEq : 8 * blockX + (8 + localColumn) = column := by
      have := Nat.mod_add_div column 8
      omega
    have boundaryEq : 8 * blockX + localBoundary = boundary := by
      have := Nat.mod_add_div boundary 8
      omega
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid (blockX + 1) blockY) ∈
        horizontalPairs := by
      exact refinedGrid_horizontalPair_mem phase depth grid blockX blockY
    have localPath := PairCoverSeamCreatedAdjacentFullTransport.horizontalLeft
      oldGrid blockX blockY hpair (row := localRow)
      (boundary := localBoundary) (column := 8 + localColumn)
      (by simpa only [List.mem_range]) hcreated
      (by
        simp only [rightQueries, List.mem_map]
        exact ⟨localColumn, by simpa only [List.mem_range], rfl⟩)
      (by simpa only [oldGrid, boundaryEq, rowEq] using wrongFacing.2)
    have widened := HorizontalSeamPath.widen localPath
      (by simpa only [quarterSouth, quarterWest] using collar.1)
      (by simpa only [quarterNorth, quarterEast] using collar.2)
    simpa only [oldGrid, columnEq, rowEq, boundaryEq] using widened

end PairCoverSeamCreatedBoundaryAdjacent
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
