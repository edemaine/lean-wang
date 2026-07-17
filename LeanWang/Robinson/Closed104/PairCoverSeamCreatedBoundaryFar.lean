/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedBoundaryAdjacent
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedFarParallelAudit

/-!
# Far-macrocell created-boundary paths

For a query more than one depth-two macrocell from a created source, a local
parallel red segment on the query-facing side of the source is already strictly
between the query and source.  The finite pair audit supplies such a segment
and an even path to it.  This module translates that bounded local certificate
to the global refined grid.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundaryFar

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamCreatedAdjacentAudit
  PairCoverSeamCreatedAdjacentTransport
  PairCoverSeamCreatedBoundaryAdjacent
  PairCoverSeamCreatedFarParallelAudit
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A created horizontal source and a query separated by a complete depth-two
macrocell have the required vertical seam path. -/
theorem vertical
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (parentX _parentY : Nat) {column row boundary : Nat}
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
    (far : row / 8 + 1 < boundary / 8 ∨
      boundary / 8 + 1 < row / 8) :
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockX := column / 8
  let localColumn := column % 8
  let sourceBlock := boundary / 8
  let localBoundary := boundary % 8
  have localColumnLt : localColumn < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have columnEq : 8 * blockX + localColumn = column := by
    have := Nat.mod_add_div column 8
    omega
  have boundaryDecompose : 8 * sourceBlock + localBoundary = boundary := by
    have := Nat.mod_add_div boundary 8
    omega
  have hcreated : localBoundary ∈ createdCoordinates :=
    local_created_of_not_sparse createdBoundary
  rcases wrongFacing with south | north
  · have farBelow : row / 8 + 1 < boundary / 8 := by
      rcases far with far | far
      · exact far
      · have divLe := Nat.div_le_div_right (c := 8) (Nat.le_of_lt south.1)
        omega
    have sourceBlockPos : 0 < sourceBlock := by
      dsimp only [sourceBlock]
      omega
    let blockY := sourceBlock - 1
    have boundaryEq : 8 * blockY + (8 + localBoundary) = boundary := by
      dsimp only [blockY]
      omega
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid blockX (blockY + 1)) ∈
        verticalPairs := by
      exact refinedGrid_verticalPair_mem phase depth grid blockX blockY
    have pairChecked :
        PairCoverSeamCreatedFarParallelAudit.checkVerticalPair (canonicalPair
        (oldGrid blockX blockY, oldGrid blockX (blockY + 1))) = true := by
      exact (List.all_eq_true.mp
        PairCoverSeamCreatedFarParallelAudit.vertical_complete) _ hpair
    have localInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (verticalGrid (canonicalPair
          (oldGrid blockX blockY, oldGrid blockX (blockY + 1)))))
          localColumn (8 + localBoundary))
        (quadrantAt localColumn (8 + localBoundary)) = some .south := by
      rw [horizontalInterior_verticalWindow oldGrid blockX blockY
        localColumn (8 + localBoundary) localColumnLt (by omega)]
      simpa only [oldGrid, columnEq, boundaryEq] using south.2
    rcases verticalUpperSouth pairChecked localColumnLt hcreated localInterior with
      ⟨targetY, targetPos, targetLt, targetInterior, bounded⟩
    have targetGlobalBetween : StrictBetween row boundary
        (8 * blockY + targetY) := by
      left
      constructor
      · have rowMod := Nat.mod_lt row (by decide : 0 < 8)
        have rowDecompose := Nat.mod_add_div row 8
        dsimp only [blockY, sourceBlock] at *
        omega
      · omega
    have targetGlobalInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          column (8 * blockY + targetY))
        (quadrantAt column (8 * blockY + targetY)) ≠ none := by
      rw [← columnEq]
      rw [← horizontalInterior_verticalWindow oldGrid blockX blockY
        localColumn targetY localColumnLt (by omega)]
      exact targetInterior
    have translated := boundedPath_verticalWindow oldGrid blockX blockY bounded
    rw [horizontalPort_verticalWindow oldGrid blockX blockY
      localColumn (8 + localBoundary) localColumnLt (by omega)] at translated
    rw [horizontalPort_verticalWindow oldGrid blockX blockY
      localColumn targetY localColumnLt (by omega)] at translated
    right
    refine ⟨8 * blockY + targetY, targetGlobalBetween,
      targetGlobalInterior, ?_⟩
    simpa only [oldGrid, columnEq, boundaryEq] using translated
  · have farAbove : boundary / 8 + 1 < row / 8 := by
      rcases far with far | far
      · have divLe := Nat.div_le_div_right (c := 8) (Nat.le_of_lt north.1)
        omega
      · exact far
    let blockY := sourceBlock
    have boundaryEq : 8 * blockY + localBoundary = boundary := by
      simpa only [blockY] using boundaryDecompose
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid blockX (blockY + 1)) ∈
        verticalPairs := by
      exact refinedGrid_verticalPair_mem phase depth grid blockX blockY
    have pairChecked :
        PairCoverSeamCreatedFarParallelAudit.checkVerticalPair (canonicalPair
        (oldGrid blockX blockY, oldGrid blockX (blockY + 1))) = true := by
      exact (List.all_eq_true.mp
        PairCoverSeamCreatedFarParallelAudit.vertical_complete) _ hpair
    have localInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 (verticalGrid (canonicalPair
          (oldGrid blockX blockY, oldGrid blockX (blockY + 1)))))
          localColumn localBoundary)
        (quadrantAt localColumn localBoundary) = some .north := by
      rw [horizontalInterior_verticalWindow oldGrid blockX blockY
        localColumn localBoundary localColumnLt (by omega)]
      simpa only [oldGrid, columnEq, boundaryEq] using north.2
    rcases verticalLowerNorth pairChecked localColumnLt hcreated localInterior with
      ⟨targetY, targetGt, targetLt, targetInterior, bounded⟩
    have targetGlobalBetween : StrictBetween row boundary
        (8 * blockY + targetY) := by
      right
      constructor
      · omega
      · have rowMod := Nat.mod_lt row (by decide : 0 < 8)
        have rowDecompose := Nat.mod_add_div row 8
        dsimp only [blockY, sourceBlock] at *
        omega
    have targetGlobalInterior : Signals.horizontalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          column (8 * blockY + targetY))
        (quadrantAt column (8 * blockY + targetY)) ≠ none := by
      rw [← columnEq]
      rw [← horizontalInterior_verticalWindow oldGrid blockX blockY
        localColumn targetY localColumnLt (by omega)]
      exact targetInterior
    have translated := boundedPath_verticalWindow oldGrid blockX blockY bounded
    rw [horizontalPort_verticalWindow oldGrid blockX blockY
      localColumn localBoundary localColumnLt (by omega)] at translated
    rw [horizontalPort_verticalWindow oldGrid blockX blockY
      localColumn targetY localColumnLt (by omega)] at translated
    right
    refine ⟨8 * blockY + targetY, targetGlobalBetween,
      targetGlobalInterior, ?_⟩
    simpa only [oldGrid, columnEq, boundaryEq] using translated

/-- Horizontal dual of `vertical`. -/
theorem horizontal
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (_parentX parentY : Nat) {column row boundary : Nat}
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
    (far : column / 8 + 1 < boundary / 8 ∨
      boundary / 8 + 1 < column / 8) :
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockY := row / 8
  let localRow := row % 8
  let sourceBlock := boundary / 8
  let localBoundary := boundary % 8
  have localRowLt : localRow < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have rowEq : 8 * blockY + localRow = row := by
    have := Nat.mod_add_div row 8
    omega
  have boundaryDecompose : 8 * sourceBlock + localBoundary = boundary := by
    have := Nat.mod_add_div boundary 8
    omega
  have hcreated : localBoundary ∈ createdCoordinates :=
    local_created_of_not_sparse createdBoundary
  rcases wrongFacing with west | east
  · have farLeft : column / 8 + 1 < boundary / 8 := by
      rcases far with far | far
      · exact far
      · have divLe := Nat.div_le_div_right (c := 8) (Nat.le_of_lt west.1)
        omega
    have sourceBlockPos : 0 < sourceBlock := by
      dsimp only [sourceBlock]
      omega
    let blockX := sourceBlock - 1
    have boundaryEq : 8 * blockX + (8 + localBoundary) = boundary := by
      dsimp only [blockX]
      omega
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid (blockX + 1) blockY) ∈
        horizontalPairs := by
      exact refinedGrid_horizontalPair_mem phase depth grid blockX blockY
    have pairChecked :
        PairCoverSeamCreatedFarParallelAudit.checkHorizontalPair (canonicalPair
        (oldGrid blockX blockY, oldGrid (blockX + 1) blockY)) = true := by
      exact (List.all_eq_true.mp
        PairCoverSeamCreatedFarParallelAudit.horizontal_complete) _ hpair
    have localInterior : Signals.verticalInterior?
        (componentAt (iterateRefine 2 (horizontalGrid (canonicalPair
          (oldGrid blockX blockY, oldGrid (blockX + 1) blockY))))
          (8 + localBoundary) localRow)
        (quadrantAt (8 + localBoundary) localRow) = some .west := by
      rw [verticalInterior_horizontalWindow oldGrid blockX blockY
        (8 + localBoundary) localRow (by omega) localRowLt]
      simpa only [oldGrid, boundaryEq, rowEq] using west.2
    rcases horizontalRightWest pairChecked localRowLt hcreated localInterior with
      ⟨targetX, targetPos, targetLt, targetInterior, bounded⟩
    have targetGlobalBetween : StrictBetween column boundary
        (8 * blockX + targetX) := by
      left
      constructor
      · have columnMod := Nat.mod_lt column (by decide : 0 < 8)
        have columnDecompose := Nat.mod_add_div column 8
        dsimp only [blockX, sourceBlock] at *
        omega
      · omega
    have targetGlobalInterior : Signals.verticalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          (8 * blockX + targetX) row)
        (quadrantAt (8 * blockX + targetX) row) ≠ none := by
      rw [← rowEq]
      rw [← verticalInterior_horizontalWindow oldGrid blockX blockY
        targetX localRow (by omega) localRowLt]
      exact targetInterior
    have translated := boundedPath_horizontalWindow oldGrid blockX blockY bounded
    rw [verticalPort_horizontalWindow oldGrid blockX blockY
      (8 + localBoundary) localRow (by omega) localRowLt] at translated
    rw [verticalPort_horizontalWindow oldGrid blockX blockY
      targetX localRow (by omega) localRowLt] at translated
    right
    refine ⟨8 * blockX + targetX, targetGlobalBetween,
      targetGlobalInterior, ?_⟩
    simpa only [oldGrid, rowEq, boundaryEq] using translated
  · have farRight : boundary / 8 + 1 < column / 8 := by
      rcases far with far | far
      · have divLe := Nat.div_le_div_right (c := 8) (Nat.le_of_lt east.1)
        omega
      · exact far
    let blockX := sourceBlock
    have boundaryEq : 8 * blockX + localBoundary = boundary := by
      simpa only [blockX] using boundaryDecompose
    have hpair : canonicalPair
        (oldGrid blockX blockY, oldGrid (blockX + 1) blockY) ∈
        horizontalPairs := by
      exact refinedGrid_horizontalPair_mem phase depth grid blockX blockY
    have pairChecked :
        PairCoverSeamCreatedFarParallelAudit.checkHorizontalPair (canonicalPair
        (oldGrid blockX blockY, oldGrid (blockX + 1) blockY)) = true := by
      exact (List.all_eq_true.mp
        PairCoverSeamCreatedFarParallelAudit.horizontal_complete) _ hpair
    have localInterior : Signals.verticalInterior?
        (componentAt (iterateRefine 2 (horizontalGrid (canonicalPair
          (oldGrid blockX blockY, oldGrid (blockX + 1) blockY))))
          localBoundary localRow)
        (quadrantAt localBoundary localRow) = some .east := by
      rw [verticalInterior_horizontalWindow oldGrid blockX blockY
        localBoundary localRow (by omega) localRowLt]
      simpa only [oldGrid, boundaryEq, rowEq] using east.2
    rcases horizontalLeftEast pairChecked localRowLt hcreated localInterior with
      ⟨targetX, targetGt, targetLt, targetInterior, bounded⟩
    have targetGlobalBetween : StrictBetween column boundary
        (8 * blockX + targetX) := by
      right
      constructor
      · omega
      · have columnMod := Nat.mod_lt column (by decide : 0 < 8)
        have columnDecompose := Nat.mod_add_div column 8
        dsimp only [blockX, sourceBlock] at *
        omega
    have targetGlobalInterior : Signals.verticalInterior?
        (componentAt (iterateRefine 2 oldGrid)
          (8 * blockX + targetX) row)
        (quadrantAt (8 * blockX + targetX) row) ≠ none := by
      rw [← rowEq]
      rw [← verticalInterior_horizontalWindow oldGrid blockX blockY
        targetX localRow (by omega) localRowLt]
      exact targetInterior
    have translated := boundedPath_horizontalWindow oldGrid blockX blockY bounded
    rw [verticalPort_horizontalWindow oldGrid blockX blockY
      localBoundary localRow (by omega) localRowLt] at translated
    rw [verticalPort_horizontalWindow oldGrid blockX blockY
      targetX localRow (by omega) localRowLt] at translated
    right
    refine ⟨8 * blockX + targetX, targetGlobalBetween,
      targetGlobalInterior, ?_⟩
    simpa only [oldGrid, rowEq, boundaryEq] using translated

end PairCoverSeamCreatedBoundaryFar
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
