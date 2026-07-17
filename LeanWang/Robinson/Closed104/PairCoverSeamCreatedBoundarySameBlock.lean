/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedBoundaryPaths
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedLocalTransport
import LeanWang.Robinson.Closed104.PairCoverSeamResidualCanonicalAncestorHierarchy

/-!
# Same-macrocell created-boundary paths

The finite created-source audit already handles every query in the source's
own two-substitution macrocell.  This module widens that local seam path to the
enclosing hierarchy collar and packages the exact same-block cases needed by
`CreatedBoundaryPathsAt`.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedBoundarySameBlock

open RedCycles RedShadeCycles RedShadeGraph
  PairCoverSeamArithmetic PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamCreatedLocalAuditCheck PairCoverSeamCreatedLocalTransport
  PairCoverSeamResidualCanonicalAncestorHierarchy
  RefinedCoordinateProjection ShadedFreeLineRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Enlarging the transverse target interval preserves a vertical seam path. -/
theorem VerticalSeamPath.widen
    {grid : Nat → Nat → Index}
    {innerWest innerEast outerWest outerEast column row boundary : Nat}
    (path : VerticalSeamPath grid innerWest innerEast column row boundary)
    (west : quarterWest outerWest ≤ quarterWest innerWest)
    (east : quarterEast innerEast ≤ quarterEast outerEast) :
    VerticalSeamPath grid outerWest outerEast column row boundary := by
  rcases path with path | path
  · rcases path with
      ⟨targetX, targetWest, targetEast, interior, targetPath⟩
    exact Or.inl ⟨targetX, west.trans_lt targetWest,
      targetEast.trans_le east, interior, targetPath⟩
  · exact Or.inr path

/-- Horizontal dual of `VerticalSeamPath.widen`. -/
theorem HorizontalSeamPath.widen
    {grid : Nat → Nat → Index}
    {innerSouth innerNorth outerSouth outerNorth row column boundary : Nat}
    (path : HorizontalSeamPath grid innerSouth innerNorth row column boundary)
    (south : quarterSouth outerSouth ≤ quarterSouth innerSouth)
    (north : quarterNorth innerNorth ≤ quarterNorth outerNorth) :
    HorizontalSeamPath grid outerSouth outerNorth row column boundary := by
  rcases path with path | path
  · rcases path with
      ⟨targetY, targetSouth, targetNorth, interior, targetPath⟩
    exact Or.inl ⟨targetY, south.trans_lt targetSouth,
      targetNorth.trans_le north, interior, targetPath⟩
  · exact Or.inr path

/-- The depth-two macrocell containing a coordinate on or inside the lower
collar edge lies within its enclosing hierarchy collar. -/
theorem localBlock_within_collar
    (phase : Phase) (depth parent coordinate : Nat)
    (lower : quarterWest (successorWest phase depth parent) ≤ coordinate)
    (upper : coordinate < quarterEast (successorEast phase depth parent)) :
    quarterWest (successorWest phase depth parent) ≤
        quarterWest (4 * (coordinate / 8)) ∧
      quarterEast (4 * (coordinate / 8) + 4) ≤
        quarterEast (successorEast phase depth parent) := by
  let level := outerLevel phase depth
  have levelTwo : 2 ≤ level := by
    simp only [level, outerLevel]
    omega
  have levelEq : level = level - 2 + 2 := by omega
  let scale := 2 ^ (level - 2)
  have powerEq : 2 ^ level = 4 * scale := by
    rw [levelEq, pow_add]
    norm_num
    ring
  have westEq : quarterWest (successorWest phase depth parent) =
      8 * (scale * (4 * parent + 1)) + 1 := by
    rw [successorWest_eq_canonical]
    change quarterWest (2 ^ level * (4 * parent + 1)) = _
    rw [powerEq]
    simp only [quarterWest]
    ring
  have eastEq : quarterEast (successorEast phase depth parent) =
      8 * (scale * (4 * parent + 3)) := by
    rw [successorEast_eq_canonical]
    change quarterEast (2 ^ level * (4 * parent + 3)) = _
    rw [powerEq]
    simp only [quarterEast]
    ring
  have coordinateMod : coordinate % 8 < 8 := Nat.mod_lt _ (by decide)
  have coordinateDecompose := Nat.mod_add_div coordinate 8
  rw [westEq] at lower ⊢
  rw [eastEq] at upper ⊢
  simp only [quarterWest, quarterEast]
  constructor <;> omega

private theorem local_created_of_not_sparse {coordinate : Nat}
    (created : ¬IsSparseCoordinate coordinate) :
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
-- The translated path depends on three quotient/remainder decompositions.
/-- A created horizontal source and query in the same depth-two macrocell
already have the required vertical seam path. -/
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
    (sameBlock : row / 8 = boundary / 8) :
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockX := column / 8
  let blockY := boundary / 8
  let localColumn := column % 8
  let localRow := row % 8
  let localBoundary := boundary % 8
  have localColumnLt : localColumn < 8 := Nat.mod_lt _ (by decide)
  have localRowLt : localRow < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have columnEq : 8 * blockX + localColumn = column := by
    have := Nat.mod_add_div column 8
    omega
  have rowEq : 8 * blockY + localRow = row := by
    have := Nat.mod_add_div row 8
    dsimp only [blockY, localRow]
    omega
  have boundaryEq : 8 * blockY + localBoundary = boundary := by
    have := Nat.mod_add_div boundary 8
    omega
  have localPath := PairCoverSeamCreatedLocalTransport.verticalSameBlock
    oldGrid blockX blockY localColumnLt localBoundaryLt localRowLt
    (by
      rcases wrongFacing with wrongFacing | wrongFacing
      · left
        refine ⟨by omega, ?_⟩
        simpa only [oldGrid, columnEq, boundaryEq] using wrongFacing.2
      · right
        refine ⟨by omega, ?_⟩
        simpa only [oldGrid, columnEq, boundaryEq] using wrongFacing.2)
    (by
      simp only [Bool.or_eq_true]
      exact Or.inl (local_created_of_not_sparse createdBoundary))
  have collar := localBlock_within_collar phase (depth + 1) parentX column
    columnWest columnEast
  have widened := VerticalSeamPath.widen localPath collar.1 collar.2
  simpa only [oldGrid, columnEq, rowEq, boundaryEq] using widened

set_option maxHeartbeats 1000000 in
-- The translated path depends on three quotient/remainder decompositions.
/-- Vertical-source dual of `vertical`. -/
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
    (sameBlock : column / 8 = boundary / 8) :
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary := by
  let oldGrid := refinedGrid phase (depth + 1) grid
  let blockX := boundary / 8
  let blockY := row / 8
  let localColumn := column % 8
  let localRow := row % 8
  let localBoundary := boundary % 8
  have localColumnLt : localColumn < 8 := Nat.mod_lt _ (by decide)
  have localRowLt : localRow < 8 := Nat.mod_lt _ (by decide)
  have localBoundaryLt : localBoundary < 8 := Nat.mod_lt _ (by decide)
  have columnEq : 8 * blockX + localColumn = column := by
    have := Nat.mod_add_div column 8
    dsimp only [blockX, localColumn]
    omega
  have rowEq : 8 * blockY + localRow = row := by
    have := Nat.mod_add_div row 8
    omega
  have boundaryEq : 8 * blockX + localBoundary = boundary := by
    have := Nat.mod_add_div boundary 8
    omega
  have localPath := PairCoverSeamCreatedLocalTransport.horizontalSameBlock
    oldGrid blockX blockY localRowLt localBoundaryLt localColumnLt
    (by
      rcases wrongFacing with wrongFacing | wrongFacing
      · left
        refine ⟨by omega, ?_⟩
        simpa only [oldGrid, boundaryEq, rowEq] using wrongFacing.2
      · right
        refine ⟨by omega, ?_⟩
        simpa only [oldGrid, boundaryEq, rowEq] using wrongFacing.2)
    (by
      simp only [Bool.or_eq_true]
      exact Or.inl (local_created_of_not_sparse createdBoundary))
  have collar := localBlock_within_collar phase (depth + 1) parentY row
    (by simpa only [quarterSouth, quarterWest] using rowSouth)
    (by simpa only [quarterNorth, quarterEast] using rowNorth)
  have widened := HorizontalSeamPath.widen localPath
    (by simpa only [quarterSouth, quarterWest] using collar.1)
    (by simpa only [quarterNorth, quarterEast] using collar.2)
  simpa only [oldGrid, columnEq, rowEq, boundaryEq] using widened

end PairCoverSeamCreatedBoundarySameBlock
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
