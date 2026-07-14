/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathExactPredecessorAudit
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftTransport
import LeanWang.OllingerRobinson104PairCoverSeamCreatedLocalTransport

/-!
# Exact predecessor transport

Translate the exact local predecessor certificate into an arbitrary
two-substitution macrocell.  Unlike the older predecessor interface, the
coarse selector is definitionally the fine selector's `coarseCoordinate`.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathExactPredecessorTransport

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphTranslation
  PairCoverSeamCreatedLocalTransport PairCoverSeamShadePaths
  PairCoverSeamResidualDirectPathExactPredecessorAudit
  PairCoverSeamResidualDirectPathFamilyTargetLiftTransport
  RefinedCoordinateProjection SparseFreeLineLocalTransport
  Signals.FreeCellLocal Signals.FreeCellEmbedding

set_option maxRecDepth 20000

/-- A fine horizontal source on a sparse boundary has an exact projected
coarse source and an even connector to its literal sparse copy. -/
def HorizontalExactPredecessor (grid : Nat → Nat → Index)
    (column boundary : Nat) : Prop :=
  ∃ oldBoundary,
    sparseCoordinate oldBoundary = boundary ∧
    Signals.horizontalInterior?
      (componentAt grid (coarseCoordinate column) oldBoundary)
      (quadrantAt (coarseCoordinate column) oldBoundary) ≠ none ∧
    Signals.horizontalInterior?
        (componentAt grid (coarseCoordinate column) oldBoundary)
        (quadrantAt (coarseCoordinate column) oldBoundary) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid) column boundary)
        (quadrantAt column boundary) ∧
    Path (iterateRefine 2 grid)
      (horizontalPort (iterateRefine 2 grid) column boundary)
      (sparsePort (horizontalPort grid
        (coarseCoordinate column) oldBoundary)) false

/-- Vertical dual of `HorizontalExactPredecessor`. -/
def VerticalExactPredecessor (grid : Nat → Nat → Index)
    (boundary row : Nat) : Prop :=
  ∃ oldBoundary,
    sparseCoordinate oldBoundary = boundary ∧
    Signals.verticalInterior?
      (componentAt grid oldBoundary (coarseCoordinate row))
      (quadrantAt oldBoundary (coarseCoordinate row)) ≠ none ∧
    Signals.verticalInterior?
        (componentAt grid oldBoundary (coarseCoordinate row))
        (quadrantAt oldBoundary (coarseCoordinate row)) =
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid) boundary row)
        (quadrantAt boundary row) ∧
    Path (iterateRefine 2 grid)
      (verticalPort (iterateRefine 2 grid) boundary row)
      (sparsePort (verticalPort grid
        oldBoundary (coarseCoordinate row))) false

private theorem horizontalSparsePort_oldBlock
    (grid : Nat → Nat → Index) (blockX blockY sourceX sourceY : Nat)
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2) :
    translatePort
        (sparsePort (horizontalPort (coarseGrid (grid blockX blockY))
          sourceX sourceY)) (8 * blockX) (8 * blockY) =
      sparsePort (horizontalPort grid
        (2 * blockX + sourceX) (2 * blockY + sourceY)) := by
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  change componentAt grid (2 * blockX + sourceX) (2 * blockY + sourceY) =
    componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY at component
  unfold horizontalPort
  rw [← component, ← quadrant]
  split <;>
    simp [translatePort, sparsePort,
      sparseCoordinate_two_block blockX sourceX sourceXLt,
      sparseCoordinate_two_block blockY sourceY sourceYLt]

private theorem verticalSparsePort_oldBlock
    (grid : Nat → Nat → Index) (blockX blockY sourceX sourceY : Nat)
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2) :
    translatePort
        (sparsePort (verticalPort (coarseGrid (grid blockX blockY))
          sourceX sourceY)) (8 * blockX) (8 * blockY) =
      sparsePort (verticalPort grid
        (2 * blockX + sourceX) (2 * blockY + sourceY)) := by
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  change componentAt grid (2 * blockX + sourceX) (2 * blockY + sourceY) =
    componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY at component
  unfold verticalPort
  rw [← component, ← quadrant]
  split <;>
    simp [translatePort, sparsePort,
      sparseCoordinate_two_block blockX sourceX sourceXLt,
      sparseCoordinate_two_block blockY sourceY sourceYLt]

set_option maxHeartbeats 2000000 in
-- Translated selectors occur dependently in both path endpoints.
/-- Every live horizontal sparse source has the certified exact predecessor. -/
theorem horizontalExactPredecessor
    (grid : Nat → Nat → Index) (column boundary : Nat)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) column boundary)
      (quadrantAt column boundary) ≠ none) :
    HorizontalExactPredecessor grid column boundary := by
  rcases sparseBoundary with ⟨oldBoundary, boundaryEq⟩
  let blockX := column / 8
  let targetX := column % 8
  let sourceX := coarseCoordinate targetX
  let blockY := oldBoundary / 2
  let sourceY := oldBoundary % 2
  have targetXLt : targetX < 8 := Nat.mod_lt _ (by decide)
  have sourceXLt : sourceX < 2 := by
    dsimp only [sourceX, targetX]
    unfold coarseCoordinate
    have divZero : column % 8 / 8 = 0 := by omega
    rw [divZero]
    split <;> omega
  have sourceYLt : sourceY < 2 := Nat.mod_lt _ (by decide)
  have columnEq : 8 * blockX + targetX = column := by
    have := Nat.mod_add_div column 8
    dsimp [blockX, targetX]
    omega
  have oldColumnEq : 2 * blockX + sourceX = coarseCoordinate column := by
    calc
      2 * blockX + sourceX = coarseCoordinate (8 * blockX + targetX) := by
        symm
        exact coarseCoordinate_twoBlock blockX targetX targetXLt
      _ = coarseCoordinate column := congrArg coarseCoordinate columnEq
  have oldBoundaryEq : 2 * blockY + sourceY = oldBoundary := by
    have := Nat.mod_add_div oldBoundary 2
    dsimp [blockY, sourceY]
    omega
  have localYBound : sparseCoordinate sourceY < 8 := by
    simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega
  have boundaryLocal :
      8 * blockY + sparseCoordinate sourceY = boundary := by
    rw [← boundaryEq, ← oldBoundaryEq,
      sparseCoordinate_two_block blockY sourceY sourceYLt]
  have localInterior : Signals.horizontalInterior?
      (componentAt (fineGrid (grid blockX blockY))
        targetX (sparseCoordinate sourceY))
      (quadrantAt targetX (sparseCoordinate sourceY)) ≠ none := by
    rw [horizontalInterior_twoBlock grid blockX blockY targetX
      (sparseCoordinate sourceY) targetXLt localYBound]
    simpa only [columnEq, boundaryLocal] using interior
  have checked := horizontalAt_of_checkParent
    (complete (grid blockX blockY)) sourceYLt targetXLt
  rcases horizontalAt_sound sourceYLt targetXLt checked localInterior with
    ⟨sourceInterior, orientationEq, localPath⟩
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have component' : componentAt grid (2 * blockX + sourceX)
      (2 * blockY + sourceY) =
      componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY := by
    simpa only [iterateRefine] using component
  have oldInteriorEq : Signals.horizontalInterior?
      (componentAt grid (coarseCoordinate column) oldBoundary)
      (quadrantAt (coarseCoordinate column) oldBoundary) =
    Signals.horizontalInterior?
      (componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY)
      (quadrantAt sourceX sourceY) := by
    rw [← oldColumnEq, ← oldBoundaryEq, component', quadrant]
  have globalSourceInterior : Signals.horizontalInterior?
      (componentAt grid (coarseCoordinate column) oldBoundary)
      (quadrantAt (coarseCoordinate column) oldBoundary) ≠ none := by
    rw [oldInteriorEq]
    exact sourceInterior
  have globalOrientationEq : Signals.horizontalInterior?
        (componentAt grid (coarseCoordinate column) oldBoundary)
        (quadrantAt (coarseCoordinate column) oldBoundary) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid) column boundary)
        (quadrantAt column boundary) := by
    calc
      _ = Signals.horizontalInterior?
          (componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY)
          (quadrantAt sourceX sourceY) := oldInteriorEq
      _ = Signals.horizontalInterior?
          (componentAt (fineGrid (grid blockX blockY))
            targetX (sparseCoordinate sourceY))
          (quadrantAt targetX (sparseCoordinate sourceY)) := orientationEq
      _ = Signals.horizontalInterior?
          (componentAt (iterateRefine 2 grid)
            (8 * blockX + targetX)
            (8 * blockY + sparseCoordinate sourceY))
          (quadrantAt (8 * blockX + targetX)
            (8 * blockY + sparseCoordinate sourceY)) :=
        horizontalInterior_twoBlock grid blockX blockY targetX
          (sparseCoordinate sourceY) targetXLt localYBound
      _ = _ := by rw [columnEq, boundaryLocal]
  have translated := boundedPath_twoBlock grid blockX blockY localPath
  have targetPort := horizontalPort_twoBlock grid blockX blockY
    targetX (sparseCoordinate sourceY) targetXLt localYBound
  have sourcePort := horizontalSparsePort_oldBlock grid blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  rw [sourcePort, targetPort, columnEq, boundaryLocal] at translated
  refine ⟨oldBoundary, boundaryEq, globalSourceInterior,
    globalOrientationEq, ?_⟩
  simpa only [oldColumnEq, oldBoundaryEq] using path_symm translated

set_option maxHeartbeats 2000000 in
-- Translated selectors occur dependently in both path endpoints.
/-- Vertical dual of `horizontalExactPredecessor`. -/
theorem verticalExactPredecessor
    (grid : Nat → Nat → Index) (boundary row : Nat)
    (sparseBoundary : IsSparseCoordinate boundary)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) boundary row)
      (quadrantAt boundary row) ≠ none) :
    VerticalExactPredecessor grid boundary row := by
  rcases sparseBoundary with ⟨oldBoundary, boundaryEq⟩
  let blockX := oldBoundary / 2
  let sourceX := oldBoundary % 2
  let blockY := row / 8
  let targetY := row % 8
  let sourceY := coarseCoordinate targetY
  have sourceXLt : sourceX < 2 := Nat.mod_lt _ (by decide)
  have targetYLt : targetY < 8 := Nat.mod_lt _ (by decide)
  have sourceYLt : sourceY < 2 := by
    dsimp only [sourceY, targetY]
    unfold coarseCoordinate
    have divZero : row % 8 / 8 = 0 := by omega
    rw [divZero]
    split <;> omega
  have oldBoundaryEq : 2 * blockX + sourceX = oldBoundary := by
    have := Nat.mod_add_div oldBoundary 2
    dsimp [blockX, sourceX]
    omega
  have rowEq : 8 * blockY + targetY = row := by
    have := Nat.mod_add_div row 8
    dsimp [blockY, targetY]
    omega
  have oldRowEq : 2 * blockY + sourceY = coarseCoordinate row := by
    calc
      2 * blockY + sourceY = coarseCoordinate (8 * blockY + targetY) := by
        symm
        exact coarseCoordinate_twoBlock blockY targetY targetYLt
      _ = coarseCoordinate row := congrArg coarseCoordinate rowEq
  have localXBound : sparseCoordinate sourceX < 8 := by
    simp [sparseCoordinate, macroOrigin, localCoordinate]
    omega
  have boundaryLocal :
      8 * blockX + sparseCoordinate sourceX = boundary := by
    rw [← boundaryEq, ← oldBoundaryEq,
      sparseCoordinate_two_block blockX sourceX sourceXLt]
  have localInterior : Signals.verticalInterior?
      (componentAt (fineGrid (grid blockX blockY))
        (sparseCoordinate sourceX) targetY)
      (quadrantAt (sparseCoordinate sourceX) targetY) ≠ none := by
    rw [verticalInterior_twoBlock grid blockX blockY
      (sparseCoordinate sourceX) targetY localXBound targetYLt]
    simpa only [boundaryLocal, rowEq] using interior
  have checked := verticalAt_of_checkParent
    (complete (grid blockX blockY)) sourceXLt targetYLt
  rcases verticalAt_sound sourceXLt targetYLt checked localInterior with
    ⟨sourceInterior, orientationEq, localPath⟩
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have component' : componentAt grid (2 * blockX + sourceX)
      (2 * blockY + sourceY) =
      componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY := by
    simpa only [iterateRefine] using component
  have oldInteriorEq : Signals.verticalInterior?
      (componentAt grid oldBoundary (coarseCoordinate row))
      (quadrantAt oldBoundary (coarseCoordinate row)) =
    Signals.verticalInterior?
      (componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY)
      (quadrantAt sourceX sourceY) := by
    rw [← oldBoundaryEq, ← oldRowEq, component', quadrant]
  have globalSourceInterior : Signals.verticalInterior?
      (componentAt grid oldBoundary (coarseCoordinate row))
      (quadrantAt oldBoundary (coarseCoordinate row)) ≠ none := by
    rw [oldInteriorEq]
    exact sourceInterior
  have globalOrientationEq : Signals.verticalInterior?
        (componentAt grid oldBoundary (coarseCoordinate row))
        (quadrantAt oldBoundary (coarseCoordinate row)) =
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid) boundary row)
        (quadrantAt boundary row) := by
    calc
      _ = Signals.verticalInterior?
          (componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY)
          (quadrantAt sourceX sourceY) := oldInteriorEq
      _ = Signals.verticalInterior?
          (componentAt (fineGrid (grid blockX blockY))
            (sparseCoordinate sourceX) targetY)
          (quadrantAt (sparseCoordinate sourceX) targetY) := orientationEq
      _ = Signals.verticalInterior?
          (componentAt (iterateRefine 2 grid)
            (8 * blockX + sparseCoordinate sourceX)
            (8 * blockY + targetY))
          (quadrantAt (8 * blockX + sparseCoordinate sourceX)
            (8 * blockY + targetY)) :=
        verticalInterior_twoBlock grid blockX blockY
          (sparseCoordinate sourceX) targetY localXBound targetYLt
      _ = _ := by rw [boundaryLocal, rowEq]
  have translated := boundedPath_twoBlock grid blockX blockY localPath
  have targetPort := verticalPort_twoBlock grid blockX blockY
    (sparseCoordinate sourceX) targetY localXBound targetYLt
  have sourcePort := verticalSparsePort_oldBlock grid blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  rw [sourcePort, targetPort, boundaryLocal, rowEq] at translated
  refine ⟨oldBoundary, boundaryEq, globalSourceInterior,
    globalOrientationEq, ?_⟩
  simpa only [oldBoundaryEq, oldRowEq] using path_symm translated

end PairCoverSeamResidualDirectPathExactPredecessorTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
