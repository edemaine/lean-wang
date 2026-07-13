/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedLocalAudit
import LeanWang.OllingerRobinson104PairCoverSeamPathTranslation

/-!
# Transport local created-coordinate seam paths

The finite audit works on one constant-parent two-substitution macrocell.
This module transplants its bounded paths into the corresponding 8-by-8
quarter-coordinate block of an arbitrary grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedLocalTransport

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphRefinement RedShadeGraphTranslation RefinementTranslation
  PairCoverSeamShadePaths PairCoverSeamPathSearch
  PairCoverSeamPathBoundedBase PairCoverSeamPathTranslation
  PairCoverSeamCreatedLocalAudit PairCoverSeamCreatedLocalAuditCheck
  Signals.FreeCellLocal Signals.FreeCellEmbedding

set_option maxRecDepth 20000

theorem horizontalPort_twoBlock (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat) (hx : x < 8) (hy : y < 8) :
    translatePort
        (horizontalPort
          (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y)
        (8 * blockX) (8 * blockY) =
      horizontalPort (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
  unfold horizontalPort
  have component := componentAt_two_block grid 0 blockX blockY x y hx hy
  change componentAt (iterateRefine 2 grid)
      (8 * blockX + x) (8 * blockY + y) =
    componentAt
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y at component
  rw [component, quadrantAt_block]
  split <;> simp [translatePort]

theorem verticalPort_twoBlock (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat) (hx : x < 8) (hy : y < 8) :
    translatePort
        (verticalPort
          (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y)
        (8 * blockX) (8 * blockY) =
      verticalPort (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
  unfold verticalPort
  have component := componentAt_two_block grid 0 blockX blockY x y hx hy
  change componentAt (iterateRefine 2 grid)
      (8 * blockX + x) (8 * blockY + y) =
    componentAt
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y at component
  rw [component, quadrantAt_block]
  split <;> simp [translatePort]

theorem verticalInterior_twoBlock (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat) (hx : x < 8) (hy : y < 8) :
    Signals.verticalInterior?
        (componentAt
          (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y)
        (quadrantAt x y) =
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid)
          (8 * blockX + x) (8 * blockY + y))
        (quadrantAt (8 * blockX + x) (8 * blockY + y)) := by
  have component := componentAt_two_block grid 0 blockX blockY x y hx hy
  change componentAt (iterateRefine 2 grid)
      (8 * blockX + x) (8 * blockY + y) =
    componentAt
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y at component
  rw [component, quadrantAt_block]

theorem horizontalInterior_twoBlock (grid : Nat → Nat → Index)
    (blockX blockY x y : Nat) (hx : x < 8) (hy : y < 8) :
    Signals.horizontalInterior?
        (componentAt
          (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y)
        (quadrantAt x y) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid)
          (8 * blockX + x) (8 * blockY + y))
        (quadrantAt (8 * blockX + x) (8 * blockY + y)) := by
  have component := componentAt_two_block grid 0 blockX blockY x y hx hy
  change componentAt (iterateRefine 2 grid)
      (8 * blockX + x) (8 * blockY + y) =
    componentAt
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y at component
  rw [component, quadrantAt_block]

/-- A bounded local path becomes a global path in the selected depth-two
macrocell. -/
theorem boundedPath_twoBlock
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
      8 8 first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity := by
  have componentsEq : ∀ x y, x < 8 → y < 8 →
      componentAt
          (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) x y =
        componentAt
          (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact (componentAt_shift_eq_constant 2 grid blockX blockY x y
      (by norm_num; omega) (by norm_num; omega)).symm
  have shifted :=
    (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
      componentsEq path).path
  simpa using (path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted)

theorem boundedVerticalSeamPath_twoBlock
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {column row boundary : Nat}
    (hcolumn : column < 8) (hrow : row < 8) (hboundary : boundary < 8)
    (path : BoundedVerticalSeamPath
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
      8 0 4 column row boundary) :
    VerticalSeamPath (iterateRefine 2 grid)
      (4 * blockX) (4 * blockX + 4)
      (8 * blockX + column) (8 * blockY + row)
      (8 * blockY + boundary) := by
  rcases path with path | path
  · rcases path with ⟨targetX, hwest, heast, hinterior, path⟩
    have htargetX : targetX < 8 := by
      have hbounds := path.second_inBounds
      unfold verticalPort at hbounds
      split at hbounds <;> exact hbounds.1
    left
    refine ⟨8 * blockX + targetX, ?_, ?_, ?_, ?_⟩
    · simp [quarterWest] at hwest ⊢
      omega
    · simp [quarterEast] at heast ⊢
      omega
    · rw [← verticalInterior_twoBlock grid blockX blockY
        targetX row htargetX hrow]
      exact hinterior
    · have translated := boundedPath_twoBlock grid blockX blockY path
      rw [horizontalPort_twoBlock grid blockX blockY column boundary
        hcolumn hboundary] at translated
      rw [verticalPort_twoBlock grid blockX blockY targetX row
        htargetX hrow] at translated
      exact translated
  · rcases path with ⟨targetY, hbetween, hinterior, path⟩
    have htargetY : targetY < 8 := by
      have hbounds := path.second_inBounds
      unfold horizontalPort at hbounds
      split at hbounds <;> exact hbounds.2
    right
    refine ⟨8 * blockY + targetY, ?_, ?_, ?_⟩
    · unfold StrictBetween at hbetween ⊢
      omega
    · rw [← horizontalInterior_twoBlock grid blockX blockY
        column targetY hcolumn htargetY]
      exact hinterior
    · have translated := boundedPath_twoBlock grid blockX blockY path
      rw [horizontalPort_twoBlock grid blockX blockY column boundary
        hcolumn hboundary] at translated
      rw [horizontalPort_twoBlock grid blockX blockY column targetY
        hcolumn htargetY] at translated
      exact translated

theorem boundedHorizontalSeamPath_twoBlock
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {row column boundary : Nat}
    (hrow : row < 8) (hcolumn : column < 8) (hboundary : boundary < 8)
    (path : BoundedHorizontalSeamPath
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
      8 0 4 row column boundary) :
    HorizontalSeamPath (iterateRefine 2 grid)
      (4 * blockY) (4 * blockY + 4)
      (8 * blockY + row) (8 * blockX + column)
      (8 * blockX + boundary) := by
  rcases path with path | path
  · rcases path with ⟨targetY, hsouth, hnorth, hinterior, path⟩
    have htargetY : targetY < 8 := by
      have hbounds := path.second_inBounds
      unfold horizontalPort at hbounds
      split at hbounds <;> exact hbounds.2
    left
    refine ⟨8 * blockY + targetY, ?_, ?_, ?_, ?_⟩
    · simp [quarterSouth] at hsouth ⊢
      omega
    · simp [quarterNorth] at hnorth ⊢
      omega
    · rw [← horizontalInterior_twoBlock grid blockX blockY
        column targetY hcolumn htargetY]
      exact hinterior
    · have translated := boundedPath_twoBlock grid blockX blockY path
      rw [verticalPort_twoBlock grid blockX blockY boundary row
        hboundary hrow] at translated
      rw [horizontalPort_twoBlock grid blockX blockY column targetY
        hcolumn htargetY] at translated
      exact translated
  · rcases path with ⟨targetX, hbetween, hinterior, path⟩
    have htargetX : targetX < 8 := by
      have hbounds := path.second_inBounds
      unfold verticalPort at hbounds
      split at hbounds <;> exact hbounds.1
    right
    refine ⟨8 * blockX + targetX, ?_, ?_, ?_⟩
    · unfold StrictBetween at hbetween ⊢
      omega
    · rw [← verticalInterior_twoBlock grid blockX blockY
        targetX row htargetX hrow]
      exact hinterior
    · have translated := boundedPath_twoBlock grid blockX blockY path
      rw [verticalPort_twoBlock grid blockX blockY boundary row
        hboundary hrow] at translated
      rw [verticalPort_twoBlock grid blockX blockY targetX row
        htargetX hrow] at translated
      exact translated

/-- The certified local vertical query transplants into any coarse grid. -/
theorem verticalQuery
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {column boundary row : Nat}
    (hcolumn : column ∈ coordinates) (hboundary : boundary ∈ coordinates)
    (hquery : row ∈ verticalQueries
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) column boundary) :
    VerticalSeamPath (iterateRefine 2 grid)
      (4 * blockX) (4 * blockX + 4)
      (8 * blockX + column) (8 * blockY + row)
      (8 * blockY + boundary) := by
  have localPath := (parentPaths (grid blockX blockY)).vertical
    hcolumn hboundary hquery
  apply boundedVerticalSeamPath_twoBlock grid blockX blockY
  · simpa [coordinates] using hcolumn
  · have := List.mem_of_mem_filter hquery
    simpa [coordinates] using this
  · simpa [coordinates] using hboundary
  · exact localPath

/-- Horizontal dual of `verticalQuery`. -/
theorem horizontalQuery
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {row boundary column : Nat}
    (hrow : row ∈ coordinates) (hboundary : boundary ∈ coordinates)
    (hquery : column ∈ horizontalQueries
      (RedShadeGraphRefinement.fineGrid (grid blockX blockY)) row boundary) :
    HorizontalSeamPath (iterateRefine 2 grid)
      (4 * blockY) (4 * blockY + 4)
      (8 * blockY + row) (8 * blockX + column)
      (8 * blockX + boundary) := by
  have localPath := (parentPaths (grid blockX blockY)).horizontal
    hrow hboundary hquery
  apply boundedHorizontalSeamPath_twoBlock grid blockX blockY
  · simpa [coordinates] using hrow
  · have := List.mem_of_mem_filter hquery
    simpa [coordinates] using this
  · simpa [coordinates] using hboundary
  · exact localPath

/-- A same-macrocell wrong-facing query in either audited vertical family has
a global seam path. -/
theorem verticalSameBlock
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {column boundary row : Nat}
    (hcolumn : column < 8) (hboundary : boundary < 8) (hrow : row < 8)
    (wrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2 grid)
            (8 * blockX + column) (8 * blockY + boundary))
          (quadrantAt (8 * blockX + column) (8 * blockY + boundary)) =
            some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt (iterateRefine 2 grid)
            (8 * blockX + column) (8 * blockY + boundary))
          (quadrantAt (8 * blockX + column) (8 * blockY + boundary)) =
            some .north))
    (audited : (isCreated boundary ||
      (!isCreated row && isCreated column)) = true) :
    VerticalSeamPath (iterateRefine 2 grid)
      (4 * blockX) (4 * blockX + 4)
      (8 * blockX + column) (8 * blockY + row)
      (8 * blockY + boundary) := by
  have interior := horizontalInterior_twoBlock grid blockX blockY
    column boundary hcolumn hboundary
  have localWrongFacing :
      (row < boundary ∧
        Signals.horizontalInterior?
          (componentAt
            (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
            column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt
            (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
            column boundary)
          (quadrantAt column boundary) = some .north) := by
    rcases wrongFacing with wrongFacing | wrongFacing
    · exact Or.inl ⟨wrongFacing.1, interior.trans wrongFacing.2⟩
    · exact Or.inr ⟨wrongFacing.1, interior.trans wrongFacing.2⟩
  have audited' : isCreated boundary = true ∨
      (!isCreated row) = true ∧ isCreated column = true := by
    simpa only [Bool.or_eq_true, Bool.and_eq_true] using audited
  apply verticalQuery grid blockX blockY
  · simp [coordinates, hcolumn]
  · simp [coordinates, hboundary]
  · simp only [verticalQueries, List.mem_filter, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨by simp [coordinates, hrow], localWrongFacing, audited'⟩

/-- Horizontal dual of `verticalSameBlock`. -/
theorem horizontalSameBlock
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {row boundary column : Nat}
    (hrow : row < 8) (hboundary : boundary < 8) (hcolumn : column < 8)
    (wrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2 grid)
            (8 * blockX + boundary) (8 * blockY + row))
          (quadrantAt (8 * blockX + boundary) (8 * blockY + row)) =
            some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt (iterateRefine 2 grid)
            (8 * blockX + boundary) (8 * blockY + row))
          (quadrantAt (8 * blockX + boundary) (8 * blockY + row)) =
            some .east))
    (audited : (isCreated boundary ||
      (!isCreated column && isCreated row)) = true) :
    HorizontalSeamPath (iterateRefine 2 grid)
      (4 * blockY) (4 * blockY + 4)
      (8 * blockY + row) (8 * blockX + column)
      (8 * blockX + boundary) := by
  have interior := verticalInterior_twoBlock grid blockX blockY
    boundary row hboundary hrow
  have localWrongFacing :
      (column < boundary ∧
        Signals.verticalInterior?
          (componentAt
            (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
            boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt
            (RedShadeGraphRefinement.fineGrid (grid blockX blockY))
            boundary row)
          (quadrantAt boundary row) = some .east) := by
    rcases wrongFacing with wrongFacing | wrongFacing
    · exact Or.inl ⟨wrongFacing.1, interior.trans wrongFacing.2⟩
    · exact Or.inr ⟨wrongFacing.1, interior.trans wrongFacing.2⟩
  have audited' : isCreated boundary = true ∨
      (!isCreated column) = true ∧ isCreated row = true := by
    simpa only [Bool.or_eq_true, Bool.and_eq_true] using audited
  apply horizontalQuery grid blockX blockY
  · simp [coordinates, hrow]
  · simp [coordinates, hboundary]
  · simp only [horizontalQueries, List.mem_filter, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨by simp [coordinates, hcolumn], localWrongFacing, audited'⟩

end PairCoverSeamCreatedLocalTransport
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
