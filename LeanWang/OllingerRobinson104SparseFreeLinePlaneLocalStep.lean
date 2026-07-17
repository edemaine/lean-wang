/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineLocalProjection
import LeanWang.OllingerRobinson104SparseFreeLinePlaneBase

/-!
# Local sparse projection in arbitrary coarse grids

The child-class audits used by the local sparse recurrence depend only on the
last substitution parity, not on a constant coarse parent.  This module lifts
the locally projected successor branches to arbitrary coarse grids.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneLocalStep

open RedCycles RedShadeGraphRefinement ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement ShadedFreeLineRecurrence
  BorderCoverageOffsets SparseFreeLineOffsets SparseFreeLineLocalStates
  SparseFreeLineLocalProjection SparseFreeLinePlaneBase

set_option maxRecDepth 20000

theorem refinedGrid_succ (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    refinedGrid phase (depth + 1) grid =
      iterateRefine 2 (refinedGrid phase depth grid) := by
  unfold refinedGrid
  rw [show refinementDepth phase (depth + 1) =
      2 + refinementDepth phase depth by
    simp [refinementDepth]
    omega]
  exact (PlaneRedBoards.iterateRefine_add 2
    (refinementDepth phase depth) grid).symm

theorem refinedGrid_mem_rowChildren (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (x y : Nat) :
    refinedGrid phase depth grid x y ∈ rowChildren (parityOffset y) := by
  cases phase
  · simpa [refinedGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_rowChildren (2 * depth + 1) grid x y
  · simpa [refinedGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_rowChildren (2 * depth + 2) grid x y

theorem refinedGrid_mem_columnChildren (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) (x y : Nat) :
    refinedGrid phase depth grid x y ∈ columnChildren (parityOffset x) := by
  cases phase
  · simpa [refinedGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_columnChildren (2 * depth + 1) grid x y
  · simpa [refinedGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_columnChildren (2 * depth + 2) grid x y

theorem pivot_line_block_even (phase : Phase) (depth : Nat) :
    (lineCoordinate phase depth (pivot depth) / 2) % 2 = 0 := by
  cases phase
  · rw [even_pivot_coordinate]
    omega
  · rw [odd_pivot_coordinate]
    omega

theorem verticalChecks_pivot (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    ∀ blockX,
      verticalCheck
        (lineCoordinate phase depth (pivot depth) % 2)
        (lineCoordinate phase depth (pivot depth) % 2)
        (refinedGrid phase depth grid blockX
          (lineCoordinate phase depth (pivot depth) / 2)) = true := by
  intro blockX
  let row := lineCoordinate phase depth (pivot depth)
  have hblock := pivot_line_block_even phase depth
  have hparity : parityOffset (row / 2) = 0 := by
    apply Fin.ext
    simpa [row, parityOffset] using hblock
  have hmem := refinedGrid_mem_rowChildren phase depth grid blockX (row / 2)
  rw [hparity] at hmem
  have hmod : row % 2 = 0 ∨ row % 2 = 1 := by
    have := Nat.mod_lt row (by decide : 0 < 2)
    omega
  rcases hmod with hzero | hone
  · simpa [row, hzero] using lowerRow_sparse_zero _ hmem
  · simpa [row, hone] using lowerRow_sparse_one _ hmem

theorem horizontalChecks_pivot (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) :
    ∀ blockY,
      horizontalCheck
        (lineCoordinate phase depth (pivot depth) % 2)
        (lineCoordinate phase depth (pivot depth) % 2)
        (refinedGrid phase depth grid
          (lineCoordinate phase depth (pivot depth) / 2) blockY) = true := by
  intro blockY
  let column := lineCoordinate phase depth (pivot depth)
  have hblock := pivot_line_block_even phase depth
  have hparity : parityOffset (column / 2) = 0 := by
    apply Fin.ext
    simpa [column, parityOffset] using hblock
  have hmem := refinedGrid_mem_columnChildren phase depth grid (column / 2) blockY
  rw [hparity] at hmem
  have hmod : column % 2 = 0 ∨ column % 2 = 1 := by
    have := Nat.mod_lt column (by decide : 0 < 2)
    omega
  rcases hmod with hzero | hone
  · simpa [column, hzero] using leftColumn_sparse_zero _ hmem
  · simpa [column, hone] using leftColumn_sparse_one _ hmem

/-- The pivot main child projects in every arbitrary coarse grid. -/
theorem evenMainChildStep
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    {offset : Nat} (hold : offset ∈ offsets depth)
    (heven : offset % 2 = 0)
    (row : LiveRowCertificate (refinedGrid phase depth grid)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset))
    (column : LiveColumnCertificate (refinedGrid phase depth grid)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset)) :
    LiveRowCertificate (refinedGrid phase (depth + 1) grid)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) (mainChild offset)) ∧
      LiveColumnCertificate (refinedGrid phase (depth + 1) grid)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) (mainChild offset)) := by
  have hoffset := even_offset_eq_pivot depth hold heven
  subst offset
  have hcoordinate : lineCoordinate phase (depth + 1) (mainChild (pivot depth)) =
      sparseCoordinate (lineCoordinate phase depth (pivot depth)) := by
    simpa [mainChild, pivot_even] using
      lineCoordinate_evenOffset_sparse phase depth (pivot depth) (pivot_even depth)
  have vertical := verticalProjectionAt_of_checks row
    (verticalChecks_pivot phase depth grid)
  have horizontal := horizontalProjectionAt_of_checks column
    (horizontalChecks_pivot phase depth grid)
  constructor
  · rw [hcoordinate]
    simpa [refinedGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [refinedGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- The even-phase pivot extra child projects in every arbitrary coarse grid. -/
theorem evenPivotExtraStep
    (depth : Nat) (grid : Nat → Nat → Index)
    (row : LiveRowCertificate (refinedGrid .even depth grid)
      (west .even depth) (east .even depth)
      (west .even depth) (east .even depth)
      (lineCoordinate .even depth (pivot depth)))
    (column : LiveColumnCertificate (refinedGrid .even depth grid)
      (west .even depth) (east .even depth)
      (west .even depth) (east .even depth)
      (lineCoordinate .even depth (pivot depth))) :
    LiveRowCertificate (refinedGrid .even (depth + 1) grid)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) (extraChild (pivot depth))) ∧
      LiveColumnCertificate (refinedGrid .even (depth + 1) grid)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) (extraChild (pivot depth))) := by
  let oldCoordinate := lineCoordinate .even depth (pivot depth)
  have hodd : oldCoordinate % 2 = 1 := by
    dsimp [oldCoordinate]
    rw [even_pivot_coordinate]
    omega
  have hblock : (oldCoordinate / 2) % 2 = 0 := by
    simpa [oldCoordinate] using pivot_line_block_even .even depth
  have vertical := verticalProjectionAt_of_alignedChecks row hodd (by decide)
    (fun blockX => boundedRouteClasses.1 _ (by
      have hmem := refinedGrid_mem_rowChildren .even depth grid
        blockX (oldCoordinate / 2)
      have hparity : parityOffset (oldCoordinate / 2) = 0 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have horizontal := horizontalProjectionAt_of_alignedChecks column hodd (by decide)
    (fun blockY => boundedRouteClasses.2.2.1 _ (by
      have hmem := refinedGrid_mem_columnChildren .even depth grid
        (oldCoordinate / 2) blockY
      have hparity : parityOffset (oldCoordinate / 2) = 0 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have hcoordinate :
      lineCoordinate .even (depth + 1) (extraChild (pivot depth)) =
        8 * (oldCoordinate / 2) + 2 := by
    dsimp [oldCoordinate]
    rw [even_extra_coordinate, even_pivot_coordinate]
    omega
  constructor
  · rw [hcoordinate]
    simpa [refinedGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [refinedGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- Every ordinary odd-phase main child projects in an arbitrary coarse grid. -/
theorem oddMainChildStep
    (depth : Nat) (grid : Nat → Nat → Index) {offset : Nat}
    (hodd : offset % 2 = 1)
    (row : LiveRowCertificate (refinedGrid .odd depth grid)
      (west .odd depth) (east .odd depth)
      (west .odd depth) (east .odd depth)
      (lineCoordinate .odd depth offset))
    (column : LiveColumnCertificate (refinedGrid .odd depth grid)
      (west .odd depth) (east .odd depth)
      (west .odd depth) (east .odd depth)
      (lineCoordinate .odd depth offset)) :
    LiveRowCertificate (refinedGrid .odd (depth + 1) grid)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (mainChild offset)) ∧
      LiveColumnCertificate (refinedGrid .odd (depth + 1) grid)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (mainChild offset)) := by
  let oldCoordinate := lineCoordinate .odd depth offset
  have hcoordinateOdd : oldCoordinate % 2 = 1 := by
    dsimp [oldCoordinate]
    rw [lineCoordinate_odd]
    omega
  have hblock : (oldCoordinate / 2) % 2 = 1 := by
    dsimp [oldCoordinate]
    rw [lineCoordinate_odd]
    omega
  have vertical := verticalProjectionAt_of_alignedChecks row hcoordinateOdd (by decide)
    (fun blockX => boundedRouteClasses.2.1 _ (by
      have hmem := refinedGrid_mem_rowChildren .odd depth grid
        blockX (oldCoordinate / 2)
      have hparity : parityOffset (oldCoordinate / 2) = 1 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have horizontal := horizontalProjectionAt_of_alignedChecks column
    hcoordinateOdd (by decide)
    (fun blockY => boundedRouteClasses.2.2.2 _ (by
      have hmem := refinedGrid_mem_columnChildren .odd depth grid
        (oldCoordinate / 2) blockY
      have hparity : parityOffset (oldCoordinate / 2) = 1 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have heven : ¬ offset % 2 = 0 := by omega
  have hcoordinate :
      lineCoordinate .odd (depth + 1) (mainChild offset) =
        8 * (oldCoordinate / 2) + 7 := by
    dsimp [oldCoordinate]
    simp only [mainChild, heven, if_false]
    rw [lineCoordinate_odd, lineCoordinate_odd, pow_succ]
    omega
  constructor
  · rw [hcoordinate]
    simpa [refinedGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [refinedGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

end SparseFreeLinePlaneLocalStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
