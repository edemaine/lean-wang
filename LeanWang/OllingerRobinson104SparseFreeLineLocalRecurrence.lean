/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineLocalProjection
import LeanWang.OllingerRobinson104SparseFreeLineRecurrence

/-!
# Local branches of the sparse free-line recurrence

The unique even offset always lies in the lower row and column child classes.
Its main child is therefore the literal sparse projection in both recurrence
phases.  This module discharges that branch using the finite local-state
certificates.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineLocalRecurrence

open RedCycles RedShadeGraphRefinement ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement ShadedFreeLineRecurrence
  BorderCoverageOffsets SparseFreeLineOffsets SparseFreeLineRecurrence
  SparseFreeLineLocalStates SparseFreeLineLocalProjection

set_option maxRecDepth 20000

theorem localGrid_mem_rowChildren (phase : Phase) (depth : Nat)
    (parent : Index) (x y : Nat) :
    localGrid phase depth parent x y ∈ rowChildren (parityOffset y) := by
  cases phase
  · simpa [localGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_rowChildren (2 * depth + 1)
        (fun _ _ => parent) x y
  · simpa [localGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_rowChildren (2 * depth + 2)
        (fun _ _ => parent) x y

theorem localGrid_mem_columnChildren (phase : Phase) (depth : Nat)
    (parent : Index) (x y : Nat) :
    localGrid phase depth parent x y ∈ columnChildren (parityOffset x) := by
  cases phase
  · simpa [localGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_columnChildren (2 * depth + 1)
        (fun _ _ => parent) x y
  · simpa [localGrid, refinementDepth, Phase.extra] using
      iterateRefine_succ_mem_columnChildren (2 * depth + 2)
        (fun _ _ => parent) x y

theorem pivot_line_block_even (phase : Phase) (depth : Nat) :
    (lineCoordinate phase depth (pivot depth) / 2) % 2 = 0 := by
  cases phase
  · rw [even_pivot_coordinate]
    omega
  · rw [odd_pivot_coordinate]
    omega

theorem verticalChecks_pivot (phase : Phase) (depth : Nat) (parent : Index) :
    ∀ blockX,
      verticalCheck
        (lineCoordinate phase depth (pivot depth) % 2)
        (lineCoordinate phase depth (pivot depth) % 2)
        (localGrid phase depth parent blockX
          (lineCoordinate phase depth (pivot depth) / 2)) = true := by
  intro blockX
  let row := lineCoordinate phase depth (pivot depth)
  have hblock := pivot_line_block_even phase depth
  have hparity : parityOffset (row / 2) = 0 := by
    apply Fin.ext
    simpa [row, parityOffset] using hblock
  have hmem := localGrid_mem_rowChildren phase depth parent blockX (row / 2)
  rw [hparity] at hmem
  have hmod : row % 2 = 0 ∨ row % 2 = 1 := by
    have := Nat.mod_lt row (by decide : 0 < 2)
    omega
  rcases hmod with hzero | hone
  · simpa [row, hzero] using lowerRow_sparse_zero _ hmem
  · simpa [row, hone] using lowerRow_sparse_one _ hmem

theorem horizontalChecks_pivot (phase : Phase) (depth : Nat) (parent : Index) :
    ∀ blockY,
      horizontalCheck
        (lineCoordinate phase depth (pivot depth) % 2)
        (lineCoordinate phase depth (pivot depth) % 2)
        (localGrid phase depth parent
          (lineCoordinate phase depth (pivot depth) / 2) blockY) = true := by
  intro blockY
  let column := lineCoordinate phase depth (pivot depth)
  have hblock := pivot_line_block_even phase depth
  have hparity : parityOffset (column / 2) = 0 := by
    apply Fin.ext
    simpa [column, parityOffset] using hblock
  have hmem := localGrid_mem_columnChildren phase depth parent (column / 2) blockY
  rw [hparity] at hmem
  have hmod : column % 2 = 0 ∨ column % 2 = 1 := by
    have := Nat.mod_lt column (by decide : 0 < 2)
    omega
  rcases hmod with hzero | hone
  · simpa [column, hzero] using leftColumn_sparse_zero _ hmem
  · simpa [column, hone] using leftColumn_sparse_one _ hmem

/-- The main child of the unique even offset is locally projected in both phases. -/
theorem evenMainChildStep :
    ∀ phase depth parent offset,
      offset ∈ offsets depth →
      offset % 2 = 0 →
      LiveRowCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset) →
      LiveColumnCertificate (localGrid phase depth parent)
        (west phase depth) (east phase depth)
        (west phase depth) (east phase depth)
        (lineCoordinate phase depth offset) →
      LiveRowCertificate (localGrid phase (depth + 1) parent)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) (mainChild offset)) ∧
      LiveColumnCertificate (localGrid phase (depth + 1) parent)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) (mainChild offset)) := by
  intro phase depth parent offset hold heven row column
  have hoffset := even_offset_eq_pivot depth hold heven
  subst offset
  have hcoordinate : lineCoordinate phase (depth + 1) (mainChild (pivot depth)) =
      sparseCoordinate (lineCoordinate phase depth (pivot depth)) := by
    simpa [mainChild, pivot_even] using
      lineCoordinate_evenOffset_sparse phase depth (pivot depth) (pivot_even depth)
  have vertical := verticalProjectionAt_of_checks row
    (verticalChecks_pivot phase depth parent)
  have horizontal := horizontalProjectionAt_of_checks column
    (horizontalChecks_pivot phase depth parent)
  constructor
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- In the even phase, the pivot's extra child is the certified near line. -/
theorem evenPivotExtraStep :
    ∀ depth parent,
      LiveRowCertificate (localGrid .even depth parent)
        (west .even depth) (east .even depth)
        (west .even depth) (east .even depth)
        (lineCoordinate .even depth (pivot depth)) →
      LiveColumnCertificate (localGrid .even depth parent)
        (west .even depth) (east .even depth)
        (west .even depth) (east .even depth)
        (lineCoordinate .even depth (pivot depth)) →
      LiveRowCertificate (localGrid .even (depth + 1) parent)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) (extraChild (pivot depth))) ∧
      LiveColumnCertificate (localGrid .even (depth + 1) parent)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) (extraChild (pivot depth))) := by
  intro depth parent row column
  let oldCoordinate := lineCoordinate .even depth (pivot depth)
  have hodd : oldCoordinate % 2 = 1 := by
    dsimp [oldCoordinate]
    rw [even_pivot_coordinate]
    omega
  have hblock : (oldCoordinate / 2) % 2 = 0 := by
    simpa [oldCoordinate] using pivot_line_block_even .even depth
  have vertical := verticalProjectionAt_of_alignedChecks row hodd (by decide)
    (fun blockX => boundedRouteClasses.1 _ (by
      have hmem := localGrid_mem_rowChildren .even depth parent
        blockX (oldCoordinate / 2)
      have hparity : parityOffset (oldCoordinate / 2) = 0 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have horizontal := horizontalProjectionAt_of_alignedChecks column hodd (by decide)
    (fun blockY => boundedRouteClasses.2.2.1 _ (by
      have hmem := localGrid_mem_columnChildren .even depth parent
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
    simpa [localGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

/-- In the odd phase, every odd offset's main child is the certified exit line. -/
theorem oddMainChildStep_of_odd :
    ∀ depth parent offset,
      offset ∈ offsets depth →
      offset % 2 = 1 →
      LiveRowCertificate (localGrid .odd depth parent)
        (west .odd depth) (east .odd depth)
        (west .odd depth) (east .odd depth)
        (lineCoordinate .odd depth offset) →
      LiveColumnCertificate (localGrid .odd depth parent)
        (west .odd depth) (east .odd depth)
        (west .odd depth) (east .odd depth)
        (lineCoordinate .odd depth offset) →
      LiveRowCertificate (localGrid .odd (depth + 1) parent)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (mainChild offset)) ∧
      LiveColumnCertificate (localGrid .odd (depth + 1) parent)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (lineCoordinate .odd (depth + 1) (mainChild offset)) := by
  intro depth parent offset hold hoffset row column
  let oldCoordinate := lineCoordinate .odd depth offset
  have hodd : oldCoordinate % 2 = 1 := by
    dsimp [oldCoordinate]
    rw [lineCoordinate_odd]
    omega
  have hblock : (oldCoordinate / 2) % 2 = 1 := by
    dsimp [oldCoordinate]
    rw [lineCoordinate_odd]
    omega
  have vertical := verticalProjectionAt_of_alignedChecks row hodd (by decide)
    (fun blockX => boundedRouteClasses.2.1 _ (by
      have hmem := localGrid_mem_rowChildren .odd depth parent
        blockX (oldCoordinate / 2)
      have hparity : parityOffset (oldCoordinate / 2) = 1 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have horizontal := horizontalProjectionAt_of_alignedChecks column hodd (by decide)
    (fun blockY => boundedRouteClasses.2.2.2 _ (by
      have hmem := localGrid_mem_columnChildren .odd depth parent
        (oldCoordinate / 2) blockY
      have hparity : parityOffset (oldCoordinate / 2) = 1 := by
        apply Fin.ext
        simpa [parityOffset] using hblock
      rw [hparity] at hmem
      exact hmem))
  have heven : ¬offset % 2 = 0 := by omega
  have hcoordinate :
      lineCoordinate .odd (depth + 1) (mainChild offset) =
        8 * (oldCoordinate / 2) + 7 := by
    dsimp [oldCoordinate]
    simp only [mainChild, heven, if_false]
    rw [lineCoordinate_odd, lineCoordinate_odd, pow_succ]
    omega
  constructor
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

end SparseFreeLineLocalRecurrence
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
