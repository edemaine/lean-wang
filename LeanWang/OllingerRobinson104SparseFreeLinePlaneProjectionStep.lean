/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLinePlaneOddExtraStep
import LeanWang.OllingerRobinson104SparseFreeLinePlaneEvenExtraCreatedStep

/-! Assembly of the sparse free-line recurrence in arbitrary coarse grids. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneProjectionStep

open RedCycles RedShadeGraphRefinement ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence BorderCoverageOffsets SparseFreeLineOffsets
  SparseFreeLineRecurrence SparseFreeLineLocalStates
  SparseFreeLineLocalProjection SparseFreeLineLocalRecurrence
  SparseFreeLinePlaneBase

set_option maxRecDepth 20000

/-- The ordinary odd retained offset in the even phase is locally projected. -/
theorem evenOddMainChildStep
    (depth : Nat) (grid : Nat → Nat → Index) {offset : Nat}
    (hmod : offset % 4 = 3)
    (row : LiveRowCertificate (refinedGrid .even (depth + 1) grid)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (lineCoordinate .even (depth + 1) offset))
    (column : LiveColumnCertificate (refinedGrid .even (depth + 1) grid)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (lineCoordinate .even (depth + 1) offset)) :
    LiveRowCertificate (refinedGrid .even (depth + 2) grid)
        (west .even (depth + 2)) (east .even (depth + 2))
        (west .even (depth + 2)) (east .even (depth + 2))
        (lineCoordinate .even (depth + 2) (mainChild offset)) ∧
      LiveColumnCertificate (refinedGrid .even (depth + 2) grid)
        (west .even (depth + 2)) (east .even (depth + 2))
        (west .even (depth + 2)) (east .even (depth + 2))
        (lineCoordinate .even (depth + 2) (mainChild offset)) := by
  have hcoordinate := even_mainChild_coordinate (depth + 1) offset
  have hrowmod := SparseFreeLineEvenOddLocalStep.coordinate_even
    (depth := depth) hmod
  have hhalf := SparseFreeLineEvenOddLocalStep.coordinate_half_even
    (depth := depth) hmod
  have verticalChecks : ∀ blockX,
      verticalCheck 0 0
        (refinedGrid .even (depth + 1) grid blockX
          (lineCoordinate .even (depth + 1) offset / 2)) = true := by
    intro blockX
    have hparity : parityOffset
        (lineCoordinate .even (depth + 1) offset / 2) = 0 := by
      apply Fin.ext
      simpa [parityOffset] using hhalf
    have hmem := SparseFreeLinePlaneLocalStep.refinedGrid_mem_rowChildren
      .even (depth + 1) grid blockX
      (lineCoordinate .even (depth + 1) offset / 2)
    rw [hparity] at hmem
    exact lowerRow_sparse_zero _ hmem
  have horizontalChecks : ∀ blockY,
      horizontalCheck 0 0
        (refinedGrid .even (depth + 1) grid
          (lineCoordinate .even (depth + 1) offset / 2) blockY) = true := by
    intro blockY
    have hparity : parityOffset
        (lineCoordinate .even (depth + 1) offset / 2) = 0 := by
      apply Fin.ext
      simpa [parityOffset] using hhalf
    have hmem := SparseFreeLinePlaneLocalStep.refinedGrid_mem_columnChildren
      .even (depth + 1) grid
      (lineCoordinate .even (depth + 1) offset / 2) blockY
    rw [hparity] at hmem
    exact leftColumn_sparse_zero _ hmem
  have vertical := verticalProjectionAt_of_checks row (by
    simpa [hrowmod] using verticalChecks)
  have horizontal := horizontalProjectionAt_of_checks column (by
    simpa [hrowmod] using horizontalChecks)
  constructor
  · rw [hcoordinate]
    simpa [SparseFreeLinePlaneLocalStep.refinedGrid_succ, west_succ,
      east_succ, Nat.add_assoc] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [SparseFreeLinePlaneLocalStep.refinedGrid_succ, west_succ,
      east_succ, Nat.add_assoc] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

theorem evenOddMainChild_of_pattern
    (depth : Nat) (grid : Nat → Nat → Index) {offset : Nat}
    (hold : offset ∈ offsets depth) (hodd : offset % 2 = 1)
    (rows : ∀ oldOffset ∈ offsets depth,
      LiveRowCertificate (refinedGrid .even depth grid)
        (west .even depth) (east .even depth)
        (west .even depth) (east .even depth)
        (lineCoordinate .even depth oldOffset))
    (columns : ∀ oldOffset ∈ offsets depth,
      LiveColumnCertificate (refinedGrid .even depth grid)
        (west .even depth) (east .even depth)
        (west .even depth) (east .even depth)
        (lineCoordinate .even depth oldOffset)) :
    LiveRowCertificate (refinedGrid .even (depth + 1) grid)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) (mainChild offset)) ∧
      LiveColumnCertificate (refinedGrid .even (depth + 1) grid)
        (west .even (depth + 1)) (east .even (depth + 1))
        (west .even (depth + 1)) (east .even (depth + 1))
        (lineCoordinate .even (depth + 1) (mainChild offset)) := by
  cases depth with
  | zero =>
      simp only [offsets_zero, List.mem_singleton] at hold
      subst offset
      norm_num at hodd
  | succ depth =>
      rcases odd_mem_offsets_succ_cases depth hold hodd with hmod | hextra
      · exact evenOddMainChildStep depth grid hmod
          (rows offset hold) (columns offset hold)
      · subst offset
        simpa [Nat.add_assoc] using
          SparseFreeLinePlaneEvenExtraCreatedStep.certificates
            depth grid rows columns

theorem childStep
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (holds : GridGraphHolds phase depth grid)
    {offset child : Nat} (hold : offset ∈ offsets depth)
    (hchild : child ∈ children offset) :
    LiveRowCertificate (refinedGrid phase (depth + 1) grid)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) child) ∧
      LiveColumnCertificate (refinedGrid phase (depth + 1) grid)
        (west phase (depth + 1)) (east phase (depth + 1))
        (west phase (depth + 1)) (east phase (depth + 1))
        (lineCoordinate phase (depth + 1) child) := by
  rcases mem_children_cases hchild with hmain | ⟨heven, hextra⟩
  · subst child
    by_cases hoffsetEven : offset % 2 = 0
    · exact SparseFreeLinePlaneLocalStep.evenMainChildStep phase depth grid
        hold hoffsetEven (holds.1 offset hold) (holds.2 offset hold)
    · have hoffsetOdd : offset % 2 = 1 := by omega
      cases phase
      · exact evenOddMainChild_of_pattern depth grid hold hoffsetOdd
          holds.1 holds.2
      · exact SparseFreeLinePlaneLocalStep.oddMainChildStep depth grid
          hoffsetOdd (holds.1 offset hold) (holds.2 offset hold)
  · subst child
    have hpivot := even_offset_eq_pivot depth hold heven
    subst offset
    cases phase
    · exact SparseFreeLinePlaneLocalStep.evenPivotExtraStep depth grid
        (holds.1 (pivot depth) (pivot_mem_offsets depth))
        (holds.2 (pivot depth) (pivot_mem_offsets depth))
    · exact SparseFreeLinePlaneOddExtraStep.oddExtraCertificates depth grid

/-- All sparse row and column certificates advance together. -/
theorem graphHolds_succ {phase : Phase} {depth : Nat}
    {grid : Nat → Nat → Index} (holds : GridGraphHolds phase depth grid) :
    GridGraphHolds phase (depth + 1) grid := by
  constructor
  · intro child hchild
    rcases mem_offsets_succ_cases depth hchild with
      ⟨offset, hold, childOf⟩
    exact (childStep phase depth grid holds hold childOf).1
  · intro child hchild
    rcases mem_offsets_succ_cases depth hchild with
      ⟨offset, hold, childOf⟩
    exact (childStep phase depth grid holds hold childOf).2

theorem graphHolds_from (phase : Phase) (grid : Nat → Nat → Index)
    (baseDepth : Nat) (base : GridGraphHolds phase baseDepth grid) :
    ∀ extra, GridGraphHolds phase (baseDepth + extra) grid := by
  intro extra
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [show baseDepth + (extra + 1) = (baseDepth + extra) + 1 by omega]
      exact graphHolds_succ ih

/-- Arbitrarily deep sparse free-line graphs exist in every coarse grid. -/
theorem graphHolds_unbounded (grid : Nat → Nat → Index) (size : Nat) :
    GridGraphHolds .even (1 + size) grid ∧ GridGraphHolds .odd size grid := by
  constructor
  · exact graphHolds_from .even grid 1 (SparseFreeLinePlaneBase.even_one grid) size
  · simpa using graphHolds_from .odd grid 0
      (SparseFreeLinePlaneBase.odd_zero grid) size

end SparseFreeLinePlaneProjectionStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
