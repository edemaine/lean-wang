/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineLocalRecurrence

/-!
# The local even-phase odd-offset recurrence

At positive depth, retained odd offsets congruent to three modulo four lie in
the lower child row and left child column. Their main child is therefore the
literal sparse projection supplied by the finite local-state audit.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineEvenOddLocalStep

open RedCycles RedShadeGraphRefinement ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement ShadedFreeLineRecurrence
  BorderCoverageOffsets SparseFreeLineOffsets SparseFreeLineRecurrence
  SparseFreeLineLocalStates SparseFreeLineLocalProjection
  SparseFreeLineLocalRecurrence

set_option maxRecDepth 20000

theorem coordinate_mod_four {depth offset : Nat} (hmod : offset % 4 = 3) :
    lineCoordinate .even (depth + 1) offset % 4 = 0 := by
  rw [lineCoordinate_even, pow_succ]
  omega

theorem coordinate_even {depth offset : Nat} (hmod : offset % 4 = 3) :
    lineCoordinate .even (depth + 1) offset % 2 = 0 := by
  have hfour := coordinate_mod_four (depth := depth) hmod
  omega

theorem coordinate_half_even {depth offset : Nat} (hmod : offset % 4 = 3) :
    (lineCoordinate .even (depth + 1) offset / 2) % 2 = 0 := by
  have hfour := coordinate_mod_four (depth := depth) hmod
  omega

theorem verticalChecks (depth : Nat) (parent : Index) {offset : Nat}
    (hmod : offset % 4 = 3) :
    ∀ blockX,
      verticalCheck 0 0
        (localGrid .even (depth + 1) parent blockX
          (lineCoordinate .even (depth + 1) offset / 2)) = true := by
  intro blockX
  have hhalf := coordinate_half_even (depth := depth) hmod
  have hparity :
      parityOffset (lineCoordinate .even (depth + 1) offset / 2) = 0 := by
    apply Fin.ext
    simpa [parityOffset] using hhalf
  have hmem := localGrid_mem_rowChildren .even (depth + 1) parent blockX
    (lineCoordinate .even (depth + 1) offset / 2)
  rw [hparity] at hmem
  exact lowerRow_sparse_zero _ hmem

theorem horizontalChecks (depth : Nat) (parent : Index) {offset : Nat}
    (hmod : offset % 4 = 3) :
    ∀ blockY,
      horizontalCheck 0 0
        (localGrid .even (depth + 1) parent
          (lineCoordinate .even (depth + 1) offset / 2) blockY) = true := by
  intro blockY
  have hhalf := coordinate_half_even (depth := depth) hmod
  have hparity :
      parityOffset (lineCoordinate .even (depth + 1) offset / 2) = 0 := by
    apply Fin.ext
    simpa [parityOffset] using hhalf
  have hmem := localGrid_mem_columnChildren .even (depth + 1) parent
    (lineCoordinate .even (depth + 1) offset / 2) blockY
  rw [hparity] at hmem
  exact leftColumn_sparse_zero _ hmem

/-- The ordinary odd retained offset has a locally projected main child. -/
theorem mainChildStep (depth : Nat) (parent : Index) {offset : Nat}
    (hmod : offset % 4 = 3)
    (row : LiveRowCertificate (localGrid .even (depth + 1) parent)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (lineCoordinate .even (depth + 1) offset))
    (column : LiveColumnCertificate (localGrid .even (depth + 1) parent)
      (west .even (depth + 1)) (east .even (depth + 1))
      (west .even (depth + 1)) (east .even (depth + 1))
      (lineCoordinate .even (depth + 1) offset)) :
    LiveRowCertificate (localGrid .even (depth + 2) parent)
        (west .even (depth + 2)) (east .even (depth + 2))
        (west .even (depth + 2)) (east .even (depth + 2))
        (lineCoordinate .even (depth + 2) (mainChild offset)) ∧
      LiveColumnCertificate (localGrid .even (depth + 2) parent)
        (west .even (depth + 2)) (east .even (depth + 2))
        (west .even (depth + 2)) (east .even (depth + 2))
        (lineCoordinate .even (depth + 2) (mainChild offset)) := by
  have hcoordinate := even_mainChild_coordinate (depth + 1) offset
  have hrowmod := coordinate_even (depth := depth) hmod
  have vertical := verticalProjectionAt_of_checks row (by
    simpa [hrowmod] using verticalChecks depth parent hmod)
  have horizontal := horizontalProjectionAt_of_checks column (by
    simpa [hrowmod] using horizontalChecks depth parent hmod)
  constructor
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ, Nat.add_assoc] using
      liveRowCertificate_of_verticalProjectionAt vertical
  · rw [hcoordinate]
    simpa [localGrid_succ, west_succ, east_succ, Nat.add_assoc] using
      liveColumnCertificate_of_horizontalProjectionAt horizontal

end SparseFreeLineEvenOddLocalStep
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
