/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBase
import LeanWang.OllingerRobinson104ShadedFreeLineOddBase
import LeanWang.OllingerRobinson104ShadedFreeLineRecurrence
import LeanWang.OllingerRobinson104SparseFreeLineOffsets

/-!
# Sparse free-line bases in arbitrary coarse grids

Unlike the constant-parent recurrence, this invariant is stated directly on
an arbitrary coarse index grid.  Its checked even and odd bases are obtained
by transporting the finite bounded searches into the southwest coarse block.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneBase

open RedCycles ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence SparseFreeLineOffsets

set_option maxRecDepth 20000

def refinedGrid (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  iterateRefine (refinementDepth phase depth) grid

/-- Sparse live certificates in an arbitrary refined coarse grid. -/
def GridGraphHolds (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) : Prop :=
  (∀ offset ∈ offsets depth,
    LiveRowCertificate (refinedGrid phase depth grid)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset)) ∧
  (∀ offset ∈ offsets depth,
    LiveColumnCertificate (refinedGrid phase depth grid)
      (west phase depth) (east phase depth)
      (west phase depth) (east phase depth)
      (lineCoordinate phase depth offset))

theorem shiftGrid_zero (grid : Nat → Nat → Index) :
    RefinementTranslation.shiftGrid grid 0 0 = grid := by
  funext x y
  simp [RefinementTranslation.shiftGrid]

/-- The checked even base works in every coarse grid. -/
theorem even_one (grid : Nat → Nat → Index) :
    GridGraphHolds .even 1 grid := by
  constructor
  · intro offset hoffset
    have hfree := offsets_mem_freeOffsets 1 offset hoffset
    have certificate := ShadedFreeLineGraphBase.liveRowCertificate_shift
      grid 0 0 (parent := grid 0 0) rfl hfree
    rw [shiftGrid_zero] at certificate
    simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, BorderCoverageOffsets.lineCoordinate_even] using certificate
  · intro offset hoffset
    have hfree := offsets_mem_freeOffsets 1 offset hoffset
    have certificate := ShadedFreeLineGraphBase.liveColumnCertificate_shift
      grid 0 0 (parent := grid 0 0) rfl hfree
    rw [shiftGrid_zero] at certificate
    simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, BorderCoverageOffsets.lineCoordinate_even] using certificate

/-- The checked odd base works in every coarse grid. -/
theorem odd_zero (grid : Nat → Nat → Index) :
    GridGraphHolds .odd 0 grid := by
  constructor
  · intro offset hoffset
    have hfree := offsets_mem_freeOffsets 0 offset hoffset
    have certificate := ShadedFreeLineOddBase.liveRowCertificate_shift
      grid 0 0 (parent := grid 0 0) rfl hfree
    rw [shiftGrid_zero] at certificate
    simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, BorderCoverageOffsets.lineCoordinate_odd] using certificate
  · intro offset hoffset
    have hfree := offsets_mem_freeOffsets 0 offset hoffset
    have certificate := ShadedFreeLineOddBase.liveColumnCertificate_shift
      grid 0 0 (parent := grid 0 0) rfl hfree
    rw [shiftGrid_zero] at certificate
    simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, BorderCoverageOffsets.lineCoordinate_odd] using certificate

end SparseFreeLinePlaneBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
