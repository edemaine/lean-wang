/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentFullAudit
import LeanWang.OllingerRobinson104PairCoverSeamCreatedAdjacentTransport

/-! Transport the full adjacent created-boundary certificates globally. -/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamCreatedAdjacentFullTransport

open RedCycles RedShadeCycles RedShadeGraph PairCoverSeamPathSearch
  PairCoverSeamShadePaths
  PairCoverSeamCreatedAdjacentAudit
  PairCoverSeamCreatedAdjacentFullAudit
  PairCoverSeamCreatedAdjacentTransport Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A created boundary in the lower cell reaches every query row in the upper
cell of the canonical adjacent window. -/
theorem verticalLower
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (hpair : canonicalPair
      (grid blockX blockY, grid blockX (blockY + 1)) ∈ verticalPairs)
    {column boundary row : Nat}
    (hcolumn : column ∈ List.range 8)
    (hboundary : boundary ∈ createdCoordinates)
    (hrow : row ∈ upperQueries)
    (hinterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid)
        (8 * blockX + column) (8 * blockY + boundary))
      (quadrantAt (8 * blockX + column) (8 * blockY + boundary)) =
        some .north) :
    VerticalSeamPath (iterateRefine 2 grid)
      (4 * blockX) (4 * blockX + 4)
      (8 * blockX + column) (8 * blockY + row)
      (8 * blockY + boundary) := by
  have hcolumn' : column < 8 := by simpa using hcolumn
  have hboundary' : boundary < 8 := by
    have hcases := hboundary
    simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
      or_false] at hcases
    omega
  have hrow' : row < 16 := by
    simp only [upperQueries, List.mem_map] at hrow
    rcases hrow with ⟨offset, hlocal, rfl⟩
    simp only [List.mem_range] at hlocal
    omega
  have localInterior : Signals.horizontalInterior?
      (componentAt
        (iterateRefine 2
          (verticalGrid (canonicalPair
            (grid blockX blockY, grid blockX (blockY + 1)))))
        column boundary)
      (quadrantAt column boundary) = some .north := by
    rw [horizontalInterior_verticalWindow grid blockX blockY
      column boundary hcolumn' (by omega)]
    exact hinterior
  have localPath :=
    (PairCoverSeamCreatedAdjacentFullAudit.verticalPairPaths hpair).lower
      hcolumn hboundary hrow localInterior
  simpa using rectangularVerticalSeamPath_verticalWindow
    grid blockX blockY hcolumn' hrow' (by omega) localPath

/-- A created boundary in the upper cell reaches every query row in the lower
cell of the canonical adjacent window. -/
theorem verticalUpper
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (hpair : canonicalPair
      (grid blockX blockY, grid blockX (blockY + 1)) ∈ verticalPairs)
    {column boundary row : Nat}
    (hcolumn : column ∈ List.range 8)
    (hboundary : boundary ∈ createdCoordinates)
    (hrow : row ∈ lowerQueries)
    (hinterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid)
        (8 * blockX + column) (8 * blockY + (8 + boundary)))
      (quadrantAt (8 * blockX + column) (8 * blockY + (8 + boundary))) =
        some .south) :
    VerticalSeamPath (iterateRefine 2 grid)
      (4 * blockX) (4 * blockX + 4)
      (8 * blockX + column) (8 * blockY + row)
      (8 * blockY + (8 + boundary)) := by
  have hcolumn' : column < 8 := by simpa using hcolumn
  have hboundary' : boundary < 8 := by
    have hcases := hboundary
    simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
      or_false] at hcases
    omega
  have hrow' : row < 8 := by simpa [lowerQueries] using hrow
  have localInterior : Signals.horizontalInterior?
      (componentAt
        (iterateRefine 2
          (verticalGrid (canonicalPair
            (grid blockX blockY, grid blockX (blockY + 1)))))
        column (8 + boundary))
      (quadrantAt column (8 + boundary)) = some .south := by
    rw [horizontalInterior_verticalWindow grid blockX blockY
      column (8 + boundary) hcolumn' (by omega)]
    exact hinterior
  have localPath :=
    (PairCoverSeamCreatedAdjacentFullAudit.verticalPairPaths hpair).upper
      hcolumn hboundary hrow localInterior
  simpa using rectangularVerticalSeamPath_verticalWindow
    grid blockX blockY hcolumn' (by omega) (by omega) localPath

/-- A created boundary in the left cell reaches every query column in the
right cell of the canonical adjacent window. -/
theorem horizontalLeft
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (hpair : canonicalPair
      (grid blockX blockY, grid (blockX + 1) blockY) ∈ horizontalPairs)
    {row boundary column : Nat}
    (hrow : row ∈ List.range 8)
    (hboundary : boundary ∈ createdCoordinates)
    (hcolumn : column ∈ rightQueries)
    (hinterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid)
        (8 * blockX + boundary) (8 * blockY + row))
      (quadrantAt (8 * blockX + boundary) (8 * blockY + row)) =
        some .east) :
    HorizontalSeamPath (iterateRefine 2 grid)
      (4 * blockY) (4 * blockY + 4)
      (8 * blockY + row) (8 * blockX + column)
      (8 * blockX + boundary) := by
  have hrow' : row < 8 := by simpa using hrow
  have hboundary' : boundary < 8 := by
    have hcases := hboundary
    simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
      or_false] at hcases
    omega
  have hcolumn' : column < 16 := by
    simp only [rightQueries, List.mem_map] at hcolumn
    rcases hcolumn with ⟨offset, hlocal, rfl⟩
    simp only [List.mem_range] at hlocal
    omega
  have localInterior : Signals.verticalInterior?
      (componentAt
        (iterateRefine 2
          (horizontalGrid (canonicalPair
            (grid blockX blockY, grid (blockX + 1) blockY))))
        boundary row)
      (quadrantAt boundary row) = some .east := by
    rw [verticalInterior_horizontalWindow grid blockX blockY
      boundary row (by omega) hrow']
    exact hinterior
  have localPath :=
    (PairCoverSeamCreatedAdjacentFullAudit.horizontalPairPaths hpair).left
      hrow hboundary hcolumn localInterior
  simpa using rectangularHorizontalSeamPath_horizontalWindow
    grid blockX blockY hrow' hcolumn' (by omega) localPath

/-- A created boundary in the right cell reaches every query column in the
left cell of the canonical adjacent window. -/
theorem horizontalRight
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    (hpair : canonicalPair
      (grid blockX blockY, grid (blockX + 1) blockY) ∈ horizontalPairs)
    {row boundary column : Nat}
    (hrow : row ∈ List.range 8)
    (hboundary : boundary ∈ createdCoordinates)
    (hcolumn : column ∈ leftQueries)
    (hinterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid)
        (8 * blockX + (8 + boundary)) (8 * blockY + row))
      (quadrantAt (8 * blockX + (8 + boundary)) (8 * blockY + row)) =
        some .west) :
    HorizontalSeamPath (iterateRefine 2 grid)
      (4 * blockY) (4 * blockY + 4)
      (8 * blockY + row) (8 * blockX + column)
      (8 * blockX + (8 + boundary)) := by
  have hrow' : row < 8 := by simpa using hrow
  have hboundary' : boundary < 8 := by
    have hcases := hboundary
    simp only [createdCoordinates, List.mem_cons, List.not_mem_nil,
      or_false] at hcases
    omega
  have hcolumn' : column < 8 := by simpa [leftQueries] using hcolumn
  have localInterior : Signals.verticalInterior?
      (componentAt
        (iterateRefine 2
          (horizontalGrid (canonicalPair
            (grid blockX blockY, grid (blockX + 1) blockY))))
        (8 + boundary) row)
      (quadrantAt (8 + boundary) row) = some .west := by
    rw [verticalInterior_horizontalWindow grid blockX blockY
      (8 + boundary) row (by omega) hrow']
    exact hinterior
  have localPath :=
    (PairCoverSeamCreatedAdjacentFullAudit.horizontalPairPaths hpair).right
      hrow hboundary hcolumn localInterior
  simpa using rectangularHorizontalSeamPath_horizontalWindow
    grid blockX blockY hrow' (by omega) (by omega) localPath

end PairCoverSeamCreatedAdjacentFullTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
