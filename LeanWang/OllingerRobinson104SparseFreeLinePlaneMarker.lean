/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineOddMarkerBase
import LeanWang.OllingerRobinson104SparseFreeLinePlaneProjectionStep
import LeanWang.OllingerRobinson104SparseFreeLineMarker

/-! Distinguished center-marker free lines in arbitrary-grid odd phases. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneMarker

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraphRefinement
  RedShadeGraphTranslation RefinementTranslation
  ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal

set_option maxRecDepth 100000

def oddMarkerCoordinate (depth : Nat) : Nat := 8 * 4 ^ depth

theorem oddMarkerCoordinate_zero : oddMarkerCoordinate 0 = 8 := by rfl

theorem oddMarkerCoordinate_succ (depth : Nat) :
    oddMarkerCoordinate (depth + 1) = 4 * oddMarkerCoordinate depth := by
  simp [oddMarkerCoordinate, pow_succ]
  omega

theorem baseRowCertificate (grid : Nat → Nat → Index) :
    LiveRowCertificate (refinedGrid .odd 0 grid) 2 6 2 6 8 := by
  have certificate := SparseFreeLineOddMarkerBase.liveRowCertificate_shift
    grid 0 0 (parent := grid 0 0) rfl
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at certificate
  simpa [refinedGrid, refinementDepth, Phase.extra] using certificate

theorem baseColumnCertificate (grid : Nat → Nat → Index) :
    LiveColumnCertificate (refinedGrid .odd 0 grid) 2 6 2 6 8 := by
  have certificate := SparseFreeLineOddMarkerBase.liveColumnCertificate_shift
    grid 0 0 (parent := grid 0 0) rfl
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at certificate
  simpa [refinedGrid, refinementDepth, Phase.extra] using certificate

set_option maxHeartbeats 1000000 in
-- Normalizing the two-refinement marker projection carries dependent paths.
theorem markerStep (depth : Nat) (grid : Nat → Nat → Index)
    (row : LiveRowCertificate (refinedGrid .odd depth grid)
      (west .odd depth) (east .odd depth) (west .odd depth) (east .odd depth)
      (oddMarkerCoordinate depth))
    (column : LiveColumnCertificate (refinedGrid .odd depth grid)
      (west .odd depth) (east .odd depth) (west .odd depth) (east .odd depth)
      (oddMarkerCoordinate depth)) :
    LiveRowCertificate (refinedGrid .odd (depth + 1) grid)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (oddMarkerCoordinate (depth + 1)) ∧
      LiveColumnCertificate (refinedGrid .odd (depth + 1) grid)
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (west .odd (depth + 1)) (east .odd (depth + 1))
        (oddMarkerCoordinate (depth + 1)) := by
  have heven : oddMarkerCoordinate depth % 2 = 0 := by
    have h : oddMarkerCoordinate depth = 2 * (4 * 4 ^ depth) := by
      dsimp [oddMarkerCoordinate]
      omega
    rw [h]
    simp
  have hhalf : (oddMarkerCoordinate depth / 2) % 2 = 0 := by
    have h : oddMarkerCoordinate depth = 2 * (4 * 4 ^ depth) := by
      dsimp [oddMarkerCoordinate]
      omega
    rw [h]
    omega
  have verticalChecks : ∀ blockX,
      SparseFreeLineLocalStates.verticalCheck 0 0
        (refinedGrid .odd depth grid blockX
          (oddMarkerCoordinate depth / 2)) = true := by
    intro blockX
    have hparity : parityOffset (oddMarkerCoordinate depth / 2) = 0 := by
      apply Fin.ext
      simpa [parityOffset] using hhalf
    have hmem := SparseFreeLinePlaneLocalStep.refinedGrid_mem_rowChildren
      .odd depth grid blockX (oddMarkerCoordinate depth / 2)
    rw [hparity] at hmem
    exact SparseFreeLineLocalStates.lowerRow_sparse_zero _ hmem
  have horizontalChecks : ∀ blockY,
      SparseFreeLineLocalStates.horizontalCheck 0 0
        (refinedGrid .odd depth grid
          (oddMarkerCoordinate depth / 2) blockY) = true := by
    intro blockY
    have hparity : parityOffset (oddMarkerCoordinate depth / 2) = 0 := by
      apply Fin.ext
      simpa [parityOffset] using hhalf
    have hmem := SparseFreeLinePlaneLocalStep.refinedGrid_mem_columnChildren
      .odd depth grid (oddMarkerCoordinate depth / 2) blockY
    rw [hparity] at hmem
    exact SparseFreeLineLocalStates.leftColumn_sparse_zero _ hmem
  have vertical := SparseFreeLineLocalProjection.verticalProjectionAt_of_checks
    row (by simpa [heven] using verticalChecks)
  have horizontal := SparseFreeLineLocalProjection.horizontalProjectionAt_of_checks
    column (by simpa [heven] using horizontalChecks)
  have hcoordinate : sparseCoordinate (oddMarkerCoordinate depth) =
      oddMarkerCoordinate (depth + 1) := by
    rw [oddMarkerCoordinate_succ]
    simp [sparseCoordinate, macroOrigin, localCoordinate, oddMarkerCoordinate]
    omega
  constructor
  · rw [← hcoordinate]
    simpa [SparseFreeLinePlaneLocalStep.refinedGrid_succ, west_succ,
      east_succ] using
      SparseFreeLineLocalProjection.liveRowCertificate_of_verticalProjectionAt
        vertical
  · rw [← hcoordinate]
    simpa [SparseFreeLinePlaneLocalStep.refinedGrid_succ, west_succ,
      east_succ] using
      SparseFreeLineLocalProjection.liveColumnCertificate_of_horizontalProjectionAt
        horizontal

theorem certificates (depth : Nat) (grid : Nat → Nat → Index) :
    LiveRowCertificate (refinedGrid .odd depth grid)
        (west .odd depth) (east .odd depth) (west .odd depth) (east .odd depth)
        (oddMarkerCoordinate depth) ∧
      LiveColumnCertificate (refinedGrid .odd depth grid)
        (west .odd depth) (east .odd depth) (west .odd depth) (east .odd depth)
        (oddMarkerCoordinate depth) := by
  induction depth with
  | zero => exact ⟨baseRowCertificate grid, baseColumnCertificate grid⟩
  | succ depth ih => exact markerStep depth grid ih.1 ih.2

set_option linter.style.nativeDecide false in
theorem baseMarkerQuarter_constant (parent : Index) :
    (ShadedFreeLineOddBase.localGrid parent 4 4, quadrantAt 8 8) ∈
      ShadedSignals.markerQuarters := by
  revert parent
  native_decide

theorem baseMarkerQuarter (grid : Nat → Nat → Index) :
    (refinedGrid .odd 0 grid 4 4, quadrantAt 8 8) ∈
      ShadedSignals.markerQuarters := by
  have hlocal := iterateRefine_shift_eq_constant 3 grid 0 0 4 4
    (by norm_num) (by norm_num)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  unfold refinedGrid
  simp only [refinementDepth, Phase.extra]
  rw [hlocal]
  simpa [refinementDepth, Phase.extra,
    ShadedFreeLineOddBase.localGrid] using baseMarkerQuarter_constant (grid 0 0)

theorem markerQuarter (depth : Nat) (grid : Nat → Nat → Index) :
    (refinedGrid .odd depth grid
        (4 * 4 ^ depth) (4 * 4 ^ depth), Quadrant.southwest) ∈
      ShadedSignals.markerQuarters := by
  induction depth with
  | zero =>
      simpa [quadrantAt, Quadrant.ofBits] using baseMarkerQuarter grid
  | succ depth ih =>
      rw [SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      change
        (refineIndexGrid (refineIndexGrid (refinedGrid .odd depth grid))
            (4 * 4 ^ (depth + 1)) (4 * 4 ^ (depth + 1)),
          Quadrant.southwest) ∈ ShadedSignals.markerQuarters
      rw [show 4 * 4 ^ (depth + 1) = 2 * (2 * (4 * 4 ^ depth)) by
        rw [pow_succ]
        omega]
      simp only [refineIndexGrid_even_even]
      exact SparseFreeLineMarker.markerSouthwest_refines _ ih

theorem markerAtCoordinate (depth : Nat) (grid : Nat → Nat → Index) :
    (refinedGrid .odd depth grid
        (oddMarkerCoordinate depth / 2) (oddMarkerCoordinate depth / 2),
      quadrantAt (oddMarkerCoordinate depth) (oddMarkerCoordinate depth)) ∈
      ShadedSignals.markerQuarters := by
  have hhalf : oddMarkerCoordinate depth / 2 = 4 * 4 ^ depth := by
    have h : oddMarkerCoordinate depth = 2 * (4 * 4 ^ depth) := by
      dsimp [oddMarkerCoordinate]
      omega
    rw [h]
    omega
  have hquadrant : quadrantAt (oddMarkerCoordinate depth)
      (oddMarkerCoordinate depth) = Quadrant.southwest := by
    have h : oddMarkerCoordinate depth = 2 * (4 * 4 ^ depth) := by
      dsimp [oddMarkerCoordinate]
      omega
    rw [h]
    simp [quadrantAt, Quadrant.ofBits]
  rw [hhalf, hquadrant]
  exact markerQuarter depth grid

theorem evenBaseCertificates (grid : Nat → Nat → Index) :
    LiveRowCertificate (refinedGrid .even 1 grid)
        (west .even 1) (east .even 1) (west .even 1) (east .even 1)
        (lineCoordinate .even 1 (SparseFreeLineMarker.markerOffset 1)) ∧
      LiveColumnCertificate (refinedGrid .even 1 grid)
        (west .even 1) (east .even 1) (west .even 1) (east .even 1)
        (lineCoordinate .even 1 (SparseFreeLineMarker.markerOffset 1)) := by
  have hmem : SparseFreeLineMarker.markerOffset 1 ∈
      ShadedFreeLineOffsets.freeOffsets 1 := by
    rw [SparseFreeLineMarker.markerOffset_one,
      ShadedFreeLineOffsets.freeOffsets_one]
    simp
  constructor
  · have certificate := ShadedFreeLineGraphBase.liveRowCertificate_shift
      grid 0 0 (parent := grid 0 0) rfl hmem
    rw [SparseFreeLinePlaneBase.shiftGrid_zero] at certificate
    simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, BorderCoverageOffsets.lineCoordinate_even] using certificate
  · have certificate := ShadedFreeLineGraphBase.liveColumnCertificate_shift
      grid 0 0 (parent := grid 0 0) rfl hmem
    rw [SparseFreeLinePlaneBase.shiftGrid_zero] at certificate
    simpa [refinedGrid, refinementDepth, Phase.extra, west, east, scale,
      Phase.factor, BorderCoverageOffsets.lineCoordinate_even] using certificate

theorem evenCertificates (extra : Nat) (grid : Nat → Nat → Index) :
    LiveRowCertificate (refinedGrid .even (extra + 1) grid)
        (west .even (extra + 1)) (east .even (extra + 1))
        (west .even (extra + 1)) (east .even (extra + 1))
        (lineCoordinate .even (extra + 1)
          (SparseFreeLineMarker.markerOffset (extra + 1))) ∧
      LiveColumnCertificate (refinedGrid .even (extra + 1) grid)
        (west .even (extra + 1)) (east .even (extra + 1))
        (west .even (extra + 1)) (east .even (extra + 1))
        (lineCoordinate .even (extra + 1)
          (SparseFreeLineMarker.markerOffset (extra + 1))) := by
  induction extra with
  | zero => simpa using evenBaseCertificates grid
  | succ extra ih =>
      have next := SparseFreeLinePlaneProjectionStep.evenOddMainChildStep
        extra grid (SparseFreeLineMarker.markerOffset_mod_four extra) ih.1 ih.2
      rw [SparseFreeLineMarker.mainChild_markerOffset extra] at next
      simpa [Nat.add_assoc] using next

theorem evenBaseMarkerQuarter (grid : Nat → Nat → Index) :
    (refinedGrid .even 1 grid 8 8, quadrantAt 16 16) ∈
      ShadedSignals.markerQuarters := by
  have hlocal := iterateRefine_shift_eq_constant 4 grid 0 0 8 8
    (by norm_num) (by norm_num)
  rw [SparseFreeLinePlaneBase.shiftGrid_zero] at hlocal
  unfold refinedGrid
  simp only [refinementDepth, Phase.extra]
  rw [hlocal]
  simpa [ShadedFreeLineGraphBase.localGrid] using
    ShadedFreeLineGraphBase.markerQuarter_at_sixteen (grid 0 0)

theorem evenMarkerIndex (extra : Nat) (grid : Nat → Nat → Index) :
    (refinedGrid .even (extra + 1) grid
        (2 * 4 ^ (extra + 1)) (2 * 4 ^ (extra + 1)),
      Quadrant.southwest) ∈ ShadedSignals.markerQuarters := by
  induction extra with
  | zero =>
      have hquadrant : quadrantAt 16 16 = Quadrant.southwest := by
        decide
      rw [← hquadrant]
      simpa using evenBaseMarkerQuarter grid
  | succ extra ih =>
      rw [show extra + 1 + 1 = (extra + 1) + 1 by omega,
        SparseFreeLinePlaneLocalStep.refinedGrid_succ]
      change
        (refineIndexGrid (refineIndexGrid (refinedGrid .even (extra + 1) grid))
            (2 * 4 ^ (extra + 2)) (2 * 4 ^ (extra + 2)),
          Quadrant.southwest) ∈ ShadedSignals.markerQuarters
      rw [show 2 * 4 ^ (extra + 2) =
          2 * (2 * (2 * 4 ^ (extra + 1))) by
        rw [pow_succ]
        omega]
      simp only [refineIndexGrid_even_even]
      exact SparseFreeLineMarker.markerSouthwest_refines _ ih

theorem evenMarkerQuarter (extra : Nat) (grid : Nat → Nat → Index) :
    let coordinate := lineCoordinate .even (extra + 1)
      (SparseFreeLineMarker.markerOffset (extra + 1))
    (refinedGrid .even (extra + 1) grid
        (coordinate / 2) (coordinate / 2),
      quadrantAt coordinate coordinate) ∈ ShadedSignals.markerQuarters := by
  dsimp only
  rw [SparseFreeLineMarker.lineCoordinate_markerOffset]
  have hhalf : 4 ^ (extra + 2) / 2 = 2 * 4 ^ (extra + 1) := by
    rw [show 4 ^ (extra + 2) = 2 * (2 * 4 ^ (extra + 1)) by
      rw [pow_succ]
      omega]
    omega
  have hquadrant : quadrantAt (4 ^ (extra + 2)) (4 ^ (extra + 2)) =
      Quadrant.southwest := by
    rw [show 4 ^ (extra + 2) = 2 * (2 * 4 ^ (extra + 1)) by
      rw [pow_succ]
      omega]
    simp [quadrantAt, Quadrant.ofBits]
  rw [hhalf, hquadrant]
  exact evenMarkerIndex extra grid

end SparseFreeLinePlaneMarker
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
