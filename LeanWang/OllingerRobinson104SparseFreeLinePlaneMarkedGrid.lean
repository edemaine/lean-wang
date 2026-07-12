/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLinePlaneFreeGrid
import LeanWang.OllingerRobinson104SparseFreeLinePlaneMarker
import LeanWang.OllingerRobinson104SparseFreeLineMarkedGrid

/-! Marked semantic free grids in arbitrary coarse grids. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneMarkedGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  ShadedFreeGrid ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid SparseFreeLineOffsets
  SparseFreeLineRecurrence SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem finCons_strictMono {size first : Nat} {rest : Fin size → Nat}
    (first_lt : ∀ index, first < rest index)
    (rest_strictMono : ∀ {i j}, i < j → rest i < rest j) :
    ∀ {i j : Fin (size + 1)}, i < j →
      Fin.cons (α := fun _ => Nat) first rest i <
        Fin.cons (α := fun _ => Nat) first rest j := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hjne : j ≠ 0 := ne_of_gt hij
    rw [← Fin.succ_pred j hjne]
    simpa only [Fin.cons_zero, Fin.cons_succ] using first_lt (j.pred hjne)
  · have hjne : j ≠ 0 := by
      apply ne_of_gt
      exact lt_trans (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)) hij
    rw [← Fin.succ_pred i hi, ← Fin.succ_pred j hjne] at hij ⊢
    simpa only [Fin.cons_succ] using rest_strictMono (by simpa using hij)

def consFreeGrid
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north size column row : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north size)
    (column_before : ∀ i, column < freeGrid.columnAt i)
    (row_before : ∀ i, row < freeGrid.rowAt i)
    (column_west : quarterWest west < column)
    (column_east : column < quarterEast east)
    (row_south : quarterSouth south < row)
    (row_north : row < quarterNorth north)
    (freeColumn : IsFreeColumn indexGrid shadeGrid south north column)
    (freeRow : IsFreeRow indexGrid shadeGrid west east row) :
    FreeGrid indexGrid shadeGrid west east south north (size + 1) where
  columnAt := Fin.cons column freeGrid.columnAt
  rowAt := Fin.cons row freeGrid.rowAt
  column_strictMono := finCons_strictMono column_before freeGrid.column_strictMono
  row_strictMono := finCons_strictMono row_before freeGrid.row_strictMono
  column_west := fun index => Fin.cases column_west freeGrid.column_west index
  column_east := fun index => Fin.cases column_east freeGrid.column_east index
  row_south := fun index => Fin.cases row_south freeGrid.row_south index
  row_north := fun index => Fin.cases row_north freeGrid.row_north index
  freeColumn := fun index => Fin.cases freeColumn freeGrid.freeColumn index
  freeRow := fun index => Fin.cases freeRow freeGrid.freeRow index

def castSize
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north first second : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north first)
    (hsize : first = second) :
    FreeGrid indexGrid shadeGrid west east south north second where
  columnAt := fun i => freeGrid.columnAt (Fin.cast hsize.symm i)
  rowAt := fun i => freeGrid.rowAt (Fin.cast hsize.symm i)
  column_strictMono := by
    intro i j hij
    apply freeGrid.column_strictMono
    simpa [Fin.cast] using hij
  row_strictMono := by
    intro i j hij
    apply freeGrid.row_strictMono
    simpa [Fin.cast] using hij
  column_west := fun i => freeGrid.column_west (Fin.cast hsize.symm i)
  column_east := fun i => freeGrid.column_east (Fin.cast hsize.symm i)
  row_south := fun i => freeGrid.row_south (Fin.cast hsize.symm i)
  row_north := fun i => freeGrid.row_north (Fin.cast hsize.symm i)
  freeColumn := fun i => freeGrid.freeColumn (Fin.cast hsize.symm i)
  freeRow := fun i => freeGrid.freeRow (Fin.cast hsize.symm i)

set_option maxHeartbeats 2000000 in
-- Normalizing the prepended dependent `Fin` index is elaboration-intensive.
def evenMarkedFreeGrid (size : Nat) (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .even (1 + size) grid) stateGrid)
    (cycle : CycleOn (refinedGrid .even (1 + size) grid)
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)))
    (shaded : CycleShade stateGrid
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) .light) :
    FreeGrid (refinedGrid .even (1 + size) grid) stateGrid
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) (size + 3) := by
  have graph :=
    (SparseFreeLinePlaneProjectionStep.graphHolds_unbounded grid size).1
  let sparse := SparseFreeLinePlaneFreeGrid.freeGridOfGraphHolds
    graph valid cycle shaded
  let coordinate := lineCoordinate .even (1 + size)
    (SparseFreeLineMarker.markerOffset (1 + size))
  have marker :
      LiveRowCertificate (refinedGrid .even (1 + size) grid)
          (west .even (1 + size)) (east .even (1 + size))
          (west .even (1 + size)) (east .even (1 + size)) coordinate ∧
        LiveColumnCertificate (refinedGrid .even (1 + size) grid)
          (west .even (1 + size)) (east .even (1 + size))
          (west .even (1 + size)) (east .even (1 + size)) coordinate := by
    simpa [coordinate, Nat.add_comm] using
      SparseFreeLinePlaneMarker.evenCertificates size grid
  have markerFreeColumn : IsFreeColumn
      (refinedGrid .even (1 + size) grid) stateGrid
      (west .even (1 + size)) (east .even (1 + size)) coordinate :=
    isFreeColumn_of_certificate valid cycle shaded marker.2.toColumnCertificate
  have markerFreeRow : IsFreeRow
      (refinedGrid .even (1 + size) grid) stateGrid
      (west .even (1 + size)) (east .even (1 + size)) coordinate :=
    isFreeRow_of_certificate valid cycle shaded marker.1.toRowCertificate
  have before : ∀ index, coordinate < sparse.columnAt index := by
    intro index
    change lineCoordinate .even (1 + size)
        (SparseFreeLineMarker.markerOffset (1 + size)) <
      lineCoordinate .even (1 + size) (offsetAt (1 + size) index)
    have hoffset := SparseFreeLineMarkedGrid.markerOffset_lt_of_mem (1 + size)
      (offsetAt_mem (1 + size) index)
    simpa [lineCoordinate, Phase.factor] using hoffset
  have hwest : quarterWest (west .even (1 + size)) < coordinate := by
    have hcoordinate : coordinate = 4 ^ (size + 2) := by
      dsimp [coordinate]
      simpa [Nat.add_comm] using
        SparseFreeLineMarker.lineCoordinate_markerOffset size
    rw [hcoordinate]
    have hp1 : 4 ^ (1 + size) = 4 * 4 ^ size := by
      rw [show 1 + size = size + 1 by omega, pow_succ]
      omega
    have hp2 : 4 ^ (size + 2) = 16 * 4 ^ size := by
      rw [show size + 2 = (size + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    simp [west, scale, Phase.factor, quarterWest, hp1, hp2]
    have hpow : 0 < 4 ^ size := pow_pos (by decide) _
    omega
  have heast : coordinate < quarterEast (east .even (1 + size)) := by
    have hcoordinate : coordinate = 4 ^ (size + 2) := by
      dsimp [coordinate]
      simpa [Nat.add_comm] using
        SparseFreeLineMarker.lineCoordinate_markerOffset size
    rw [hcoordinate]
    have hp1 : 4 ^ (1 + size) = 4 * 4 ^ size := by
      rw [show 1 + size = size + 1 by omega, pow_succ]
      omega
    have hp2 : 4 ^ (size + 2) = 16 * 4 ^ size := by
      rw [show size + 2 = (size + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    simp [east, scale, Phase.factor, quarterEast, hp1, hp2]
    have hpow : 0 < 4 ^ size := pow_pos (by decide) _
    omega
  have result := consFreeGrid sparse before before hwest heast hwest heast
    markerFreeColumn markerFreeRow
  apply castSize result
  rw [offsets_length]
  omega

set_option maxHeartbeats 2000000 in
-- Normalizing the prepended dependent `Fin` index is elaboration-intensive.
def oddMarkedFreeGrid (size : Nat) (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .odd size grid) stateGrid)
    (cycle : CycleOn (refinedGrid .odd size grid)
      (west .odd size) (east .odd size) (west .odd size) (east .odd size))
    (shaded : CycleShade stateGrid
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) .light) :
    FreeGrid (refinedGrid .odd size grid) stateGrid
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) (size + 2) := by
  have graph :=
    (SparseFreeLinePlaneProjectionStep.graphHolds_unbounded grid size).2
  let sparse := SparseFreeLinePlaneFreeGrid.freeGridOfGraphHolds
    graph valid cycle shaded
  let coordinate := SparseFreeLinePlaneMarker.oddMarkerCoordinate size
  have marker := SparseFreeLinePlaneMarker.certificates size grid
  have markerFreeColumn : IsFreeColumn (refinedGrid .odd size grid) stateGrid
      (west .odd size) (east .odd size) coordinate :=
    isFreeColumn_of_certificate valid cycle shaded marker.2.toColumnCertificate
  have markerFreeRow : IsFreeRow (refinedGrid .odd size grid) stateGrid
      (west .odd size) (east .odd size) coordinate :=
    isFreeRow_of_certificate valid cycle shaded marker.1.toRowCertificate
  have before : ∀ index, coordinate < sparse.columnAt index := by
    intro index
    change SparseFreeLinePlaneMarker.oddMarkerCoordinate size <
      lineCoordinate .odd size (offsetAt size index)
    have hpivot := SparseFreeLineMarkedGrid.pivot_le_of_mem size
      (offsetAt_mem size index)
    rw [BorderCoverageOffsets.lineCoordinate_odd]
    simp [pivot] at hpivot
    dsimp [SparseFreeLinePlaneMarker.oddMarkerCoordinate]
    omega
  have hwest : quarterWest (west .odd size) < coordinate := by
    dsimp [coordinate]
    simp [SparseFreeLinePlaneMarker.oddMarkerCoordinate, west, scale,
      Phase.factor, quarterWest]
    have hpow : 0 < 4 ^ size := pow_pos (by decide) _
    omega
  have heast : coordinate < quarterEast (east .odd size) := by
    dsimp [coordinate]
    simp [SparseFreeLinePlaneMarker.oddMarkerCoordinate, east, scale,
      Phase.factor, quarterEast]
    have hpow : 0 < 4 ^ size := pow_pos (by decide) _
    omega
  have result := consFreeGrid sparse before before hwest heast hwest heast
    markerFreeColumn markerFreeRow
  apply castSize result
  rw [offsets_length]

@[simp] theorem castSize_columnAt_zero
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north first second : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north first)
    (hsize : first = second) (hpositive : 0 < first) :
    (castSize freeGrid hsize).columnAt ⟨0, hsize ▸ hpositive⟩ =
      freeGrid.columnAt ⟨0, hpositive⟩ := by
  rfl

@[simp] theorem castSize_rowAt_zero
    {indexGrid : Nat → Nat → Index}
    {shadeGrid : Nat → Nat → RedShades.State}
    {west east south north first second : Nat}
    (freeGrid : FreeGrid indexGrid shadeGrid west east south north first)
    (hsize : first = second) (hpositive : 0 < first) :
    (castSize freeGrid hsize).rowAt ⟨0, hsize ▸ hpositive⟩ =
      freeGrid.rowAt ⟨0, hpositive⟩ := by
  rfl

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent size cast exposes the prepended coordinate.
theorem evenMarkedFreeGrid_lowerLeft
    (size : Nat) (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .even (1 + size) grid) stateGrid)
    (cycle : CycleOn (refinedGrid .even (1 + size) grid)
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)))
    (shaded : CycleShade stateGrid
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) .light) :
    (evenMarkedFreeGrid size grid valid cycle shaded).columnAt 0 =
        lineCoordinate .even (1 + size)
          (SparseFreeLineMarker.markerOffset (1 + size)) ∧
      (evenMarkedFreeGrid size grid valid cycle shaded).rowAt 0 =
        lineCoordinate .even (1 + size)
          (SparseFreeLineMarker.markerOffset (1 + size)) := by
  simp [evenMarkedFreeGrid, castSize, consFreeGrid]

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent size cast exposes the prepended coordinate.
theorem oddMarkedFreeGrid_lowerLeft
    (size : Nat) (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .odd size grid) stateGrid)
    (cycle : CycleOn (refinedGrid .odd size grid)
      (west .odd size) (east .odd size) (west .odd size) (east .odd size))
    (shaded : CycleShade stateGrid
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) .light) :
    (oddMarkedFreeGrid size grid valid cycle shaded).columnAt 0 =
        SparseFreeLinePlaneMarker.oddMarkerCoordinate size ∧
      (oddMarkedFreeGrid size grid valid cycle shaded).rowAt 0 =
        SparseFreeLinePlaneMarker.oddMarkerCoordinate size := by
  simp [oddMarkedFreeGrid, castSize, consFreeGrid]

theorem evenMarkedFreeGrid_lowerLeft_marker
    (size : Nat) (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .even (1 + size) grid) stateGrid)
    (cycle : CycleOn (refinedGrid .even (1 + size) grid)
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)))
    (shaded : CycleShade stateGrid
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) .light) :
    let freeGrid := evenMarkedFreeGrid size grid valid cycle shaded
    (refinedGrid .even (1 + size) grid
        (freeGrid.columnAt 0 / 2) (freeGrid.rowAt 0 / 2),
      quadrantAt (freeGrid.columnAt 0) (freeGrid.rowAt 0)) ∈
      ShadedSignals.markerQuarters := by
  dsimp only
  rw [(evenMarkedFreeGrid_lowerLeft size grid valid cycle shaded).1,
    (evenMarkedFreeGrid_lowerLeft size grid valid cycle shaded).2]
  simpa [Nat.add_comm] using
    SparseFreeLinePlaneMarker.evenMarkerQuarter size grid

theorem oddMarkedFreeGrid_lowerLeft_marker
    (size : Nat) (grid : Nat → Nat → Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .odd size grid) stateGrid)
    (cycle : CycleOn (refinedGrid .odd size grid)
      (west .odd size) (east .odd size) (west .odd size) (east .odd size))
    (shaded : CycleShade stateGrid
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) .light) :
    let freeGrid := oddMarkedFreeGrid size grid valid cycle shaded
    (refinedGrid .odd size grid
        (freeGrid.columnAt 0 / 2) (freeGrid.rowAt 0 / 2),
      quadrantAt (freeGrid.columnAt 0) (freeGrid.rowAt 0)) ∈
      ShadedSignals.markerQuarters := by
  dsimp only
  rw [(oddMarkedFreeGrid_lowerLeft size grid valid cycle shaded).1,
    (oddMarkedFreeGrid_lowerLeft size grid valid cycle shaded).2]
  exact SparseFreeLinePlaneMarker.markerAtCoordinate size grid

end SparseFreeLinePlaneMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
