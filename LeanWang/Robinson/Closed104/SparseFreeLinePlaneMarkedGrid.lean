/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.SparseFreeLinePlaneFreeGrid
import LeanWang.Robinson.Closed104.SparseFreeLinePivotMarker

/-! Sparse semantic free grids whose first retained crossing is the marker. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLinePlaneMarkedGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  ShadedFreeGrid ShadedFreeLineRecurrence SparseFreeLineOffsets
  SparseFreeLinePlaneBase Signals.FreeCellLocal

set_option maxRecDepth 20000

structure MarkedFreeGrid
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east south north size : Nat) where
  grid : FreeGrid indexGrid shadeGrid west east south north size
  positive : 0 < size
  lowerLeftMarker :
    (indexGrid (grid.columnAt ⟨0, positive⟩ / 2)
        (grid.rowAt ⟨0, positive⟩ / 2),
      quadrantAt (grid.columnAt ⟨0, positive⟩)
        (grid.rowAt ⟨0, positive⟩)) ∈
      ShadedSignals.markerQuarters

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

/-- The even light board, starting directly at its retained pivot. -/
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
      (west .even (1 + size)) (east .even (1 + size)) (size + 2) := by
  have graph :=
    (SparseFreeLinePlaneProjectionStep.graphHolds_unbounded grid size).1
  let sparse := SparseFreeLinePlaneFreeGrid.freeGridOfGraphHolds
    graph valid cycle shaded
  apply castSize sparse
  rw [offsets_length]
  omega

/-- The odd light board, starting directly at its retained pivot. -/
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
      (west .odd size) (east .odd size) (size + 1) := by
  have graph :=
    (SparseFreeLinePlaneProjectionStep.graphHolds_unbounded grid size).2
  let sparse := SparseFreeLinePlaneFreeGrid.freeGridOfGraphHolds
    graph valid cycle shaded
  apply castSize sparse
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
-- Unfolding the dependent size cast exposes the first retained offset.
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
        lineCoordinate .even (1 + size) (pivot (1 + size)) ∧
      (evenMarkedFreeGrid size grid valid cycle shaded).rowAt 0 =
        lineCoordinate .even (1 + size) (pivot (1 + size)) := by
  simp only [evenMarkedFreeGrid, castSize,
    SparseFreeLinePlaneFreeGrid.freeGridOfGraphHolds]
  have positive : 0 < (offsets (1 + size)).length := by
    rw [offsets_length]
    omega
  exact ⟨congrArg (lineCoordinate .even (1 + size))
      (offsetAt_zero (1 + size) positive),
    congrArg (lineCoordinate .even (1 + size))
      (offsetAt_zero (1 + size) positive)⟩

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent size cast exposes the first retained offset.
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
        lineCoordinate .odd size (pivot size) ∧
      (oddMarkedFreeGrid size grid valid cycle shaded).rowAt 0 =
        lineCoordinate .odd size (pivot size) := by
  simp only [oddMarkedFreeGrid, castSize,
    SparseFreeLinePlaneFreeGrid.freeGridOfGraphHolds]
  have positive : 0 < (offsets size).length := by
    rw [offsets_length]
    omega
  exact ⟨congrArg (lineCoordinate .odd size) (offsetAt_zero size positive),
    congrArg (lineCoordinate .odd size) (offsetAt_zero size positive)⟩

theorem evenMarkedFreeGrid_lowerLeft_marker
    (size : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0)
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
    SparseFreeLinePivotMarker.evenPivotMarkerQuarter size grid root

theorem oddMarkedFreeGrid_lowerLeft_marker
    (size : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0)
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
  exact SparseFreeLinePivotMarker.oddPivotMarkerQuarter size grid root

def evenMarkedWitness
    (size : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .even (1 + size) grid) stateGrid)
    (cycle : CycleOn (refinedGrid .even (1 + size) grid)
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)))
    (shaded : CycleShade stateGrid
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) .light) :
    MarkedFreeGrid (refinedGrid .even (1 + size) grid) stateGrid
      (west .even (1 + size)) (east .even (1 + size))
      (west .even (1 + size)) (east .even (1 + size)) (size + 2) where
  grid := evenMarkedFreeGrid size grid valid cycle shaded
  positive := by omega
  lowerLeftMarker := evenMarkedFreeGrid_lowerLeft_marker
    size grid root valid cycle shaded

def oddMarkedWitness
    (size : Nat) (grid : Nat → Nat → Index)
    (root : grid 0 0 = 0)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (refinedGrid .odd size grid) stateGrid)
    (cycle : CycleOn (refinedGrid .odd size grid)
      (west .odd size) (east .odd size) (west .odd size) (east .odd size))
    (shaded : CycleShade stateGrid
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) .light) :
    MarkedFreeGrid (refinedGrid .odd size grid) stateGrid
      (west .odd size) (east .odd size)
      (west .odd size) (east .odd size) (size + 1) where
  grid := oddMarkedFreeGrid size grid valid cycle shaded
  positive := by omega
  lowerLeftMarker := oddMarkedFreeGrid_lowerLeft_marker
    size grid root valid cycle shaded

end SparseFreeLinePlaneMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
