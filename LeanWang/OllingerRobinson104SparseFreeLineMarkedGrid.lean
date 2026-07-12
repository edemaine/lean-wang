/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineComplete
import LeanWang.OllingerRobinson104SparseFreeLineMarker

/-!
# Unbounded marked free grids

The recursively preserved marker line is prepended to the sparse free-line
family.  It is strictly southwest of every retained sparse line, so the marked
crossing is index zero in both dimensions.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineMarkedGrid

open RedCycles RedShadeCycles RedShadePaths ShadedFreeGrid ShadedFreeLineGraph
  ShadedFreeLinePatternRefinement ShadedFreeLineRecurrence
  ShadedPlaneSignalGrid SparseFreeLineOffsets SparseFreeLineRecurrence
  SparseFreeLineMarker Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem pivot_le_of_mem (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) :
    pivot depth ≤ offset := by
  induction depth generalizing offset with
  | zero =>
      change 2 ≤ offset
      simp [offsets] at hoffset
      omega
  | succ depth ih =>
      rcases mem_offsets_succ_cases depth hoffset with
        ⟨oldOffset, hold, hchild⟩
      have hlower := ih hold
      by_cases heven : oldOffset % 2 = 0
      · simp only [children, heven, if_true, List.mem_cons,
          List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl <;>
          simp [pivot, pow_succ] at * <;> omega
      · simp only [children, heven, if_false, List.mem_singleton] at hchild
        subst offset
        simp [pivot, pow_succ] at *
        omega

theorem markerOffset_lt_of_mem (depth : Nat) {offset : Nat}
    (hoffset : offset ∈ offsets depth) :
    markerOffset depth < offset := by
  have hlower := pivot_le_of_mem depth hoffset
  have hpositive : 0 < 4 ^ depth := pow_pos (by decide) _
  have hmarker : markerOffset depth + 1 = pivot depth := by
    simp [markerOffset, pivot]
    omega
  omega

private theorem finCons_strictMono {size first : Nat} {rest : Fin size → Nat}
    (first_lt : ∀ index, first < rest index)
    (rest_strictMono : ∀ {i j}, i < j → rest i < rest j) :
    ∀ {i j : Fin (size + 1)}, i < j →
      Fin.cons (α := fun _ => Nat) first rest i <
        Fin.cons (α := fun _ => Nat) first rest j := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hjpos : 0 < j := hij
    have hjne : j ≠ 0 := ne_of_gt hjpos
    have hj : (j.pred hjne).succ = j := Fin.succ_pred j hjne
    rw [← hj]
    simpa only [Fin.cons_zero, Fin.cons_succ] using first_lt (j.pred hjne)
  · have hipos : 0 < i := by
      apply Nat.pos_of_ne_zero
      intro hzero
      apply hi
      apply Fin.ext
      simpa using hzero
    have hjpos : 0 < j := lt_trans hipos hij
    have hjne : j ≠ 0 := ne_of_gt hjpos
    have hiEq : (i.pred hi).succ = i := Fin.succ_pred i hi
    have hjEq : (j.pred hjne).succ = j := Fin.succ_pred j hjne
    rw [← hiEq, ← hjEq] at hij ⊢
    simpa only [Fin.cons_succ] using
      rest_strictMono (by simpa using hij)

private def consFreeGrid
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

/-- The marked crossing followed by all sparse crossings at even depth. -/
def markedFreeGrid (extra : Nat) (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid .even (extra + 1) parent) stateGrid)
    (shaded : CycleShade stateGrid
      (west .even (extra + 1)) (east .even (extra + 1))
      (west .even (extra + 1)) (east .even (extra + 1)) .light) :
    FreeGrid (localGrid .even (extra + 1) parent) stateGrid
      (west .even (extra + 1)) (east .even (extra + 1))
      (west .even (extra + 1)) (east .even (extra + 1))
      ((offsets (extra + 1)).length + 1) := by
  let depth := extra + 1
  have graph : SparseFreeLineRecurrence.GraphHolds .even depth := by
    simpa [depth, Nat.add_comm] using
      (SparseFreeLineComplete.graphHolds_unbounded extra).1
  let sparse := freeGridOfGraphHolds graph parent valid shaded
  let coordinate := lineCoordinate .even depth (markerOffset depth)
  have markerCertificates := SparseFreeLineMarker.certificates extra parent
  have cycle := canonicalCycle .even depth parent
  have markerFreeColumn :
      IsFreeColumn (localGrid .even depth parent) stateGrid
        (west .even depth) (east .even depth) coordinate := by
    exact isFreeColumn_of_certificate valid cycle shaded
      markerCertificates.2.toColumnCertificate
  have markerFreeRow :
      IsFreeRow (localGrid .even depth parent) stateGrid
        (west .even depth) (east .even depth) coordinate := by
    exact isFreeRow_of_certificate valid cycle shaded
      markerCertificates.1.toRowCertificate
  have coordinate_before : ∀ index, coordinate < sparse.columnAt index := by
    intro index
    change lineCoordinate .even depth (markerOffset depth) <
      lineCoordinate .even depth (offsetAt depth index)
    have hoffset := markerOffset_lt_of_mem depth (offsetAt_mem depth index)
    simpa [lineCoordinate, Phase.factor] using hoffset
  have coordinate_west : quarterWest (west .even depth) < coordinate := by
    dsimp only [coordinate, depth]
    rw [lineCoordinate_markerOffset]
    have hpositive : 0 < 4 ^ (extra + 1) := pow_pos (by decide) _
    simp [west, scale, Phase.factor, quarterWest, pow_succ]
    omega
  have coordinate_east : coordinate < quarterEast (east .even depth) := by
    dsimp only [coordinate, depth]
    rw [lineCoordinate_markerOffset]
    have hpositive : 0 < 4 ^ (extra + 1) := pow_pos (by decide) _
    simp [east, scale, Phase.factor, quarterEast, pow_succ]
    omega
  have grid := consFreeGrid sparse coordinate_before coordinate_before
    coordinate_west coordinate_east coordinate_west coordinate_east
    markerFreeColumn markerFreeRow
  simpa only [depth] using grid

@[simp] theorem markedFreeGrid_lowerLeft_coordinate
    (extra : Nat) (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid .even (extra + 1) parent) stateGrid)
    (shaded : CycleShade stateGrid
      (west .even (extra + 1)) (east .even (extra + 1))
      (west .even (extra + 1)) (east .even (extra + 1)) .light) :
    (markedFreeGrid extra parent valid shaded).columnAt 0 =
        lineCoordinate .even (extra + 1) (markerOffset (extra + 1)) ∧
      (markedFreeGrid extra parent valid shaded).rowAt 0 =
        lineCoordinate .even (extra + 1) (markerOffset (extra + 1)) := by
  simp only [markedFreeGrid, consFreeGrid, Fin.cons_zero]
  exact ⟨trivial, trivial⟩

/-- The lower-left crossing of the marked grid has the scaffold marker type. -/
theorem markedFreeGrid_lowerLeft_marker (extra : Nat) (parent : Index) :
    let coordinate :=
      lineCoordinate .even (extra + 1) (markerOffset (extra + 1))
    (localGrid .even (extra + 1) parent
        (coordinate / 2) (coordinate / 2), quadrantAt coordinate coordinate) ∈
      ShadedSignals.markerQuarters :=
  SparseFreeLineMarker.markerQuarter extra parent

end SparseFreeLineMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
