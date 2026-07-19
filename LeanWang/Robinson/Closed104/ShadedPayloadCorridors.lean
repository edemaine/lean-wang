/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedConsecutiveFreeGrid
import LeanWang.Robinson.Closed104.SignalCorridors

/-!
# Payload corridors through complete Robinson free grids

This module isolates the payload-routing consequence of Robinson's Section 7
obstruction characterization. Once non-free columns and rows are known to be
obstructed at free crossings, consecutive free lines transmit payload edge
colors and form a fixed-corner square.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedPayloadCorridors

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths ShadedPlaneShadeGrid
  ShadedPlaneSignalGrid ShadedFreeGrid ShadedConsecutiveFreeGrid
  Signals.FreeCellLocal

set_option maxRecDepth 20000

structure CrossingObstruction
    (indexGrid : Nat -> Nat -> Index)
    (shadeGrid : Nat -> Nat -> RedShades.State)
    (signalGrid : Nat -> Nat -> Signals.State)
    (west east south north : Nat) : Prop where
  verticalBlocked : forall {column row : Nat},
    quarterWest west < column -> column < quarterEast east ->
    quarterSouth south < row -> row < quarterNorth north ->
    IsFreeRow indexGrid shadeGrid west east row ->
    ¬IsFreeColumn indexGrid shadeGrid south north column ->
      ¬((signalGrid column row).south = .none ∧
        (signalGrid column row).north = .none)
  horizontalBlocked : forall {column row : Nat},
    quarterWest west < column -> column < quarterEast east ->
    quarterSouth south < row -> row < quarterNorth north ->
    IsFreeColumn indexGrid shadeGrid south north column ->
    ¬IsFreeRow indexGrid shadeGrid west east row ->
      ¬((signalGrid column row).west = .none ∧
        (signalGrid column row).east = .none)

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int -> TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

theorem routeRole_channel_iff
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int) (column row : Nat) :
    let signal := ShadedPlaneSignalGrid.signalGrid decoded parentOrigin column row
    let role := ShadedSignals.routeRole
      (decoded.base (point decoded parentOrigin column row)).1
    (role = .horizontal ↔
        signal.west = .none ∧ signal.east = .none ∧
          ¬(signal.south = .none ∧ signal.north = .none)) ∧
      (role = .vertical ↔
        ¬(signal.west = .none ∧ signal.east = .none) ∧
          signal.south = .none ∧ signal.north = .none) := by
  let site := ShadedSignals.decode
    (decoded.base (point decoded parentOrigin column row))
  rw [← ShadedSignals.decode_tile
    (decoded.base (point decoded parentOrigin column row))]
  have hstate : ShadedPlaneSignalGrid.signalGrid decoded parentOrigin column row =
      site.2 := by
    rfl
  rw [hstate]
  exact ⟨ShadedSignals.routeRole_tile_eq_horizontal_iff site,
    ShadedSignals.routeRole_tile_eq_vertical_iff site⟩

theorem horizontal_payload_across
    (tiles : Nat -> WangTile) (start count : Nat)
    (hmatch : forall i, i ≤ count ->
      WangTile.HMatches (tiles (start + i)) (tiles (start + i + 1)))
    (hwire : forall i, i < count ->
      (tiles (start + i + 1)).w = (tiles (start + i + 1)).e) :
    WangTile.HMatches (tiles start) (tiles (start + count + 1)) :=
  Signals.value_across tiles WangTile.e WangTile.w start count hmatch hwire

theorem vertical_payload_across
    (tiles : Nat -> WangTile) (start count : Nat)
    (hmatch : forall i, i ≤ count ->
      WangTile.VMatches (tiles (start + i)) (tiles (start + i + 1)))
    (hwire : forall i, i < count ->
      (tiles (start + i + 1)).s = (tiles (start + i + 1)).n) :
    WangTile.VMatches (tiles start) (tiles (start + count + 1)) :=
  Signals.value_across tiles WangTile.n WangTile.s start count hmatch hwire

set_option maxHeartbeats 1000000 in
-- Elaborating the variable-length payload corridor and decoded point arithmetic.
theorem payload_hmatch_of_consecutive
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int)
    {west east south north size : Nat}
    (grid : ConsecutiveMarkedFreeGrid
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north size)
    (cycle : CycleOn (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      west east south north)
    (shaded : CycleShade (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north .light)
    (crossing : CrossingObstruction
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      (ShadedPlaneSignalGrid.signalGrid decoded parentOrigin)
      west east south north)
    (i j : Fin size) (hi : i.val + 1 < size) :
    WangTile.HMatches
      (decoded.payload (point decoded parentOrigin (grid.columnAt i) (grid.rowAt j)))
      (decoded.payload (point decoded parentOrigin
        (grid.columnAt ⟨i.val + 1, hi⟩) (grid.rowAt j))) := by
  let left := grid.columnAt i
  let right := grid.columnAt ⟨i.val + 1, hi⟩
  have hlr : left < right := grid.column_strictMono (by
    change i.val < i.val + 1
    omega)
  have hend : left + (right - left - 1) + 1 = right := by omega
  change WangTile.HMatches
    (decoded.payload (point decoded parentOrigin left (grid.rowAt j)))
    (decoded.payload (point decoded parentOrigin right (grid.rowAt j)))
  rw [← hend]
  refine horizontal_payload_across
    (fun column => decoded.payload
      (point decoded parentOrigin column (grid.rowAt j)))
    left (right - left - 1) ?_ ?_
  · intro offset hoffset
    have hpoint : point decoded parentOrigin (left + offset + 1) (grid.rowAt j) =
        ((point decoded parentOrigin (left + offset) (grid.rowAt j)).1 + 1,
          (point decoded parentOrigin (left + offset) (grid.rowAt j)).2) := by
      simp [point, quarterGridOrigin, Desubstitution.shift]
      omega
    simpa only [hpoint] using decoded.payload_hmatch
      (point decoded parentOrigin (left + offset) (grid.rowAt j))
  · intro offset hoffset
    let column := left + offset + 1
    have hleft : left < column := by simp [column]
    have hright : column < right := by simp [column]; omega
    have hnotFree := grid.noFreeColumnBetween i hi column hleft hright
    have hrowClear := ShadedPlaneSignalGrid.CycleShade.clear_at_free_row shaded cycle
      (ShadedPlaneSignalGrid.valid decoded parentOrigin)
      (grid.row_south j) (grid.row_north j) (grid.freeRow j)
      (lt_trans (grid.column_west i) hleft)
      (hright.trans (grid.column_east ⟨i.val + 1, hi⟩))
    have hblocked := crossing.verticalBlocked
      (lt_trans (grid.column_west i) hleft)
      (hright.trans (grid.column_east ⟨i.val + 1, hi⟩))
      (grid.row_south j) (grid.row_north j) (grid.freeRow j) hnotFree
    have hrole := (routeRole_channel_iff decoded parentOrigin
      column (grid.rowAt j)).1.2 ⟨hrowClear.1, hrowClear.2, hblocked⟩
    exact (decoded.horizontal_payload_wire
      (point decoded parentOrigin column (grid.rowAt j)) hrole).2

set_option maxHeartbeats 1000000 in
-- Elaborating the variable-length payload corridor and decoded point arithmetic.
theorem payload_vmatch_of_consecutive
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int)
    {west east south north size : Nat}
    (grid : ConsecutiveMarkedFreeGrid
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north size)
    (cycle : CycleOn (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      west east south north)
    (shaded : CycleShade (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north .light)
    (crossing : CrossingObstruction
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      (ShadedPlaneSignalGrid.signalGrid decoded parentOrigin)
      west east south north)
    (i j : Fin size) (hj : j.val + 1 < size) :
    WangTile.VMatches
      (decoded.payload (point decoded parentOrigin (grid.columnAt i) (grid.rowAt j)))
      (decoded.payload (point decoded parentOrigin
        (grid.columnAt i) (grid.rowAt ⟨j.val + 1, hj⟩))) := by
  let lower := grid.rowAt j
  let upper := grid.rowAt ⟨j.val + 1, hj⟩
  have hlu : lower < upper := grid.row_strictMono (by
    change j.val < j.val + 1
    omega)
  have hend : lower + (upper - lower - 1) + 1 = upper := by omega
  change WangTile.VMatches
    (decoded.payload (point decoded parentOrigin (grid.columnAt i) lower))
    (decoded.payload (point decoded parentOrigin (grid.columnAt i) upper))
  rw [← hend]
  refine vertical_payload_across
    (fun row => decoded.payload
      (point decoded parentOrigin (grid.columnAt i) row))
    lower (upper - lower - 1) ?_ ?_
  · intro offset hoffset
    have hpoint : point decoded parentOrigin (grid.columnAt i) (lower + offset + 1) =
        ((point decoded parentOrigin (grid.columnAt i) (lower + offset)).1,
          (point decoded parentOrigin (grid.columnAt i) (lower + offset)).2 + 1) := by
      simp [point, quarterGridOrigin, Desubstitution.shift]
      omega
    simpa only [hpoint] using decoded.payload_vmatch
      (point decoded parentOrigin (grid.columnAt i) (lower + offset))
  · intro offset hoffset
    let row := lower + offset + 1
    have hlower : lower < row := by simp [row]
    have hupper : row < upper := by simp [row]; omega
    have hnotFree := grid.noFreeRowBetween j hj row hlower hupper
    have hcolumnClear := ShadedPlaneSignalGrid.CycleShade.clear_at_free_column shaded cycle
      (ShadedPlaneSignalGrid.valid decoded parentOrigin)
      (grid.column_west i) (grid.column_east i) (grid.freeColumn i)
      (lt_trans (grid.row_south j) hlower)
      (hupper.trans (grid.row_north ⟨j.val + 1, hj⟩))
    have hblocked := crossing.horizontalBlocked
      (grid.column_west i) (grid.column_east i)
      (lt_trans (grid.row_south j) hlower)
      (hupper.trans (grid.row_north ⟨j.val + 1, hj⟩))
      (grid.freeColumn i) hnotFree
    have hrole := (routeRole_channel_iff decoded parentOrigin
      (grid.columnAt i) row).2.2 ⟨hblocked, hcolumnClear⟩
    exact (decoded.vertical_payload_wire
      (point decoded parentOrigin (grid.columnAt i) row) hrole).2

set_option maxHeartbeats 1000000 in
-- Packaging both routed corridors into a dependent finite rectangle.
/-- A complete consecutive marked grid carries a fixed-corner payload square. -/
theorem tileableFixedCornerSquare_of_consecutive
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (parentOrigin : Int × Int)
    {west east south north size : Nat}
    (grid : ConsecutiveMarkedFreeGrid
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north size)
    (cycle : CycleOn (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      west east south north)
    (shaded : CycleShade (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      west east south north .light)
    (crossing : CrossingObstruction
      (HierarchyEmbedding.natGridAt decoded.parent parentOrigin)
      (ShadedPlaneShadeGrid.stateGrid decoded parentOrigin)
      (ShadedPlaneSignalGrid.signalGrid decoded parentOrigin)
      west east south north) :
    TileableFixedCornerSquare T seed size := by
  let payloadRect : Rectangle size size := fun i j =>
    decoded.payload (point decoded parentOrigin (grid.columnAt i) (grid.rowAt j))
  refine ⟨grid.positive, payloadRect, ?_, ?_⟩
  · constructor
    · intro i j
      exact payload_free_crossing_mem decoded parentOrigin cycle shaded
        (grid.column_west i) (grid.column_east i)
        (grid.row_south j) (grid.row_north j)
        (grid.freeRow j) (grid.freeColumn i)
    constructor
    · intro i j hi
      exact payload_hmatch_of_consecutive decoded parentOrigin grid cycle shaded
        crossing i j hi
    · intro i j hj
      exact payload_vmatch_of_consecutive decoded parentOrigin grid cycle shaded
        crossing i j hj
  · have hclear := grid.toFreeGrid.signal_clear cycle shaded
      (ShadedPlaneSignalGrid.valid decoded parentOrigin)
      (⟨0, grid.positive⟩ : Fin size) (⟨0, grid.positive⟩ : Fin size)
    have hmarker : decoded.quarter (point decoded parentOrigin
        (grid.columnAt ⟨0, grid.positive⟩)
        (grid.rowAt ⟨0, grid.positive⟩)) ∈ ShadedSignals.markerQuarters := by
      rw [quarter_at_point]
      exact grid.lowerLeftMarker
    exact payload_at_clear_corner_eq_seed decoded parentOrigin
      (grid.columnAt ⟨0, grid.positive⟩)
      (grid.rowAt ⟨0, grid.positive⟩) hclear hmarker

end ShadedPayloadCorridors
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
