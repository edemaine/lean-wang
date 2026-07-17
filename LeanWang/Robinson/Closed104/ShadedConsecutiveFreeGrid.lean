/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.SparseFreeLineDecodedMarkedGrid
import LeanWang.Robinson.Closed104.ShadedFreeLineEnumeration

/-!
# Consecutive complete free grids

Sort all free rows and columns at or above a marked crossing. A sufficiently
large marked sparse grid supplies the cardinality bound for taking a prefix;
successive coordinates in that prefix have no omitted free line between them.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedConsecutiveFreeGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  ShadedPlaneSignalGrid ShadedFreeGrid ShadedFreeLineEnumeration
  SparseFreeLinePlaneMarkedGrid
  SparseFreeLineDecodedMarkedGrid Signals.FreeCellLocal

structure OrderedPrefix (s : Finset Nat) (size : Nat) where
  coord : Fin size -> Nat
  mem_coord : forall i, coord i ∈ s
  strictMono : StrictMono coord
  first_min : forall (hsize : 0 < size) (k : Nat), k ∈ s ->
    coord ⟨0, hsize⟩ ≤ k
  no_mem_between : forall (i : Fin size) (hi : i.val + 1 < size) (k : Nat),
    coord i < k -> k < coord ⟨i.val + 1, hi⟩ -> k ∉ s

noncomputable def OrderedPrefix.ofCardLE (s : Finset Nat) (size : Nat)
    (hsize : size ≤ s.card) : OrderedPrefix s size where
  coord := fun i =>
    (s.sort (· ≤ ·)).get ⟨i.val, by simpa using lt_of_lt_of_le i.isLt hsize⟩
  mem_coord := by
    intro i
    rw [← Finset.mem_sort (· ≤ ·)]
    exact List.get_mem _ _
  strictMono := by
    intro i j hij
    exact (Finset.sortedLT_sort s).pairwise.rel_get_of_lt hij
  first_min := by
    intro hpositive k hk
    have hkl : k ∈ s.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).2 hk
    rcases List.mem_iff_get.1 hkl with ⟨j, hj⟩
    have hle := (Finset.pairwise_sort s (· ≤ ·)).rel_get_of_le
      (show (⟨0, by simpa using lt_of_lt_of_le hpositive hsize⟩ :
        Fin (s.sort (· ≤ ·)).length) ≤ j by
          change 0 ≤ j.val
          exact Nat.zero_le _)
    simpa only [hj] using hle
  no_mem_between := by
    intro i hi k hik hki hk
    have hkl : k ∈ s.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).2 hk
    rcases List.mem_iff_get.1 hkl with ⟨j, hj⟩
    let left : Fin (s.sort (· ≤ ·)).length :=
      ⟨i.val, by simpa using lt_of_lt_of_le i.isLt hsize⟩
    let right : Fin (s.sort (· ≤ ·)).length :=
      ⟨i.val + 1, by simpa using lt_of_lt_of_le hi hsize⟩
    by_cases hji : j ≤ left
    · have hle := (Finset.pairwise_sort s (· ≤ ·)).rel_get_of_le hji
      change (s.sort (· ≤ ·)).get left < k at hik
      rw [hj] at hle
      omega
    · have hright : right ≤ j := by
        change i.val + 1 ≤ j.val
        change ¬j.val ≤ i.val at hji
        omega
      have hle := (Finset.pairwise_sort s (· ≤ ·)).rel_get_of_le hright
      change k < (s.sort (· ≤ ·)).get right at hki
      rw [hj] at hle
      omega

theorem OrderedPrefix.at_zero_eq
    {s : Finset Nat} {size marker : Nat} (hsize : 0 < size)
    (selection : OrderedPrefix s size) (hmarker : marker ∈ s)
    (hmin : ∀ k ∈ s, marker ≤ k) :
    selection.coord ⟨0, hsize⟩ = marker := by
  have hge := hmin _ (selection.mem_coord ⟨0, hsize⟩)
  have hle := selection.first_min hsize marker hmarker
  omega

structure ConsecutiveMarkedFreeGrid
    (indexGrid : Nat -> Nat -> Index)
    (shadeGrid : Nat -> Nat -> RedShades.State)
    (west east south north size : Nat)
    extends FreeGrid indexGrid shadeGrid west east south north size where
  positive : 0 < size
  noFreeColumnBetween : forall (i : Fin size) (hi : i.val + 1 < size) (k : Nat),
    columnAt i < k -> k < columnAt ⟨i.val + 1, hi⟩ ->
      ¬IsFreeColumn indexGrid shadeGrid south north k
  noFreeRowBetween : forall (i : Fin size) (hi : i.val + 1 < size) (k : Nat),
    rowAt i < k -> k < rowAt ⟨i.val + 1, hi⟩ ->
      ¬IsFreeRow indexGrid shadeGrid west east k
  lowerLeftMarker :
    (indexGrid (columnAt ⟨0, positive⟩ / 2) (rowAt ⟨0, positive⟩ / 2),
      quadrantAt (columnAt ⟨0, positive⟩) (rowAt ⟨0, positive⟩)) ∈
      ShadedSignals.markerQuarters

private theorem columnAt_zero_le
    {indexGrid : Nat -> Nat -> Index} {shadeGrid : Nat -> Nat -> RedShades.State}
    {west east south north size : Nat}
    (grid : FreeGrid indexGrid shadeGrid west east south north size)
    (positive : 0 < size) (i : Fin size) :
    grid.columnAt ⟨0, positive⟩ ≤ grid.columnAt i := by
  by_cases hi : i = ⟨0, positive⟩
  · rw [hi]
  · have hval : i.val ≠ 0 := by
      intro hzero
      exact hi (Fin.ext hzero)
    exact (grid.column_strictMono (show (⟨0, positive⟩ : Fin size) < i by
      change 0 < i.val
      omega)).le

private theorem rowAt_zero_le
    {indexGrid : Nat -> Nat -> Index} {shadeGrid : Nat -> Nat -> RedShades.State}
    {west east south north size : Nat}
    (grid : FreeGrid indexGrid shadeGrid west east south north size)
    (positive : 0 < size) (i : Fin size) :
    grid.rowAt ⟨0, positive⟩ ≤ grid.rowAt i := by
  by_cases hi : i = ⟨0, positive⟩
  · rw [hi]
  · have hval : i.val ≠ 0 := by
      intro hzero
      exact hi (Fin.ext hzero)
    exact (grid.row_strictMono (show (⟨0, positive⟩ : Fin size) < i by
      change 0 < i.val
      omega)).le

noncomputable def ConsecutiveMarkedFreeGrid.ofMarked
    {indexGrid : Nat -> Nat -> Index} {shadeGrid : Nat -> Nat -> RedShades.State}
    {west east south north size : Nat}
    (marked : MarkedFreeGrid indexGrid shadeGrid west east south north size) :
    ConsecutiveMarkedFreeGrid indexGrid shadeGrid west east south north size := by
  let zero : Fin size := ⟨0, marked.positive⟩
  let markerColumn := marked.grid.columnAt zero
  let markerRow := marked.grid.rowAt zero
  let columns := (freeColumns indexGrid shadeGrid west east south north).filter
    (markerColumn ≤ ·)
  let rows := (freeRows indexGrid shadeGrid west east south north).filter
    (markerRow ≤ ·)
  have column_mem (i : Fin size) : marked.grid.columnAt i ∈ columns := by
    simp only [columns, Finset.mem_filter, mem_freeColumns_iff]
    exact ⟨⟨marked.grid.column_west i, marked.grid.column_east i,
      marked.grid.freeColumn i⟩,
      columnAt_zero_le marked.grid marked.positive i⟩
  have row_mem (i : Fin size) : marked.grid.rowAt i ∈ rows := by
    simp only [rows, Finset.mem_filter, mem_freeRows_iff]
    exact ⟨⟨marked.grid.row_south i, marked.grid.row_north i,
      marked.grid.freeRow i⟩,
      rowAt_zero_le marked.grid marked.positive i⟩
  have hcolumns : size ≤ columns.card := by
    let embed : Fin size -> {column // column ∈ columns} :=
      fun i => ⟨marked.grid.columnAt i, column_mem i⟩
    have hinjective : Function.Injective embed := by
      intro i j heq
      apply Fin.ext
      by_contra hij
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (Nat.ne_of_lt (marked.grid.column_strictMono hij))
          (congrArg Subtype.val heq)
      · exact (Nat.ne_of_lt (marked.grid.column_strictMono hji))
          (congrArg Subtype.val heq).symm
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective embed hinjective
  have hrows : size ≤ rows.card := by
    let embed : Fin size -> {row // row ∈ rows} :=
      fun i => ⟨marked.grid.rowAt i, row_mem i⟩
    have hinjective : Function.Injective embed := by
      intro i j heq
      apply Fin.ext
      by_contra hij
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (Nat.ne_of_lt (marked.grid.row_strictMono hij))
          (congrArg Subtype.val heq)
      · exact (Nat.ne_of_lt (marked.grid.row_strictMono hji))
          (congrArg Subtype.val heq).symm
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective embed hinjective
  let selectedColumns := OrderedPrefix.ofCardLE columns size hcolumns
  let selectedRows := OrderedPrefix.ofCardLE rows size hrows
  have hmarkerColumn : markerColumn ∈ columns := column_mem zero
  have hmarkerRow : markerRow ∈ rows := row_mem zero
  have hcolumnZero : selectedColumns.coord zero = markerColumn :=
    selectedColumns.at_zero_eq marked.positive hmarkerColumn (by
      intro k hk
      exact (Finset.mem_filter.1 hk).2)
  have hrowZero : selectedRows.coord zero = markerRow :=
    selectedRows.at_zero_eq marked.positive hmarkerRow (by
      intro k hk
      exact (Finset.mem_filter.1 hk).2)
  refine {
    columnAt := selectedColumns.coord
    rowAt := selectedRows.coord
    column_strictMono := fun {_ _} h => selectedColumns.strictMono h
    row_strictMono := fun {_ _} h => selectedRows.strictMono h
    column_west := ?_
    column_east := ?_
    row_south := ?_
    row_north := ?_
    freeColumn := ?_
    freeRow := ?_
    positive := marked.positive
    noFreeColumnBetween := ?_
    noFreeRowBetween := ?_
    lowerLeftMarker := ?_ }
  · intro i
    exact (mem_freeColumns_iff.1 (Finset.mem_filter.1
      (selectedColumns.mem_coord i)).1).1
  · intro i
    exact (mem_freeColumns_iff.1 (Finset.mem_filter.1
      (selectedColumns.mem_coord i)).1).2.1
  · intro i
    exact (mem_freeRows_iff.1 (Finset.mem_filter.1
      (selectedRows.mem_coord i)).1).1
  · intro i
    exact (mem_freeRows_iff.1 (Finset.mem_filter.1
      (selectedRows.mem_coord i)).1).2.1
  · intro i
    exact (mem_freeColumns_iff.1 (Finset.mem_filter.1
      (selectedColumns.mem_coord i)).1).2.2
  · intro i
    exact (mem_freeRows_iff.1 (Finset.mem_filter.1
      (selectedRows.mem_coord i)).1).2.2
  · intro i hi k hik hki hfree
    apply selectedColumns.no_mem_between i hi k hik hki
    simp only [columns, Finset.mem_filter, mem_freeColumns_iff]
    refine ⟨⟨?_, ?_, hfree⟩, ?_⟩
    · exact (mem_freeColumns_iff.1 (Finset.mem_filter.1
        (selectedColumns.mem_coord i)).1).1.trans_le hik.le
    · exact hki.trans (mem_freeColumns_iff.1 (Finset.mem_filter.1
        (selectedColumns.mem_coord ⟨i.val + 1, hi⟩)).1).2.1
    · exact (Finset.mem_filter.1 (selectedColumns.mem_coord i)).2.trans hik.le
  · intro i hi k hik hki hfree
    apply selectedRows.no_mem_between i hi k hik hki
    simp only [rows, Finset.mem_filter, mem_freeRows_iff]
    refine ⟨⟨?_, ?_, hfree⟩, ?_⟩
    · exact (mem_freeRows_iff.1 (Finset.mem_filter.1
        (selectedRows.mem_coord i)).1).1.trans_le hik.le
    · exact hki.trans (mem_freeRows_iff.1 (Finset.mem_filter.1
        (selectedRows.mem_coord ⟨i.val + 1, hi⟩)).1).2.1
    · exact (Finset.mem_filter.1 (selectedRows.mem_coord i)).2.trans hik.le
  · simpa only [hcolumnZero, hrowZero, markerColumn, markerRow, zero] using
      marked.lowerLeftMarker

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int -> TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

/-- Arbitrarily large complete consecutive free grids, retaining their light board. -/
theorem unboundedConsecutiveMarkedFreeGrid_with_light
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int)
    (root : (ShadedPlaneShadeGrid.coarseGrid decoded
      (2 * (1 + size) + 2) coarseOrigin) 0 0 = 0) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    (CycleOn (iterateRefine (level + 2) coarse)
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) ∧
      CycleShade state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) .light ∧
      Nonempty (ConsecutiveMarkedFreeGrid
        (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2))) ∨
      (CycleOn (iterateRefine (level + 2) coarse)
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) ∧
        CycleShade state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) .light ∧
        Nonempty (ConsecutiveMarkedFreeGrid
          (iterateRefine (level + 2) coarse) state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1))) := by
  rcases SparseFreeLineDecodedMarkedGrid.unboundedMarkedFreeGrid_with_light
      decoded size coarseOrigin root with
    ⟨cycle, shaded, marked⟩ | ⟨cycle, shaded, marked⟩
  · rcases marked with ⟨marked⟩
    exact Or.inl ⟨cycle, shaded, ⟨ConsecutiveMarkedFreeGrid.ofMarked marked⟩⟩
  · rcases marked with ⟨marked⟩
    exact Or.inr ⟨cycle, shaded, ⟨ConsecutiveMarkedFreeGrid.ofMarked marked⟩⟩

/-- Arbitrarily large complete consecutive free grids in a decoded plane. -/
theorem unboundedConsecutiveMarkedFreeGrid
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int)
    (root : (ShadedPlaneShadeGrid.coarseGrid decoded
      (2 * (1 + size) + 2) coarseOrigin) 0 0 = 0) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    Nonempty (ConsecutiveMarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2)) ∨
      Nonempty (ConsecutiveMarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1)) := by
  rcases unboundedConsecutiveMarkedFreeGrid_with_light
      decoded size coarseOrigin root with
    ⟨_, _, grid⟩ | ⟨_, _, grid⟩
  · exact Or.inl grid
  · exact Or.inr grid

end ShadedConsecutiveFreeGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
