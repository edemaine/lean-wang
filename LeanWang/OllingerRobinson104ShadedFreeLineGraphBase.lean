/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphSearchSoundness
import LeanWang.OllingerRobinson104ShadedFreeLineGraph
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBaseComplete

/-!
Finite graph certificates for all six first-level Figure 18 free offsets.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineGraphBase

open RedCycles OrientedRedBoardTranslations RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphBoards RedShadeCycles
  RedShadePaths ShadedFreeLineGraph ShadedFreeGrid
  ShadedFreeLineOffsets Signals.FreeCellLocal

set_option maxRecDepth 100000

theorem onCycle_of_mem_boardPorts {port : Port} (hport : port ∈ boardPorts) :
    OnCycle 4 12 4 12 port := by
  rw [boardPorts, List.mem_flatMap] at hport
  rcases hport with ⟨offset, hoffset, hport⟩
  simp only [List.mem_range] at hoffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OnCycle.southWest _ (by simp [quarterWest]; omega) (by simp [quarterEast]; omega)
  · exact OnCycle.southEast _ (by simp [quarterWest]; omega) (by simp [quarterEast]; omega)
  · exact OnCycle.northWest _ (by simp [quarterWest]; omega) (by simp [quarterEast]; omega)
  · exact OnCycle.northEast _ (by simp [quarterWest]; omega) (by simp [quarterEast]; omega)
  · exact OnCycle.westSouth _ (by simp [quarterSouth]; omega) (by simp [quarterNorth]; omega)
  · exact OnCycle.westNorth _ (by simp [quarterSouth]; omega) (by simp [quarterNorth]; omega)
  · exact OnCycle.eastSouth _ (by simp [quarterSouth]; omega) (by simp [quarterNorth]; omega)
  · exact OnCycle.eastNorth _ (by simp [quarterSouth]; omega) (by simp [quarterNorth]; omega)

theorem vertical_node_exists (parent : Index) {offset quarterX : Nat}
    (hoffset : offset ∈ freeOffsets 1)
    (hwest : 9 < quarterX) (heast : quarterX < 24)
    (hinterior : Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX (9 + offset))
      (quadrantAt quarterX (9 + offset)) ≠ none) :
    ∃ node ∈ nodes parent, verticalReached offset quarterX node = true := by
  have hcomplete := completeFor_eq_true parent
  simp only [completeFor, List.all_eq_true] at hcomplete
  have hoffsetComplete := hcomplete offset hoffset
  let delta := quarterX - 10
  have hdelta : delta ∈ List.range 14 := by
    simp [delta]
    omega
  have hcoordinate : 10 + delta = quarterX := by
    simp [delta]
    omega
  have hcase := hoffsetComplete delta hdelta
  rw [hcoordinate] at hcase
  cases hvalue : Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX (9 + offset))
      (quadrantAt quarterX (9 + offset)) with
  | none => contradiction
  | some interior =>
      simp only [hvalue, Option.isSome_some, if_true, Bool.and_eq_true] at hcase
      simpa only [List.any_eq_true] using hcase.1

theorem horizontal_node_exists (parent : Index) {offset quarterY : Nat}
    (hoffset : offset ∈ freeOffsets 1)
    (hsouth : 9 < quarterY) (hnorth : quarterY < 24)
    (hinterior : Signals.horizontalInterior?
      (componentAt (localGrid parent) (9 + offset) quarterY)
      (quadrantAt (9 + offset) quarterY) ≠ none) :
    ∃ node ∈ nodes parent, horizontalReached offset quarterY node = true := by
  have hcomplete := completeFor_eq_true parent
  simp only [completeFor, List.all_eq_true] at hcomplete
  have hoffsetComplete := hcomplete offset hoffset
  let delta := quarterY - 10
  have hdelta : delta ∈ List.range 14 := by
    simp [delta]
    omega
  have hcoordinate : 10 + delta = quarterY := by
    simp [delta]
    omega
  have hcase := hoffsetComplete delta hdelta
  rw [hcoordinate] at hcase
  cases hvalue : Signals.horizontalInterior?
      (componentAt (localGrid parent) (9 + offset) quarterY)
      (quadrantAt (9 + offset) quarterY) with
  | none => contradiction
  | some interior =>
      simp only [hvalue, Option.isSome_some, if_true, Bool.and_eq_true] at hcase
      simpa only [List.any_eq_true] using hcase.2

theorem rowCertificate (parent : Index) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 1) :
    RowCertificate (localGrid parent) 4 12 4 12 (9 + offset) := by
  intro quarterX hwest heast hinterior
  have hwest' : 9 < quarterX := by simpa [quarterWest] using hwest
  have heast' : quarterX < 24 := by simpa [quarterEast] using heast
  rcases vertical_node_exists parent hoffset hwest' heast' hinterior with
    ⟨node, hnode, hreached⟩
  have sound := exploreFast_sound hnode
  have honCycle := onCycle_of_mem_boardPorts sound.1
  simp only [verticalReached, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hreached
  refine ⟨node.origin, honCycle, ?_⟩
  rcases hreached.2 with hsouth | hnorth
  · left
    rw [← hsouth]
    exact hreached.1 ▸ sound.2
  · right
    rw [← hnorth]
    exact hreached.1 ▸ sound.2

theorem columnCertificate (parent : Index) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 1) :
    ColumnCertificate (localGrid parent) 4 12 4 12 (9 + offset) := by
  intro quarterY hsouth hnorth hinterior
  have hsouth' : 9 < quarterY := by simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 24 := by simpa [quarterNorth] using hnorth
  rcases horizontal_node_exists parent hoffset hsouth' hnorth' hinterior with
    ⟨node, hnode, hreached⟩
  have sound := exploreFast_sound hnode
  have honCycle := onCycle_of_mem_boardPorts sound.1
  simp only [horizontalReached, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hreached
  refine ⟨node.origin, honCycle, ?_⟩
  rcases hreached.2 with hwest | heast
  · left
    rw [← hwest]
    exact hreached.1 ▸ sound.2
  · right
    rw [← heast]
    exact hreached.1 ▸ sound.2

def offsetAt (index : Fin 6) : Nat :=
  (freeOffsets 1).get ⟨index.val, by simp [freeOffsets_length, index.isLt]⟩

theorem offsetAt_mem (index : Fin 6) : offsetAt index ∈ freeOffsets 1 :=
  List.get_mem _ _

set_option linter.style.nativeDecide false in
theorem offsetAt_strictMono {first second : Fin 6} (hlt : first < second) :
    offsetAt first < offsetAt second := by
  revert first second
  native_decide

set_option linter.style.nativeDecide false in
theorem offsetAt_bounds (index : Fin 6) :
    0 < offsetAt index ∧ offsetAt index < 15 := by
  revert index
  native_decide

/-- All six audited offsets are free in a valid light canonical board. -/
def freeGrid (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (shaded : CycleShade stateGrid 4 12 4 12 .light) :
    FreeGrid (localGrid parent) stateGrid 4 12 4 12 6 where
  columnAt := fun index => 9 + offsetAt index
  rowAt := fun index => 9 + offsetAt index
  column_strictMono := by
    intro first second hlt
    exact Nat.add_lt_add_left (offsetAt_strictMono hlt) 9
  row_strictMono := by
    intro first second hlt
    exact Nat.add_lt_add_left (offsetAt_strictMono hlt) 9
  column_west := by
    intro index
    have := (offsetAt_bounds index).1
    simp [quarterWest]
    omega
  column_east := by
    intro index
    have := (offsetAt_bounds index).2
    simp [quarterEast]
    omega
  row_south := by
    intro index
    have := (offsetAt_bounds index).1
    simp [quarterSouth]
    omega
  row_north := by
    intro index
    have := (offsetAt_bounds index).2
    simp [quarterNorth]
    omega
  freeColumn := by
    intro index
    let cycle := at_scale (fun _ _ => parent) 2 0 0
    exact isFreeColumn_of_certificate valid cycle shaded
      (columnCertificate parent (offsetAt_mem index))
  freeRow := by
    intro index
    let cycle := at_scale (fun _ _ => parent) 2 0 0
    exact isFreeRow_of_certificate valid cycle shaded
      (rowCertificate parent (offsetAt_mem index))

/-- Drop the two southwest audited lines, placing the marker at index zero. -/
def cornerGridIndex (index : Fin 4) : Fin 6 :=
  ⟨index.val + 2, by omega⟩

/-- The northeast `4 x 4` suffix of the parent-0 grid starts at the marker. -/
def cornerFreeGrid
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid 0) stateGrid)
    (shaded : CycleShade stateGrid 4 12 4 12 .light) :
    FreeGrid (localGrid 0) stateGrid 4 12 4 12 4 :=
  let full := freeGrid 0 valid shaded
  { columnAt := fun index => full.columnAt (cornerGridIndex index)
    rowAt := fun index => full.rowAt (cornerGridIndex index)
    column_strictMono := by
      intro first second hlt
      apply full.column_strictMono
      simp [cornerGridIndex]
      omega
    row_strictMono := by
      intro first second hlt
      apply full.row_strictMono
      simp [cornerGridIndex]
      omega
    column_west := fun index => full.column_west (cornerGridIndex index)
    column_east := fun index => full.column_east (cornerGridIndex index)
    row_south := fun index => full.row_south (cornerGridIndex index)
    row_north := fun index => full.row_north (cornerGridIndex index)
    freeColumn := fun index => full.freeColumn (cornerGridIndex index)
    freeRow := fun index => full.freeRow (cornerGridIndex index) }

set_option linter.style.nativeDecide false in
theorem cornerFreeGrid_lowerLeft_quarter :
    (localGrid 0
        ((9 + offsetAt (cornerGridIndex 0)) / 2)
        ((9 + offsetAt (cornerGridIndex 0)) / 2),
      quadrantAt
        (9 + offsetAt (cornerGridIndex 0))
        (9 + offsetAt (cornerGridIndex 0))) = Signals.cornerQuarter := by
  native_decide

set_option linter.style.nativeDecide false in
@[simp] theorem cornerFreeGrid_lowerLeft_coordinate
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid 0) stateGrid)
    (shaded : CycleShade stateGrid 4 12 4 12 .light) :
    (cornerFreeGrid valid shaded).columnAt 0 = 16 ∧
      (cornerFreeGrid valid shaded).rowAt 0 = 16 := by
  change 9 + offsetAt (cornerGridIndex 0) = 16 ∧
    9 + offsetAt (cornerGridIndex 0) = 16
  native_decide

end ShadedFreeLineGraphBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
