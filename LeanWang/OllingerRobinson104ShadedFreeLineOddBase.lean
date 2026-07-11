/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedFreeLineOddBaseComplete
import LeanWang.OllingerRobinson104ShadedFreeLineRecurrence

/-! Proposition-level odd-phase base for the free-line recurrence. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineOddBase

open RedCycles OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphBoards RedShadeCrossingBoards
  RedShadePaths ShadedFreeLineGraph ShadedFreeLineOffsets
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid Signals.FreeCellLocal

set_option maxRecDepth 100000

theorem onCycle_of_mem_boardPorts {port : Port} (hport : port ∈ boardPorts) :
    OnCycle 2 6 2 6 port := by
  rw [boardPorts, List.mem_flatMap] at hport
  rcases hport with ⟨offset, hoffset, hport⟩
  simp only [List.mem_range] at hoffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OnCycle.southWest _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.southEast _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.northWest _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.northEast _ (by simp [quarterWest]; omega)
      (by simp [quarterEast]; omega)
  · exact OnCycle.westSouth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)
  · exact OnCycle.westNorth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)
  · exact OnCycle.eastSouth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)
  · exact OnCycle.eastNorth _ (by simp [quarterSouth]; omega)
      (by simp [quarterNorth]; omega)

theorem vertical_node_exists (parent : Index) {offset quarterX : Nat}
    (hoffset : offset ∈ freeOffsets 0)
    (hwest : 5 < quarterX) (heast : quarterX < 12)
    (hinterior : Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX (5 + 2 * offset))
      (quadrantAt quarterX (5 + 2 * offset)) ≠ none) :
    ∃ node ∈ nodes parent, verticalReached offset quarterX node = true := by
  have hcomplete := completeFor_eq_true parent
  simp only [completeFor, List.all_eq_true] at hcomplete
  have hoffsetComplete := hcomplete offset hoffset
  let delta := quarterX - 6
  have hdelta : delta ∈ List.range 6 := by simp [delta]; omega
  have hcoordinate : 6 + delta = quarterX := by simp [delta]; omega
  have hcase := hoffsetComplete delta hdelta
  rw [hcoordinate] at hcase
  cases hvalue : Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX (5 + 2 * offset))
      (quadrantAt quarterX (5 + 2 * offset)) with
  | none => contradiction
  | some interior =>
      simp only [hvalue, Option.isSome_some, if_true, Bool.and_eq_true] at hcase
      simpa only [List.any_eq_true] using hcase.1

theorem horizontal_node_exists (parent : Index) {offset quarterY : Nat}
    (hoffset : offset ∈ freeOffsets 0)
    (hsouth : 5 < quarterY) (hnorth : quarterY < 12)
    (hinterior : Signals.horizontalInterior?
      (componentAt (localGrid parent) (5 + 2 * offset) quarterY)
      (quadrantAt (5 + 2 * offset) quarterY) ≠ none) :
    ∃ node ∈ nodes parent, horizontalReached offset quarterY node = true := by
  have hcomplete := completeFor_eq_true parent
  simp only [completeFor, List.all_eq_true] at hcomplete
  have hoffsetComplete := hcomplete offset hoffset
  let delta := quarterY - 6
  have hdelta : delta ∈ List.range 6 := by simp [delta]; omega
  have hcoordinate : 6 + delta = quarterY := by simp [delta]; omega
  have hcase := hoffsetComplete delta hdelta
  rw [hcoordinate] at hcase
  cases hvalue : Signals.horizontalInterior?
      (componentAt (localGrid parent) (5 + 2 * offset) quarterY)
      (quadrantAt (5 + 2 * offset) quarterY) with
  | none => contradiction
  | some interior =>
      simp only [hvalue, Option.isSome_some, if_true, Bool.and_eq_true] at hcase
      simpa only [List.any_eq_true] using hcase.2

theorem rowCertificate (parent : Index) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 0) :
    RowCertificate (localGrid parent) 2 6 2 6 (5 + 2 * offset) := by
  intro quarterX hwest heast hinterior
  have hwest' : 5 < quarterX := by simpa [quarterWest] using hwest
  have heast' : quarterX < 12 := by simpa [quarterEast] using heast
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
    (hoffset : offset ∈ freeOffsets 0) :
    ColumnCertificate (localGrid parent) 2 6 2 6 (5 + 2 * offset) := by
  intro quarterY hsouth hnorth hinterior
  have hsouth' : 5 < quarterY := by simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 12 := by simpa [quarterNorth] using hnorth
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

/-- The odd base also retains its graph paths for recursive refinement. -/
theorem graphHolds_odd_zero : GraphHolds .odd 0 := by
  intro parent
  constructor
  · intro offset mem
    simpa [ShadedFreeLineRecurrence.localGrid, localGrid,
      refinementDepth, Phase.extra, west, east, scale, Phase.factor,
      lineCoordinate, quarterStart, quarterWest] using
      rowCertificate parent mem
  · intro offset mem
    simpa [ShadedFreeLineRecurrence.localGrid, localGrid,
      refinementDepth, Phase.extra, west, east, scale, Phase.factor,
      lineCoordinate, quarterStart, quarterWest] using
      columnCertificate parent mem

/-- The two checked lines establish the minimal odd-scale recurrence base. -/
theorem holds_odd_zero : Holds .odd 0 :=
  holds_of_graphHolds graphHolds_odd_zero

end ShadedFreeLineOddBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
