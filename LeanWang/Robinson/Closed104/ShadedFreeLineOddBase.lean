/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedFreeLineOddBaseComplete
import LeanWang.Robinson.Closed104.ShadedFreeLineRecurrence

/-! Proposition-level odd-phase base for the free-line recurrence. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedFreeLineOddBase

open RedCycles OrientedRedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphBoards RedShadeCrossingBoards
  RedShadePaths RedShadeGraphRefinement RedShadeGraphTranslation
  RefinementTranslation ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineOffsets
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
    ∃ node ∈ nodes parent, verticalReached parent offset quarterX node = true := by
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
    ∃ node ∈ nodes parent, horizontalReached parent offset quarterY node = true := by
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

theorem liveRowCertificate (parent : Index) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 0) :
    LiveRowCertificate (localGrid parent) 2 6 2 6 (5 + 2 * offset) := by
  intro quarterX hwest heast hinterior
  have hwest' : 5 < quarterX := by simpa [quarterWest] using hwest
  have heast' : quarterX < 12 := by simpa [quarterEast] using heast
  rcases vertical_node_exists parent hoffset hwest' heast' hinterior with
    ⟨node, hnode, hreached⟩
  have sound := exploreFast_sound hnode
  have onCycle := onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn (localGrid parent) 2 6 2 6 := by
    simpa [localGrid] using largeCycle (fun _ _ => parent) 1
  simp only [verticalReached, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hreached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := onCycle
    path := sound.2
    startLive := portPresent_of_onCycle cycle onCycle
    portLive := hreached.1.2
  }, hreached.1.1, hreached.2⟩

theorem liveColumnCertificate (parent : Index) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 0) :
    LiveColumnCertificate (localGrid parent) 2 6 2 6 (5 + 2 * offset) := by
  intro quarterY hsouth hnorth hinterior
  have hsouth' : 5 < quarterY := by simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 12 := by simpa [quarterNorth] using hnorth
  rcases horizontal_node_exists parent hoffset hsouth' hnorth' hinterior with
    ⟨node, hnode, hreached⟩
  have sound := exploreFast_sound hnode
  have onCycle := onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn (localGrid parent) 2 6 2 6 := by
    simpa [localGrid] using largeCycle (fun _ _ => parent) 1
  simp only [horizontalReached, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hreached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := onCycle
    path := sound.2
    startLive := portPresent_of_onCycle cycle onCycle
    portLive := hreached.1.2
  }, hreached.1.1, hreached.2⟩

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
    exact hreached.1.1 ▸ sound.2
  · right
    rw [← hnorth]
    exact hreached.1.1 ▸ sound.2

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
    exact hreached.1.1 ▸ sound.2
  · right
    rw [← heast]
    exact hreached.1.1 ▸ sound.2

theorem boardPorts_inBounds {port : Port} (hport : port ∈ boardPorts) :
    PortInBounds port 16 16 := by
  rw [boardPorts, List.mem_flatMap] at hport
  rcases hport with ⟨offset, hoffset, hport⟩
  simp only [List.mem_range] at hoffset
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PortInBounds] <;> omega

theorem componentAt_localGrid_eq_shift
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {parent : Index} (hparent : grid blockX blockY = parent)
    {quarterX quarterY : Nat} (hx : quarterX < 16) (hy : quarterY < 16) :
    componentAt (localGrid parent) quarterX quarterY =
      componentAt (iterateRefine 3 (shiftGrid grid blockX blockY))
        quarterX quarterY := by
  have hlocal := componentAt_shift_eq_constant 3 grid blockX blockY
    quarterX quarterY (by norm_num; exact hx) (by norm_num; exact hy)
  rw [hparent] at hlocal
  exact hlocal.symm

theorem portPresent_localGrid_eq_shift
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {parent : Index} (hparent : grid blockX blockY = parent)
    (port : Port) (hport : PortInBounds port 16 16) :
    portPresent (localGrid parent) port =
      portPresent (iterateRefine 3 (shiftGrid grid blockX blockY)) port := by
  rcases port with ⟨x, y, side⟩
  cases side <;> simp only [portPresent] <;>
    rw [componentAt_localGrid_eq_shift grid blockX blockY hparent
      hport.1 hport.2]

/-- The checked odd live row certificate in an arbitrary refined coarse block. -/
theorem liveRowCertificate_shift (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {parent : Index}
    (hparent : grid blockX blockY = parent) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 0) :
    LiveRowCertificate (iterateRefine 3 (shiftGrid grid blockX blockY))
      2 6 2 6 (5 + 2 * offset) := by
  intro quarterX hwest heast hinterior
  have hwest' : 5 < quarterX := by simpa [quarterWest] using hwest
  have heast' : quarterX < 12 := by simpa [quarterEast] using heast
  have hoffsetBounds : offset < 3 := by
    norm_num [freeOffsets, extendedOffsets] at hoffset
    omega
  have hcomponent : componentAt (localGrid parent) quarterX (5 + 2 * offset) =
      componentAt (iterateRefine 3 (shiftGrid grid blockX blockY))
        quarterX (5 + 2 * offset) :=
    componentAt_localGrid_eq_shift grid blockX blockY hparent
      (by omega) (by omega)
  have hinteriorLocal : Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX (5 + 2 * offset))
      (quadrantAt quarterX (5 + 2 * offset)) ≠ none := by
    rwa [hcomponent]
  rcases vertical_node_exists parent hoffset hwest' heast' hinteriorLocal with
    ⟨node, hnode, hreached⟩
  have sound := exploreFast_bounded_sound
    (fun port hport => boardPorts_inBounds hport) hnode
  have componentsEq : ∀ x y, x < 16 → y < 16 →
      componentAt (localGrid parent) x y =
        componentAt (iterateRefine 3 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact componentAt_localGrid_eq_shift grid blockX blockY hparent hx hy
  have path := BoundedPath.congr_of_component_eq componentsEq sound.2
  have honCycle := onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn
      (iterateRefine 3 (shiftGrid grid blockX blockY)) 2 6 2 6 := by
    simpa using largeCycle (shiftGrid grid blockX blockY) 1
  simp only [verticalReached, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hreached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := honCycle
    path := path.path
    startLive := portPresent_of_onCycle cycle honCycle
    portLive := ?_
  }, hreached.1.1, hreached.2⟩
  rw [← portPresent_localGrid_eq_shift grid blockX blockY hparent
    node.current path.second_inBounds]
  exact hreached.1.2

/-- The checked odd live column certificate in an arbitrary refined coarse block. -/
theorem liveColumnCertificate_shift (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {parent : Index}
    (hparent : grid blockX blockY = parent) {offset : Nat}
    (hoffset : offset ∈ freeOffsets 0) :
    LiveColumnCertificate (iterateRefine 3 (shiftGrid grid blockX blockY))
      2 6 2 6 (5 + 2 * offset) := by
  intro quarterY hsouth hnorth hinterior
  have hsouth' : 5 < quarterY := by simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 12 := by simpa [quarterNorth] using hnorth
  have hoffsetBounds : offset < 3 := by
    norm_num [freeOffsets, extendedOffsets] at hoffset
    omega
  have hcomponent : componentAt (localGrid parent) (5 + 2 * offset) quarterY =
      componentAt (iterateRefine 3 (shiftGrid grid blockX blockY))
        (5 + 2 * offset) quarterY :=
    componentAt_localGrid_eq_shift grid blockX blockY hparent
      (by omega) (by omega)
  have hinteriorLocal : Signals.horizontalInterior?
      (componentAt (localGrid parent) (5 + 2 * offset) quarterY)
      (quadrantAt (5 + 2 * offset) quarterY) ≠ none := by
    rwa [hcomponent]
  rcases horizontal_node_exists parent hoffset hsouth' hnorth' hinteriorLocal with
    ⟨node, hnode, hreached⟩
  have sound := exploreFast_bounded_sound
    (fun port hport => boardPorts_inBounds hport) hnode
  have componentsEq : ∀ x y, x < 16 → y < 16 →
      componentAt (localGrid parent) x y =
        componentAt (iterateRefine 3 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact componentAt_localGrid_eq_shift grid blockX blockY hparent hx hy
  have path := BoundedPath.congr_of_component_eq componentsEq sound.2
  have honCycle := onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn
      (iterateRefine 3 (shiftGrid grid blockX blockY)) 2 6 2 6 := by
    simpa using largeCycle (shiftGrid grid blockX blockY) 1
  simp only [horizontalReached, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hreached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := honCycle
    path := path.path
    startLive := portPresent_of_onCycle cycle honCycle
    portLive := ?_
  }, hreached.1.1, hreached.2⟩
  rw [← portPresent_localGrid_eq_shift grid blockX blockY hparent
    node.current path.second_inBounds]
  exact hreached.1.2

/-- The odd base also retains its graph paths for recursive refinement. -/
theorem graphHolds_odd_zero : GraphHolds .odd 0 := by
  intro parent
  constructor
  · intro offset mem
    simpa [ShadedFreeLineRecurrence.localGrid, localGrid,
      refinementDepth, Phase.extra, west, east, scale, Phase.factor,
      lineCoordinate, quarterStart, quarterWest] using
      liveRowCertificate parent mem
  · intro offset mem
    simpa [ShadedFreeLineRecurrence.localGrid, localGrid,
      refinementDepth, Phase.extra, west, east, scale, Phase.factor,
      lineCoordinate, quarterStart, quarterWest] using
      liveColumnCertificate parent mem

/-- The two checked lines establish the minimal odd-scale recurrence base. -/
theorem holds_odd_zero : Holds .odd 0 :=
  holds_of_graphHolds graphHolds_odd_zero

end ShadedFreeLineOddBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
