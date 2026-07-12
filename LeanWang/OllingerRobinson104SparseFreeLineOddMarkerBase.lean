/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104SparseFreeLineOddMarkerBaseComplete
import LeanWang.OllingerRobinson104ShadedFreeLineOddBase

/-! Soundness of the finite odd-phase center-marker audit. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineOddMarkerBase

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearch
  RedShadeGraphSearchSoundness RedShadeGraphRefinement RedShadeGraphTranslation
  RefinementTranslation
  ShadedFreeLineGraph ShadedFreeLinePatternRefinement
  ShadedFreeLineOddBase SparseFreeLineOddMarkerBaseAudit
  Signals.FreeCellLocal

set_option maxRecDepth 100000

theorem vertical_node_exists (parent : Index) {quarterX : Nat}
    (hwest : 5 < quarterX) (heast : quarterX < 12)
    (interior : Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX 8)
      (quadrantAt quarterX 8) ≠ none) :
    ∃ node ∈ nodes parent, verticalReached parent quarterX node = true := by
  have checked := SparseFreeLineOddMarkerBaseAudit.completeFor_eq_true parent
  simp only [SparseFreeLineOddMarkerBaseAudit.completeFor,
    List.all_eq_true, List.mem_range] at checked
  let delta := quarterX - 6
  have hdelta : delta < 6 := by simp [delta]; omega
  have hcoordinate : 6 + delta = quarterX := by simp [delta]; omega
  have covered := checked delta hdelta
  simp only [Bool.and_eq_true] at covered
  have covered := covered.1
  rw [hcoordinate] at covered
  have required : (Signals.verticalInterior?
      (componentAt (localGrid parent) quarterX 8)
      (quadrantAt quarterX 8)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, if_true, List.any_eq_true] at covered
  exact covered

theorem horizontal_node_exists (parent : Index) {quarterY : Nat}
    (hsouth : 5 < quarterY) (hnorth : quarterY < 12)
    (interior : Signals.horizontalInterior?
      (componentAt (localGrid parent) 8 quarterY)
      (quadrantAt 8 quarterY) ≠ none) :
    ∃ node ∈ nodes parent, horizontalReached parent quarterY node = true := by
  have checked := SparseFreeLineOddMarkerBaseAudit.completeFor_eq_true parent
  simp only [SparseFreeLineOddMarkerBaseAudit.completeFor,
    List.all_eq_true, List.mem_range] at checked
  let delta := quarterY - 6
  have hdelta : delta < 6 := by simp [delta]; omega
  have hcoordinate : 6 + delta = quarterY := by simp [delta]; omega
  have covered := checked delta hdelta
  simp only [Bool.and_eq_true] at covered
  have covered := covered.2
  rw [hcoordinate] at covered
  have required : (Signals.horizontalInterior?
      (componentAt (localGrid parent) 8 quarterY)
      (quadrantAt 8 quarterY)).isSome = true :=
    Option.isSome_iff_ne_none.mpr interior
  simp only [required, if_true, List.any_eq_true] at covered
  exact covered

theorem liveRowCertificate (parent : Index) :
    LiveRowCertificate (localGrid parent) 2 6 2 6 8 := by
  intro quarterX hwest heast interior
  have hwest' : 5 < quarterX := by simpa [quarterWest] using hwest
  have heast' : quarterX < 12 := by simpa [quarterEast] using heast
  rcases vertical_node_exists parent hwest' heast' interior with
    ⟨node, hnode, reached⟩
  have sound := exploreFast_sound hnode
  have onCycle := ShadedFreeLineOddBase.onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn (localGrid parent) 2 6 2 6 := by
    simpa [ShadedFreeLineOddBase.localGrid] using RedShadeCrossingBoards.largeCycle
      (fun _ _ => parent) 1
  simp only [SparseFreeLineOddMarkerBaseAudit.verticalReached,
    Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at reached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := onCycle
    path := sound.2
    startLive := portPresent_of_onCycle cycle onCycle
    portLive := reached.1.2
  }, reached.1.1, reached.2⟩

theorem liveColumnCertificate (parent : Index) :
    LiveColumnCertificate (localGrid parent) 2 6 2 6 8 := by
  intro quarterY hsouth hnorth interior
  have hsouth' : 5 < quarterY := by simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 12 := by simpa [quarterNorth] using hnorth
  rcases horizontal_node_exists parent hsouth' hnorth' interior with
    ⟨node, hnode, reached⟩
  have sound := exploreFast_sound hnode
  have onCycle := ShadedFreeLineOddBase.onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn (localGrid parent) 2 6 2 6 := by
    simpa [ShadedFreeLineOddBase.localGrid] using RedShadeCrossingBoards.largeCycle
      (fun _ _ => parent) 1
  simp only [SparseFreeLineOddMarkerBaseAudit.horizontalReached,
    Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at reached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := onCycle
    path := sound.2
    startLive := portPresent_of_onCycle cycle onCycle
    portLive := reached.1.2
  }, reached.1.1, reached.2⟩

theorem liveRowCertificate_shift (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {parent : Index}
    (hparent : grid blockX blockY = parent) :
    LiveRowCertificate (iterateRefine 3 (shiftGrid grid blockX blockY))
      2 6 2 6 8 := by
  intro quarterX hwest heast interior
  have hwest' : 5 < quarterX := by simpa [quarterWest] using hwest
  have heast' : quarterX < 12 := by simpa [quarterEast] using heast
  have hcomponent : componentAt (ShadedFreeLineOddBase.localGrid parent)
      quarterX 8 = componentAt
        (iterateRefine 3 (shiftGrid grid blockX blockY)) quarterX 8 :=
    ShadedFreeLineOddBase.componentAt_localGrid_eq_shift
      grid blockX blockY hparent (by omega) (by omega)
  have localInterior : Signals.verticalInterior?
      (componentAt (ShadedFreeLineOddBase.localGrid parent) quarterX 8)
      (quadrantAt quarterX 8) ≠ none := by
    rwa [hcomponent]
  rcases vertical_node_exists parent hwest' heast' localInterior with
    ⟨node, hnode, reached⟩
  have sound := exploreFast_bounded_sound
    (fun port hport => ShadedFreeLineOddBase.boardPorts_inBounds hport) hnode
  have same : ∀ x y, x < 16 → y < 16 →
      componentAt (ShadedFreeLineOddBase.localGrid parent) x y =
        componentAt (iterateRefine 3 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact ShadedFreeLineOddBase.componentAt_localGrid_eq_shift
      grid blockX blockY hparent hx hy
  have path := BoundedPath.congr_of_component_eq same sound.2
  have onCycle := ShadedFreeLineOddBase.onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn
      (iterateRefine 3 (shiftGrid grid blockX blockY)) 2 6 2 6 := by
    simpa using RedShadeCrossingBoards.largeCycle
      (shiftGrid grid blockX blockY) 1
  simp only [SparseFreeLineOddMarkerBaseAudit.verticalReached,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at reached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := onCycle
    path := path.path
    startLive := portPresent_of_onCycle cycle onCycle
    portLive := ?_
  }, reached.1.1, reached.2⟩
  rw [← ShadedFreeLineOddBase.portPresent_localGrid_eq_shift
    grid blockX blockY hparent node.current path.second_inBounds]
  exact reached.1.2

theorem liveColumnCertificate_shift (grid : Nat → Nat → Index)
    (blockX blockY : Nat) {parent : Index}
    (hparent : grid blockX blockY = parent) :
    LiveColumnCertificate (iterateRefine 3 (shiftGrid grid blockX blockY))
      2 6 2 6 8 := by
  intro quarterY hsouth hnorth interior
  have hsouth' : 5 < quarterY := by simpa [quarterSouth] using hsouth
  have hnorth' : quarterY < 12 := by simpa [quarterNorth] using hnorth
  have hcomponent : componentAt (ShadedFreeLineOddBase.localGrid parent)
      8 quarterY = componentAt
        (iterateRefine 3 (shiftGrid grid blockX blockY)) 8 quarterY :=
    ShadedFreeLineOddBase.componentAt_localGrid_eq_shift
      grid blockX blockY hparent (by omega) (by omega)
  have localInterior : Signals.horizontalInterior?
      (componentAt (ShadedFreeLineOddBase.localGrid parent) 8 quarterY)
      (quadrantAt 8 quarterY) ≠ none := by
    rwa [hcomponent]
  rcases horizontal_node_exists parent hsouth' hnorth' localInterior with
    ⟨node, hnode, reached⟩
  have sound := exploreFast_bounded_sound
    (fun port hport => ShadedFreeLineOddBase.boardPorts_inBounds hport) hnode
  have same : ∀ x y, x < 16 → y < 16 →
      componentAt (ShadedFreeLineOddBase.localGrid parent) x y =
        componentAt (iterateRefine 3 (shiftGrid grid blockX blockY)) x y := by
    intro x y hx hy
    exact ShadedFreeLineOddBase.componentAt_localGrid_eq_shift
      grid blockX blockY hparent hx hy
  have path := BoundedPath.congr_of_component_eq same sound.2
  have onCycle := ShadedFreeLineOddBase.onCycle_of_mem_boardPorts sound.1
  have cycle : CycleOn
      (iterateRefine 3 (shiftGrid grid blockX blockY)) 2 6 2 6 := by
    simpa using RedShadeCrossingBoards.largeCycle
      (shiftGrid grid blockX blockY) 1
  simp only [SparseFreeLineOddMarkerBaseAudit.horizontalReached,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at reached
  refine ⟨{
    port := node.current
    parity := node.parity
    start := node.origin
    onCycle := onCycle
    path := path.path
    startLive := portPresent_of_onCycle cycle onCycle
    portLive := ?_
  }, reached.1.1, reached.2⟩
  rw [← ShadedFreeLineOddBase.portPresent_localGrid_eq_shift
    grid blockX blockY hparent node.current path.second_inBounds]
  exact reached.1.2

end SparseFreeLineOddMarkerBase
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
