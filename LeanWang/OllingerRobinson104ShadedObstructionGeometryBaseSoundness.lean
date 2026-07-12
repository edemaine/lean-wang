/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBaseComplete
import LeanWang.OllingerRobinson104ShadedFreeLineGraphBase

/-!
# Soundness of the nearest-boundary audit bitmap

Every true entry in the compact audit bitmap comes from an actual retained
graph-search node.  The fixed-width state code can then be decoded back to the
node's port and parity.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedObstructionGeometryBaseSoundness

set_option maxRecDepth 20000

open OrientedRedCycles RedShadeGraph RedShadeGraphSearch RedShadeGraphSearchSoundness
  RedShadeGraphRefinement RedShadeGraphBoards RedShadeCycles RedShadePaths
  ShadedFreeLineGraphBase
  ShadedObstructionGeometryBaseAudit Signals.FreeCellLocal

private theorem foldl_reachedBitmap_true
    (nodes : List Node) (visited : Array Bool) (code : Nat)
    (htrue : (nodes.foldl (fun bitmap node =>
      bitmap.setIfInBounds (stateCode 32 node.state) true) visited)[code]?.getD false =
        true) :
    visited[code]?.getD false = true ∨
      ∃ node ∈ nodes, stateCode 32 node.state = code := by
  induction nodes generalizing visited with
  | nil => exact Or.inl htrue
  | cons first rest ih =>
      have result := ih
        (visited.setIfInBounds (stateCode 32 first.state) true) htrue
      rcases result with hvisited | ⟨node, hnode, hcode⟩
      · by_cases heq : stateCode 32 first.state = code
        · exact Or.inr ⟨first, by simp, heq⟩
        · exact Or.inl (by
            simpa only [Array.getElem?_setIfInBounds, heq, if_false] using hvisited)
      · exact Or.inr ⟨node, by simp [hnode], hcode⟩

theorem reachedBitmap_true_has_node
    (nodes : List Node) (code : Nat)
    (htrue : (reachedBitmap nodes)[code]?.getD false = true) :
    ∃ node ∈ nodes, stateCode 32 node.state = code := by
  have result := foldl_reachedBitmap_true nodes
    (Array.replicate (32 * 32 * 8) false) code (by
      simpa only [reachedBitmap] using htrue)
  rcases result with hinitial | hnode
  · have hsize : (Array.replicate (32 * 32 * 8) false).size = 32 * 32 * 8 := by
      simp
    by_cases hcode : code < 32 * 32 * 8
    · rw [Array.getElem?_eq_getElem (by simpa [hsize] using hcode)] at hinitial
      simp at hinitial
    · rw [Array.getElem?_eq_none (by simpa [hsize] using Nat.le_of_not_gt hcode)]
        at hinitial
      simp at hinitial
  · exact hnode

theorem stateCode_32_injective_of_bounds
    {first second : Port × Bool}
    (hfirstX : first.1.x < 32) (hsecondX : second.1.x < 32)
    (hcode : stateCode 32 first = stateCode 32 second) :
    first = second := by
  rcases first with ⟨⟨firstX, firstY, firstSide⟩, firstParity⟩
  rcases second with ⟨⟨secondX, secondY, secondSide⟩, secondParity⟩
  change firstX < 32 at hfirstX
  change secondX < 32 at hsecondX
  cases firstSide <;> cases secondSide <;>
    cases firstParity <;> cases secondParity <;>
    simp [stateCode, sideCode] at hcode ⊢ <;> omega

theorem reachedWithParity_has_node
    (parent : Index) {port : Port} {parity : Bool}
    (hportX : port.x < 32)
    (hreached : reachedWithParity parent
      (reachedBitmap (nodes parent)) port parity = true) :
    ∃ node ∈ nodes parent, node.current = port ∧ node.parity = parity := by
  have hparts :
      (reachedBitmap (nodes parent))[stateCode 32 (port, parity)]?.getD false = true ∧
        portPresent (localGrid parent) port = true := by
    simpa only [reachedWithParity, Bool.and_eq_true] using hreached
  rcases reachedBitmap_true_has_node (nodes parent)
      (stateCode 32 (port, parity)) hparts.1 with ⟨node, hnode, hcode⟩
  have hbounded := exploreFast_bounded_sound
    (fun candidate hcandidate => boardPorts_inBounds hcandidate) hnode
  have hstate : node.state = (port, parity) :=
    stateCode_32_injective_of_bounds hbounded.2.second_inBounds.1 hportX hcode
  exact ⟨node, hnode, congrArg Prod.fst hstate, congrArg Prod.snd hstate⟩

theorem reachedWithParity_has_path
    (parent : Index) {port : Port} {parity : Bool}
    (hportX : port.x < 32)
    (hreached : reachedWithParity parent
      (reachedBitmap (nodes parent)) port parity = true) :
    ∃ start ∈ boardPorts, Path (localGrid parent) start port parity := by
  rcases reachedWithParity_has_node parent hportX hreached with
    ⟨node, hnode, hcurrent, hparity⟩
  rcases exploreFast_sound hnode with ⟨horigin, path⟩
  rw [hcurrent, hparity] at path
  exact ⟨node.origin, horigin, path⟩

theorem value_eq_light_of_reached
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {port : Port} (hportX : port.x < 32)
    (hreached : reachedWithParity parent
      (reachedBitmap (nodes parent)) port (!parentLight) = true) :
    value stateGrid port = some .light := by
  rcases reachedWithParity_has_path parent hportX hreached with
    ⟨start, hstart, path⟩
  have startValue := (onCycle_of_mem_boardPorts hstart).value_eq
    cycle shaded valid
  have relation := path.sound valid
  cases parentLight with
  | false =>
      simp only [Bool.not_false, related_true_iff] at relation
      rcases relation with ⟨shade, hfirst, hfinish⟩
      have hshade : shade = .dark :=
        Option.some.inj (hfirst.symm.trans startValue)
      subst shade
      simpa [RedShades.Shade.opposite] using hfinish
  | true =>
      simp only [Bool.not_true, related_false_iff] at relation
      exact relation.symm.trans startValue

private theorem horizontalShade_eq_light_of_east
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.VerticalInterior}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hinterior : Signals.horizontalInterior? component quadrant = some interior)
    (heast : state.east = some .light) :
    ShadedSignals.horizontalShade? state = some .light := by
  rcases state with ⟨west, east, south, north⟩
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
      RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
      RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
      RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
      QuarterGeometry.redHorizontalAt, QuarterGeometry.redVerticalAt,
      QuarterGeometry.containsLine, Figure16.Thick.lineSum?, Quadrant.xBit,
      Quadrant.yBit,
      Signals.horizontalInterior?, ShadedSignals.horizontalShade?]

private theorem verticalShade_eq_light_of_north
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.HorizontalInterior}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hinterior : Signals.verticalInterior? component quadrant = some interior)
    (hnorth : state.north = some .light) :
    ShadedSignals.verticalShade? state = some .light := by
  rcases state with ⟨west, east, south, north⟩
  cases component <;> cases quadrant <;>
    simp_all [RedShades.allowedFor, RedShades.hasWest, RedShades.hasEast,
      RedShades.hasSouth, RedShades.hasNorth, RedShades.hasHorizontal,
      RedShades.hasVertical, RedShades.cornerWest, RedShades.cornerEast,
      RedShades.cornerSouth, RedShades.cornerNorth, RedShades.optionPresent,
      QuarterGeometry.redHorizontalAt, QuarterGeometry.redVerticalAt,
      QuarterGeometry.containsLine, Figure16.Thick.lineSum?, Quadrant.xBit,
      Quadrant.yBit,
      Signals.verticalInterior?, ShadedSignals.verticalShade?]

theorem selectedHorizontal_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hselected : selectedHorizontal parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ShadedSignals.selectedHorizontalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none := by
  have hcolumnBound : column < 32 := by
    simp only [coordinates, List.mem_map, List.mem_range] at hcolumn
    rcases hcolumn with ⟨offset, hoffset, rfl⟩
    omega
  have hparts :
      (Signals.horizontalInterior?
        (componentAt (localGrid parent) column row)
        (quadrantAt column row)).isSome = true ∧
      (reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .west⟩ (!parentLight) = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .east⟩ (!parentLight) = true) := by
    simpa only [selectedHorizontal, Bool.and_eq_true, Bool.or_eq_true] using hselected
  cases hinterior : Signals.horizontalInterior?
      (componentAt (localGrid parent) column row) (quadrantAt column row) with
  | none => simp [hinterior] at hparts
  | some interior =>
      have hshade : ShadedSignals.horizontalShade? (stateGrid column row) =
          some .light := by
        rcases hparts.2 with hwest | heast
        · have hwestLight : (stateGrid column row).west = some .light := by
            simpa only [value] using value_eq_light_of_reached parent valid
              parentLight cycle shaded hcolumnBound hwest
          simp [ShadedSignals.horizontalShade?, hwestLight]
        · have heastLight : (stateGrid column row).east = some .light := by
            simpa only [value] using value_eq_light_of_reached parent valid
              parentLight cycle shaded hcolumnBound heast
          have hallowed := valid.allowed column row
          unfold RedShades.locallyAllowed at hallowed
          dsimp only at hallowed
          exact horizontalShade_eq_light_of_east hallowed hinterior heastLight
      simp [ShadedSignals.selectedHorizontalFor, hshade, hinterior]

theorem selectedVertical_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 4 12 4 12)
    (shaded : CycleShade stateGrid 4 12 4 12
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hselected : selectedVertical parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ShadedSignals.selectedVerticalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none := by
  have hcolumnBound : column < 32 := by
    simp only [coordinates, List.mem_map, List.mem_range] at hcolumn
    rcases hcolumn with ⟨offset, hoffset, rfl⟩
    omega
  have hparts :
      (Signals.verticalInterior?
        (componentAt (localGrid parent) column row)
        (quadrantAt column row)).isSome = true ∧
      (reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .south⟩ (!parentLight) = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .north⟩ (!parentLight) = true) := by
    simpa only [selectedVertical, Bool.and_eq_true, Bool.or_eq_true] using hselected
  cases hinterior : Signals.verticalInterior?
      (componentAt (localGrid parent) column row) (quadrantAt column row) with
  | none => simp [hinterior] at hparts
  | some interior =>
      have hshade : ShadedSignals.verticalShade? (stateGrid column row) =
          some .light := by
        rcases hparts.2 with hsouth | hnorth
        · have hsouthLight : (stateGrid column row).south = some .light := by
            simpa only [value] using value_eq_light_of_reached parent valid
              parentLight cycle shaded hcolumnBound hsouth
          simp [ShadedSignals.verticalShade?, hsouthLight]
        · have hnorthLight : (stateGrid column row).north = some .light := by
            simpa only [value] using value_eq_light_of_reached parent valid
              parentLight cycle shaded hcolumnBound hnorth
          have hallowed := valid.allowed column row
          unfold RedShades.locallyAllowed at hallowed
          dsimp only at hallowed
          exact verticalShade_eq_light_of_north hallowed hinterior hnorthLight
      simp [ShadedSignals.selectedVerticalFor, hshade, hinterior]

end ShadedObstructionGeometryBaseSoundness
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
