/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedObstructionGeometryOddBaseComplete
import LeanWang.Robinson.Closed104.ShadedFreeLineOddBase

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
namespace ShadedObstructionGeometryOddBaseSoundness

set_option maxRecDepth 20000

open OrientedRedCycles RedShadeGraph RedShadeGraphSearch RedShadeGraphSearchSoundness
  RedShadeGraphRefinement RedShadeGraphBoards RedShadeCycles RedShadePaths
  ShadedFreeLineOddBase ShadedObstructionGeometry
  ShadedObstructionGeometryOddBaseAudit ShadedPlaneSignalGrid Signals.FreeCellLocal

private theorem foldl_reachedBitmap_true
    (nodes : List Node) (visited : Array Bool) (code : Nat)
    (htrue : (nodes.foldl (fun bitmap node =>
      bitmap.setIfInBounds (stateCode 16 node.state) true) visited)[code]?.getD false =
        true) :
    visited[code]?.getD false = true ∨
      ∃ node ∈ nodes, stateCode 16 node.state = code := by
  induction nodes generalizing visited with
  | nil => exact Or.inl htrue
  | cons first rest ih =>
      have result := ih
        (visited.setIfInBounds (stateCode 16 first.state) true) htrue
      rcases result with hvisited | ⟨node, hnode, hcode⟩
      · by_cases heq : stateCode 16 first.state = code
        · exact Or.inr ⟨first, by simp, heq⟩
        · exact Or.inl (by
            simpa only [Array.getElem?_setIfInBounds, heq, if_false] using hvisited)
      · exact Or.inr ⟨node, by simp [hnode], hcode⟩

theorem reachedBitmap_true_has_node
    (nodes : List Node) (code : Nat)
    (htrue : (reachedBitmap nodes)[code]?.getD false = true) :
    ∃ node ∈ nodes, stateCode 16 node.state = code := by
  have result := foldl_reachedBitmap_true nodes
    (Array.replicate (16 * 16 * 8) false) code (by
      simpa only [reachedBitmap] using htrue)
  rcases result with hinitial | hnode
  · have hsize : (Array.replicate (16 * 16 * 8) false).size = 16 * 16 * 8 := by
      simp
    by_cases hcode : code < 16 * 16 * 8
    · rw [Array.getElem?_eq_getElem (by simpa [hsize] using hcode)] at hinitial
      simp at hinitial
    · rw [Array.getElem?_eq_none (by simpa [hsize] using Nat.le_of_not_gt hcode)]
        at hinitial
      simp at hinitial
  · exact hnode

theorem stateCode_16_injective_of_bounds
    {first second : Port × Bool}
    (hfirstX : first.1.x < 16) (hsecondX : second.1.x < 16)
    (hcode : stateCode 16 first = stateCode 16 second) :
    first = second := by
  rcases first with ⟨⟨firstX, firstY, firstSide⟩, firstParity⟩
  rcases second with ⟨⟨secondX, secondY, secondSide⟩, secondParity⟩
  change firstX < 16 at hfirstX
  change secondX < 16 at hsecondX
  cases firstSide <;> cases secondSide <;>
    cases firstParity <;> cases secondParity <;>
    simp [stateCode, sideCode] at hcode ⊢ <;> omega

theorem reachedWithParity_has_node
    (parent : Index) {port : Port} {parity : Bool}
    (hportX : port.x < 16)
    (hreached : reachedWithParity parent
      (reachedBitmap (nodes parent)) port parity = true) :
    ∃ node ∈ nodes parent, node.current = port ∧ node.parity = parity := by
  have hparts :
      (reachedBitmap (nodes parent))[stateCode 16 (port, parity)]?.getD false = true ∧
        portPresent (localGrid parent) port = true := by
    simpa only [reachedWithParity, Bool.and_eq_true] using hreached
  rcases reachedBitmap_true_has_node (nodes parent)
      (stateCode 16 (port, parity)) hparts.1 with ⟨node, hnode, hcode⟩
  have hbounded := exploreFast_bounded_sound
    (fun candidate hcandidate => boardPorts_inBounds hcandidate) hnode
  have hstate : node.state = (port, parity) :=
    stateCode_16_injective_of_bounds hbounded.2.second_inBounds.1 hportX hcode
  exact ⟨node, hnode, congrArg Prod.fst hstate, congrArg Prod.snd hstate⟩

theorem reachedWithParity_has_path
    (parent : Index) {port : Port} {parity : Bool}
    (hportX : port.x < 16)
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
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    {port : Port} (hportX : port.x < 16)
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

theorem value_eq_dark_of_reached
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    {port : Port} (hportX : port.x < 16)
    (hreached : reachedWithParity parent
      (reachedBitmap (nodes parent)) port parentLight = true) :
    value stateGrid port = some .dark := by
  rcases reachedWithParity_has_path parent hportX hreached with
    ⟨start, hstart, path⟩
  have startValue := (onCycle_of_mem_boardPorts hstart).value_eq
    cycle shaded valid
  have relation := path.sound valid
  cases parentLight with
  | false =>
      simp only [related_false_iff] at relation
      exact relation.symm.trans startValue
  | true =>
      simp only [related_true_iff] at relation
      rcases relation with ⟨shade, hfirst, hfinish⟩
      have hshade : shade = .light :=
        Option.some.inj (hfirst.symm.trans startValue)
      subst shade
      simpa [RedShades.Shade.opposite] using hfinish

theorem horizontalShade_eq_light_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state ≠ none) :
    ShadedSignals.horizontalShade? state = some .light := by
  unfold ShadedSignals.selectedHorizontalFor at hselected
  by_contra hshade
  simp [hshade] at hselected

theorem verticalShade_eq_light_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state ≠ none) :
    ShadedSignals.verticalShade? state = some .light := by
  unfold ShadedSignals.selectedVerticalFor at hselected
  by_contra hshade
  simp [hshade] at hselected

theorem hasWest_of_allowedFor_present
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hpresent : state.west.isSome = true) :
    RedShades.hasWest component quadrant = true := by
  cases hvalue : RedShades.hasWest component quadrant
  · simp [RedShades.allowedFor, RedShades.optionPresent, hvalue, hpresent]
      at hallowed
  · rfl

theorem hasSouth_of_allowedFor_present
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hpresent : state.south.isSome = true) :
    RedShades.hasSouth component quadrant = true := by
  cases hvalue : RedShades.hasSouth component quadrant
  · simp [RedShades.allowedFor, RedShades.optionPresent, hvalue, hpresent]
      at hallowed
  · rfl

theorem north_present_of_allowedFor
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hnorth : RedShades.hasNorth component quadrant = true) :
    state.north.isSome = true := by
  cases hvalue : state.north
  · simp [RedShades.allowedFor, RedShades.optionPresent, hnorth, hvalue]
      at hallowed
  · simp

theorem hasHorizontal_of_hasWest_hasEast
    {component : Figure16.Thick} {quadrant : Quadrant}
    (hwest : RedShades.hasWest component quadrant = true)
    (heast : RedShades.hasEast component quadrant = true) :
    RedShades.hasHorizontal component quadrant = true := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.hasWest, RedShades.hasEast, RedShades.hasHorizontal,
      RedShades.cornerWest, RedShades.cornerEast,
      QuarterGeometry.redHorizontalAt, QuarterGeometry.containsLine,
      Figure16.Thick.lineSum?, Figure16.ThickLineSum.mkDistinct, Quadrant.yBit]

theorem hasVertical_of_hasSouth_hasNorth
    {component : Figure16.Thick} {quadrant : Quadrant}
    (hsouth : RedShades.hasSouth component quadrant = true)
    (hnorth : RedShades.hasNorth component quadrant = true) :
    RedShades.hasVertical component quadrant = true := by
  cases component <;> cases quadrant <;>
    simp_all [RedShades.hasSouth, RedShades.hasNorth, RedShades.hasVertical,
      RedShades.cornerSouth, RedShades.cornerNorth,
      QuarterGeometry.redVerticalAt, QuarterGeometry.containsLine,
      Figure16.Thick.lineSum?, Figure16.ThickLineSum.mkDistinct, Quadrant.xBit]

theorem horizontal_west_light_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state ≠ none)
    (hwest : RedShades.hasWest component quadrant = true) :
    state.west = some .light := by
  have hpresent := RedShades.west_present_of_allowedFor hallowed hwest
  have hshade := horizontalShade_eq_light_of_selected hselected
  cases hvalue : state.west <;>
    simp_all [ShadedSignals.horizontalShade?]

theorem horizontal_east_light_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state ≠ none)
    (heast : RedShades.hasEast component quadrant = true) :
    state.east = some .light := by
  have heastPresent := RedShades.east_present_of_allowedFor hallowed heast
  have hshade := horizontalShade_eq_light_of_selected hselected
  cases hwest : state.west with
  | none => simpa [ShadedSignals.horizontalShade?, hwest] using hshade
  | some westShade =>
      have hwestPresent : state.west.isSome = true := by simp [hwest]
      have hhasWest := hasWest_of_allowedFor_present hallowed hwestPresent
      have heq := RedShades.horizontal_eq_of_allowedFor hallowed
        (hasHorizontal_of_hasWest_hasEast hhasWest heast)
      have hwestLight : state.west = some .light := by
        simpa [ShadedSignals.horizontalShade?, hwest] using hshade
      exact heq.symm.trans hwestLight

theorem vertical_south_light_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state ≠ none)
    (hsouth : RedShades.hasSouth component quadrant = true) :
    state.south = some .light := by
  have hpresent := RedShades.south_present_of_allowedFor hallowed hsouth
  have hshade := verticalShade_eq_light_of_selected hselected
  cases hvalue : state.south <;>
    simp_all [ShadedSignals.verticalShade?]

theorem vertical_north_light_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant} {state : RedShades.State}
    (hallowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state ≠ none)
    (hnorth : RedShades.hasNorth component quadrant = true) :
    state.north = some .light := by
  have hnorthPresent := north_present_of_allowedFor hallowed hnorth
  have hshade := verticalShade_eq_light_of_selected hselected
  cases hsouth : state.south with
  | none => simpa [ShadedSignals.verticalShade?, hsouth] using hshade
  | some southShade =>
      have hsouthPresent : state.south.isSome = true := by simp [hsouth]
      have hhasSouth := hasSouth_of_allowedFor_present hallowed hsouthPresent
      have heq := RedShades.vertical_eq_of_allowedFor hallowed
        (hasVertical_of_hasSouth_hasNorth hhasSouth hnorth)
      have hsouthLight : state.south = some .light := by
        simpa [ShadedSignals.verticalShade?, hsouth] using hshade
      exact heq.symm.trans hsouthLight

theorem horizontalInterior_isSome_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state ≠ none) :
    (Signals.horizontalInterior? component quadrant).isSome = true := by
  unfold ShadedSignals.selectedHorizontalFor at hselected
  split at hselected
  · cases hvalue : Signals.horizontalInterior? component quadrant <;>
      simp_all
  · contradiction

theorem verticalInterior_isSome_of_selected
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State}
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state ≠ none) :
    (Signals.verticalInterior? component quadrant).isSome = true := by
  unfold ShadedSignals.selectedVerticalFor at hselected
  split at hselected
  · cases hvalue : Signals.verticalInterior? component quadrant <;>
      simp_all
  · contradiction

private theorem horizontal_not_reached_same
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumnBound : column < 16) {side : Side}
    (hside : side = .west ∨ side = .east)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, side⟩ parentLight = true) : False := by
  have hdark := value_eq_dark_of_reached parent valid parentLight cycle shaded
    hcolumnBound hreached
  have hallowed := valid.allowed column row
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  rcases hside with rfl | rfl
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 16
          (⟨column, row, .west⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .west⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have hwest : RedShades.hasWest
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hlight := horizontal_west_light_of_selected hallowed hselected hwest
    simp only [value] at hdark
    simp_all
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 16
          (⟨column, row, .east⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .east⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have heast : RedShades.hasEast
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hlight := horizontal_east_light_of_selected hallowed hselected heast
    simp only [value] at hdark
    simp_all

private theorem vertical_not_reached_same
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumnBound : column < 16) {side : Side}
    (hside : side = .south ∨ side = .north)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none)
    (hreached : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, side⟩ parentLight = true) : False := by
  have hdark := value_eq_dark_of_reached parent valid parentLight cycle shaded
    hcolumnBound hreached
  have hallowed := valid.allowed column row
  unfold RedShades.locallyAllowed at hallowed
  dsimp only at hallowed
  rcases hside with rfl | rfl
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 16
          (⟨column, row, .south⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .south⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have hsouth : RedShades.hasSouth
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hlight := vertical_south_light_of_selected hallowed hselected hsouth
    simp only [value] at hdark
    simp_all
  · have hparts :
        (reachedBitmap (nodes parent))[stateCode 16
          (⟨column, row, .north⟩, parentLight)]?.getD false = true ∧
        portPresent (localGrid parent) ⟨column, row, .north⟩ = true := by
      simpa only [reachedWithParity, Bool.and_eq_true] using hreached
    have hnorth : RedShades.hasNorth
        (componentAt (localGrid parent) column row) (quadrantAt column row) = true := by
      simpa only [portPresent] using hparts.2
    have hlight := vertical_north_light_of_selected hallowed hselected hnorth
    simp only [value] at hdark
    simp_all

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
      Quadrant.yBit, Signals.horizontalInterior?,
      ShadedSignals.horizontalShade?]

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
      Quadrant.yBit, Signals.verticalInterior?, ShadedSignals.verticalShade?]

theorem selectedHorizontal_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hselected : selectedHorizontal parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ShadedSignals.selectedHorizontalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none := by
  have hcolumnBound : column < 16 := by
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
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hselected : selectedVertical parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ShadedSignals.selectedVerticalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none := by
  have hcolumnBound : column < 16 := by
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

structure CoveragePaths (parent : Index) : Prop where
  horizontal : ∀ {column row : Nat}, column ∈ coordinates → row ∈ coordinates →
    (Signals.horizontalInterior? (componentAt (localGrid parent) column row)
      (quadrantAt column row)).isSome = true →
    (((reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .west⟩ false = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .west⟩ true = true) ∨
      reachedWithParity parent (reachedBitmap (nodes parent))
        ⟨column, row, .east⟩ false = true) ∨
    reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .east⟩ true = true)
  vertical : ∀ {column row : Nat}, column ∈ coordinates → row ∈ coordinates →
    (Signals.verticalInterior? (componentAt (localGrid parent) column row)
      (quadrantAt column row)).isSome = true →
    (((reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .south⟩ false = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .south⟩ true = true) ∨
      reachedWithParity parent (reachedBitmap (nodes parent))
        ⟨column, row, .north⟩ false = true) ∨
    reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .north⟩ true = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Decode the large boolean audit expression once into a compact proof interface.
theorem coveragePaths_of_eq_true (parent : Index)
    (coverage : coverageFor parent (reachedBitmap (nodes parent)) = true) :
    CoveragePaths parent := by
  simp only [coverageFor, List.all_eq_true] at coverage
  constructor
  · intro column row hcolumn hrow hinterior
    have hparts := coverage column hcolumn row hrow
    simp only [Bool.and_eq_true] at hparts
    simpa only [hinterior, Bool.not_true, Bool.false_or, Bool.or_eq_true]
      using hparts.2
  · intro column row hcolumn hrow hinterior
    have hparts := coverage column hcolumn row hrow
    simp only [Bool.and_eq_true] at hparts
    simpa only [hinterior, Bool.not_true, Bool.false_or, Bool.or_eq_true]
      using hparts.1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Coverage elimination expands four parity alternatives.
theorem selectedHorizontal_of_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none) :
    selectedHorizontal parent (reachedBitmap (nodes parent))
      parentLight column row = true := by
  have hcolumnBound : column < 16 := by
    simp only [coordinates, List.mem_map, List.mem_range] at hcolumn
    rcases hcolumn with ⟨offset, hoffset, rfl⟩
    omega
  have hinterior := horizontalInterior_isSome_of_selected hselected
  have hcovered' := coverage.horizontal hcolumn hrow hinterior
  by_cases hwest : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .west⟩ (!parentLight) = true
  · simp [selectedHorizontal, hinterior, hwest]
  by_cases heast : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .east⟩ (!parentLight) = true
  · simp [selectedHorizontal, hinterior, heast]
  have hsame :
      reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .west⟩ parentLight = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .east⟩ parentLight = true := by
    cases parentLight
    · simp only [Bool.not_false] at hwest heast
      rcases hcovered' with ((hwestSame | hwestOpposite) | heastSame) |
        heastOpposite
      · exact Or.inl hwestSame
      · exact (hwest hwestOpposite).elim
      · exact Or.inr heastSame
      · exact (heast heastOpposite).elim
    · simp only [Bool.not_true] at hwest heast
      rcases hcovered' with ((hwestOpposite | hwestSame) | heastOpposite) |
        heastSame
      · exact (hwest hwestOpposite).elim
      · exact Or.inl hwestSame
      · exact (heast heastOpposite).elim
      · exact Or.inr heastSame
  rcases hsame with hsame | hsame
  · exact False.elim (horizontal_not_reached_same parent valid parentLight
      cycle shaded hcolumnBound (Or.inl rfl) hselected hsame)
  · exact False.elim (horizontal_not_reached_same parent valid parentLight
      cycle shaded hcolumnBound (Or.inr rfl) hselected hsame)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Coverage elimination expands four parity alternatives.
theorem selectedVertical_of_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt (localGrid parent) column row) (quadrantAt column row)
      (stateGrid column row) ≠ none) :
    selectedVertical parent (reachedBitmap (nodes parent))
      parentLight column row = true := by
  have hcolumnBound : column < 16 := by
    simp only [coordinates, List.mem_map, List.mem_range] at hcolumn
    rcases hcolumn with ⟨offset, hoffset, rfl⟩
    omega
  have hinterior := verticalInterior_isSome_of_selected hselected
  have hcovered' := coverage.vertical hcolumn hrow hinterior
  by_cases hsouth : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .south⟩ (!parentLight) = true
  · simp [selectedVertical, hinterior, hsouth]
  by_cases hnorth : reachedWithParity parent (reachedBitmap (nodes parent))
      ⟨column, row, .north⟩ (!parentLight) = true
  · simp [selectedVertical, hinterior, hnorth]
  have hsame :
      reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .south⟩ parentLight = true ∨
        reachedWithParity parent (reachedBitmap (nodes parent))
          ⟨column, row, .north⟩ parentLight = true := by
    cases parentLight
    · simp only [Bool.not_false] at hsouth hnorth
      rcases hcovered' with ((hsouthSame | hsouthOpposite) | hnorthSame) |
        hnorthOpposite
      · exact Or.inl hsouthSame
      · exact (hsouth hsouthOpposite).elim
      · exact Or.inr hnorthSame
      · exact (hnorth hnorthOpposite).elim
    · simp only [Bool.not_true] at hsouth hnorth
      rcases hcovered' with ((hsouthOpposite | hsouthSame) | hnorthOpposite) |
        hnorthSame
      · exact (hsouth hsouthOpposite).elim
      · exact Or.inl hsouthSame
      · exact (hnorth hnorthOpposite).elim
      · exact Or.inr hnorthSame
  rcases hsame with hsame | hsame
  · exact False.elim (vertical_not_reached_same parent valid parentLight
      cycle shaded hcolumnBound (Or.inl rfl) hselected hsame)
  · exact False.elim (vertical_not_reached_same parent valid parentLight
      cycle shaded hcolumnBound (Or.inr rfl) hselected hsame)

theorem mem_coordinates_iff {coordinate : Nat} :
    coordinate ∈ coordinates ↔ 5 < coordinate ∧ coordinate < 12 := by
  simp only [coordinates, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, hoffset, rfl⟩
    omega
  · intro hbounds
    exact ⟨coordinate - 6, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
-- Relating the boolean audit to the quantified semantic predicate.
theorem freeRow_eq_true_iff
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {row : Nat} (hrow : row ∈ coordinates) :
    freeRow parent (reachedBitmap (nodes parent)) parentLight row = true ↔
      IsFreeRow (localGrid parent) stateGrid 2 6 row := by
  constructor
  · intro hfree quarterX hwest heast
    have hquarterX : quarterX ∈ coordinates :=
      mem_coordinates_iff.2 (by
        simp [quarterWest] at hwest
        simp [quarterEast] at heast
        omega)
    simp only [freeRow, List.all_eq_true] at hfree
    have hnotSelected := hfree quarterX hquarterX
    by_contra hselected
    have haudit := selectedVertical_of_semantic parent valid parentLight cycle
      shaded coverage hquarterX hrow hselected
    simp [haudit] at hnotSelected
  · intro hfree
    simp only [freeRow, List.all_eq_true]
    intro quarterX hquarterX
    cases haudit : selectedVertical parent (reachedBitmap (nodes parent))
        parentLight quarterX row
    · simp
    · have hsemantic := selectedVertical_semantic parent valid parentLight cycle
        shaded hquarterX haudit
      have hnone := hfree quarterX (by
        have := mem_coordinates_iff.1 hquarterX
        simp [quarterWest]
        omega) (by
        have := mem_coordinates_iff.1 hquarterX
        simp [quarterEast]
        omega)
      contradiction

set_option maxHeartbeats 1000000 in
-- Relating the boolean audit to the quantified semantic predicate.
theorem freeColumn_eq_true_iff
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column : Nat} (hcolumn : column ∈ coordinates) :
    freeColumn parent (reachedBitmap (nodes parent)) parentLight column = true ↔
      IsFreeColumn (localGrid parent) stateGrid 2 6 column := by
  constructor
  · intro hfree quarterY hsouth hnorth
    have hquarterY : quarterY ∈ coordinates :=
      mem_coordinates_iff.2 (by
        simp [quarterSouth] at hsouth
        simp [quarterNorth] at hnorth
        omega)
    simp only [freeColumn, List.all_eq_true] at hfree
    have hnotSelected := hfree quarterY hquarterY
    by_contra hselected
    have haudit := selectedHorizontal_of_semantic parent valid parentLight cycle
      shaded coverage hcolumn hquarterY hselected
    simp [haudit] at hnotSelected
  · intro hfree
    simp only [freeColumn, List.all_eq_true]
    intro quarterY hquarterY
    cases haudit : selectedHorizontal parent (reachedBitmap (nodes parent))
        parentLight column quarterY
    · simp
    · have hsemantic := selectedHorizontal_semantic parent valid parentLight cycle
        shaded hcolumn haudit
      have hnone := hfree quarterY (by
        have := mem_coordinates_iff.1 hquarterY
        simp [quarterSouth]
        omega) (by
        have := mem_coordinates_iff.1 hquarterY
        simp [quarterNorth]
        omega)
      contradiction

theorem selectedHorizontal_eq_of_interior
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.VerticalInterior}
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state ≠ none)
    (hinterior : Signals.horizontalInterior? component quadrant = some interior) :
    ShadedSignals.selectedHorizontalFor component quadrant state = some interior := by
  unfold ShadedSignals.selectedHorizontalFor at hselected ⊢
  by_cases hshade : ShadedSignals.horizontalShade? state = some .light
  · simp [hshade, hinterior]
  · simp [hshade] at hselected

theorem selectedVertical_eq_of_interior
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.HorizontalInterior}
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state ≠ none)
    (hinterior : Signals.verticalInterior? component quadrant = some interior) :
    ShadedSignals.selectedVerticalFor component quadrant state = some interior := by
  unfold ShadedSignals.selectedVerticalFor at hselected ⊢
  by_cases hshade : ShadedSignals.verticalShade? state = some .light
  · simp [hshade, hinterior]
  · simp [hshade] at hselected

set_option maxHeartbeats 1000000 in
-- Decoding the bounded existential witness and its intervening cells.
theorem upperWitness_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hwitness : upperWitness parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ∃ boundary, row < boundary ∧ boundary < 12 ∧
      ShadedSignals.selectedHorizontalFor
        (componentAt (localGrid parent) column boundary)
        (quadrantAt column boundary) (stateGrid column boundary) = some .north ∧
      ∀ y, row < y → y < boundary →
        ShadedSignals.selectedHorizontalFor
          (componentAt (localGrid parent) column y) (quadrantAt column y)
          (stateGrid column y) = none := by
  simp only [upperWitness, List.any_eq_true] at hwitness
  rcases hwitness with ⟨boundary, hboundary, hparts⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hparts
  simp only [List.all_eq_true] at hparts
  refine ⟨boundary, hparts.1.1.1, (mem_coordinates_iff.1 hboundary).2, ?_, ?_⟩
  · exact selectedHorizontal_eq_of_interior
      (selectedHorizontal_semantic parent valid parentLight cycle shaded hcolumn
        hparts.1.2)
      hparts.1.1.2
  · intro y hry hyb
    have hy : y ∈ coordinates := mem_coordinates_iff.2 (by
      have hrowBounds := mem_coordinates_iff.1 hrow
      have hboundaryBounds := mem_coordinates_iff.1 hboundary
      omega)
    have hnotAudit := hparts.2 y hy
    simp only [hry, hyb] at hnotAudit
    cases hsemantic : ShadedSignals.selectedHorizontalFor
        (componentAt (localGrid parent) column y) (quadrantAt column y)
        (stateGrid column y) with
    | none => rfl
    | some interior =>
        have haudit := selectedHorizontal_of_semantic parent valid parentLight cycle
          shaded coverage hcolumn hy (by simp [hsemantic])
        simp [haudit] at hnotAudit

set_option maxHeartbeats 1000000 in
-- Decoding the bounded existential witness and its intervening cells.
theorem lowerWitness_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hwitness : lowerWitness parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ∃ boundary, 5 < boundary ∧ boundary < row ∧
      ShadedSignals.selectedHorizontalFor
        (componentAt (localGrid parent) column boundary)
        (quadrantAt column boundary) (stateGrid column boundary) = some .south ∧
      ∀ y, boundary < y → y < row →
        ShadedSignals.selectedHorizontalFor
          (componentAt (localGrid parent) column y) (quadrantAt column y)
          (stateGrid column y) = none := by
  simp only [lowerWitness, List.any_eq_true] at hwitness
  rcases hwitness with ⟨boundary, hboundary, hparts⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hparts
  simp only [List.all_eq_true] at hparts
  refine ⟨boundary, (mem_coordinates_iff.1 hboundary).1, hparts.1.1.1, ?_, ?_⟩
  · exact selectedHorizontal_eq_of_interior
      (selectedHorizontal_semantic parent valid parentLight cycle shaded hcolumn
        hparts.1.2)
      hparts.1.1.2
  · intro y hby hyr
    have hy : y ∈ coordinates := mem_coordinates_iff.2 (by
      have hrowBounds := mem_coordinates_iff.1 hrow
      have hboundaryBounds := mem_coordinates_iff.1 hboundary
      omega)
    have hnotAudit := hparts.2 y hy
    simp only [hby, hyr] at hnotAudit
    cases hsemantic : ShadedSignals.selectedHorizontalFor
        (componentAt (localGrid parent) column y) (quadrantAt column y)
        (stateGrid column y) with
    | none => rfl
    | some interior =>
        have haudit := selectedHorizontal_of_semantic parent valid parentLight cycle
          shaded coverage hcolumn hy (by simp [hsemantic])
        simp [haudit] at hnotAudit

set_option maxHeartbeats 1000000 in
-- Decoding the bounded existential witness and its intervening cells.
theorem rightWitness_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hwitness : rightWitness parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ∃ boundary, column < boundary ∧ boundary < 12 ∧
      ShadedSignals.selectedVerticalFor
        (componentAt (localGrid parent) boundary row)
        (quadrantAt boundary row) (stateGrid boundary row) = some .east ∧
      ∀ x, column < x → x < boundary →
        ShadedSignals.selectedVerticalFor
          (componentAt (localGrid parent) x row) (quadrantAt x row)
          (stateGrid x row) = none := by
  simp only [rightWitness, List.any_eq_true] at hwitness
  rcases hwitness with ⟨boundary, hboundary, hparts⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hparts
  simp only [List.all_eq_true] at hparts
  refine ⟨boundary, hparts.1.1.1, (mem_coordinates_iff.1 hboundary).2, ?_, ?_⟩
  · exact selectedVertical_eq_of_interior
      (selectedVertical_semantic parent valid parentLight cycle shaded hboundary
        hparts.1.2)
      hparts.1.1.2
  · intro x hcx hxb
    have hx : x ∈ coordinates := mem_coordinates_iff.2 (by
      have hcolumnBounds := mem_coordinates_iff.1 hcolumn
      have hboundaryBounds := mem_coordinates_iff.1 hboundary
      omega)
    have hnotAudit := hparts.2 x hx
    simp only [hcx, hxb] at hnotAudit
    cases hsemantic : ShadedSignals.selectedVerticalFor
        (componentAt (localGrid parent) x row) (quadrantAt x row)
        (stateGrid x row) with
    | none => rfl
    | some interior =>
        have haudit := selectedVertical_of_semantic parent valid parentLight cycle
          shaded coverage hx hrow (by simp [hsemantic])
        simp [haudit] at hnotAudit

set_option maxHeartbeats 1000000 in
-- Decoding the bounded existential witness and its intervening cells.
theorem leftWitness_semantic
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    {column row : Nat} (hcolumn : column ∈ coordinates)
    (hrow : row ∈ coordinates)
    (hwitness : leftWitness parent (reachedBitmap (nodes parent))
      parentLight column row = true) :
    ∃ boundary, 5 < boundary ∧ boundary < column ∧
      ShadedSignals.selectedVerticalFor
        (componentAt (localGrid parent) boundary row)
        (quadrantAt boundary row) (stateGrid boundary row) = some .west ∧
      ∀ x, boundary < x → x < column →
        ShadedSignals.selectedVerticalFor
          (componentAt (localGrid parent) x row) (quadrantAt x row)
          (stateGrid x row) = none := by
  simp only [leftWitness, List.any_eq_true] at hwitness
  rcases hwitness with ⟨boundary, hboundary, hparts⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hparts
  simp only [List.all_eq_true] at hparts
  refine ⟨boundary, (mem_coordinates_iff.1 hboundary).1, hparts.1.1.1, ?_, ?_⟩
  · exact selectedVertical_eq_of_interior
      (selectedVertical_semantic parent valid parentLight cycle shaded hboundary
        hparts.1.2)
      hparts.1.1.2
  · intro x hbx hxc
    have hx : x ∈ coordinates := mem_coordinates_iff.2 (by
      have hcolumnBounds := mem_coordinates_iff.1 hcolumn
      have hboundaryBounds := mem_coordinates_iff.1 hboundary
      omega)
    have hnotAudit := hparts.2 x hx
    simp only [hbx, hxc] at hnotAudit
    cases hsemantic : ShadedSignals.selectedVerticalFor
        (componentAt (localGrid parent) x row) (quadrantAt x row)
        (stateGrid x row) with
    | none => rfl
    | some interior =>
        have haudit := selectedVertical_of_semantic parent valid parentLight cycle
          shaded coverage hx hrow (by simp [hsemantic])
        simp [haudit] at hnotAudit

set_option maxHeartbeats 1000000 in
-- Combining four audited witness forms elaborates a large dependent structure.
theorem geometry_of_audit
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark))
    (coverage : CoveragePaths parent)
    (complete : completeFor parent (reachedBitmap (nodes parent))
      parentLight = true) :
    Geometry (localGrid parent) stateGrid 2 6 2 6 := by
  constructor
  · intro column row hwest heast hsouth hnorth hfreeRow hnotFreeColumn
    have hcolumn : column ∈ coordinates := mem_coordinates_iff.2 (by
      simp [quarterWest, quarterEast] at hwest heast
      omega)
    have hrow : row ∈ coordinates := mem_coordinates_iff.2 (by
      simp [quarterSouth, quarterNorth] at hsouth hnorth
      omega)
    have hfreeRowAudit := (freeRow_eq_true_iff parent valid parentLight cycle
      shaded coverage hrow).2 hfreeRow
    have hfreeColumnAudit : freeColumn parent (reachedBitmap (nodes parent))
        parentLight column = false := by
      cases hvalue : freeColumn parent (reachedBitmap (nodes parent))
          parentLight column
      · rfl
      · have := (freeColumn_eq_true_iff parent valid parentLight cycle
            shaded coverage hcolumn).1 hvalue
        contradiction
    simp only [ShadedObstructionGeometryOddBaseAudit.completeFor,
      List.all_eq_true] at complete
    have crossing := complete column hcolumn row hrow
    rw [Bool.and_eq_true] at crossing
    have vertical := crossing.1
    simp only [hfreeRowAudit, hfreeColumnAudit, Bool.not_true,
      Bool.false_or, Bool.or_eq_true] at vertical
    rcases vertical with (hselected | hupper) | hlower
    · exact Or.inl (selectedHorizontal_semantic parent valid parentLight cycle
        shaded hcolumn hselected)
    · exact Or.inr (Or.inl (by
        rcases upperWitness_semantic parent valid parentLight cycle shaded coverage
          hcolumn hrow hupper with
          ⟨boundary, hrb, hbn, hselected, hbetween⟩
        exact ⟨boundary, hrb, by simpa [quarterNorth] using hbn,
          hselected, hbetween⟩))
    · exact Or.inr (Or.inr (by
        rcases lowerWitness_semantic parent valid parentLight cycle shaded coverage
          hcolumn hrow hlower with
          ⟨boundary, hsb, hbr, hselected, hbetween⟩
        exact ⟨boundary, by simpa [quarterSouth] using hsb, hbr,
          hselected, hbetween⟩))
  · intro column row hwest heast hsouth hnorth hfreeColumn hnotFreeRow
    have hcolumn : column ∈ coordinates := mem_coordinates_iff.2 (by
      simp [quarterWest, quarterEast] at hwest heast
      omega)
    have hrow : row ∈ coordinates := mem_coordinates_iff.2 (by
      simp [quarterSouth, quarterNorth] at hsouth hnorth
      omega)
    have hfreeColumnAudit := (freeColumn_eq_true_iff parent valid parentLight cycle
      shaded coverage hcolumn).2 hfreeColumn
    have hfreeRowAudit : freeRow parent (reachedBitmap (nodes parent))
        parentLight row = false := by
      cases hvalue : freeRow parent (reachedBitmap (nodes parent)) parentLight row
      · rfl
      · have := (freeRow_eq_true_iff parent valid parentLight cycle shaded
            coverage hrow).1 hvalue
        contradiction
    simp only [ShadedObstructionGeometryOddBaseAudit.completeFor,
      List.all_eq_true] at complete
    have crossing := complete column hcolumn row hrow
    rw [Bool.and_eq_true] at crossing
    have horizontal := crossing.2
    simp only [hfreeColumnAudit, hfreeRowAudit, Bool.not_true,
      Bool.false_or, Bool.or_eq_true] at horizontal
    rcases horizontal with (hselected | hright) | hleft
    · exact Or.inl (selectedVertical_semantic parent valid parentLight cycle
        shaded hcolumn hselected)
    · exact Or.inr (Or.inl (by
        rcases rightWitness_semantic parent valid parentLight cycle shaded coverage
          hcolumn hrow hright with
          ⟨boundary, hcb, hbe, hselected, hbetween⟩
        exact ⟨boundary, hcb, by simpa [quarterEast] using hbe,
          hselected, hbetween⟩))
    · exact Or.inr (Or.inr (by
        rcases leftWitness_semantic parent valid parentLight cycle shaded coverage
          hcolumn hrow hleft with
          ⟨boundary, hwb, hbc, hselected, hbetween⟩
        exact ⟨boundary, by simpa [quarterWest] using hwb, hbc,
          hselected, hbetween⟩))

theorem geometry
    (parent : Index)
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid
      (localGrid parent) stateGrid)
    (parentLight : Bool)
    (cycle : CycleOn
      (localGrid parent) 2 6 2 6)
    (shaded : CycleShade stateGrid 2 6 2 6
      (if parentLight then .light else .dark)) :
    Geometry (localGrid parent)
      stateGrid 2 6 2 6 :=
  geometry_of_audit parent valid parentLight
    cycle shaded
    (coveragePaths_of_eq_true _
      (ShadedObstructionGeometryOddBaseComplete.coverageFor_eq_true parent))
    (ShadedObstructionGeometryOddBaseComplete.completeFor_eq_true
      parent parentLight)

end ShadedObstructionGeometryOddBaseSoundness
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
