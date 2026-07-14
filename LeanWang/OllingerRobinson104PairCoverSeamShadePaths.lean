/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphProjection
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBaseSoundness
import LeanWang.OllingerRobinson104ShadedLightBoardFreeLines
import LeanWang.OllingerRobinson104PairCoverSeamPorts

/-!
# Shade contradictions for seam paths

An even red-graph path preserves light shade.  Consequently a selected seam
boundary cannot have an even path to a perpendicular red interior on a free
row or column.  This isolates the semantic shade argument from the remaining
finite hierarchy path certificate.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamShadePaths

open RedShadeCycles RedShadeGraph RedShadeGraphProjection
  RedShadeGraphRefinement RedShadePaths
  ShadedPlaneSignalGrid ShadedObstructionGeometryBaseSoundness
  Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem horizontalPort_value_eq_light
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) {x y : Nat}
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid x y) (quadrantAt x y) (stateGrid x y) ≠ none) :
    value stateGrid (horizontalPort grid x y) = some .light := by
  have shade := horizontalShade_eq_light_of_selected selected
  cases hwest : RedShades.hasWest (componentAt grid x y) (quadrantAt x y) with
  | false =>
      have present := value_isSome_eq_portPresent valid ⟨x, y, .west⟩
      have absent : (stateGrid x y).west.isSome = false := by
        simpa [value, portPresent, hwest] using present
      cases hw : (stateGrid x y).west with
      | none =>
          simpa [horizontalPort, hwest, value,
            ShadedSignals.horizontalShade?, hw] using shade
      | some value => simp [hw] at absent
  | true =>
      have allowed := valid.allowed x y
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      have westLight := horizontal_west_light_of_selected
        allowed selected hwest
      simpa [horizontalPort, hwest, value] using westLight

theorem verticalPort_value_eq_light
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) {x y : Nat}
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid x y) (quadrantAt x y) (stateGrid x y) ≠ none) :
    value stateGrid (verticalPort grid x y) = some .light := by
  have shade := verticalShade_eq_light_of_selected selected
  cases hsouth : RedShades.hasSouth (componentAt grid x y) (quadrantAt x y) with
  | false =>
      have present := value_isSome_eq_portPresent valid ⟨x, y, .south⟩
      have absent : (stateGrid x y).south.isSome = false := by
        simpa [value, portPresent, hsouth] using present
      cases hs : (stateGrid x y).south with
      | none =>
          simpa [verticalPort, hsouth, value,
            ShadedSignals.verticalShade?, hs] using shade
      | some value => simp [hs] at absent
  | true =>
      have allowed := valid.allowed x y
      unfold RedShades.locallyAllowed at allowed
      dsimp only at allowed
      have southLight := vertical_south_light_of_selected
        allowed selected hsouth
      simpa [verticalPort, hsouth, value] using southLight

theorem selectedVertical_of_port_light
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) {x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none)
    (light : value stateGrid (verticalPort grid x y) = some .light) :
    ShadedSignals.selectedVerticalFor
      (componentAt grid x y) (quadrantAt x y) (stateGrid x y) ≠ none := by
  have shade : ShadedSignals.verticalShade? (stateGrid x y) = some .light := by
    cases hsouth : RedShades.hasSouth
        (componentAt grid x y) (quadrantAt x y)
    · have present := value_isSome_eq_portPresent valid ⟨x, y, .south⟩
      have absent : (stateGrid x y).south.isSome = false := by
        simpa [value, portPresent, hsouth] using present
      cases hs : (stateGrid x y).south with
      | none =>
          simpa [verticalPort, hsouth, value, ShadedSignals.verticalShade?, hs]
            using light
      | some value => simp [hs] at absent
    · have hs : (stateGrid x y).south = some .light := by
        simpa [verticalPort, hsouth, value] using light
      simp [ShadedSignals.verticalShade?, hs]
  simp [ShadedSignals.selectedVerticalFor, shade, interior]

theorem selectedHorizontal_of_port_light
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) {x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none)
    (light : value stateGrid (horizontalPort grid x y) = some .light) :
    ShadedSignals.selectedHorizontalFor
      (componentAt grid x y) (quadrantAt x y) (stateGrid x y) ≠ none := by
  have shade : ShadedSignals.horizontalShade? (stateGrid x y) = some .light := by
    cases hwest : RedShades.hasWest
        (componentAt grid x y) (quadrantAt x y)
    · have present := value_isSome_eq_portPresent valid ⟨x, y, .west⟩
      have absent : (stateGrid x y).west.isSome = false := by
        simpa [value, portPresent, hwest] using present
      cases hw : (stateGrid x y).west with
      | none =>
          simpa [horizontalPort, hwest, value,
            ShadedSignals.horizontalShade?, hw] using light
      | some value => simp [hw] at absent
    · have hw : (stateGrid x y).west = some .light := by
        simpa [horizontalPort, hwest, value] using light
      simp [ShadedSignals.horizontalShade?, hw]
  simp [ShadedSignals.selectedHorizontalFor, shade, interior]

private theorem hasNorth_of_verticalInterior_of_not_hasSouth
    (component : Figure16.Thick) (quadrant : Quadrant)
    (interior : Signals.verticalInterior? component quadrant ≠ none)
    (notSouth : RedShades.hasSouth component quadrant ≠ true) :
    RedShades.hasNorth component quadrant = true := by
  cases component <;> cases quadrant <;>
    simp_all [Signals.verticalInterior?, RedShades.hasSouth,
      RedShades.hasNorth, RedShades.hasVertical,
      RedShades.cornerSouth, RedShades.cornerNorth]

private theorem hasEast_of_horizontalInterior_of_not_hasWest
    (component : Figure16.Thick) (quadrant : Quadrant)
    (interior : Signals.horizontalInterior? component quadrant ≠ none)
    (notWest : RedShades.hasWest component quadrant ≠ true) :
    RedShades.hasEast component quadrant = true := by
  cases component <;> cases quadrant <;>
    simp_all [Signals.horizontalInterior?, RedShades.hasWest,
      RedShades.hasEast, RedShades.hasHorizontal,
      RedShades.cornerWest, RedShades.cornerEast]

/-- A present vertical red interior that is not selected has dark shade. -/
theorem verticalPort_value_eq_dark_of_not_selected
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) {x y : Nat}
    (interior : Signals.verticalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none)
    (notSelected : ShadedSignals.selectedVerticalFor
      (componentAt grid x y) (quadrantAt x y) (stateGrid x y) = none) :
    value stateGrid (verticalPort grid x y) = some .dark := by
  have portPresent : RedShadeGraph.portPresent grid
      (verticalPort grid x y) = true := by
    unfold verticalPort
    split
    · rename_i hsouth
      simpa [RedShadeGraph.portPresent] using hsouth
    · rename_i hsouth
      have hnorth := hasNorth_of_verticalInterior_of_not_hasSouth
        (componentAt grid x y) (quadrantAt x y) interior hsouth
      change RedShades.hasNorth
        (componentAt grid x y) (quadrantAt x y) = true
      exact hnorth
  have present := value_isSome_eq_portPresent valid (verticalPort grid x y)
  rw [portPresent] at present
  cases hvalue : value stateGrid (verticalPort grid x y) with
  | none => simp [hvalue] at present
  | some shade =>
      cases shade with
      | light =>
          exact (selectedVertical_of_port_light valid interior hvalue
            notSelected).elim
      | dark => rfl

/-- A present horizontal red interior that is not selected has dark shade. -/
theorem horizontalPort_value_eq_dark_of_not_selected
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid) {x y : Nat}
    (interior : Signals.horizontalInterior?
      (componentAt grid x y) (quadrantAt x y) ≠ none)
    (notSelected : ShadedSignals.selectedHorizontalFor
      (componentAt grid x y) (quadrantAt x y) (stateGrid x y) = none) :
    value stateGrid (horizontalPort grid x y) = some .dark := by
  have portPresent : RedShadeGraph.portPresent grid
      (horizontalPort grid x y) = true := by
    unfold horizontalPort
    split
    · rename_i hwest
      simpa [RedShadeGraph.portPresent] using hwest
    · rename_i hwest
      have heast := hasEast_of_horizontalInterior_of_not_hasWest
        (componentAt grid x y) (quadrantAt x y) interior hwest
      change RedShades.hasEast
        (componentAt grid x y) (quadrantAt x y) = true
      exact heast
  have present := value_isSome_eq_portPresent valid (horizontalPort grid x y)
  rw [portPresent] at present
  cases hvalue : value stateGrid (horizontalPort grid x y) with
  | none => simp [hvalue] at present
  | some shade =>
      cases shade with
      | light =>
          exact (selectedHorizontal_of_port_light valid interior hvalue
            notSelected).elim
      | dark => rfl

theorem freeRow_forbids_even_path
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid)
    {west east column boundary targetX row : Nat}
    (freeRow : IsFreeRow grid stateGrid west east row)
    (targetWest : quarterWest west < targetX)
    (targetEast : targetX < quarterEast east)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (targetInterior : Signals.verticalInterior?
      (componentAt grid targetX row) (quadrantAt targetX row) ≠ none)
    (path : Path grid (horizontalPort grid column boundary)
      (verticalPort grid targetX row) false) : False := by
  have sourceLight := horizontalPort_value_eq_light valid selected
  have related := path.sound valid
  have relatedEq : value stateGrid (horizontalPort grid column boundary) =
      value stateGrid (verticalPort grid targetX row) := related
  have targetLight : value stateGrid (verticalPort grid targetX row) =
      some .light := relatedEq.symm.trans sourceLight
  have targetSelected := selectedVertical_of_port_light
    valid targetInterior targetLight
  exact targetSelected (freeRow targetX targetWest targetEast)

theorem freeColumn_forbids_even_path
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid stateGrid)
    {south north boundary row column targetY : Nat}
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (targetSouth : quarterSouth south < targetY)
    (targetNorth : targetY < quarterNorth north)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (targetInterior : Signals.horizontalInterior?
      (componentAt grid column targetY) (quadrantAt column targetY) ≠ none)
    (path : Path grid (verticalPort grid boundary row)
      (horizontalPort grid column targetY) false) : False := by
  have sourceLight := verticalPort_value_eq_light valid selected
  have related := path.sound valid
  have relatedEq : value stateGrid (verticalPort grid boundary row) =
      value stateGrid (horizontalPort grid column targetY) := related
  have targetLight : value stateGrid (horizontalPort grid column targetY) =
      some .light := relatedEq.symm.trans sourceLight
  have targetSelected := selectedHorizontal_of_port_light
    valid targetInterior targetLight
  exact targetSelected (freeColumn targetY targetSouth targetNorth)

end PairCoverSeamShadePaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
