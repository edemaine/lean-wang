/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104RedShadeGraphProjection
import LeanWang.OllingerRobinson104ShadedObstructionGeometryBaseSoundness

/-!
# Transfer selected boundaries through shade-grid projection

The finite hierarchy audit supplies even red-graph paths from inherited fine
boundaries to retained coarse boundaries.  This module proves the semantic
part once: light shade transfers along such a path, making the coarse boundary
selected in the projected shade grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SelectedBoundaryProjection

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphProjection
  RedShadePaths Signals.FreeCellLocal
  ShadedObstructionGeometryBaseSoundness

set_option maxRecDepth 20000

def horizontalPort (grid : Nat → Nat → Index) (x y : Nat) : Port :=
  if RedShades.hasWest (componentAt grid x y) (quadrantAt x y) then
    ⟨x, y, .west⟩
  else ⟨x, y, .east⟩

def verticalPort (grid : Nat → Nat → Index) (x y : Nat) : Port :=
  if RedShades.hasSouth (componentAt grid x y) (quadrantAt x y) then
    ⟨x, y, .south⟩
  else ⟨x, y, .north⟩

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
    cases hvalue : (stateGrid x y).west with
    | none =>
      simpa [horizontalPort, hwest, value, ShadedSignals.horizontalShade?,
        hvalue] using shade
    | some shade => simp [hvalue] at absent
  | true =>
    have allowed := valid.allowed x y
    unfold RedShades.locallyAllowed at allowed
    dsimp only at allowed
    have westLight := horizontal_west_light_of_selected allowed selected hwest
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
    cases hvalue : (stateGrid x y).south with
    | none =>
      simpa [verticalPort, hsouth, value, ShadedSignals.verticalShade?,
        hvalue] using shade
    | some shade => simp [hvalue] at absent
  | true =>
    have allowed := valid.allowed x y
    unfold RedShades.locallyAllowed at allowed
    dsimp only at allowed
    have southLight := vertical_south_light_of_selected allowed selected hsouth
    simpa [verticalPort, hsouth, value] using southLight

/-- An inherited fine horizontal boundary remains selected in the projected
coarse shade state. -/
theorem selectedHorizontal_of_even_path
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    {fineX fineY coarseX coarseY : Nat}
    (fineSelected : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 grid) fineX fineY)
      (quadrantAt fineX fineY) (stateGrid fineX fineY) ≠ none)
    (coarseInterior : Signals.horizontalInterior?
      (componentAt grid coarseX coarseY) (quadrantAt coarseX coarseY) ≠ none)
    (path : Path (iterateRefine 2 grid)
      (sparsePort (horizontalPort grid coarseX coarseY))
      (horizontalPort (iterateRefine 2 grid) fineX fineY) false) :
    ShadedSignals.selectedHorizontalFor
      (componentAt grid coarseX coarseY) (quadrantAt coarseX coarseY)
      (projectStateGrid stateGrid coarseX coarseY) ≠ none := by
  have fineLight := horizontalPort_value_eq_light valid fineSelected
  have related := path.sound valid
  have sourceLight : value stateGrid
      (sparsePort (horizontalPort grid coarseX coarseY)) = some .light :=
    (show value stateGrid (sparsePort (horizontalPort grid coarseX coarseY)) =
        value stateGrid (horizontalPort (iterateRefine 2 grid) fineX fineY)
      from related).trans fineLight
  have projectedLight : value (projectStateGrid stateGrid)
      (horizontalPort grid coarseX coarseY) = some .light := by
    cases hwest : RedShades.hasWest
        (componentAt grid coarseX coarseY) (quadrantAt coarseX coarseY) with
    | false =>
      simp only [horizontalPort, hwest, Bool.false_eq_true, ↓reduceIte,
        value] at sourceLight ⊢
      rw [projectStateGrid_eq_sparse valid]
      simpa [sparsePort] using sourceLight
    | true =>
      simp only [horizontalPort, hwest, ↓reduceIte, value] at sourceLight ⊢
      rw [projectStateGrid_eq_sparse valid]
      simpa [sparsePort] using sourceLight
  have coarseValid := projectStateGrid_valid valid
  have coarseShade : ShadedSignals.horizontalShade?
      (projectStateGrid stateGrid coarseX coarseY) = some .light := by
    cases hwest : RedShades.hasWest (componentAt grid coarseX coarseY)
        (quadrantAt coarseX coarseY) with
    | false =>
      have present := value_isSome_eq_portPresent coarseValid
          ⟨coarseX, coarseY, .west⟩
      have absent : (projectStateGrid stateGrid coarseX coarseY).west = none := by
        cases hvalue : (projectStateGrid stateGrid coarseX coarseY).west with
        | none => rfl
        | some shade =>
          have : (projectStateGrid stateGrid coarseX coarseY).west.isSome =
              false := by
            simpa [value, portPresent, hwest] using present
          simp [hvalue] at this
      simpa [horizontalPort, hwest, value, ShadedSignals.horizontalShade?,
        absent] using projectedLight
    | true =>
      have westLight : (projectStateGrid stateGrid coarseX coarseY).west =
          some .light := by
        simpa [horizontalPort, hwest, value] using projectedLight
      simp [ShadedSignals.horizontalShade?, westLight]
  unfold ShadedSignals.selectedHorizontalFor
  simp [coarseShade, coarseInterior]

/-- An inherited fine vertical boundary remains selected in the projected
coarse shade state. -/
theorem selectedVertical_of_even_path
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    {fineX fineY coarseX coarseY : Nat}
    (fineSelected : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 grid) fineX fineY)
      (quadrantAt fineX fineY) (stateGrid fineX fineY) ≠ none)
    (coarseInterior : Signals.verticalInterior?
      (componentAt grid coarseX coarseY) (quadrantAt coarseX coarseY) ≠ none)
    (path : Path (iterateRefine 2 grid)
      (sparsePort (verticalPort grid coarseX coarseY))
      (verticalPort (iterateRefine 2 grid) fineX fineY) false) :
    ShadedSignals.selectedVerticalFor
      (componentAt grid coarseX coarseY) (quadrantAt coarseX coarseY)
      (projectStateGrid stateGrid coarseX coarseY) ≠ none := by
  have fineLight := verticalPort_value_eq_light valid fineSelected
  have related := path.sound valid
  have sourceLight : value stateGrid
      (sparsePort (verticalPort grid coarseX coarseY)) = some .light :=
    (show value stateGrid (sparsePort (verticalPort grid coarseX coarseY)) =
        value stateGrid (verticalPort (iterateRefine 2 grid) fineX fineY)
      from related).trans fineLight
  have projectedLight : value (projectStateGrid stateGrid)
      (verticalPort grid coarseX coarseY) = some .light := by
    cases hsouth : RedShades.hasSouth
        (componentAt grid coarseX coarseY) (quadrantAt coarseX coarseY) with
    | false =>
      simp only [verticalPort, hsouth, Bool.false_eq_true, ↓reduceIte,
        value] at sourceLight ⊢
      rw [projectStateGrid_eq_sparse valid]
      simpa [sparsePort] using sourceLight
    | true =>
      simp only [verticalPort, hsouth, ↓reduceIte, value] at sourceLight ⊢
      rw [projectStateGrid_eq_sparse valid]
      simpa [sparsePort] using sourceLight
  have coarseValid := projectStateGrid_valid valid
  have coarseShade : ShadedSignals.verticalShade?
      (projectStateGrid stateGrid coarseX coarseY) = some .light := by
    cases hsouth : RedShades.hasSouth (componentAt grid coarseX coarseY)
        (quadrantAt coarseX coarseY) with
    | false =>
      have present := value_isSome_eq_portPresent coarseValid
          ⟨coarseX, coarseY, .south⟩
      have absent : (projectStateGrid stateGrid coarseX coarseY).south = none := by
        cases hvalue : (projectStateGrid stateGrid coarseX coarseY).south with
        | none => rfl
        | some shade =>
          have : (projectStateGrid stateGrid coarseX coarseY).south.isSome =
              false := by
            simpa [value, portPresent, hsouth] using present
          simp [hvalue] at this
      simpa [verticalPort, hsouth, value, ShadedSignals.verticalShade?,
        absent] using projectedLight
    | true =>
      have southLight : (projectStateGrid stateGrid coarseX coarseY).south =
          some .light := by
        simpa [verticalPort, hsouth, value] using projectedLight
      simp [ShadedSignals.verticalShade?, southLight]
  unfold ShadedSignals.selectedVerticalFor
  simp [coarseShade, coarseInterior]

end SelectedBoundaryProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
