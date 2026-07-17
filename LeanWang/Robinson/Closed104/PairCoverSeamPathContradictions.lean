/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamPathSearch
import LeanWang.Robinson.Closed104.PairCoverSeamShadePaths

/-! Shade contradictions obtained from the proof-producing seam searches. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathSearch

open RedCycles RedShadeCycles RedShadeGraph RedShadePaths
  PairCoverSeamShadePaths ShadedPlaneSignalGrid Signals.FreeCellLocal

theorem false_of_verticalPathCheck_of_freeRow
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel west east column boundary row : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid west east row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (checked : verticalPathCheck grid width height fuel
      west east column boundary row = true) : False := by
  rcases verticalPathCheck_sound checked with
    ⟨targetX, hwest, heast, hinterior, path⟩
  exact freeRow_forbids_even_path valid freeRow hwest heast
    selected hinterior path

theorem false_of_horizontalPathCheck_of_freeColumn
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel south north boundary row column : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (checked : horizontalPathCheck grid width height fuel
      south north boundary row column = true) : False := by
  rcases horizontalPathCheck_sound checked with
    ⟨targetY, hsouth, hnorth, hinterior, path⟩
  exact freeColumn_forbids_even_path valid freeColumn hsouth hnorth
    selected hinterior path

theorem false_of_verticalSeamPath
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east column row boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid west east row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (noneBetween : ∀ y, StrictBetween row boundary y →
      ShadedSignals.selectedHorizontalFor
        (componentAt grid column y) (quadrantAt column y)
        (stateGrid column y) = none)
    (paths : VerticalSeamPath grid west east column row boundary) : False := by
  rcases paths with perpendicular | between
  · rcases perpendicular with ⟨targetX, hwest, heast, hinterior, path⟩
    exact freeRow_forbids_even_path valid freeRow hwest heast
      selected hinterior path
  · rcases between with ⟨targetY, hbetween, hinterior, path⟩
    have sourceLight := horizontalPort_value_eq_light valid selected
    have related := path.sound valid
    have relatedEq : value stateGrid (horizontalPort grid column boundary) =
        value stateGrid (horizontalPort grid column targetY) := related
    have targetLight : value stateGrid (horizontalPort grid column targetY) =
        some .light := relatedEq.symm.trans sourceLight
    have targetSelected := selectedHorizontal_of_port_light
      valid hinterior targetLight
    exact targetSelected (noneBetween targetY hbetween)

theorem false_of_horizontalSeamPath
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {south north row column boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (noneBetween : ∀ x, StrictBetween column boundary x →
      ShadedSignals.selectedVerticalFor
        (componentAt grid x row) (quadrantAt x row)
        (stateGrid x row) = none)
    (paths : HorizontalSeamPath grid south north row column boundary) : False := by
  rcases paths with perpendicular | between
  · rcases perpendicular with ⟨targetY, hsouth, hnorth, hinterior, path⟩
    exact freeColumn_forbids_even_path valid freeColumn hsouth hnorth
      selected hinterior path
  · rcases between with ⟨targetX, hbetween, hinterior, path⟩
    have sourceLight := verticalPort_value_eq_light valid selected
    have related := path.sound valid
    have relatedEq : value stateGrid (verticalPort grid boundary row) =
        value stateGrid (verticalPort grid targetX row) := related
    have targetLight : value stateGrid (verticalPort grid targetX row) =
        some .light := relatedEq.symm.trans sourceLight
    have targetSelected := selectedVertical_of_port_light
      valid hinterior targetLight
    exact targetSelected (noneBetween targetX hbetween)

theorem false_of_verticalSeamFloodCheck
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel west east column row boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeRow : IsFreeRow grid stateGrid west east row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt grid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (noneBetween : ∀ y, StrictBetween row boundary y →
      ShadedSignals.selectedHorizontalFor
        (componentAt grid column y) (quadrantAt column y)
        (stateGrid column y) = none)
    (checked : verticalSeamFloodCheck grid width height fuel
      west east column row boundary = true) : False :=
  false_of_verticalSeamPath valid freeRow selected noneBetween
    (verticalSeamFloodCheck_sound checked)

theorem false_of_horizontalSeamFloodCheck
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {width height fuel south north row column boundary : Nat}
    (valid : ValidShadeGrid grid stateGrid)
    (freeColumn : IsFreeColumn grid stateGrid south north column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt grid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (noneBetween : ∀ x, StrictBetween column boundary x →
      ShadedSignals.selectedVerticalFor
        (componentAt grid x row) (quadrantAt x row)
        (stateGrid x row) = none)
    (checked : horizontalSeamFloodCheck grid width height fuel
      south north row column boundary = true) : False :=
  false_of_horizontalSeamPath valid freeColumn selected noneBetween
    (horizontalSeamFloodCheck_sound checked)

end PairCoverSeamPathSearch
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
