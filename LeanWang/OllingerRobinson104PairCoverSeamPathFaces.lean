/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamComposition
import LeanWang.OllingerRobinson104PairCoverSeamPathContradictions
import LeanWang.OllingerRobinson104PairCoverSeamPathTranslation

/-!
# Boundary orientations from seam-path certificates

A wrong-facing selected boundary gives one of the certified even seam paths.
Shade preservation contradicts either the queried free line or the absence of
another selected boundary strictly between the query and that boundary.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamPathFaces

open Figure16 RedCycles RedShadeCycles RedShadeGraph RedShadePaths
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid Signals.FreeCellLocal
  PairCoverSeamArithmetic PairCoverSeamComposition
  PairCoverSeamPathBoundedBase PairCoverSeamPathSearch
  PairCoverSeamPathTranslation SparseFreeLinePlaneBase

set_option maxRecDepth 20000

private theorem horizontalInterior_eq_of_selected_eq
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    {interior : Signals.VerticalInterior}
    (selected : ShadedSignals.selectedHorizontalFor
      component quadrant state = some interior) :
    Signals.horizontalInterior? component quadrant = some interior := by
  unfold ShadedSignals.selectedHorizontalFor at selected
  split at selected
  · exact selected
  · contradiction

private theorem verticalInterior_eq_of_selected_eq
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    {interior : Signals.HorizontalInterior}
    (selected : ShadedSignals.selectedVerticalFor
      component quadrant state = some interior) :
    Signals.verticalInterior? component quadrant = some interior := by
  unfold ShadedSignals.selectedVerticalFor at selected
  split at selected
  · exact selected
  · contradiction

set_option maxHeartbeats 1000000 in
-- The four dependent grid occurrences make elaboration exceed the default.
theorem BoundedPaths.verticalBoundaryFaces
    (paths : ∀ (phase : Phase) (depth : Nat), BoundedPaths phase depth) :
    VerticalBoundaryFaces := by
  constructor
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid hcolumnWest hcolumnEast hrowSouth hrowBoundary hboundaryNorth
      freeRow selected noneBetween notFits
    cases hselected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
          column boundary)
        (quadrantAt column boundary) (shadeGrid column boundary) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | north => rfl
        | south =>
            exfalso
            apply false_of_verticalSeamPath valid freeRow selected
            · intro y hbetween
              rcases hbetween with hbetween | hbetween
              · exact noneBetween y hbetween.1 hbetween.2
              · omega
            · apply BoundedPaths.verticalSeamPath (paths phase depth)
                grid parentX parentY
                hcolumnWest hcolumnEast hrowSouth
                (hrowBoundary.trans hboundaryNorth)
                (hrowSouth.trans hrowBoundary) hboundaryNorth
              · left
                exact ⟨hrowBoundary,
                  horizontalInterior_eq_of_selected_eq hselected⟩
              · exact notFits
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid hcolumnWest hcolumnEast hboundarySouth hboundaryRow hrowNorth
      freeRow selected noneBetween notFits
    cases hselected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
          column boundary)
        (quadrantAt column boundary) (shadeGrid column boundary) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | north =>
            exfalso
            apply false_of_verticalSeamPath valid freeRow selected
            · intro y hbetween
              rcases hbetween with hbetween | hbetween
              · omega
              · exact noneBetween y hbetween.1 hbetween.2
            · apply BoundedPaths.verticalSeamPath (paths phase depth)
                grid parentX parentY
                hcolumnWest hcolumnEast
                (hboundarySouth.trans hboundaryRow) hrowNorth
                hboundarySouth (hboundaryRow.trans hrowNorth)
              · right
                exact ⟨hboundaryRow,
                  horizontalInterior_eq_of_selected_eq hselected⟩
              · exact notFits
        | south => rfl

set_option maxHeartbeats 1000000 in
-- The four dependent grid occurrences make elaboration exceed the default.
theorem BoundedPaths.horizontalBoundaryFaces
    (paths : ∀ (phase : Phase) (depth : Nat), BoundedPaths phase depth) :
    HorizontalBoundaryFaces := by
  constructor
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid hcolumnWest hcolumnBoundary hboundaryEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits
    cases hselected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
          boundary row)
        (quadrantAt boundary row) (shadeGrid boundary row) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | east => rfl
        | west =>
            exfalso
            apply false_of_horizontalSeamPath valid freeColumn selected
            · intro x hbetween
              rcases hbetween with hbetween | hbetween
              · exact noneBetween x hbetween.1 hbetween.2
              · omega
            · apply BoundedPaths.horizontalSeamPath (paths phase depth)
                grid parentX parentY
                hcolumnWest (hcolumnBoundary.trans hboundaryEast)
                hrowSouth hrowNorth
                (hcolumnWest.trans hcolumnBoundary) hboundaryEast
              · left
                exact ⟨hcolumnBoundary,
                  verticalInterior_eq_of_selected_eq hselected⟩
              · exact notFits
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid hboundaryWest hboundaryColumn hcolumnEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits
    cases hselected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
          boundary row)
        (quadrantAt boundary row) (shadeGrid boundary row) with
    | none => exact (selected hselected).elim
    | some interior =>
        cases interior with
        | east =>
            exfalso
            apply false_of_horizontalSeamPath valid freeColumn selected
            · intro x hbetween
              rcases hbetween with hbetween | hbetween
              · omega
              · exact noneBetween x hbetween.1 hbetween.2
            · apply BoundedPaths.horizontalSeamPath (paths phase depth)
                grid parentX parentY
                (hboundaryWest.trans hboundaryColumn) hcolumnEast
                hrowSouth hrowNorth hboundaryWest
                (hboundaryColumn.trans hcolumnEast)
              · right
                exact ⟨hboundaryColumn,
                  verticalInterior_eq_of_selected_eq hselected⟩
              · exact notFits
        | west => rfl

end PairCoverSeamPathFaces
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
