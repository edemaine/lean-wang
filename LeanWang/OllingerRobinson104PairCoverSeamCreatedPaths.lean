/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamFaceStep
import LeanWang.OllingerRobinson104PairCoverSeamPathContradictions

/-!
# Created-coordinate seam paths

This module removes shade semantics from the remaining one-step face
obligation.  A finite geometric certificate only has to provide an even seam
path for each wrong-facing query with at least one created coordinate.  The
standard shade contradiction then supplies both created face structures.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedPaths

open Figure16 RedCycles RedShadeCycles RedShadeGraph RedShadePaths
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid Signals.FreeCellLocal
  ShadedObstructionPairCoverRecurrence
  PairCoverSeamArithmetic PairCoverSeamComposition PairCoverSeamFacesAt
  PairCoverSeamFaceStep PairCoverSeamPathSearch SparseFreeLinePlaneBase
  RefinedCoordinateProjection

set_option maxRecDepth 20000

/-- Pure red-graph obligations for all genuinely created cases in one
two-substitution refinement step. -/
structure CreatedPathsAt (phase : Phase) (depth : Nat) : Prop where
  vertical : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    ((row < boundary ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            column boundary)
          (quadrantAt column boundary) = some .south) ∨
      (boundary < row ∧
        Signals.horizontalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            column boundary)
          (quadrantAt column boundary) = some .north)) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬(IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
      IsSparseCoordinate boundary) →
    VerticalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) column row boundary
  horizontal : ∀ (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    ((column < boundary ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            boundary row)
          (quadrantAt boundary row) = some .west) ∨
      (boundary < column ∧
        Signals.verticalInterior?
          (componentAt
            (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
            boundary row)
          (quadrantAt boundary row) = some .east)) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    ¬(IsSparseCoordinate column ∧ IsSparseCoordinate row ∧
      IsSparseCoordinate boundary) →
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary

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
-- The dependent fine grid appears throughout each face proposition.
theorem CreatedPathsAt.verticalFaces
    {phase : Phase} {depth : Nat} (paths : CreatedPathsAt phase depth) :
    CreatedVerticalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hrowSouth hrowBoundary hboundaryNorth
      freeRow selected noneBetween notFits created
    cases hselected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
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
            · exact paths.vertical grid parentX parentY hcolumnWest hcolumnEast
                hrowSouth (hrowBoundary.trans hboundaryNorth)
                (hrowSouth.trans hrowBoundary) hboundaryNorth
                (Or.inl ⟨hrowBoundary,
                  horizontalInterior_eq_of_selected_eq hselected⟩)
                notFits created
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hboundarySouth hboundaryRow hrowNorth
      freeRow selected noneBetween notFits created
    cases hselected : ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
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
            · exact paths.vertical grid parentX parentY hcolumnWest hcolumnEast
                (hboundarySouth.trans hboundaryRow) hrowNorth
                hboundarySouth (hboundaryRow.trans hrowNorth)
                (Or.inr ⟨hboundaryRow,
                  horizontalInterior_eq_of_selected_eq hselected⟩)
                notFits created
        | south => rfl

set_option maxHeartbeats 1000000 in
-- The dependent fine grid appears throughout each face proposition.
theorem CreatedPathsAt.horizontalFaces
    {phase : Phase} {depth : Nat} (paths : CreatedPathsAt phase depth) :
    CreatedHorizontalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnBoundary hboundaryEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits created
    cases hselected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
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
            · exact paths.horizontal grid parentX parentY hcolumnWest
                (hcolumnBoundary.trans hboundaryEast) hrowSouth hrowNorth
                (hcolumnWest.trans hcolumnBoundary) hboundaryEast
                (Or.inl ⟨hcolumnBoundary,
                  verticalInterior_eq_of_selected_eq hselected⟩)
                notFits created
  · intro grid shadeGrid parentX parentY column row boundary valid
      hboundaryWest hboundaryColumn hcolumnEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits created
    cases hselected : ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
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
            · exact paths.horizontal grid parentX parentY
                (hboundaryWest.trans hboundaryColumn) hcolumnEast
                hrowSouth hrowNorth hboundaryWest
                (hboundaryColumn.trans hcolumnEast)
                (Or.inr ⟨hboundaryColumn,
                  verticalInterior_eq_of_selected_eq hselected⟩)
                notFits created
        | west => rfl

/-- A previous face certificate and a shade-independent created-path
certificate give the complete next-depth face invariants. -/
theorem CreatedPathsAt.refineFaces
    {phase : Phase} {depth : Nat}
    (faces : VerticalBoundaryFacesAt phase depth ∧
      HorizontalBoundaryFacesAt phase depth)
    (paths : CreatedPathsAt phase depth) :
    VerticalBoundaryFacesAt phase (depth + 1) ∧
      HorizontalBoundaryFacesAt phase (depth + 1) :=
  ⟨PairCoverSeamFaceStep.VerticalBoundaryFacesAt.refine
      faces.1 paths.verticalFaces,
    PairCoverSeamFaceStep.HorizontalBoundaryFacesAt.refine
      faces.2 paths.horizontalFaces⟩

end PairCoverSeamCreatedPaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
