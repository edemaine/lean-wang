/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamFaceStep
import LeanWang.OllingerRobinson104PairCoverSeamPathContradictions

/-!
# Created-coordinate seam cases

Most remaining one-step face queries reduce to a shade-independent even seam
path.  There is one genuine semantic residual: the selected boundary is a
retained sparse coordinate while the free line is newly created.  Separating
that residual avoids asking the finite path audit for a false property.
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

/-- Pure red-graph obligations for the created cases covered by the finite
path audits.  Vertically these are exactly a created boundary, or a sparse free
row together with a created transverse column; horizontally the roles are
transposed. -/
structure CoveredCreatedPathsAt (phase : Phase) (depth : Nat) : Prop where
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
    (¬IsSparseCoordinate boundary ∨
      (IsSparseCoordinate row ∧ ¬IsSparseCoordinate column)) →
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
    (¬IsSparseCoordinate boundary ∨
      (IsSparseCoordinate column ∧ ¬IsSparseCoordinate row)) →
    HorizontalSeamPath
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) row column boundary

/-- The vertical semantic residual not supplied by an even-path certificate:
the selected boundary is retained, but the free row is created. -/
structure ResidualVerticalBoundaryFacesAt (phase : Phase) (depth : Nat) : Prop where
  above : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < boundary →
    boundary < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    (∀ y, row < y → y < boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .north
  below : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < boundary →
    boundary < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentX)
      (successorEast phase (depth + 1) parentX) row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    (∀ y, boundary < y → y < row →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .south

/-- Horizontal dual of `ResidualVerticalBoundaryFacesAt`. -/
structure ResidualHorizontalBoundaryFacesAt (phase : Phase) (depth : Nat) : Prop where
  right : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < column →
    column < boundary →
    boundary < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    (∀ x, column < x → x < boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .east
  left : ∀ (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid →
    quarterWest (successorWest phase (depth + 1) parentX) < boundary →
    boundary < column →
    column < quarterEast (successorEast phase (depth + 1) parentX) →
    quarterSouth (successorWest phase (depth + 1) parentY) < row →
    row < quarterNorth (successorEast phase (depth + 1) parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase (depth + 1) grid)) shadeGrid
      (successorWest phase (depth + 1) parentY)
      (successorEast phase (depth + 1) parentY) column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    (∀ x, boundary < x → x < column →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
          x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase (depth + 1) parentX parentY
      column row boundary →
    IsSparseCoordinate boundary →
    ¬IsSparseCoordinate column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase (depth + 1) grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .west

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
theorem CoveredCreatedPathsAt.verticalFaces
    {phase : Phase} {depth : Nat}
    (paths : CoveredCreatedPathsAt phase depth)
    (residual : ResidualVerticalBoundaryFacesAt phase depth) :
    CreatedVerticalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hrowSouth hrowBoundary hboundaryNorth
      freeRow selected noneBetween notFits created
    by_cases hresidual :
        IsSparseCoordinate boundary ∧ ¬IsSparseCoordinate row
    · exact residual.above grid shadeGrid parentX parentY valid
        hcolumnWest hcolumnEast hrowSouth hrowBoundary hboundaryNorth
        freeRow selected noneBetween notFits hresidual.1 hresidual.2
    have hcovered : ¬IsSparseCoordinate boundary ∨
        (IsSparseCoordinate row ∧ ¬IsSparseCoordinate column) := by
      by_cases hboundary : IsSparseCoordinate boundary
      · right
        have hrow : IsSparseCoordinate row := by
          by_contra hrow
          exact hresidual ⟨hboundary, hrow⟩
        exact ⟨hrow, fun hcolumn => created ⟨hcolumn, hrow, hboundary⟩⟩
      · exact Or.inl hboundary
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
                notFits hcovered
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnEast hboundarySouth hboundaryRow hrowNorth
      freeRow selected noneBetween notFits created
    by_cases hresidual :
        IsSparseCoordinate boundary ∧ ¬IsSparseCoordinate row
    · exact residual.below grid shadeGrid parentX parentY valid
        hcolumnWest hcolumnEast hboundarySouth hboundaryRow hrowNorth
        freeRow selected noneBetween notFits hresidual.1 hresidual.2
    have hcovered : ¬IsSparseCoordinate boundary ∨
        (IsSparseCoordinate row ∧ ¬IsSparseCoordinate column) := by
      by_cases hboundary : IsSparseCoordinate boundary
      · right
        have hrow : IsSparseCoordinate row := by
          by_contra hrow
          exact hresidual ⟨hboundary, hrow⟩
        exact ⟨hrow, fun hcolumn => created ⟨hcolumn, hrow, hboundary⟩⟩
      · exact Or.inl hboundary
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
                notFits hcovered
        | south => rfl

set_option maxHeartbeats 1000000 in
-- The dependent fine grid appears throughout each face proposition.
theorem CoveredCreatedPathsAt.horizontalFaces
    {phase : Phase} {depth : Nat}
    (paths : CoveredCreatedPathsAt phase depth)
    (residual : ResidualHorizontalBoundaryFacesAt phase depth) :
    CreatedHorizontalBoundaryFacesAt phase depth := by
  constructor
  · intro grid shadeGrid parentX parentY column row boundary valid
      hcolumnWest hcolumnBoundary hboundaryEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits created
    by_cases hresidual :
        IsSparseCoordinate boundary ∧ ¬IsSparseCoordinate column
    · exact residual.right grid shadeGrid parentX parentY valid
        hcolumnWest hcolumnBoundary hboundaryEast hrowSouth hrowNorth
        freeColumn selected noneBetween notFits hresidual.1 hresidual.2
    have hcovered : ¬IsSparseCoordinate boundary ∨
        (IsSparseCoordinate column ∧ ¬IsSparseCoordinate row) := by
      by_cases hboundary : IsSparseCoordinate boundary
      · right
        have hcolumn : IsSparseCoordinate column := by
          by_contra hcolumn
          exact hresidual ⟨hboundary, hcolumn⟩
        exact ⟨hcolumn, fun hrow => created ⟨hcolumn, hrow, hboundary⟩⟩
      · exact Or.inl hboundary
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
                notFits hcovered
  · intro grid shadeGrid parentX parentY column row boundary valid
      hboundaryWest hboundaryColumn hcolumnEast hrowSouth hrowNorth
      freeColumn selected noneBetween notFits created
    by_cases hresidual :
        IsSparseCoordinate boundary ∧ ¬IsSparseCoordinate column
    · exact residual.left grid shadeGrid parentX parentY valid
        hboundaryWest hboundaryColumn hcolumnEast hrowSouth hrowNorth
        freeColumn selected noneBetween notFits hresidual.1 hresidual.2
    have hcovered : ¬IsSparseCoordinate boundary ∨
        (IsSparseCoordinate column ∧ ¬IsSparseCoordinate row) := by
      by_cases hboundary : IsSparseCoordinate boundary
      · right
        have hcolumn : IsSparseCoordinate column := by
          by_contra hcolumn
          exact hresidual ⟨hboundary, hcolumn⟩
        exact ⟨hcolumn, fun hrow => created ⟨hcolumn, hrow, hboundary⟩⟩
      · exact Or.inl hboundary
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
                notFits hcovered
        | west => rfl

/-- A previous face certificate, the finite path cases, and the exact semantic
residual give the complete next-depth face invariants. -/
theorem CoveredCreatedPathsAt.refineFaces
    {phase : Phase} {depth : Nat}
    (faces : VerticalBoundaryFacesAt phase depth ∧
      HorizontalBoundaryFacesAt phase depth)
    (paths : CoveredCreatedPathsAt phase depth)
    (verticalResidual : ResidualVerticalBoundaryFacesAt phase depth)
    (horizontalResidual : ResidualHorizontalBoundaryFacesAt phase depth) :
    VerticalBoundaryFacesAt phase (depth + 1) ∧
      HorizontalBoundaryFacesAt phase (depth + 1) :=
  ⟨PairCoverSeamFaceStep.VerticalBoundaryFacesAt.refine
      faces.1 (paths.verticalFaces verticalResidual),
    PairCoverSeamFaceStep.HorizontalBoundaryFacesAt.refine
      faces.2 (paths.horizontalFaces horizontalResidual)⟩

end PairCoverSeamCreatedPaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
