/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamFaceRequired
import LeanWang.OllingerRobinson104PairCoverSeamForward
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathAllFamilyTargetsAllDepth
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyExceptionalAllDepth

/-!
# Required-depth seam faces imply forward square forcing

The final light-board construction uses only the even boards at depths `1 + d`
and the odd boards at depths `d`.  This module assembles contained pair covers
directly from the fixed-depth face structures, avoiding the stronger and unused
requirement of an even depth-zero face certificate.
-/

noncomputable section

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamRequiredForward

open RedCycles RedShadeCycles RedShadePaths RedShadeGraphRefinement
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid
  ShadedObstructionGeometry ShadedObstructionGeometryCover
  ShadedObstructionPairCoverRecurrence ShadedRoutedScaffoldForward
  SparseFreeLinePlaneBase Signals.FreeCellLocal
  PairCoverSeamArithmetic PairCoverSeamComposition PairCoverSeamFacesAt
  PairCoverSeamFaceRecurrence PairCoverSeamFaceRequired
  PairCoverSeamResidualDirectPathAllFamilyTargetsAllDepth
  PairCoverSeamResidualDirectPathFamilyExceptionalAllDepth
  PairCoverSeamResidualDirectPathFamilyExceptionalTargets

set_option maxRecDepth 20000

private theorem verticalConclusion_of_child
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY column row boundary : Nat)
    (children : ContainedChildCovers phase depth grid shadeGrid)
    (freeRow : IsFreeRow
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX) row)
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none)
    (fits : FitsContainedVerticalChild phase depth parentX parentY
      column row boundary) :
    VerticalBoundaryConclusion
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY)
      column row := by
  rcases fits with ⟨childX, childY,
    hparentWest, hparentEast, hparentSouth, hparentNorth,
    hchildWest, hchildEast, hchildSouth, hchildNorth,
    hboundaryChildSouth, hboundaryChildNorth⟩
  rcases (children childX childY).vertical
    hchildWest hchildEast hchildSouth hchildNorth
    hboundaryChildSouth hboundaryChildNorth selected with
    ⟨localWest, localEast, localSouth, localNorth,
      houterWest, houterEast, houterSouth, houterNorth,
      hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
      hboundaryLocalSouth, hboundaryLocalNorth, geometry⟩
  have localFreeRow : IsFreeRow
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      localWest localEast row := by
    intro x hxWest hxEast
    exact freeRow x
      ((hparentWest.trans houterWest).trans_lt hxWest)
      (hxEast.trans_le (houterEast.trans hparentEast))
  have localNotFreeColumn : ¬IsFreeColumn
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      localSouth localNorth column := by
    intro free
    exact selected (free boundary hboundaryLocalSouth hboundaryLocalNorth)
  rcases geometry.verticalBoundary hlocalWest hlocalEast
    hlocalSouth hlocalNorth localFreeRow localNotFreeColumn with
    hat | hupper | hlower
  · exact Or.inl hat
  · rcases hupper with ⟨found, hrowFound, hfoundNorth,
      hfoundSelected, hbetween⟩
    exact Or.inr (Or.inl ⟨found, hrowFound,
      hfoundNorth.trans_le (houterNorth.trans hparentNorth),
      hfoundSelected, hbetween⟩)
  · rcases hlower with ⟨found, hfoundSouth, hfoundRow,
      hfoundSelected, hbetween⟩
    exact Or.inr (Or.inr ⟨found,
      (hparentSouth.trans houterSouth).trans_lt hfoundSouth,
      hfoundRow, hfoundSelected, hbetween⟩)

set_option maxHeartbeats 1000000 in
-- The nearest selected boundary may fall inside a child cover or on a seam.
theorem verticalBoundaryConclusion_of_facesAt
    {phase : Phase} {depth : Nat}
    (faces : VerticalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY column row boundary : Nat)
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid)
    (children : ContainedChildCovers phase depth grid shadeGrid)
    (hwest : quarterWest (successorWest phase depth parentX) < column)
    (heast : column < quarterEast (successorEast phase depth parentX))
    (hsouth : quarterSouth (successorWest phase depth parentY) < row)
    (hnorth : row < quarterNorth (successorEast phase depth parentY))
    (freeRow : IsFreeRow
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX) row)
    (hboundarySouth : quarterSouth (successorWest phase depth parentY) < boundary)
    (hboundaryNorth : boundary < quarterNorth (successorEast phase depth parentY))
    (selected : ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none) :
    VerticalBoundaryConclusion
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY)
      column row := by
  let P : Nat → Prop := fun y =>
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) column y)
      (quadrantAt column y) (shadeGrid column y) ≠ none
  rcases lt_trichotomy row boundary with hrowBoundary | rfl | hboundaryRow
  · rcases exists_first_after (P := P) hrowBoundary selected with
      ⟨found, hrowFound, hfoundBoundary, foundSelected, hbetween⟩
    have hfoundNorth : found < quarterNorth (successorEast phase depth parentY) :=
      hfoundBoundary.trans_lt hboundaryNorth
    have hnone : ∀ y, row < y → y < found →
        ShadedSignals.selectedHorizontalFor
          (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) column y)
          (quadrantAt column y) (shadeGrid column y) = none := by
      intro y hyRow hyFound
      by_contra hySelected
      exact hbetween y hyRow hyFound hySelected
    by_cases fits : FitsContainedVerticalChild phase depth parentX parentY
      column row found
    · exact verticalConclusion_of_child phase depth grid shadeGrid
        parentX parentY column row found children freeRow foundSelected fits
    · have foundFacesNorth := faces.above grid shadeGrid parentX parentY valid
        hwest heast hsouth hrowFound hfoundNorth freeRow foundSelected hnone fits
      exact Or.inr (Or.inl ⟨found, hrowFound, hfoundNorth,
        foundFacesNorth, hnone⟩)
  · exact Or.inl selected
  · rcases exists_last_before (P := P) hboundaryRow selected with
      ⟨found, hboundaryFound, hfoundRow, foundSelected, hbetween⟩
    have hfoundSouth : quarterSouth (successorWest phase depth parentY) < found :=
      hboundarySouth.trans_le hboundaryFound
    have hnone : ∀ y, found < y → y < row →
        ShadedSignals.selectedHorizontalFor
          (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) column y)
          (quadrantAt column y) (shadeGrid column y) = none := by
      intro y hyFound hyRow
      by_contra hySelected
      exact hbetween y hyFound hyRow hySelected
    by_cases fits : FitsContainedVerticalChild phase depth parentX parentY
      column row found
    · exact verticalConclusion_of_child phase depth grid shadeGrid
        parentX parentY column row found children freeRow foundSelected fits
    · have foundFacesSouth := faces.below grid shadeGrid parentX parentY valid
        hwest heast hfoundSouth hfoundRow hnorth freeRow foundSelected hnone fits
      exact Or.inr (Or.inr ⟨found, hfoundSouth, hfoundRow,
        foundFacesSouth, hnone⟩)

private theorem horizontalConclusion_of_child
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY column row boundary : Nat)
    (children : ContainedChildCovers phase depth grid shadeGrid)
    (freeColumn : IsFreeColumn
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY) column)
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none)
    (fits : FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary) :
    HorizontalBoundaryConclusion
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX)
      column row := by
  rcases fits with ⟨childX, childY,
    hparentWest, hparentEast, hparentSouth, hparentNorth,
    hchildWest, hchildEast, hchildSouth, hchildNorth,
    hboundaryChildWest, hboundaryChildEast⟩
  rcases (children childX childY).horizontal
    hchildWest hchildEast hchildSouth hchildNorth
    hboundaryChildWest hboundaryChildEast selected with
    ⟨localWest, localEast, localSouth, localNorth,
      houterWest, houterEast, houterSouth, houterNorth,
      hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
      hboundaryLocalWest, hboundaryLocalEast, geometry⟩
  have localFreeColumn : IsFreeColumn
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      localSouth localNorth column := by
    intro y hySouth hyNorth
    exact freeColumn y
      ((hparentSouth.trans houterSouth).trans_lt hySouth)
      (hyNorth.trans_le (houterNorth.trans hparentNorth))
  have localNotFreeRow : ¬IsFreeRow
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      localWest localEast row := by
    intro free
    exact selected (free boundary hboundaryLocalWest hboundaryLocalEast)
  rcases geometry.horizontalBoundary hlocalWest hlocalEast
    hlocalSouth hlocalNorth localFreeColumn localNotFreeRow with
    hat | hright | hleft
  · exact Or.inl hat
  · rcases hright with ⟨found, hcolumnFound, hfoundEast,
      hfoundSelected, hbetween⟩
    exact Or.inr (Or.inl ⟨found, hcolumnFound,
      hfoundEast.trans_le (houterEast.trans hparentEast),
      hfoundSelected, hbetween⟩)
  · rcases hleft with ⟨found, hfoundWest, hfoundColumn,
      hfoundSelected, hbetween⟩
    exact Or.inr (Or.inr ⟨found,
      (hparentWest.trans houterWest).trans_lt hfoundWest,
      hfoundColumn, hfoundSelected, hbetween⟩)

set_option maxHeartbeats 1000000 in
-- Horizontal dual of the fixed-depth vertical boundary argument.
theorem horizontalBoundaryConclusion_of_facesAt
    {phase : Phase} {depth : Nat}
    (faces : HorizontalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY column row boundary : Nat)
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid)
    (children : ContainedChildCovers phase depth grid shadeGrid)
    (hwest : quarterWest (successorWest phase depth parentX) < column)
    (heast : column < quarterEast (successorEast phase depth parentX))
    (hsouth : quarterSouth (successorWest phase depth parentY) < row)
    (hnorth : row < quarterNorth (successorEast phase depth parentY))
    (freeColumn : IsFreeColumn
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY) column)
    (hboundaryWest : quarterWest (successorWest phase depth parentX) < boundary)
    (hboundaryEast : boundary < quarterEast (successorEast phase depth parentX))
    (selected : ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none) :
    HorizontalBoundaryConclusion
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX)
      column row := by
  let P : Nat → Prop := fun x =>
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) x row)
      (quadrantAt x row) (shadeGrid x row) ≠ none
  rcases lt_trichotomy column boundary with hcolumnBoundary | rfl | hboundaryColumn
  · rcases exists_first_after (P := P) hcolumnBoundary selected with
      ⟨found, hcolumnFound, hfoundBoundary, foundSelected, hbetween⟩
    have hfoundEast : found < quarterEast (successorEast phase depth parentX) :=
      hfoundBoundary.trans_lt hboundaryEast
    have hnone : ∀ x, column < x → x < found →
        ShadedSignals.selectedVerticalFor
          (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) x row)
          (quadrantAt x row) (shadeGrid x row) = none := by
      intro x hxColumn hxFound
      by_contra hxSelected
      exact hbetween x hxColumn hxFound hxSelected
    by_cases fits : FitsContainedHorizontalChild phase depth parentX parentY
      column row found
    · exact horizontalConclusion_of_child phase depth grid shadeGrid
        parentX parentY column row found children freeColumn foundSelected fits
    · have foundFacesEast := faces.right grid shadeGrid parentX parentY valid
        hwest hcolumnFound hfoundEast hsouth hnorth freeColumn foundSelected hnone fits
      exact Or.inr (Or.inl ⟨found, hcolumnFound, hfoundEast,
        foundFacesEast, hnone⟩)
  · exact Or.inl selected
  · rcases exists_last_before (P := P) hboundaryColumn selected with
      ⟨found, hboundaryFound, hfoundColumn, foundSelected, hbetween⟩
    have hfoundWest : quarterWest (successorWest phase depth parentX) < found :=
      hboundaryWest.trans_le hboundaryFound
    have hnone : ∀ x, found < x → x < column →
        ShadedSignals.selectedVerticalFor
          (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) x row)
          (quadrantAt x row) (shadeGrid x row) = none := by
      intro x hxFound hxColumn
      by_contra hxSelected
      exact hbetween x hxFound hxColumn hxSelected
    by_cases fits : FitsContainedHorizontalChild phase depth parentX parentY
      column row found
    · exact horizontalConclusion_of_child phase depth grid shadeGrid
        parentX parentY column row found children freeColumn foundSelected fits
    · have foundFacesWest := faces.left grid shadeGrid parentX parentY valid
        hfoundWest hfoundColumn heast hsouth hnorth freeColumn foundSelected hnone fits
      exact Or.inr (Or.inr ⟨found, hfoundWest, hfoundColumn,
        foundFacesWest, hnone⟩)

set_option maxHeartbeats 1000000 in
-- Child geometries handle inherited regions; fixed-depth faces handle seams.
theorem parentGeometry_of_facesAt
    {phase : Phase} {depth : Nat}
    (verticalFaces : VerticalBoundaryFacesAt phase depth)
    (horizontalFaces : HorizontalBoundaryFacesAt phase depth)
    (grid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (parentX parentY : Nat)
    (valid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid)
    (children : ContainedChildCovers phase depth grid shadeGrid) :
    Geometry (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX)
      (successorWest phase depth parentY) (successorEast phase depth parentY) := by
  classical
  constructor
  · intro column row hwest heast hsouth hnorth hfreeRow hnotFreeColumn
    have selectedWitness : ∃ boundary,
        quarterSouth (successorWest phase depth parentY) < boundary ∧
        boundary < quarterNorth (successorEast phase depth parentY) ∧
        ShadedSignals.selectedHorizontalFor
          (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
            column boundary)
          (quadrantAt column boundary) (shadeGrid column boundary) ≠ none := by
      by_contra hnone
      apply hnotFreeColumn
      intro boundary hboundarySouth hboundaryNorth
      by_contra hselected
      exact hnone ⟨boundary, hboundarySouth, hboundaryNorth, hselected⟩
    rcases selectedWitness with
      ⟨boundary, hboundarySouth, hboundaryNorth, hselected⟩
    exact verticalBoundaryConclusion_of_facesAt verticalFaces grid shadeGrid
      parentX parentY column row boundary valid children hwest heast hsouth hnorth
      hfreeRow hboundarySouth hboundaryNorth hselected
  · intro column row hwest heast hsouth hnorth hfreeColumn hnotFreeRow
    have selectedWitness : ∃ boundary,
        quarterWest (successorWest phase depth parentX) < boundary ∧
        boundary < quarterEast (successorEast phase depth parentX) ∧
        ShadedSignals.selectedVerticalFor
          (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
            boundary row)
          (quadrantAt boundary row) (shadeGrid boundary row) ≠ none := by
      by_contra hnone
      apply hnotFreeRow
      intro boundary hboundaryWest hboundaryEast
      by_contra hselected
      exact hnone ⟨boundary, hboundaryWest, hboundaryEast, hselected⟩
    rcases selectedWitness with
      ⟨boundary, hboundaryWest, hboundaryEast, hselected⟩
    exact horizontalBoundaryConclusion_of_facesAt horizontalFaces grid shadeGrid
      parentX parentY column row boundary valid children hwest heast hsouth hnorth
      hfreeColumn hboundaryWest hboundaryEast hselected

/-- Fixed-depth face certificates advance the contained pair-cover invariant by
one hierarchy level. -/
theorem containedHolds_succ_of_facesAt
    {phase : Phase} {depth : Nat}
    (verticalFaces : VerticalBoundaryFacesAt phase depth)
    (horizontalFaces : HorizontalBoundaryFacesAt phase depth)
    (holds : ContainedHolds phase depth) :
    ContainedHolds phase (depth + 1) := by
  intro grid shadeGrid valid parentX parentY
  have fineValid : ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid := by
    simpa only [refinedGrid_succ] using valid
  have children := holds.childCovers fineValid
  have geometry := parentGeometry_of_facesAt verticalFaces horizontalFaces
    grid shadeGrid parentX parentY fineValid children
  have cover := containedPairCover_of_geometry geometry
  simpa only [refinedGrid_succ, successorWest, successorEast] using cover

/-- The two required face families produce exactly the contained boards used by
the unbounded light-board construction. -/
theorem allContainedHolds_of_requiredFaces
    (faces : ∀ depth : Nat,
      (VerticalBoundaryFacesAt .even (1 + depth) ∧
        HorizontalBoundaryFacesAt .even (1 + depth)) ∧
      (VerticalBoundaryFacesAt .odd depth ∧
        HorizontalBoundaryFacesAt .odd depth)) :
    AllContainedHolds := by
  intro size
  constructor
  · induction size with
    | zero => simpa using contained_even_one
    | succ size ih =>
        have step := containedHolds_succ_of_facesAt
          (faces size).1.1 (faces size).1.2 ih
        simpa [Nat.add_assoc] using step
  · induction size with
    | zero => exact contained_odd_zero
    | succ size ih =>
        simpa using containedHolds_succ_of_facesAt
          (faces size).2.1 (faces size).2.2 ih

/-- Required-depth boundary faces imply the routed scaffold's forward
fixed-corner-square property. -/
theorem forcesRoutedFixedCornerSquares_of_requiredFaces
    (faces : ∀ depth : Nat,
      (VerticalBoundaryFacesAt .even (1 + depth) ∧
        HorizontalBoundaryFacesAt .even (1 + depth)) ∧
      (VerticalBoundaryFacesAt .odd depth ∧
        HorizontalBoundaryFacesAt .odd depth)) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares
    (lightBoardPairCovers_of_allHolds
      (allContainedHolds_of_requiredFaces faces).allHolds)

/-- Semantic one-step data at the used depths is sufficient for forward square
forcing; no all-depth bounded-search hypothesis remains. -/
theorem forcesRoutedFixedCornerSquares_of_stepData
    (oddSteps : ∀ depth : Nat, StepData .odd depth)
    (evenSteps : ∀ depth : Nat, StepData .even (1 + depth)) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_requiredFaces
    (requiredFaces oddSteps evenSteps)

/-- Exceptional projected-query targets are the sole remaining semantic input
to forward square forcing. -/
theorem forcesRoutedFixedCornerSquares_of_exceptionalTargets
    (oddExceptional :
      ∀ depth, ExceptionalFamilyTargetsAt .odd (depth + 1))
    (evenExceptional :
      ∀ depth, ExceptionalFamilyTargetsAt .even (depth + 1)) :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_stepData
    (oddStepData oddExceptional) (evenStepData evenExceptional)

/-- The corrected 104-symbol substitution unconditionally forces every routed
fixed-corner square required by the scaffold reduction. -/
theorem closed104_forcesRoutedFixedCornerSquares :
    ForcesRoutedFixedCornerSquares ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_exceptionalTargets
    (fun depth => odd (depth + 1))
    (fun depth => even (depth + 1))

end PairCoverSeamRequiredForward
end LeanWang.OllingerRobinson.Figure13Layers.Closed104

end
