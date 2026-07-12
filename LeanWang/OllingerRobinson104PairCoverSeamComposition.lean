/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamArithmetic

/-!
# Compose contained child covers across hierarchy seams

Child covers discharge crossings localized to one recursive board.  The only
new semantic input is a nearest-boundary conclusion when the crossing and a
selected witness span a seam.  These lemmas assemble those two cases into the
contained successor geometry required by the recurrence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamComposition

open RedShadeCycles ShadedFreeLineRecurrence ShadedPlaneSignalGrid
  ShadedObstructionGeometry ShadedObstructionGeometryCover
  ShadedObstructionPairCoverRecurrence

def successorWest (phase : Phase) (depth block : Nat) : Nat :=
  2 ^ refinementDepth phase (depth + 1) * block + west phase (depth + 1)

def successorEast (phase : Phase) (depth block : Nat) : Nat :=
  2 ^ refinementDepth phase (depth + 1) * block + east phase (depth + 1)

def VerticalBoundaryConclusion
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (south north column row : Nat) : Prop :=
  ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (shadeGrid column row) ≠ none ∨
    (∃ boundary, row < boundary ∧ boundary < quarterNorth north ∧
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column boundary) (quadrantAt column boundary)
        (shadeGrid column boundary) = some .north ∧
      ∀ y, row < y → y < boundary →
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column y) (quadrantAt column y)
          (shadeGrid column y) = none) ∨
    (∃ boundary, quarterSouth south < boundary ∧ boundary < row ∧
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column boundary) (quadrantAt column boundary)
        (shadeGrid column boundary) = some .south ∧
      ∀ y, boundary < y → y < row →
        ShadedSignals.selectedHorizontalFor
          (componentAt indexGrid column y) (quadrantAt column y)
          (shadeGrid column y) = none)

def HorizontalBoundaryConclusion
    (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (west east column row : Nat) : Prop :=
  ShadedSignals.selectedVerticalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (shadeGrid column row) ≠ none ∨
    (∃ boundary, column < boundary ∧ boundary < quarterEast east ∧
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid boundary row) (quadrantAt boundary row)
        (shadeGrid boundary row) = some .east ∧
      ∀ x, column < x → x < boundary →
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid x row) (quadrantAt x row)
          (shadeGrid x row) = none) ∨
    (∃ boundary, quarterWest west < boundary ∧ boundary < column ∧
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid boundary row) (quadrantAt boundary row)
        (shadeGrid boundary row) = some .west ∧
      ∀ x, boundary < x → x < column →
        ShadedSignals.selectedVerticalFor
          (componentAt indexGrid x row) (quadrantAt x row)
          (shadeGrid x row) = none)

/-- Scale-independent seam facts still needed after recursive child covers. -/
structure BoundarySeams : Prop where
  vertical : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ContainedChildCovers phase depth grid shadeGrid →
    quarterWest (successorWest phase depth parentX) < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < quarterNorth (successorEast phase depth parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX) row →
    quarterSouth (successorWest phase depth parentY) < boundary →
    boundary < quarterNorth (successorEast phase depth parentY) →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary →
    VerticalBoundaryConclusion
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY)
      column row
  horizontal : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    ContainedChildCovers phase depth grid shadeGrid →
    quarterWest (successorWest phase depth parentX) < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < quarterNorth (successorEast phase depth parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY) column →
    quarterWest (successorWest phase depth parentX) < boundary →
    boundary < quarterEast (successorEast phase depth parentX) →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary →
    HorizontalBoundaryConclusion
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX)
      column row

set_option maxHeartbeats 1000000 in
theorem parentGeometry
    (seams : BoundarySeams)
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
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
    by_cases fits : FitsContainedVerticalChild phase depth parentX parentY
      column row boundary
    · rcases fits with ⟨childX, childY,
        hparentWest, hparentEast, hparentSouth, hparentNorth,
        hchildWest, hchildEast, hchildSouth, hchildNorth,
        hboundaryChildSouth, hboundaryChildNorth⟩
      rcases (children childX childY).vertical
        hchildWest hchildEast hchildSouth hchildNorth
        hboundaryChildSouth hboundaryChildNorth hselected with
        ⟨localWest, localEast, localSouth, localNorth,
          houterWest, houterEast, houterSouth, houterNorth,
          hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
          hboundaryLocalSouth, hboundaryLocalNorth, geometry⟩
      have localFreeRow : IsFreeRow
          (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
          localWest localEast row := by
        intro x hxWest hxEast
        exact hfreeRow x
          ((hparentWest.trans houterWest).trans_lt hxWest)
          (hxEast.trans_le (houterEast.trans hparentEast))
      have localNotFreeColumn : ¬IsFreeColumn
          (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
          localSouth localNorth column := by
        intro free
        exact hselected (free boundary hboundaryLocalSouth hboundaryLocalNorth)
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
    · exact seams.vertical phase depth grid shadeGrid parentX parentY
        valid children hwest heast hsouth hnorth hfreeRow
        hboundarySouth hboundaryNorth hselected fits
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
    by_cases fits : FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary
    · rcases fits with ⟨childX, childY,
        hparentWest, hparentEast, hparentSouth, hparentNorth,
        hchildWest, hchildEast, hchildSouth, hchildNorth,
        hboundaryChildWest, hboundaryChildEast⟩
      rcases (children childX childY).horizontal
        hchildWest hchildEast hchildSouth hchildNorth
        hboundaryChildWest hboundaryChildEast hselected with
        ⟨localWest, localEast, localSouth, localNorth,
          houterWest, houterEast, houterSouth, houterNorth,
          hlocalWest, hlocalEast, hlocalSouth, hlocalNorth,
          hboundaryLocalWest, hboundaryLocalEast, geometry⟩
      have localFreeColumn : IsFreeColumn
          (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
          localSouth localNorth column := by
        intro y hySouth hyNorth
        exact hfreeColumn y
          ((hparentSouth.trans houterSouth).trans_lt hySouth)
          (hyNorth.trans_le (houterNorth.trans hparentNorth))
      have localNotFreeRow : ¬IsFreeRow
          (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
          localWest localEast row := by
        intro free
        exact hselected (free boundary hboundaryLocalWest hboundaryLocalEast)
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
    · exact seams.horizontal phase depth grid shadeGrid parentX parentY
        valid children hwest heast hsouth hnorth hfreeColumn
        hboundaryWest hboundaryEast hselected fits

theorem containedSeamCover_of_boundarySeams
    (seams : BoundarySeams) : ContainedSeamCover := by
  constructor
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid children hwest heast hsouth hnorth hboundarySouth
      hboundaryNorth _ _
    have geometry := parentGeometry seams phase depth grid shadeGrid
      parentX parentY valid children
    exact ⟨successorWest phase depth parentX,
      successorEast phase depth parentX,
      successorWest phase depth parentY,
      successorEast phase depth parentY,
      le_rfl, le_rfl, le_rfl, le_rfl,
      hwest, heast, hsouth, hnorth,
      hboundarySouth, hboundaryNorth, geometry⟩
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid children hwest heast hsouth hnorth hboundaryWest
      hboundaryEast _ _
    have geometry := parentGeometry seams phase depth grid shadeGrid
      parentX parentY valid children
    exact ⟨successorWest phase depth parentX,
      successorEast phase depth parentX,
      successorWest phase depth parentY,
      successorEast phase depth parentY,
      le_rfl, le_rfl, le_rfl, le_rfl,
      hwest, heast, hsouth, hnorth,
      hboundaryWest, hboundaryEast, geometry⟩

theorem forcesRoutedFixedCornerSquares_of_boundarySeams
    (seams : BoundarySeams) :
    ShadedRoutedScaffoldForward.ForcesRoutedFixedCornerSquares
      ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_containedSeamCover
    (containedSeamCover_of_boundarySeams seams)

end PairCoverSeamComposition
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
