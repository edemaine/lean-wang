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

open RedCycles RedShadeCycles RedShadePaths RedShadeGraphRefinement
  ShadedFreeLineRecurrence ShadedPlaneSignalGrid
  ShadedObstructionGeometry ShadedObstructionGeometryCover
  ShadedObstructionPairCoverRecurrence SparseFreeLinePlaneBase
  Signals.FreeCellLocal PairCoverSeamArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem exists_first_after
    {P : Nat → Prop} {start finish : Nat}
    (hstart : start < finish) (hfinish : P finish) :
    ∃ first, start < first ∧ first ≤ finish ∧ P first ∧
      ∀ value, start < value → value < first → ¬P value := by
  classical
  let Q : Nat → Prop := fun distance =>
    0 < distance ∧ start + distance ≤ finish ∧ P (start + distance)
  have existsQ : ∃ distance, Q distance := by
    refine ⟨finish - start, ?_⟩
    dsimp [Q]
    have : start + (finish - start) = finish := by omega
    exact ⟨by omega, by omega, by simpa [this] using hfinish⟩
  let distance := Nat.find existsQ
  have found : Q distance := by
    dsimp [distance]
    exact Nat.find_spec existsQ
  refine ⟨start + distance, by omega, found.2.1, found.2.2, ?_⟩
  intro value hvalueStart hvalueFirst hvalue
  have candidate : Q (value - start) := by
    dsimp [Q]
    have hsum : start + (value - start) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsum] using hvalue⟩
  have minimal : distance ≤ value - start := by
    dsimp [distance]
    exact Nat.find_min' existsQ candidate
  dsimp [distance] at hvalueFirst
  omega

theorem exists_last_before
    {P : Nat → Prop} {first finish : Nat}
    (hfirst : first < finish) (hfirstP : P first) :
    ∃ last, first ≤ last ∧ last < finish ∧ P last ∧
      ∀ value, last < value → value < finish → ¬P value := by
  classical
  let Q : Nat → Prop := fun distance =>
    0 < distance ∧ distance ≤ finish - first ∧ P (finish - distance)
  have existsQ : ∃ distance, Q distance := by
    refine ⟨finish - first, ?_⟩
    dsimp [Q]
    have : finish - (finish - first) = first := by omega
    exact ⟨by omega, le_rfl, by simpa [this] using hfirstP⟩
  let distance := Nat.find existsQ
  have found : Q distance := by
    dsimp [distance]
    exact Nat.find_spec existsQ
  refine ⟨finish - distance, by omega, by omega, found.2.2, ?_⟩
  intro value hlastValue hvalueFinish hvalue
  have candidate : Q (finish - value) := by
    dsimp [Q]
    have hsub : finish - (finish - value) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsub] using hvalue⟩
  have minimal : distance ≤ finish - value := by
    dsimp [distance]
    exact Nat.find_min' existsQ candidate
  dsimp [distance] at hlastValue
  omega

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

/-- The vertical finite audit only decides which way a selected seam boundary
faces relative to the queried row. -/
structure VerticalBoundaryFaces : Prop where
  above : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    quarterWest (successorWest phase depth parentX) < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < boundary →
    boundary < quarterNorth (successorEast phase depth parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX) row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    (∀ y, row < y → y < boundary →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .north
  below : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    quarterWest (successorWest phase depth parentX) < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < boundary →
    boundary < row →
    row < quarterNorth (successorEast phase depth parentY) →
    IsFreeRow (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentX) (successorEast phase depth parentX) row →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) ≠ none →
    (∀ y, boundary < y → y < row →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) column y)
        (quadrantAt column y) (shadeGrid column y) = none) →
    ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary →
    ShadedSignals.selectedHorizontalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        column boundary)
      (quadrantAt column boundary) (shadeGrid column boundary) = some .south

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
theorem verticalBoundaryConclusion_of_faces
    (faces : VerticalBoundaryFaces)
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
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
    · have foundFacesNorth := faces.above phase depth grid shadeGrid
        parentX parentY valid hwest heast hsouth hrowFound hfoundNorth
        freeRow foundSelected hnone fits
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
    · have foundFacesSouth := faces.below phase depth grid shadeGrid
        parentX parentY valid hwest heast hfoundSouth hfoundRow hnorth
        freeRow foundSelected hnone fits
      exact Or.inr (Or.inr ⟨found, hfoundSouth, hfoundRow,
        foundFacesSouth, hnone⟩)

/-- Horizontal dual of `VerticalBoundaryFaces`. -/
structure HorizontalBoundaryFaces : Prop where
  right : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    quarterWest (successorWest phase depth parentX) < column →
    column < boundary →
    boundary < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < quarterNorth (successorEast phase depth parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY) column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    (∀ x, column < x → x < boundary →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .east
  left : ∀ (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
      (shadeGrid : Nat → Nat → RedShades.State)
      (parentX parentY : Nat) {column row boundary : Nat},
    ValidShadeGrid
      (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid →
    quarterWest (successorWest phase depth parentX) < boundary →
    boundary < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < quarterNorth (successorEast phase depth parentY) →
    IsFreeColumn (iterateRefine 2 (refinedGrid phase depth grid)) shadeGrid
      (successorWest phase depth parentY) (successorEast phase depth parentY) column →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) ≠ none →
    (∀ x, boundary < x → x < column →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 (refinedGrid phase depth grid)) x row)
        (quadrantAt x row) (shadeGrid x row) = none) →
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary →
    ShadedSignals.selectedVerticalFor
      (componentAt (iterateRefine 2 (refinedGrid phase depth grid))
        boundary row)
      (quadrantAt boundary row) (shadeGrid boundary row) = some .west

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
theorem horizontalBoundaryConclusion_of_faces
    (faces : HorizontalBoundaryFaces)
    (phase : Phase) (depth : Nat) (grid : Nat → Nat → Index)
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
    · have foundFacesEast := faces.right phase depth grid shadeGrid
        parentX parentY valid hwest hcolumnFound hfoundEast hsouth hnorth
        freeColumn foundSelected hnone fits
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
    · have foundFacesWest := faces.left phase depth grid shadeGrid
        parentX parentY valid hfoundWest hfoundColumn heast hsouth hnorth
        freeColumn foundSelected hnone fits
      exact Or.inr (Or.inr ⟨found, hfoundWest, hfoundColumn,
        foundFacesWest, hnone⟩)

theorem boundarySeams_of_faces
    (verticalFaces : VerticalBoundaryFaces)
    (horizontalFaces : HorizontalBoundaryFaces) : BoundarySeams := by
  constructor
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid children hwest heast hsouth hnorth freeRow
      hboundarySouth hboundaryNorth selected _
    exact verticalBoundaryConclusion_of_faces verticalFaces
      phase depth grid shadeGrid parentX parentY column row boundary
      valid children hwest heast hsouth hnorth freeRow
      hboundarySouth hboundaryNorth selected
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      valid children hwest heast hsouth hnorth freeColumn
      hboundaryWest hboundaryEast selected _
    exact horizontalBoundaryConclusion_of_faces horizontalFaces
      phase depth grid shadeGrid parentX parentY column row boundary
      valid children hwest heast hsouth hnorth freeColumn
      hboundaryWest hboundaryEast selected

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

end PairCoverSeamComposition
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
