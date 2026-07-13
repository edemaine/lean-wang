/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamComposition

/-!
# Fixed-depth pair-cover boundary faces

The public face structures quantify over every hierarchy depth.  Induction
through one two-substitution refinement instead needs the corresponding
fixed-phase, fixed-depth proposition.  This module provides that proposition
and lossless adapters to and from the public structures.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamFacesAt

open RedCycles RedShadeCycles RedShadePaths ShadedFreeLineRecurrence
  ShadedPlaneSignalGrid ShadedObstructionPairCoverRecurrence
  SparseFreeLinePlaneBase Signals.FreeCellLocal PairCoverSeamArithmetic
  PairCoverSeamComposition

structure VerticalBoundaryFacesAt (phase : Phase) (depth : Nat) : Prop where
  above : ∀ (grid : Nat → Nat → Index)
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
  below : ∀ (grid : Nat → Nat → Index)
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

structure HorizontalBoundaryFacesAt (phase : Phase) (depth : Nat) : Prop where
  right : ∀ (grid : Nat → Nat → Index)
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
  left : ∀ (grid : Nat → Nat → Index)
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

theorem VerticalBoundaryFaces.at (faces : VerticalBoundaryFaces)
    (phase : Phase) (depth : Nat) : VerticalBoundaryFacesAt phase depth :=
  ⟨faces.above phase depth, faces.below phase depth⟩

theorem HorizontalBoundaryFaces.at (faces : HorizontalBoundaryFaces)
    (phase : Phase) (depth : Nat) : HorizontalBoundaryFacesAt phase depth :=
  ⟨faces.right phase depth, faces.left phase depth⟩

theorem verticalBoundaryFaces_of_at
    (faces : ∀ phase depth, VerticalBoundaryFacesAt phase depth) :
    VerticalBoundaryFaces := by
  constructor
  · exact fun phase depth => (faces phase depth).above
  · exact fun phase depth => (faces phase depth).below

theorem horizontalBoundaryFaces_of_at
    (faces : ∀ phase depth, HorizontalBoundaryFacesAt phase depth) :
    HorizontalBoundaryFaces := by
  constructor
  · exact fun phase depth => (faces phase depth).right
  · exact fun phase depth => (faces phase depth).left

end PairCoverSeamFacesAt
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
