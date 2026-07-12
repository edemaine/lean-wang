/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamComposition

/-!
# Pure index-grid seam orientation

Selected-boundary shade semantics are independent of the finite geometric
question: at a nonrecursive seam, which interior direction does the corrected
index tile carry?  This module isolates that pure index-grid certificate and
converts it to the shaded boundary-facing interface.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamInteriorFaces

open RedShadeCycles ShadedFreeLineRecurrence
  ShadedObstructionPairCoverRecurrence PairCoverSeamComposition

def fineGrid (phase : Phase) (depth : Nat)
    (grid : Nat → Nat → Index) : Nat → Nat → Index :=
  iterateRefine 2 (refinedGrid phase depth grid)

/-- The four finite geometric orientation facts, with all shade state removed. -/
structure InteriorFaces : Prop where
  horizontalAbove : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase depth parentX) < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < boundary →
    boundary < quarterNorth (successorEast phase depth parentY) →
    Signals.horizontalInterior?
      (componentAt (fineGrid phase depth grid) column boundary)
      (quadrantAt column boundary) ≠ none →
    ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary →
    Signals.horizontalInterior?
      (componentAt (fineGrid phase depth grid) column boundary)
      (quadrantAt column boundary) = some .north
  horizontalBelow : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase depth parentX) < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < boundary →
    boundary < row →
    row < quarterNorth (successorEast phase depth parentY) →
    Signals.horizontalInterior?
      (componentAt (fineGrid phase depth grid) column boundary)
      (quadrantAt column boundary) ≠ none →
    ¬FitsContainedVerticalChild phase depth parentX parentY
      column row boundary →
    Signals.horizontalInterior?
      (componentAt (fineGrid phase depth grid) column boundary)
      (quadrantAt column boundary) = some .south
  verticalRight : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase depth parentX) < column →
    column < boundary →
    boundary < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < quarterNorth (successorEast phase depth parentY) →
    Signals.verticalInterior?
      (componentAt (fineGrid phase depth grid) boundary row)
      (quadrantAt boundary row) ≠ none →
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary →
    Signals.verticalInterior?
      (componentAt (fineGrid phase depth grid) boundary row)
      (quadrantAt boundary row) = some .east
  verticalLeft : ∀ (phase : Phase) (depth : Nat)
      (grid : Nat → Nat → Index) (parentX parentY : Nat)
      {column row boundary : Nat},
    quarterWest (successorWest phase depth parentX) < boundary →
    boundary < column →
    column < quarterEast (successorEast phase depth parentX) →
    quarterSouth (successorWest phase depth parentY) < row →
    row < quarterNorth (successorEast phase depth parentY) →
    Signals.verticalInterior?
      (componentAt (fineGrid phase depth grid) boundary row)
      (quadrantAt boundary row) ≠ none →
    ¬FitsContainedHorizontalChild phase depth parentX parentY
      column row boundary →
    Signals.verticalInterior?
      (componentAt (fineGrid phase depth grid) boundary row)
      (quadrantAt boundary row) = some .west

theorem selectedHorizontal_eq_of_interior
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.VerticalInterior}
    (selected : ShadedSignals.selectedHorizontalFor component quadrant state ≠ none)
    (hinterior : Signals.horizontalInterior? component quadrant = some interior) :
    ShadedSignals.selectedHorizontalFor component quadrant state = some interior := by
  have shade :=
    ShadedObstructionGeometryBaseSoundness.horizontalShade_eq_light_of_selected selected
  simp [ShadedSignals.selectedHorizontalFor, shade, hinterior]

theorem selectedVertical_eq_of_interior
    {component : Figure16.Thick} {quadrant : Quadrant}
    {state : RedShades.State} {interior : Signals.HorizontalInterior}
    (selected : ShadedSignals.selectedVerticalFor component quadrant state ≠ none)
    (hinterior : Signals.verticalInterior? component quadrant = some interior) :
    ShadedSignals.selectedVerticalFor component quadrant state = some interior := by
  have shade :=
    ShadedObstructionGeometryBaseSoundness.verticalShade_eq_light_of_selected selected
  simp [ShadedSignals.selectedVerticalFor, shade, hinterior]

theorem verticalBoundaryFaces (faces : InteriorFaces) : VerticalBoundaryFaces := by
  constructor
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      _ hwest heast hsouth hrowBoundary hboundaryNorth selected hnotFit
    have interior : Signals.horizontalInterior?
        (componentAt (fineGrid phase depth grid) column boundary)
        (quadrantAt column boundary) ≠ none :=
      Option.isSome_iff_ne_none.mp
        (ShadedObstructionGeometryBaseSoundness.horizontalInterior_isSome_of_selected
          selected)
    apply selectedHorizontal_eq_of_interior selected
    exact faces.horizontalAbove phase depth grid parentX parentY
      hwest heast hsouth hrowBoundary hboundaryNorth interior hnotFit
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      _ hwest heast hboundarySouth hboundaryRow hnorth selected hnotFit
    have interior : Signals.horizontalInterior?
        (componentAt (fineGrid phase depth grid) column boundary)
        (quadrantAt column boundary) ≠ none :=
      Option.isSome_iff_ne_none.mp
        (ShadedObstructionGeometryBaseSoundness.horizontalInterior_isSome_of_selected
          selected)
    apply selectedHorizontal_eq_of_interior selected
    exact faces.horizontalBelow phase depth grid parentX parentY
      hwest heast hboundarySouth hboundaryRow hnorth interior hnotFit

theorem horizontalBoundaryFaces (faces : InteriorFaces) : HorizontalBoundaryFaces := by
  constructor
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      _ hwest hcolumnBoundary hboundaryEast hsouth hnorth selected hnotFit
    have interior : Signals.verticalInterior?
        (componentAt (fineGrid phase depth grid) boundary row)
        (quadrantAt boundary row) ≠ none :=
      Option.isSome_iff_ne_none.mp
        (ShadedObstructionGeometryBaseSoundness.verticalInterior_isSome_of_selected
          selected)
    apply selectedVertical_eq_of_interior selected
    exact faces.verticalRight phase depth grid parentX parentY
      hwest hcolumnBoundary hboundaryEast hsouth hnorth interior hnotFit
  · intro phase depth grid shadeGrid parentX parentY column row boundary
      _ hboundaryWest hboundaryColumn heast hsouth hnorth selected hnotFit
    have interior : Signals.verticalInterior?
        (componentAt (fineGrid phase depth grid) boundary row)
        (quadrantAt boundary row) ≠ none :=
      Option.isSome_iff_ne_none.mp
        (ShadedObstructionGeometryBaseSoundness.verticalInterior_isSome_of_selected
          selected)
    apply selectedVertical_eq_of_interior selected
    exact faces.verticalLeft phase depth grid parentX parentY
      hboundaryWest hboundaryColumn heast hsouth hnorth interior hnotFit

theorem forcesRoutedFixedCornerSquares_of_interiorFaces
    (faces : InteriorFaces) :
    ShadedRoutedScaffoldForward.ForcesRoutedFixedCornerSquares
      ShadedSignals.routedScaffold :=
  forcesRoutedFixedCornerSquares_of_boundaryFaces
    (verticalBoundaryFaces faces) (horizontalBoundaryFaces faces)

end PairCoverSeamInteriorFaces
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
