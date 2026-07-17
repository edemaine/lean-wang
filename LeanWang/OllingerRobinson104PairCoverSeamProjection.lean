/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamRefinementCoordinates
import LeanWang.OllingerRobinson104RedShadeGraphProjection
import LeanWang.OllingerRobinson104ShadedLightBoardFreeLines

/-!
# Semantic projection for inherited pair-cover seams

On literal sparse coordinates, selected boundaries and free rows or columns
are preserved exactly by the two-level shade-grid projection.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamProjection

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphRefinement
  RedShadeGraphProjection RedShadePaths ShadedPlaneSignalGrid
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Selection on a coarse horizontal interior is exactly selection on its
literal sparse copy in a valid two-level refinement. -/
theorem selectedHorizontal_projectStateGrid_eq_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    (x y : Nat) :
    ShadedSignals.selectedHorizontalFor
        (componentAt grid x y) (quadrantAt x y)
        (projectStateGrid stateGrid x y) =
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 grid)
          (sparseCoordinate x) (sparseCoordinate y))
        (quadrantAt (sparseCoordinate x) (sparseCoordinate y))
        (stateGrid (sparseCoordinate x) (sparseCoordinate y)) := by
  rw [projectStateGrid_eq_sparse valid,
    componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]

/-- Vertical dual of `selectedHorizontal_projectStateGrid_eq_sparse`. -/
theorem selectedVertical_projectStateGrid_eq_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    (x y : Nat) :
    ShadedSignals.selectedVerticalFor
        (componentAt grid x y) (quadrantAt x y)
        (projectStateGrid stateGrid x y) =
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 grid)
          (sparseCoordinate x) (sparseCoordinate y))
        (quadrantAt (sparseCoordinate x) (sparseCoordinate y))
        (stateGrid (sparseCoordinate x) (sparseCoordinate y)) := by
  rw [projectStateGrid_eq_sparse valid,
    componentAt_iterateRefine_two_sparse, quadrantAt_sparseCoordinate]

/-- A free literal sparse row projects to a free coarse row. -/
theorem isFreeRow_project_of_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    {west east row : Nat}
    (free : IsFreeRow (iterateRefine 2 grid) stateGrid
      (4 * west) (4 * east) (sparseCoordinate row)) :
    IsFreeRow grid (projectStateGrid stateGrid) west east row := by
  intro x hwest heast
  rw [selectedVertical_projectStateGrid_eq_sparse valid]
  apply free (sparseCoordinate x)
  · simpa only [sparseCoordinate_quarterWest] using
      sparseCoordinate_strictMono hwest
  · simpa only [sparseCoordinate_quarterEast] using
      sparseCoordinate_strictMono heast

/-- A free literal sparse column projects to a free coarse column. -/
theorem isFreeColumn_project_of_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    {south north column : Nat}
    (free : IsFreeColumn (iterateRefine 2 grid) stateGrid
      (4 * south) (4 * north) (sparseCoordinate column)) :
    IsFreeColumn grid (projectStateGrid stateGrid) south north column := by
  intro y hsouth hnorth
  rw [selectedHorizontal_projectStateGrid_eq_sparse valid]
  apply free (sparseCoordinate y)
  · simpa only [sparseCoordinate_quarterSouth] using
      sparseCoordinate_strictMono hsouth
  · simpa only [sparseCoordinate_quarterNorth] using
      sparseCoordinate_strictMono hnorth

/-- Absence of selected horizontal boundaries between retained fine
coordinates projects to absence between the corresponding coarse coordinates. -/
theorem noSelectedHorizontalBetween_project_of_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    {x first second : Nat}
    (noneBetween : ∀ y,
      sparseCoordinate first < y → y < sparseCoordinate second →
      ShadedSignals.selectedHorizontalFor
        (componentAt (iterateRefine 2 grid) (sparseCoordinate x) y)
        (quadrantAt (sparseCoordinate x) y)
        (stateGrid (sparseCoordinate x) y) = none) :
    ∀ y, first < y → y < second →
      ShadedSignals.selectedHorizontalFor
        (componentAt grid x y) (quadrantAt x y)
        (projectStateGrid stateGrid x y) = none := by
  intro y hfirst hsecond
  rw [selectedHorizontal_projectStateGrid_eq_sparse valid]
  exact noneBetween (sparseCoordinate y)
    (sparseCoordinate_strictMono hfirst)
    (sparseCoordinate_strictMono hsecond)

/-- Vertical dual of `noSelectedHorizontalBetween_project_of_sparse`. -/
theorem noSelectedVerticalBetween_project_of_sparse
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid (iterateRefine 2 grid) stateGrid)
    {y first second : Nat}
    (noneBetween : ∀ x,
      sparseCoordinate first < x → x < sparseCoordinate second →
      ShadedSignals.selectedVerticalFor
        (componentAt (iterateRefine 2 grid) x (sparseCoordinate y))
        (quadrantAt x (sparseCoordinate y))
        (stateGrid x (sparseCoordinate y)) = none) :
    ∀ x, first < x → x < second →
      ShadedSignals.selectedVerticalFor
        (componentAt grid x y) (quadrantAt x y)
        (projectStateGrid stateGrid x y) = none := by
  intro x hfirst hsecond
  rw [selectedVertical_projectStateGrid_eq_sparse valid]
  exact noneBetween (sparseCoordinate x)
    (sparseCoordinate_strictMono hfirst)
    (sparseCoordinate_strictMono hsecond)

end PairCoverSeamProjection
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
