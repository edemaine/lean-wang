/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentAudit
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentComponents

/-! Transport adjacent created-seam certificates to global coordinates. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedAdjacentTransport

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphTranslation RefinementTranslation
  PairCoverSeamPathSearch PairCoverSeamShadePaths PairCoverSeamPathTranslation
  PairCoverSeamCreatedAdjacentAudit
  PairCoverSeamCreatedAdjacentClassification Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem boundedPath_verticalWindow
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath
      (iterateRefine 2
        (verticalGrid (canonicalPair
          (grid blockX blockY, grid blockX (blockY + 1)))))
      8 16 first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity := by
  have shifted :=
    (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
      (componentAt_verticalCanonicalPair_shift grid blockX blockY) path).path
  simpa using (path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted)

theorem horizontalPort_verticalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 8) (hy : y < 16) :
    translatePort
        (horizontalPort
          (iterateRefine 2
            (verticalGrid (canonicalPair
              (grid blockX blockY, grid blockX (blockY + 1))))) x y)
        (8 * blockX) (8 * blockY) =
      horizontalPort (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
  have localEq :
      horizontalPort
          (iterateRefine 2
            (verticalGrid (canonicalPair
              (grid blockX blockY, grid blockX (blockY + 1))))) x y =
        horizontalPort (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    unfold horizontalPort
    rw [componentAt_verticalCanonicalPair_shift grid blockX blockY x y hx hy]
  rw [localEq]
  simpa using horizontalPort_translate 2 grid blockX blockY x y

theorem verticalPort_verticalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 8) (hy : y < 16) :
    translatePort
        (verticalPort
          (iterateRefine 2
            (verticalGrid (canonicalPair
              (grid blockX blockY, grid blockX (blockY + 1))))) x y)
        (8 * blockX) (8 * blockY) =
      verticalPort (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
  have localEq :
      verticalPort
          (iterateRefine 2
            (verticalGrid (canonicalPair
              (grid blockX blockY, grid blockX (blockY + 1))))) x y =
        verticalPort (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    unfold verticalPort
    rw [componentAt_verticalCanonicalPair_shift grid blockX blockY x y hx hy]
  rw [localEq]
  simpa using verticalPort_translate 2 grid blockX blockY x y

theorem verticalInterior_verticalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 8) (hy : y < 16) :
    Signals.verticalInterior?
        (componentAt
          (iterateRefine 2
            (verticalGrid (canonicalPair
              (grid blockX blockY, grid blockX (blockY + 1))))) x y)
        (quadrantAt x y) =
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid)
          (8 * blockX + x) (8 * blockY + y))
        (quadrantAt (8 * blockX + x) (8 * blockY + y)) := by
  rw [componentAt_verticalCanonicalPair_shift grid blockX blockY x y hx hy]
  simpa using verticalInterior_iterateRefine_shift 2
    grid blockX blockY x y

theorem horizontalInterior_verticalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 8) (hy : y < 16) :
    Signals.horizontalInterior?
        (componentAt
          (iterateRefine 2
            (verticalGrid (canonicalPair
              (grid blockX blockY, grid blockX (blockY + 1))))) x y)
        (quadrantAt x y) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid)
          (8 * blockX + x) (8 * blockY + y))
        (quadrantAt (8 * blockX + x) (8 * blockY + y)) := by
  rw [componentAt_verticalCanonicalPair_shift grid blockX blockY x y hx hy]
  simpa using horizontalInterior_iterateRefine_shift 2
    grid blockX blockY x y

/-- A rectangular certificate on a canonical vertical pair becomes a global
seam path across the corresponding two neighboring macrocells. -/
theorem rectangularVerticalSeamPath_verticalWindow
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {west east column row boundary : Nat}
    (hcolumn : column < 8) (hrow : row < 16) (hboundary : boundary < 16)
    (path : RectangularVerticalSeamPath
      (iterateRefine 2
        (verticalGrid (canonicalPair
          (grid blockX blockY, grid blockX (blockY + 1)))))
      8 16 west east column row boundary) :
    VerticalSeamPath (iterateRefine 2 grid)
      (4 * blockX + west) (4 * blockX + east)
      (8 * blockX + column) (8 * blockY + row)
      (8 * blockY + boundary) := by
  rcases path with path | path
  · rcases path with ⟨targetX, hwest, heast, hinterior, bounded⟩
    have htargetX : targetX < 8 := by
      have hbounds := bounded.second_inBounds
      unfold verticalPort at hbounds
      split at hbounds <;> exact hbounds.1
    left
    refine ⟨8 * blockX + targetX, ?_, ?_, ?_, ?_⟩
    · simp [quarterWest] at hwest ⊢
      omega
    · simp [quarterEast] at heast ⊢
      omega
    · rw [← verticalInterior_verticalWindow grid blockX blockY
        targetX row htargetX hrow]
      exact hinterior
    · have translated := boundedPath_verticalWindow grid blockX blockY bounded
      rw [horizontalPort_verticalWindow grid blockX blockY column boundary
        hcolumn hboundary] at translated
      rw [verticalPort_verticalWindow grid blockX blockY targetX row
        htargetX hrow] at translated
      exact translated
  · rcases path with ⟨targetY, hbetween, hinterior, bounded⟩
    have htargetY : targetY < 16 := by
      have hbounds := bounded.second_inBounds
      unfold horizontalPort at hbounds
      split at hbounds <;> exact hbounds.2
    right
    refine ⟨8 * blockY + targetY, ?_, ?_, ?_⟩
    · unfold StrictBetween at hbetween ⊢
      omega
    · rw [← horizontalInterior_verticalWindow grid blockX blockY
        column targetY hcolumn htargetY]
      exact hinterior
    · have translated := boundedPath_verticalWindow grid blockX blockY bounded
      rw [horizontalPort_verticalWindow grid blockX blockY column boundary
        hcolumn hboundary] at translated
      rw [horizontalPort_verticalWindow grid blockX blockY column targetY
        hcolumn htargetY] at translated
      exact translated

theorem boundedPath_horizontalWindow
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {first target : Port} {parity : Bool}
    (path : BoundedPath
      (iterateRefine 2
        (horizontalGrid (canonicalPair
          (grid blockX blockY, grid (blockX + 1) blockY))))
      16 8 first target parity) :
    Path (iterateRefine 2 grid)
      (translatePort first (8 * blockX) (8 * blockY))
      (translatePort target (8 * blockX) (8 * blockY)) parity := by
  have shifted :=
    (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
      (componentAt_horizontalCanonicalPair_shift grid blockX blockY) path).path
  simpa using (path_translate (depth := 2) (grid := grid)
    (blockX := blockX) (blockY := blockY) shifted)

theorem horizontalPort_horizontalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 16) (hy : y < 8) :
    translatePort
        (horizontalPort
          (iterateRefine 2
            (horizontalGrid (canonicalPair
              (grid blockX blockY, grid (blockX + 1) blockY)))) x y)
        (8 * blockX) (8 * blockY) =
      horizontalPort (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
  have localEq :
      horizontalPort
          (iterateRefine 2
            (horizontalGrid (canonicalPair
              (grid blockX blockY, grid (blockX + 1) blockY)))) x y =
        horizontalPort (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    unfold horizontalPort
    rw [componentAt_horizontalCanonicalPair_shift grid blockX blockY x y hx hy]
  rw [localEq]
  simpa using horizontalPort_translate 2 grid blockX blockY x y

theorem verticalPort_horizontalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 16) (hy : y < 8) :
    translatePort
        (verticalPort
          (iterateRefine 2
            (horizontalGrid (canonicalPair
              (grid blockX blockY, grid (blockX + 1) blockY)))) x y)
        (8 * blockX) (8 * blockY) =
      verticalPort (iterateRefine 2 grid)
        (8 * blockX + x) (8 * blockY + y) := by
  have localEq :
      verticalPort
          (iterateRefine 2
            (horizontalGrid (canonicalPair
              (grid blockX blockY, grid (blockX + 1) blockY)))) x y =
        verticalPort (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
    unfold verticalPort
    rw [componentAt_horizontalCanonicalPair_shift grid blockX blockY x y hx hy]
  rw [localEq]
  simpa using verticalPort_translate 2 grid blockX blockY x y

theorem verticalInterior_horizontalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 16) (hy : y < 8) :
    Signals.verticalInterior?
        (componentAt
          (iterateRefine 2
            (horizontalGrid (canonicalPair
              (grid blockX blockY, grid (blockX + 1) blockY)))) x y)
        (quadrantAt x y) =
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid)
          (8 * blockX + x) (8 * blockY + y))
        (quadrantAt (8 * blockX + x) (8 * blockY + y)) := by
  rw [componentAt_horizontalCanonicalPair_shift grid blockX blockY x y hx hy]
  simpa using verticalInterior_iterateRefine_shift 2
    grid blockX blockY x y

theorem horizontalInterior_horizontalWindow
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 16) (hy : y < 8) :
    Signals.horizontalInterior?
        (componentAt
          (iterateRefine 2
            (horizontalGrid (canonicalPair
              (grid blockX blockY, grid (blockX + 1) blockY)))) x y)
        (quadrantAt x y) =
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid)
          (8 * blockX + x) (8 * blockY + y))
        (quadrantAt (8 * blockX + x) (8 * blockY + y)) := by
  rw [componentAt_horizontalCanonicalPair_shift grid blockX blockY x y hx hy]
  simpa using horizontalInterior_iterateRefine_shift 2
    grid blockX blockY x y

/-- Horizontal dual of `rectangularVerticalSeamPath_verticalWindow`. -/
theorem rectangularHorizontalSeamPath_horizontalWindow
    (grid : Nat → Nat → Index) (blockX blockY : Nat)
    {south north row column boundary : Nat}
    (hrow : row < 8) (hcolumn : column < 16) (hboundary : boundary < 16)
    (path : RectangularHorizontalSeamPath
      (iterateRefine 2
        (horizontalGrid (canonicalPair
          (grid blockX blockY, grid (blockX + 1) blockY))))
      16 8 south north row column boundary) :
    HorizontalSeamPath (iterateRefine 2 grid)
      (4 * blockY + south) (4 * blockY + north)
      (8 * blockY + row) (8 * blockX + column)
      (8 * blockX + boundary) := by
  rcases path with path | path
  · rcases path with ⟨targetY, hsouth, hnorth, hinterior, bounded⟩
    have htargetY : targetY < 8 := by
      have hbounds := bounded.second_inBounds
      unfold horizontalPort at hbounds
      split at hbounds <;> exact hbounds.2
    left
    refine ⟨8 * blockY + targetY, ?_, ?_, ?_, ?_⟩
    · simp [quarterSouth] at hsouth ⊢
      omega
    · simp [quarterNorth] at hnorth ⊢
      omega
    · rw [← horizontalInterior_horizontalWindow grid blockX blockY
        column targetY hcolumn htargetY]
      exact hinterior
    · have translated := boundedPath_horizontalWindow grid blockX blockY bounded
      rw [verticalPort_horizontalWindow grid blockX blockY boundary row
        hboundary hrow] at translated
      rw [horizontalPort_horizontalWindow grid blockX blockY column targetY
        hcolumn htargetY] at translated
      exact translated
  · rcases path with ⟨targetX, hbetween, hinterior, bounded⟩
    have htargetX : targetX < 16 := by
      have hbounds := bounded.second_inBounds
      unfold verticalPort at hbounds
      split at hbounds <;> exact hbounds.1
    right
    refine ⟨8 * blockX + targetX, ?_, ?_, ?_⟩
    · unfold StrictBetween at hbetween ⊢
      omega
    · rw [← verticalInterior_horizontalWindow grid blockX blockY
        targetX row htargetX hrow]
      exact hinterior
    · have translated := boundedPath_horizontalWindow grid blockX blockY bounded
      rw [verticalPort_horizontalWindow grid blockX blockY boundary row
        hboundary hrow] at translated
      rw [verticalPort_horizontalWindow grid blockX blockY targetX row
        htargetX hrow] at translated
      exact translated


end PairCoverSeamCreatedAdjacentTransport
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
