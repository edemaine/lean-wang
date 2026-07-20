/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalShadeMarkedFreeGrid
import LeanWang.Robinson.Closed104.CanonicalOddShadeMarkedFreeGrid

/-!
# Marked free grids in decoded planes

At a sufficiently deep hierarchy level, the shade argument supplies a light
board in one of two adjacent parity phases.  The even and odd canonical
comparison theorems each provide a marked free grid for their respective
phase.  This module chooses between those cases and rewrites both witnesses
onto the same actual refined grid of the decoded plane.

The requested grid is deliberately larger than the eventual payload square:
later enumeration discards lines below the marker and still needs enough rows
and columns to select a consecutive prefix.  The marker at the lower-left
crossing is what forces the payload seed.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace SparseFreeLineDecodedMarkedGrid

open OrientedRedCycles RedCycles RedShadeCycles RedShadePaths
  RedShadeCrossingBoards
  SparseFreeLinePlaneMarkedGrid CanonicalShadeComparison
  CanonicalShadeMarkedFreeGrid ShadedSubstitution

set_option maxRecDepth 20000

variable {T : TileSet} {seed : WangTile}
  {x : Int × Int → TileIn
    (combineWithRoutedScaffold ShadedSignals.routedScaffold T seed)}

set_option linter.style.nativeDecide false in
set_option maxHeartbeats 2000000 in
-- The two light-cycle cases use different phase representations of one grid.
theorem unboundedMarkedFreeGrid_with_light
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int)
    (root : (ShadedPlaneShadeGrid.coarseGrid decoded
      (2 * (1 + size) + 2) coarseOrigin) 0 0 = 0) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    (CycleOn (iterateRefine (level + 2) coarse)
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) ∧
      CycleShade state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) .light ∧
      Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2))) ∨
      (CycleOn (iterateRefine (level + 2) coarse)
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) ∧
        CycleShade state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) .light ∧
        Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
          (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1))) := by
  let level := 2 * (1 + size)
  let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
  let state := ShadedPlaneShadeGrid.stateGrid decoded
    (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
  have coarseRoot : coarse 0 0 = 0 := by
    simpa only [coarse, level] using root
  have hlevel : 1 ≤ level := by simp [level]; omega
  have valid : ValidShadeGrid (iterateRefine (level + 2) coarse) state :=
    ShadedPlaneShadeGrid.refined_stateGrid_valid decoded
      (level + 2) coarseOrigin
  have light := ShadedPlaneShadeGrid.hasLightCycleAtLevel decoded hlevel coarseOrigin
  change HasLightCycleAtLevel state level at light
  have hlargePow : 2 ^ level = 4 ^ (1 + size) := by
    dsimp [level]
    rw [pow_mul]
    norm_num
  have hsmallPow : 2 ^ (level - 1) = 2 * 4 ^ size := by
    dsimp [level]
    rw [show 2 * (1 + size) - 1 = 1 + 2 * size by omega, pow_add, pow_mul]
    norm_num
  rcases light with largeLight | smallLight
  · left
    have cycle := RedShadeCrossingBoards.largeCycle coarse level
    have directValid : ValidShadeGrid (actualGrid (size + 1) coarse) state := by
      simpa only [actualGrid, level, Nat.add_comm] using valid
    have directLight : CycleShade state
        (CanonicalShadeComparison.scale (size + 1))
        (3 * CanonicalShadeComparison.scale (size + 1))
        (CanonicalShadeComparison.scale (size + 1))
        (3 * CanonicalShadeComparison.scale (size + 1)) .light := by
      simpa only [CanonicalShadeComparison.scale, hlargePow,
        Nat.add_comm] using largeLight
    exact ⟨cycle, largeLight, ⟨by
      have witness := markedFreeGrid size coarse state seedNode coarseRoot
        seedNode_parent directValid directLight
      have gridEq : actualGrid (size + 1) coarse =
          iterateRefine (level + 2) coarse := by
        unfold actualGrid
        congr 1
        dsimp [level]
        omega
      have hlargePow' : 2 ^ level = 4 ^ (size + 1) := by
        simpa only [Nat.add_comm] using hlargePow
      simp only [CanonicalShadeComparison.scale] at witness
      rw [gridEq, ← hlargePow'] at witness
      exact witness⟩⟩
  · right
    have cycle := RedShadeCrossingBoards.smallCycle coarse hlevel
    have directValid : ValidShadeGrid
        (CanonicalOddShadeComparison.actualGrid size coarse) state := by
      simpa only [CanonicalOddShadeComparison.actualGrid,
        show 2 * size + 4 = level + 2 by
          dsimp [level]
          omega] using valid
    have directLight : CycleShade state
        (CanonicalOddShadeComparison.scale size)
        (3 * CanonicalOddShadeComparison.scale size)
        (CanonicalOddShadeComparison.scale size)
        (3 * CanonicalOddShadeComparison.scale size) .light := by
      simpa only [CanonicalOddShadeComparison.scale, hsmallPow] using smallLight
    exact ⟨cycle, smallLight, ⟨by
      have witness := CanonicalOddShadeMarkedFreeGrid.markedFreeGrid size
        coarse state coarseRoot directValid directLight
      have gridEq : CanonicalOddShadeComparison.actualGrid size coarse =
          iterateRefine (level + 2) coarse := by
        unfold CanonicalOddShadeComparison.actualGrid
        congr 1
        dsimp [level]
        omega
      simp only [CanonicalOddShadeComparison.scale] at witness
      rw [gridEq, ← hsmallPow] at witness
      exact witness⟩⟩

set_option maxHeartbeats 2000000 in
-- Compatibility wrapper retaining the original grid-only interface.
theorem unboundedMarkedFreeGrid
    (decoded : ShadedRoutedPlaneDecode.Decoded x)
    (size : Nat) (coarseOrigin : Int × Int)
    (root : (ShadedPlaneShadeGrid.coarseGrid decoded
      (2 * (1 + size) + 2) coarseOrigin) 0 0 = 0) :
    let level := 2 * (1 + size)
    let coarse := ShadedPlaneShadeGrid.coarseGrid decoded (level + 2) coarseOrigin
    let state := ShadedPlaneShadeGrid.stateGrid decoded
      (ShadedPlaneShadeGrid.fineParentOrigin decoded (level + 2) coarseOrigin)
    Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level)
        (size + 2)) ∨
      Nonempty (MarkedFreeGrid (iterateRefine (level + 2) coarse) state
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
        (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) (size + 1)) := by
  rcases unboundedMarkedFreeGrid_with_light decoded size coarseOrigin root with
    ⟨_, _, grid⟩ | ⟨_, _, grid⟩
  · exact Or.inl grid
  · exact Or.inr grid

end SparseFreeLineDecodedMarkedGrid
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
