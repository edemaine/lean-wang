/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.PairCoverSeamCreatedAdjacentClassification
import LeanWang.Robinson.Closed104.PairCoverSeamPathTranslation

/-!
# Identify adjacent created-seam component windows

The finite adjacent audit observes only the red component of each tile.  This
module identifies each canonical audited two-cell window with the corresponding
shifted window of an arbitrary coarse grid.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace PairCoverSeamCreatedAdjacentTransport

open RedCycles RedShadeCycles RedShadeGraph RedShadeGraphSearchSoundness
  RedShadeGraphTranslation RefinementTranslation BorderGeometry
  PairCoverSeamPathSearch PairCoverSeamShadePaths PairCoverSeamPathTranslation
  PairCoverSeamCreatedAdjacentAudit
  PairCoverSeamCreatedAdjacentClassification Signals.FreeCellLocal

set_option maxRecDepth 20000

theorem indexState_iterateRefine_congr
    {first second : Nat → Nat → Index}
    (same : ∀ x y, BorderSubstitution.indexState (first x y) =
      BorderSubstitution.indexState (second x y))
    (depth x y : Nat) :
    BorderSubstitution.indexState (iterateRefine depth first x y) =
      BorderSubstitution.indexState (iterateRefine depth second x y) := by
  have gridEq : BorderSubstitution.ofIndexGrid first =
      BorderSubstitution.ofIndexGrid second := by
    funext sourceX sourceY
    exact same sourceX sourceY
  calc
    BorderSubstitution.indexState (iterateRefine depth first x y) =
        BorderSubstitution.iterateRefine depth
          (BorderSubstitution.ofIndexGrid first) x y := by
      have equality := BorderSubstitution.ofIndexGrid_iterateRefine depth first
      exact congrFun (congrFun equality x) y
    _ = BorderSubstitution.iterateRefine depth
          (BorderSubstitution.ofIndexGrid second) x y := by
      rw [gridEq]
    _ = BorderSubstitution.indexState (iterateRefine depth second x y) := by
      have equality := BorderSubstitution.ofIndexGrid_iterateRefine depth second
      exact (congrFun (congrFun equality x) y).symm

theorem componentAt_iterateRefine_congr
    {first second : Nat → Nat → Index}
    (same : ∀ x y, BorderSubstitution.indexState (first x y) =
      BorderSubstitution.indexState (second x y))
    (depth x y : Nat) :
    componentAt (iterateRefine depth first) x y =
      componentAt (iterateRefine depth second) x y := by
  have state := congrArg Prod.snd
    (indexState_iterateRefine_congr same depth (x / 2) (y / 2))
  simpa [componentAt, BorderSubstitution.indexState] using state

theorem indexState_verticalCanonicalPair (pair : PairState) :
    ∀ x y, BorderSubstitution.indexState
        (verticalGrid (canonicalPair pair) x y) =
      BorderSubstitution.indexState (verticalGrid pair x y) := by
  rcases pair with ⟨lower, upper⟩
  intro x y
  dsimp only [verticalGrid, canonicalPair]
  split
  · exact BorderSubstitution.indexState_canonicalIndex lower
  · exact BorderSubstitution.indexState_canonicalIndex upper

theorem indexState_horizontalCanonicalPair (pair : PairState) :
    ∀ x y, BorderSubstitution.indexState
        (horizontalGrid (canonicalPair pair) x y) =
      BorderSubstitution.indexState (horizontalGrid pair x y) := by
  rcases pair with ⟨left, right⟩
  intro x y
  dsimp only [horizontalGrid, canonicalPair]
  split
  · exact BorderSubstitution.indexState_canonicalIndex left
  · exact BorderSubstitution.indexState_canonicalIndex right

theorem componentAt_verticalPair_shift
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 8) (hy : y < 16) :
    componentAt
        (iterateRefine 2
          (verticalGrid (grid blockX blockY, grid blockX (blockY + 1)))) x y =
      componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
  have hxzero : ((x / 2) / 2) / 2 = 0 := by omega
  have parentEq :
      verticalGrid (grid blockX blockY, grid blockX (blockY + 1))
          (((x / 2) / 2) / 2) (((y / 2) / 2) / 2) =
        shiftGrid grid blockX blockY
          (((x / 2) / 2) / 2) (((y / 2) / 2) / 2) := by
    by_cases hlower : y < 8
    · have hyzero : ((y / 2) / 2) / 2 = 0 := by omega
      simp [verticalGrid, shiftGrid, hxzero, hyzero]
    · have hyone : ((y / 2) / 2) / 2 = 1 := by omega
      simp [verticalGrid, shiftGrid, hxzero, hyone]
  unfold componentAt
  rw [PlaneRedBoards.iterateRefine_two_apply,
    PlaneRedBoards.iterateRefine_two_apply, parentEq]

theorem componentAt_horizontalPair_shift
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 16) (hy : y < 8) :
    componentAt
        (iterateRefine 2
          (horizontalGrid (grid blockX blockY, grid (blockX + 1) blockY))) x y =
      componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
  have hyzero : ((y / 2) / 2) / 2 = 0 := by omega
  have parentEq :
      horizontalGrid (grid blockX blockY, grid (blockX + 1) blockY)
          (((x / 2) / 2) / 2) (((y / 2) / 2) / 2) =
        shiftGrid grid blockX blockY
          (((x / 2) / 2) / 2) (((y / 2) / 2) / 2) := by
    by_cases hleft : x < 8
    · have hxzero : ((x / 2) / 2) / 2 = 0 := by omega
      simp [horizontalGrid, shiftGrid, hxzero, hyzero]
    · have hxone : ((x / 2) / 2) / 2 = 1 := by omega
      simp [horizontalGrid, shiftGrid, hxone, hyzero]
  unfold componentAt
  rw [PlaneRedBoards.iterateRefine_two_apply,
    PlaneRedBoards.iterateRefine_two_apply, parentEq]

theorem componentAt_verticalCanonicalPair_shift
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 8) (hy : y < 16) :
    componentAt
        (iterateRefine 2
          (verticalGrid (canonicalPair
            (grid blockX blockY, grid blockX (blockY + 1))))) x y =
      componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
  exact (componentAt_iterateRefine_congr
    (indexState_verticalCanonicalPair
      (grid blockX blockY, grid blockX (blockY + 1))) 2 x y).trans
      (componentAt_verticalPair_shift grid blockX blockY x y hx hy)

theorem componentAt_horizontalCanonicalPair_shift
    (grid : Nat → Nat → Index) (blockX blockY x y : Nat)
    (hx : x < 16) (hy : y < 8) :
    componentAt
        (iterateRefine 2
          (horizontalGrid (canonicalPair
            (grid blockX blockY, grid (blockX + 1) blockY)))) x y =
      componentAt (iterateRefine 2 (shiftGrid grid blockX blockY)) x y := by
  exact (componentAt_iterateRefine_congr
    (indexState_horizontalCanonicalPair
      (grid blockX blockY, grid (blockX + 1) blockY)) 2 x y).trans
      (componentAt_horizontalPair_shift grid blockX blockY x y hx hy)

end PairCoverSeamCreatedAdjacentTransport
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
