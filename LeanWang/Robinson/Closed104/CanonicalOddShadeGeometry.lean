/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.CanonicalOddFreeLines
import LeanWang.Robinson.Closed104.CanonicalShadeGeometry

/-! Geometry and shade facts for the raw odd canonical substitution. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace CanonicalOddShadeGeometry

open RedShadePaths RedShadeCycles RedShadeGraph RedShadeGraphColoring
  RedShadeGraphRefinement RedShadeGraphLocalCoverage
  Signals.FreeCellLocal ShadedSubstitution CanonicalFreeLine
  CanonicalOddFreeLineData CanonicalOddFreeLineCertificate
  CanonicalOddFreeLines

set_option maxRecDepth 20000

/-- The raw canonical assignment is valid on its finite supertile. -/
theorem validRectangle (level : Nat) :
    ValidShadeRectangle (indexGrid level) (shadeGrid level)
      (2 * 4 ^ level) (2 * 4 ^ level) :=
  supertile_validShadeRectangle level seedNode

/-- Sparse quarter coordinates retain the preceding raw shade exactly. -/
theorem shadeGrid_succ_sparse (level x y : Nat) :
    shadeGrid (level + 1) (sparseCoordinate x) (sparseCoordinate y) =
      shadeGrid level x y :=
  CanonicalShadeGeometry.supertileShadeGrid_succ_sparse
    level seedNode x y

/-- A refined macrocell is the raw level-one supertile of its parent node. -/
theorem shadeGrid_succ_block (level blockX blockY localX localY : Nat)
    (hx : localX < 8) (hy : localY < 8) :
    shadeGrid (level + 1) (8 * blockX + localX) (8 * blockY + localY) =
      supertileShadeGrid 1
        (supertileNodeGrid level seedNode blockX blockY) localX localY := by
  unfold shadeGrid supertileShadeGrid supertileBlockGrid
  have hxDiv : ((8 * blockX + localX) / 2) / 4 = blockX := by omega
  have hyDiv : ((8 * blockY + localY) / 2) / 4 = blockY := by omega
  have hxMod : ((8 * blockX + localX) / 2) % 4 = localX / 2 := by omega
  have hyMod : ((8 * blockY + localY) / 2) % 4 = localY / 2 := by omega
  have hxQuarter : (8 * blockX + localX) % 2 = localX % 2 := by omega
  have hyQuarter : (8 * blockY + localY) % 2 = localY % 2 := by omega
  have hxHalf : localX / 2 % 4 = localX / 2 :=
    Nat.mod_eq_of_lt (by omega)
  have hyHalf : localY / 2 % 4 = localY / 2 :=
    Nat.mod_eq_of_lt (by omega)
  simp [supertileNodeGrid, iterateNodeRefine, refineNodeGrid,
    childPosition, hxDiv, hyDiv, hxMod, hyMod, hxQuarter, hyQuarter,
    hxHalf, hyHalf]

theorem levelTwoState?_eq (x y : Nat) :
    levelTwoState? seed x y = some (shadeGrid 2 x y) := by
  unfold levelTwoState?
  change (do
    let child ← seedNodeAt? (x / 2) (y / 2)
    let data ← modelData child
    some (data.block.at (x % 2) (y % 2))) = some (shadeGrid 2 x y)
  simp only [seedNodeAt?_eq]
  simp [shadeGrid, nodeAt, supertileShadeGrid,
    supertileBlockGrid]

/-- The selected raw seed has the required light odd root cycle. -/
theorem rootCycle_light : CycleShade (shadeGrid 2) 2 6 2 6 .light := by
  have checked := CanonicalOddFreeLineCertificate.rootCycle_light
  simp only [oddRootCycleLight, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨southwest, southeast⟩, northeast⟩, northwest⟩
  constructor
  · simpa [quarterWest, quarterSouth, levelTwoState?_eq] using southwest
  · simpa [quarterEast, quarterSouth, levelTwoState?_eq] using southeast
  · simpa [quarterEast, quarterNorth, levelTwoState?_eq] using northeast
  · simpa [quarterWest, quarterNorth, levelTwoState?_eq] using northwest

/-- The local cell-cycle source is dark in every raw canonical node. -/
theorem cycleSource_dark (node : Node) :
    value (supertileShadeGrid 1 node) cycleSource = some .dark := by
  have dark := CanonicalFreeLine.cycleSourceShade_eq_dark node.property
  have dark' :
      ((CanonicalFreeLineLocal.fineNode node 4 3).data.block.at 0 1).west =
        some .dark := by
    simpa [cycleSourceShade?, Node.modelData_data] using dark
  simp only [value, cycleSource, quarterWest, quarterSouth]
  change (supertileShadeGrid 1 node 4 3).west = some .dark
  change ((CanonicalFreeLineLocal.fineNode node 4 3).data.block.at 0 1).west =
    some .dark
  exact dark'

end CanonicalOddShadeGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
