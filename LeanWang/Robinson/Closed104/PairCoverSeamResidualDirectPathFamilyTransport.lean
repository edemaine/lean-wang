/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OnCycleTranslation
import LeanWang.Robinson.Closed104.PairCoverSeamResidualDirectPathFamilySearch

/-!
# Transport localized family searches into arbitrary hierarchy blocks

The finite family flood runs in the complete refinement of one constant
parent. Its bounded path can therefore be moved into the corresponding parent
block of any coarse grid without assuming that neighboring parents agree.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTransport

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeGraphBoards RedShadeGraphRefinement RedShadeGraphSearchSoundness
  RedShadeGraphTranslation
  RefinementTranslation OnCycleTranslation
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilySearch Signals.FreeCellLocal

set_option maxRecDepth 20000

private theorem hierarchyAddress_translate
    {outerLevel level block : Nat} (parent : Nat)
    (within : HierarchyAddressWithin outerLevel 0 level block) :
    HierarchyAddressWithin outerLevel parent level
      (2 ^ (outerLevel - level) * parent + block) := by
  rcases within with ⟨levelLe, quotient⟩
  refine ⟨levelLe, ?_⟩
  have denominatorPos : 0 < 2 ^ (outerLevel - level) := by positivity
  rw [Nat.mul_add_div denominatorPos, quotient]
  omega

private theorem power_product
    {outerLevel level : Nat} (levelLe : level ≤ outerLevel) :
    2 ^ level * 2 ^ (outerLevel - level) = 2 ^ outerLevel := by
  rw [← pow_add]
  congr 1
  omega

private theorem cycleCoordinate_translate
    {outerLevel level : Nat} (levelLe : level ≤ outerLevel)
    (parent block lane : Nat) :
    2 ^ (outerLevel + 2) * parent + 2 ^ level * (4 * block + lane) =
      2 ^ level *
        (4 * (2 ^ (outerLevel - level) * parent + block) + lane) := by
  have product := power_product levelLe
  rw [pow_add]
  norm_num
  rw [← product]
  ring

private theorem portOffset_eq (outerLevel parent : Nat) :
    2 * (2 ^ (outerLevel + 2) * parent) =
      familyWidth outerLevel * parent := by
  simp [familyWidth, pow_add]
  ring

private theorem onCycle_translateHierarchy
    {outerLevel level blockX blockY parentX parentY : Nat} {port : Port}
    (levelLe : level ≤ outerLevel)
    (onCycle : OnCycle
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) port) :
    OnCycle
      (2 ^ level *
        (4 * (2 ^ (outerLevel - level) * parentX + blockX) + 1))
      (2 ^ level *
        (4 * (2 ^ (outerLevel - level) * parentX + blockX) + 3))
      (2 ^ level *
        (4 * (2 ^ (outerLevel - level) * parentY + blockY) + 1))
      (2 ^ level *
        (4 * (2 ^ (outerLevel - level) * parentY + blockY) + 3))
      (translatePort port (familyWidth outerLevel * parentX)
        (familyWidth outerLevel * parentY)) := by
  have translated := OnCycleTranslation.translate
    (offsetX := 2 ^ (outerLevel + 2) * parentX)
    (offsetY := 2 ^ (outerLevel + 2) * parentY) onCycle
  convert translated using 1
  · exact (cycleCoordinate_translate levelLe parentX blockX 1).symm
  · exact (cycleCoordinate_translate levelLe parentX blockX 3).symm
  · exact (cycleCoordinate_translate levelLe parentY blockY 1).symm
  · exact (cycleCoordinate_translate levelLe parentY blockY 3).symm
  · rw [portOffset_eq, portOffset_eq]

/-- Transport one bounded constant-parent family reach into an arbitrary
coarse-grid parent block. -/
theorem BoundedCanonicalCycleReachWithinFamily.translate
    {grid : Nat → Nat → Index} {outerLevel parentX parentY : Nat}
    {family : HierarchyFamily} {target : Port}
    (reach : BoundedCanonicalCycleReachWithinFamily
      (fun _ _ => grid parentX parentY) target outerLevel
      (familyWidth outerLevel) family) :
    CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) grid)
      (translatePort target (familyWidth outerLevel * parentX)
        (familyWidth outerLevel * parentY))
      outerLevel parentX parentY family := by
  rcases reach with
    ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
      _localCycle, entry, entryOnCycle, boundedPath⟩
  let absoluteBlockX := 2 ^ (outerLevel - level) * parentX + blockX
  let absoluteBlockY := 2 ^ (outerLevel - level) * parentY + blockY
  have xWithin' : HierarchyAddressWithin outerLevel parentX level
      absoluteBlockX := hierarchyAddress_translate parentX xWithin
  have yWithin' : HierarchyAddressWithin outerLevel parentY level
      absoluteBlockY := hierarchyAddress_translate parentY yWithin
  have componentsEq : ∀ x y,
      x < familyWidth outerLevel → y < familyWidth outerLevel →
      componentAt
          (iterateRefine (outerLevel + 2)
            (fun _ _ => grid parentX parentY)) x y =
        componentAt
          (iterateRefine (outerLevel + 2)
            (shiftGrid grid parentX parentY)) x y := by
    intro x y hx hy
    exact (componentAt_shift_eq_constant (outerLevel + 2) grid
      parentX parentY x y (by simpa [familyWidth] using hx)
      (by simpa [familyWidth] using hy)).symm
  have shiftedPath :=
    (RedShadeGraphTranslation.BoundedPath.congr_of_component_eq
      componentsEq boundedPath).path
  have globalPath := path_translate (depth := outerLevel + 2)
    (grid := grid) (blockX := parentX) (blockY := parentY) shiftedPath
  have cycle := cycleAtLevelWithin grid
    (blockX := absoluteBlockX) (blockY := absoluteBlockY) xWithin'.1
  refine ⟨level, absoluteBlockX, absoluteBlockY, xWithin', yWithin',
    inFamily, cycle,
    translatePort entry (familyWidth outerLevel * parentX)
      (familyWidth outerLevel * parentY), ?_, ?_⟩
  · exact onCycle_translateHierarchy xWithin.1 entryOnCycle
  · simpa [familyWidth] using path_symm globalPath

end PairCoverSeamResidualDirectPathFamilyTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
