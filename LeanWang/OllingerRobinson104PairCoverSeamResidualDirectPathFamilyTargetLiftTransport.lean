/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetLiftAudit
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathFamilyTargetRecurrence
import LeanWang.OllingerRobinson104PairCoverSeamCreatedLocalTransport
import LeanWang.OllingerRobinson104SparseFreeLineLocalTransport

/-!
# Transport finite family-target lifts into arbitrary macrocells

The finite audit runs on a constant-parent `8 x 8` block.  These theorems
translate an accepted target and its even path into an arbitrary depth-two
refinement.  The translated target is identified by `coarseCoordinate`, which
is the invariant needed by the global strict-between recurrence.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathFamilyTargetLiftTransport

open RedCycles RedShadeGraph RedShadeGraphRefinement RedShadeGraphTranslation
  PairCoverSeamCreatedLocalTransport PairCoverSeamShadePaths
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathFamilyTargetLiftAudit
  RefinedCoordinateProjection SparseFreeLineLocalTransport
  Signals.FreeCellLocal Signals.FreeCellEmbedding

set_option maxRecDepth 20000

private theorem horizontalSparsePort_oldBlock
    (grid : Nat → Nat → Index) (blockX blockY sourceX sourceY : Nat)
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2) :
    translatePort
        (sparsePort (horizontalPort (coarseGrid (grid blockX blockY))
          sourceX sourceY)) (8 * blockX) (8 * blockY) =
      sparsePort (horizontalPort grid
        (2 * blockX + sourceX) (2 * blockY + sourceY)) := by
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  change componentAt grid (2 * blockX + sourceX) (2 * blockY + sourceY) =
    componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY at component
  unfold horizontalPort
  rw [← component, ← quadrant]
  split <;>
    simp [translatePort, sparsePort,
      sparseCoordinate_two_block blockX sourceX sourceXLt,
      sparseCoordinate_two_block blockY sourceY sourceYLt]

private theorem verticalSparsePort_oldBlock
    (grid : Nat → Nat → Index) (blockX blockY sourceX sourceY : Nat)
    (sourceXLt : sourceX < 2) (sourceYLt : sourceY < 2) :
    translatePort
        (sparsePort (verticalPort (coarseGrid (grid blockX blockY))
          sourceX sourceY)) (8 * blockX) (8 * blockY) =
      sparsePort (verticalPort grid
        (2 * blockX + sourceX) (2 * blockY + sourceY)) := by
  have component := componentAt_old_block grid 0 blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  have quadrant := quadrantAt_old_block blockX blockY
    sourceX sourceY sourceXLt sourceYLt
  change componentAt grid (2 * blockX + sourceX) (2 * blockY + sourceY) =
    componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY at component
  unfold verticalPort
  rw [← component, ← quadrant]
  split <;>
    simp [translatePort, sparsePort,
      sparseCoordinate_two_block blockX sourceX sourceXLt,
      sparseCoordinate_two_block blockY sourceY sourceYLt]

theorem intervalEnd_le_eight (source : Nat) :
    intervalEnd source ≤ 8 := by
  by_cases source = 0 <;> simp_all [intervalEnd]

/-- The block number of a fine coordinate is determined by its selected
coarse interval. -/
theorem div_two_eq_div_eight_of_coarseCoordinate
    {fine coarse : Nat} (coarseEq : coarseCoordinate fine = coarse) :
    coarse / 2 = fine / 8 := by
  by_cases residue : fine % 8 = 0
  · simp only [coarseCoordinate, residue, if_true] at coarseEq
    omega
  · simp only [coarseCoordinate, residue, if_false] at coarseEq
    omega

/-- A local coordinate in the audited source interval translates to exactly
that source's global coarse interval. -/
theorem coarseCoordinate_twoBlock_of_mem_interval
    {block source target : Nat} (sourceLt : source < 2)
    (targetLower : sparseCoordinate source ≤ target)
    (targetUpper : target < intervalEnd source) :
    coarseCoordinate (8 * block + target) = 2 * block + source := by
  have sourceCases : source = 0 ∨ source = 1 := by omega
  rcases sourceCases with rfl | rfl
  · have targetZero : target = 0 := by
      simp [intervalEnd] at targetUpper
      omega
    subst target
    simp [coarseCoordinate]
  · have targetLt : target < 8 :=
      targetUpper.trans_le (intervalEnd_le_eight 1)
    have targetPos : 0 < target := by
      simp [sparseCoordinate, macroOrigin, localCoordinate] at targetLower
      omega
    have targetMod : (8 * block + target) % 8 = target := by omega
    have targetDiv : (8 * block + target) / 8 = block := by omega
    simp [coarseCoordinate, targetMod, targetDiv, targetPos.ne']

set_option maxHeartbeats 2000000 in
-- Local and global port selectors depend on translated component values.
/-- Transport one accepted horizontal target into an arbitrary refined grid. -/
theorem horizontalTarget
    (grid : Nat → Nat → Index) (oldColumn oldTargetY fineColumn : Nat)
    (sameBlock : oldColumn / 2 = fineColumn / 8)
    (nonexceptional :
      8 ≤ (grid (oldColumn / 2) (oldTargetY / 2)).val)
    (sourceInterior : Signals.horizontalInterior?
      (componentAt grid oldColumn oldTargetY)
      (quadrantAt oldColumn oldTargetY) ≠ none) :
    ∃ targetY,
      coarseCoordinate targetY = oldTargetY ∧
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid) fineColumn targetY)
        (quadrantAt fineColumn targetY) ≠ none ∧
      Path (iterateRefine 2 grid)
        (sparsePort (horizontalPort grid oldColumn oldTargetY))
        (horizontalPort (iterateRefine 2 grid) fineColumn targetY) false := by
  let blockX := oldColumn / 2
  let blockY := oldTargetY / 2
  let sourceX := oldColumn % 2
  let sourceY := oldTargetY % 2
  let targetX := fineColumn % 8
  have sourceXLt : sourceX < 2 := Nat.mod_lt _ (by decide)
  have sourceYLt : sourceY < 2 := Nat.mod_lt _ (by decide)
  have targetXLt : targetX < 8 := Nat.mod_lt _ (by decide)
  have oldColumnEq : 2 * blockX + sourceX = oldColumn := by
    have decompose := Nat.mod_add_div oldColumn 2
    dsimp [blockX, sourceX]
    omega
  have oldTargetYEq : 2 * blockY + sourceY = oldTargetY := by
    have decompose := Nat.mod_add_div oldTargetY 2
    dsimp [blockY, sourceY]
    omega
  have fineColumnEq : 8 * blockX + targetX = fineColumn := by
    have decompose := Nat.mod_add_div fineColumn 8
    dsimp [blockX, targetX] at *
    omega
  have localSourceInterior : Signals.horizontalInterior?
      (componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY)
      (quadrantAt sourceX sourceY) ≠ none := by
    change Signals.horizontalInterior?
      (componentAt (iterateRefine 0 grid) oldColumn oldTargetY)
      (quadrantAt oldColumn oldTargetY) ≠ none at sourceInterior
    rw [← oldColumnEq, ← oldTargetYEq,
      componentAt_old_block grid 0 blockX blockY sourceX sourceY
        sourceXLt sourceYLt,
      quadrantAt_old_block blockX blockY sourceX sourceY
        sourceXLt sourceYLt] at sourceInterior
    exact sourceInterior
  have checked :=
    PairCoverSeamResidualDirectPathFamilyTargetLiftAudit.complete
      (grid blockX blockY) (by simpa [blockX, blockY] using nonexceptional)
  have found := horizontalTargetFound_of_checkParent checked
    sourceXLt sourceYLt targetXLt localSourceInterior
  rcases horizontalTargetFound_sound sourceXLt sourceYLt found with
    ⟨localTargetY, targetLower, targetUpper, localInterior, localPath⟩
  have localTargetYLt : localTargetY < 8 :=
    targetUpper.trans_le (intervalEnd_le_eight sourceY)
  let targetY := 8 * blockY + localTargetY
  have targetCoarse : coarseCoordinate targetY = oldTargetY := by
    dsimp only [targetY]
    rw [coarseCoordinate_twoBlock_of_mem_interval sourceYLt
      targetLower targetUpper, oldTargetYEq]
  have globalInterior : Signals.horizontalInterior?
      (componentAt (iterateRefine 2 grid) fineColumn targetY)
      (quadrantAt fineColumn targetY) ≠ none := by
    rw [horizontalInterior_twoBlock grid blockX blockY targetX localTargetY
      targetXLt localTargetYLt] at localInterior
    simpa only [fineColumnEq, targetY] using localInterior
  have translated := boundedPath_two_block grid blockX blockY localPath
  rw [horizontalSparsePort_oldBlock grid blockX blockY sourceX sourceY
      sourceXLt sourceYLt,
    horizontalPort_twoBlock grid blockX blockY targetX localTargetY
      targetXLt localTargetYLt] at translated
  have globalPath : Path (iterateRefine 2 grid)
      (sparsePort (horizontalPort grid oldColumn oldTargetY))
      (horizontalPort (iterateRefine 2 grid) fineColumn targetY) false := by
    simpa only [oldColumnEq, oldTargetYEq, fineColumnEq, targetY]
      using translated
  exact ⟨targetY, targetCoarse, globalInterior, globalPath⟩

set_option maxHeartbeats 2000000 in
-- Local and global port selectors depend on translated component values.
/-- Vertical dual of `horizontalTarget`. -/
theorem verticalTarget
    (grid : Nat → Nat → Index) (oldTargetX oldRow fineRow : Nat)
    (sameBlock : oldRow / 2 = fineRow / 8)
    (nonexceptional :
      8 ≤ (grid (oldTargetX / 2) (oldRow / 2)).val)
    (sourceInterior : Signals.verticalInterior?
      (componentAt grid oldTargetX oldRow)
      (quadrantAt oldTargetX oldRow) ≠ none) :
    ∃ targetX,
      coarseCoordinate targetX = oldTargetX ∧
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid) targetX fineRow)
        (quadrantAt targetX fineRow) ≠ none ∧
      Path (iterateRefine 2 grid)
        (sparsePort (verticalPort grid oldTargetX oldRow))
        (verticalPort (iterateRefine 2 grid) targetX fineRow) false := by
  let blockX := oldTargetX / 2
  let blockY := oldRow / 2
  let sourceX := oldTargetX % 2
  let sourceY := oldRow % 2
  let targetY := fineRow % 8
  have sourceXLt : sourceX < 2 := Nat.mod_lt _ (by decide)
  have sourceYLt : sourceY < 2 := Nat.mod_lt _ (by decide)
  have targetYLt : targetY < 8 := Nat.mod_lt _ (by decide)
  have oldTargetXEq : 2 * blockX + sourceX = oldTargetX := by
    have decompose := Nat.mod_add_div oldTargetX 2
    dsimp [blockX, sourceX]
    omega
  have oldRowEq : 2 * blockY + sourceY = oldRow := by
    have decompose := Nat.mod_add_div oldRow 2
    dsimp [blockY, sourceY]
    omega
  have fineRowEq : 8 * blockY + targetY = fineRow := by
    have decompose := Nat.mod_add_div fineRow 8
    dsimp [blockY, targetY] at *
    omega
  have localSourceInterior : Signals.verticalInterior?
      (componentAt (coarseGrid (grid blockX blockY)) sourceX sourceY)
      (quadrantAt sourceX sourceY) ≠ none := by
    change Signals.verticalInterior?
      (componentAt (iterateRefine 0 grid) oldTargetX oldRow)
      (quadrantAt oldTargetX oldRow) ≠ none at sourceInterior
    rw [← oldTargetXEq, ← oldRowEq,
      componentAt_old_block grid 0 blockX blockY sourceX sourceY
        sourceXLt sourceYLt,
      quadrantAt_old_block blockX blockY sourceX sourceY
        sourceXLt sourceYLt] at sourceInterior
    exact sourceInterior
  have checked :=
    PairCoverSeamResidualDirectPathFamilyTargetLiftAudit.complete
      (grid blockX blockY) (by simpa [blockX, blockY] using nonexceptional)
  have found := verticalTargetFound_of_checkParent checked
    sourceXLt sourceYLt targetYLt localSourceInterior
  rcases verticalTargetFound_sound sourceXLt sourceYLt found with
    ⟨localTargetX, targetLower, targetUpper, localInterior, localPath⟩
  have localTargetXLt : localTargetX < 8 :=
    targetUpper.trans_le (intervalEnd_le_eight sourceX)
  let targetX := 8 * blockX + localTargetX
  have targetCoarse : coarseCoordinate targetX = oldTargetX := by
    dsimp only [targetX]
    rw [coarseCoordinate_twoBlock_of_mem_interval sourceXLt
      targetLower targetUpper, oldTargetXEq]
  have globalInterior : Signals.verticalInterior?
      (componentAt (iterateRefine 2 grid) targetX fineRow)
      (quadrantAt targetX fineRow) ≠ none := by
    rw [verticalInterior_twoBlock grid blockX blockY localTargetX targetY
      localTargetXLt targetYLt] at localInterior
    simpa only [targetX, fineRowEq] using localInterior
  have translated := boundedPath_two_block grid blockX blockY localPath
  rw [verticalSparsePort_oldBlock grid blockX blockY sourceX sourceY
      sourceXLt sourceYLt,
    verticalPort_twoBlock grid blockX blockY localTargetX targetY
      localTargetXLt targetYLt] at translated
  have globalPath : Path (iterateRefine 2 grid)
      (sparsePort (verticalPort grid oldTargetX oldRow))
      (verticalPort (iterateRefine 2 grid) targetX fineRow) false := by
    simpa only [oldTargetXEq, oldRowEq, targetX, fineRowEq]
      using translated
  exact ⟨targetX, targetCoarse, globalInterior, globalPath⟩

/-- The transported horizontal target retains its old hierarchy family. -/
theorem horizontalTargetFamily
    (grid : Nat → Nat → Index) (oldColumn oldTargetY fineColumn : Nat)
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (sameBlock : oldColumn / 2 = fineColumn / 8)
    (nonexceptional :
      8 ≤ (grid (oldColumn / 2) (oldTargetY / 2)).val)
    (sourceInterior : Signals.horizontalInterior?
      (componentAt grid oldColumn oldTargetY)
      (quadrantAt oldColumn oldTargetY) ≠ none)
    (sourceFamily : CanonicalCycleAncestorWithinFamily grid
      (horizontalPort grid oldColumn oldTargetY)
      outerLevel outerBlockX outerBlockY family) :
    ∃ targetY,
      coarseCoordinate targetY = oldTargetY ∧
      Signals.horizontalInterior?
        (componentAt (iterateRefine 2 grid) fineColumn targetY)
        (quadrantAt fineColumn targetY) ≠ none ∧
      CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
        (horizontalPort (iterateRefine 2 grid) fineColumn targetY)
        (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases horizontalTarget grid oldColumn oldTargetY fineColumn sameBlock
      nonexceptional sourceInterior with
    ⟨targetY, targetCoarse, targetInterior, connector⟩
  refine ⟨targetY, targetCoarse, targetInterior, ?_⟩
  exact sourceFamily.refineThrough
    (horizontalPort_present_of_interior sourceInterior) (path_symm connector)

/-- Vertical dual of `horizontalTargetFamily`. -/
theorem verticalTargetFamily
    (grid : Nat → Nat → Index) (oldTargetX oldRow fineRow : Nat)
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (sameBlock : oldRow / 2 = fineRow / 8)
    (nonexceptional :
      8 ≤ (grid (oldTargetX / 2) (oldRow / 2)).val)
    (sourceInterior : Signals.verticalInterior?
      (componentAt grid oldTargetX oldRow)
      (quadrantAt oldTargetX oldRow) ≠ none)
    (sourceFamily : CanonicalCycleAncestorWithinFamily grid
      (verticalPort grid oldTargetX oldRow)
      outerLevel outerBlockX outerBlockY family) :
    ∃ targetX,
      coarseCoordinate targetX = oldTargetX ∧
      Signals.verticalInterior?
        (componentAt (iterateRefine 2 grid) targetX fineRow)
        (quadrantAt targetX fineRow) ≠ none ∧
      CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
        (verticalPort (iterateRefine 2 grid) targetX fineRow)
        (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases verticalTarget grid oldTargetX oldRow fineRow sameBlock
      nonexceptional sourceInterior with
    ⟨targetX, targetCoarse, targetInterior, connector⟩
  refine ⟨targetX, targetCoarse, targetInterior, ?_⟩
  exact sourceFamily.refineThrough
    (verticalPort_present_of_interior sourceInterior) (path_symm connector)

end PairCoverSeamResidualDirectPathFamilyTargetLiftTransport
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
