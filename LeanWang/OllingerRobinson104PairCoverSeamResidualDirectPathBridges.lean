/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPaths
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBridges

/-!
# Same-family hierarchy bridges for direct residual paths

Every canonical source ancestor lies an even or odd number of hierarchy levels
below its enclosing board.  Two ancestors in the same family are connected by
an even bridge.  Composing their even source routes with that bridge gives the
direct source-to-target path needed by the residual seam certificate.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathBridges

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph RedShadePaths
  RedShadeGraphBoards RedShadeGraphRefinement
  RedShadeCycleConnectivity RedShadeCycleBridgeComposition
  PairCoverSeamPathSearch PairCoverSeamShadePaths
  PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorBridges
  ShadedFreeLinePatternRefinement
  Signals.FreeCellLocal

set_option maxRecDepth 20000

inductive HierarchyFamily where
  | even
  | odd
deriving DecidableEq

/-- A level belongs to one of the two parity families below an outer level. -/
def InHierarchyFamily (outerLevel level : Nat) : HierarchyFamily → Prop
  | .even => ∃ depth, outerLevel = level + 2 * depth
  | .odd => ∃ depth, outerLevel = level + 2 * depth + 1

/-- A localized canonical ancestor retaining its hierarchy parity family. -/
def CanonicalCycleAncestorWithinFamily
    (grid : Nat → Nat → Index) (source : Port)
    (outerLevel outerBlockX outerBlockY : Nat)
    (family : HierarchyFamily) : Prop :=
  ∃ level blockX blockY,
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    InHierarchyFamily outerLevel level family ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- A created source ancestor retaining both its hierarchy family and the fact
that parity normalization stopped at level zero or one. -/
def LowCanonicalCycleAncestorWithinFamily
    (grid : Nat → Nat → Index) (source : Port)
    (outerLevel outerBlockX outerBlockY : Nat)
    (family : HierarchyFamily) : Prop :=
  ∃ level blockX blockY,
    level ≤ 1 ∧
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    InHierarchyFamily outerLevel level family ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- An exact low ancestor retaining both the audited source macrocell and its
hierarchy family. -/
def ExactLowCanonicalCycleAncestorWithinFamily
    (grid : Nat → Nat → Index) (source : Port)
    (sourceBlockX sourceBlockY : Nat)
    (outerLevel outerBlockX outerBlockY : Nat)
    (family : HierarchyFamily) : Prop :=
  ∃ level blockX blockY,
    ((level = 0 ∧ blockX = sourceBlockX ∧ blockY = sourceBlockY) ∨
      (level = 1 ∧ blockX = sourceBlockX / 2 ∧
        blockY = sourceBlockY / 2)) ∧
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    InHierarchyFamily outerLevel level family ∧
    CycleOn grid
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) ∧
    ∃ entry,
      OnCycle
        (2 ^ level * (4 * blockX + 1))
        (2 ^ level * (4 * blockX + 3))
        (2 ^ level * (4 * blockY + 1))
        (2 ^ level * (4 * blockY + 3)) entry ∧
      Path grid source entry false

/-- Forget the exact audited macrocell while retaining the low ancestor and
its family. -/
theorem ExactLowCanonicalCycleAncestorWithinFamily.toLowFamily
    {grid : Nat → Nat → Index} {source : Port}
    {sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY : Nat}
    {family : HierarchyFamily}
    (ancestor : ExactLowCanonicalCycleAncestorWithinFamily grid source
      sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY family) :
    LowCanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, exactBlock, xWithin, yWithin, inFamily,
      cycle, entry, entryOnCycle, path⟩
  refine ⟨level, blockX, blockY, ?_, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, path⟩
  rcases exactBlock with exactBlock | exactBlock <;> omega

/-- Every exact low ancestor belongs to one hierarchy family without changing
its witnessed level or blocks. -/
theorem ExactLowCanonicalCycleAncestorWithin.exists_family
    {grid : Nat → Nat → Index} {source : Port}
    {sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : ExactLowCanonicalCycleAncestorWithin grid source
      sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY) :
    ∃ family, ExactLowCanonicalCycleAncestorWithinFamily grid source
      sourceBlockX sourceBlockY outerLevel outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, exactBlock, xWithin, yWithin,
      cycle, entry, entryOnCycle, path⟩
  let difference := outerLevel - level
  have levelLe : level ≤ outerLevel := xWithin.1
  have modLt : difference % 2 < 2 := Nat.mod_lt _ (by decide)
  have decompose := Nat.mod_add_div difference 2
  by_cases even : difference % 2 = 0
  · refine ⟨.even, level, blockX, blockY, exactBlock, xWithin, yWithin,
      ?_, cycle, entry, entryOnCycle, path⟩
    refine ⟨difference / 2, ?_⟩
    dsimp [difference] at decompose ⊢
    omega
  · have odd : difference % 2 = 1 := by omega
    refine ⟨.odd, level, blockX, blockY, exactBlock, xWithin, yWithin,
      ?_, cycle, entry, entryOnCycle, path⟩
    refine ⟨difference / 2, ?_⟩
    dsimp [difference] at decompose ⊢
    omega

/-- Forget the low-level bound while retaining the source family. -/
theorem LowCanonicalCycleAncestorWithinFamily.toAncestorFamily
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (ancestor : LowCanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family) :
    CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, _low, xWithin, yWithin, inFamily,
      cycle, entry, entryOnCycle, path⟩
  exact ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, path⟩

/-- Every low created ancestor belongs to one of the two hierarchy families,
without changing its witnessed level or block. -/
theorem LowCanonicalCycleAncestorWithin.exists_family
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : LowCanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY) :
    ∃ family, LowCanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, low, xWithin, yWithin,
      cycle, entry, entryOnCycle, path⟩
  let difference := outerLevel - level
  have levelLe : level ≤ outerLevel := xWithin.1
  have modLt : difference % 2 < 2 := Nat.mod_lt _ (by decide)
  have decompose := Nat.mod_add_div difference 2
  by_cases even : difference % 2 = 0
  · refine ⟨.even, level, blockX, blockY, low, xWithin, yWithin, ?_,
      cycle, entry, entryOnCycle, path⟩
    refine ⟨difference / 2, ?_⟩
    dsimp [difference] at decompose ⊢
    omega
  · have odd : difference % 2 = 1 := by omega
    refine ⟨.odd, level, blockX, blockY, low, xWithin, yWithin, ?_,
      cycle, entry, entryOnCycle, path⟩
    refine ⟨difference / 2, ?_⟩
    dsimp [difference] at decompose ⊢
    omega

/-- Every canonical descendant named by a hierarchy level is present in the
common outer refinement. -/
theorem cycleAtLevelWithin
    (root : Nat → Nat → Index) {outerLevel level blockX blockY : Nat}
    (levelLe : level ≤ outerLevel) :
    CycleOn (iterateRefine (outerLevel + 2) root)
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) := by
  have cycle := OrientedRedBoardTranslations.at_scale
    (iterateRefine (outerLevel - level) root) level blockX blockY
  rw [PlaneRedBoards.iterateRefine_add] at cycle
  have levels : level + 2 + (outerLevel - level) = outerLevel + 2 := by
    omega
  rwa [levels] at cycle

theorem CanonicalCycleAncestorWithinFamily.toAncestor
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (ancestor : CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family) :
    CanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY := by
  rcases ancestor with
    ⟨level, blockX, blockY, xWithin, yWithin, _, cycle,
      entry, entryOnCycle, path⟩
  exact ⟨level, blockX, blockY, xWithin, yWithin,
    cycle, entry, entryOnCycle, path⟩

/-- Prepending an even route preserves the localized hierarchy family. -/
theorem CanonicalCycleAncestorWithinFamily.of_evenPath
    {grid : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (ancestor : CanonicalCycleAncestorWithinFamily grid target
      outerLevel outerBlockX outerBlockY family)
    (path : Path grid source target false) :
    CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
      cycle, entry, entryOnCycle, tail⟩
  exact ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
    cycle, entry, entryOnCycle, by simpa using Path.trans path tail⟩

private theorem InHierarchyFamily.refine
    {outerLevel level : Nat} {family : HierarchyFamily}
    (inFamily : InHierarchyFamily outerLevel level family) :
    InHierarchyFamily (outerLevel + 2) (level + 2) family := by
  cases family with
  | even =>
      rcases inFamily with ⟨depth, levelEq⟩
      exact ⟨depth, by omega⟩
  | odd =>
      rcases inFamily with ⟨depth, levelEq⟩
      exact ⟨depth, by omega⟩

/-- Two substitutions preserve a localized ancestor's hierarchy family on the
literal sparse copy of its source. -/
theorem CanonicalCycleAncestorWithinFamily.refineSparse
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (ancestor : CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family)
    (sourceLive : portPresent grid source = true) :
    CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid)
      (sparsePort source) (outerLevel + 2) outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, xWithin, yWithin, inFamily,
      cycle, entry, entryOnCycle, path⟩
  have xWithin' : HierarchyAddressWithin
      (outerLevel + 2) outerBlockX (level + 2) blockX := by
    rcases xWithin with ⟨levelLe, blockWithin⟩
    constructor
    · omega
    · have exponent : outerLevel + 2 - (level + 2) =
          outerLevel - level := by omega
      rwa [exponent]
  have yWithin' : HierarchyAddressWithin
      (outerLevel + 2) outerBlockY (level + 2) blockY := by
    rcases yWithin with ⟨levelLe, blockWithin⟩
    constructor
    · omega
    · have exponent : outerLevel + 2 - (level + 2) =
          outerLevel - level := by omega
      rwa [exponent]
  have fineCycle := cycle.iterateRefine 2
  have entryLive := portPresent_of_onCycle cycle entryOnCycle
  have hscale : 2 ^ (level + 2) = 4 * 2 ^ level := by
    rw [pow_add]
    norm_num
    ac_rfl
  refine ⟨level + 2, blockX, blockY, xWithin', yWithin', inFamily.refine,
    ?_, sparsePort entry, ?_, ?_⟩
  · simpa [RedCycles.doubleN_eq, hscale, Nat.mul_assoc] using fineCycle
  · simpa [hscale, Nat.mul_assoc] using onCycle_sparse entryOnCycle
  · exact path_refine_sparse path sourceLive entryLive

/-- An even fine-grid connector to a sparse predecessor transports that
predecessor's localized hierarchy family. -/
theorem CanonicalCycleAncestorWithinFamily.refineThrough
    {grid : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat} {family : HierarchyFamily}
    (ancestor : CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family)
    (sourceLive : portPresent grid source = true)
    (connector : Path (iterateRefine 2 grid)
      target (sparsePort source) false) :
    CanonicalCycleAncestorWithinFamily (iterateRefine 2 grid) target
      (outerLevel + 2) outerBlockX outerBlockY family :=
  (ancestor.refineSparse sourceLive).of_evenPath connector

/-- Every localized ancestor belongs to exactly one of the two families; only
existence is needed by target selection. -/
theorem CanonicalCycleAncestorWithin.exists_family
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    (ancestor : CanonicalCycleAncestorWithin grid source
      outerLevel outerBlockX outerBlockY) :
    ∃ family, CanonicalCycleAncestorWithinFamily grid source
      outerLevel outerBlockX outerBlockY family := by
  rcases ancestor with
    ⟨level, blockX, blockY, xWithin, yWithin, cycle,
      entry, entryOnCycle, path⟩
  let difference := outerLevel - level
  have levelLe : level ≤ outerLevel := xWithin.1
  have modLt : difference % 2 < 2 := Nat.mod_lt _ (by decide)
  have decompose := Nat.mod_add_div difference 2
  by_cases even : difference % 2 = 0
  · refine ⟨.even, level, blockX, blockY, xWithin, yWithin, ?_,
      cycle, entry, entryOnCycle, path⟩
    refine ⟨difference / 2, ?_⟩
    dsimp [difference] at decompose ⊢
    omega
  · have odd : difference % 2 = 1 := by omega
    refine ⟨.odd, level, blockX, blockY, xWithin, yWithin, ?_,
      cycle, entry, entryOnCycle, path⟩
    refine ⟨difference / 2, ?_⟩
    dsimp [difference] at decompose ⊢
    omega

/-- Sources whose localized ancestors have the same hierarchy family are
connected by an even path. -/
theorem evenPath_of_sameFamilyAncestors
    {root : Nat → Nat → Index} {source target : Port}
    {outerLevel outerBlockX outerBlockY : Nat}
    {family : HierarchyFamily}
    (sourceAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) source
      outerLevel outerBlockX outerBlockY family)
    (targetAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) target
      outerLevel outerBlockX outerBlockY family) :
    Path (iterateRefine (outerLevel + 2) root) source target false := by
  rcases sourceAncestor with
    ⟨sourceLevel, sourceBlockX, sourceBlockY,
      sourceXWithin, sourceYWithin, sourceFamily, sourceCycle,
      sourceEntry, sourceEntryOnCycle, sourcePath⟩
  rcases targetAncestor with
    ⟨targetLevel, targetBlockX, targetBlockY,
      targetXWithin, targetYWithin, targetFamily, targetCycle,
      targetEntry, targetEntryOnCycle, targetPath⟩
  have bridge : EvenCycleBridge (iterateRefine (outerLevel + 2) root)
      (2 ^ sourceLevel * (4 * sourceBlockX + 1))
      (2 ^ sourceLevel * (4 * sourceBlockX + 3))
      (2 ^ sourceLevel * (4 * sourceBlockY + 1))
      (2 ^ sourceLevel * (4 * sourceBlockY + 3))
      (2 ^ targetLevel * (4 * targetBlockX + 1))
      (2 ^ targetLevel * (4 * targetBlockX + 3))
      (2 ^ targetLevel * (4 * targetBlockY + 1))
      (2 ^ targetLevel * (4 * targetBlockY + 3)) := by
    cases family with
    | even =>
        rcases sourceFamily with ⟨sourceDepth, sourceLevelEq⟩
        rcases targetFamily with ⟨targetDepth, targetLevelEq⟩
        exact evenFamilyBridgeWithin sourceLevelEq targetLevelEq
          sourceXWithin sourceYWithin targetXWithin targetYWithin
    | odd =>
        rcases sourceFamily with ⟨sourceDepth, sourceLevelEq⟩
        rcases targetFamily with ⟨targetDepth, targetLevelEq⟩
        exact oddFamilyBridgeWithin sourceLevelEq targetLevelEq
          sourceXWithin sourceYWithin targetXWithin targetYWithin
  rcases bridge with
    ⟨sourceExit, targetExit, sourceExitOnCycle,
      targetExitOnCycle, bridgePath⟩
  have sourceAround := onCycle_connected sourceCycle
    sourceEntryOnCycle sourceExitOnCycle
  have targetAround := onCycle_connected targetCycle
    targetExitOnCycle targetEntryOnCycle
  simpa [Bool.xor_assoc] using
    Path.trans sourcePath
      (Path.trans sourceAround
        (Path.trans bridgePath
          (Path.trans targetAround (path_symm targetPath))))

/-- A same-family live vertical target on the query row supplies the crossing
alternative of a vertical seam path. -/
theorem verticalSeamPath_of_sameFamilyTarget
    {root : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary targetX : Nat} {family : HierarchyFamily}
    (sourceEq : source = horizontalPort
      (iterateRefine (outerLevel + 2) root) column boundary)
    (sourceAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) source
      outerLevel outerBlockX outerBlockY family)
    (targetAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)
      outerLevel outerBlockX outerBlockY family)
    (targetWest : quarterWest outerWest < targetX)
    (targetEast : targetX < quarterEast outerEast)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row) ≠ none) :
    VerticalSeamPath (iterateRefine (outerLevel + 2) root)
      outerWest outerEast column row boundary := by
  subst source
  exact Or.inl ⟨targetX, targetWest, targetEast, interior,
    evenPath_of_sameFamilyAncestors sourceAncestor targetAncestor⟩

/-- Horizontal dual of `verticalSeamPath_of_sameFamilyTarget`. -/
theorem horizontalSeamPath_of_sameFamilyTarget
    {root : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary targetY : Nat} {family : HierarchyFamily}
    (sourceEq : source = verticalPort
      (iterateRefine (outerLevel + 2) root) boundary row)
    (sourceAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) source
      outerLevel outerBlockX outerBlockY family)
    (targetAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)
      outerLevel outerBlockX outerBlockY family)
    (targetSouth : quarterSouth outerSouth < targetY)
    (targetNorth : targetY < quarterNorth outerNorth)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY) ≠ none) :
    HorizontalSeamPath (iterateRefine (outerLevel + 2) root)
      outerSouth outerNorth row column boundary := by
  subst source
  exact Or.inl ⟨targetY, targetSouth, targetNorth, interior,
    evenPath_of_sameFamilyAncestors sourceAncestor targetAncestor⟩

/-- A same-family horizontal target strictly between the source and query row
supplies the second alternative of a vertical seam path. -/
theorem verticalSeamPath_of_sameFamilyBetweenTarget
    {root : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary targetY : Nat} {family : HierarchyFamily}
    (sourceEq : source = horizontalPort
      (iterateRefine (outerLevel + 2) root) column boundary)
    (sourceAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) source
      outerLevel outerBlockX outerBlockY family)
    (targetAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (horizontalPort (iterateRefine (outerLevel + 2) root) column targetY)
      outerLevel outerBlockX outerBlockY family)
    (between : StrictBetween row boundary targetY)
    (interior : Signals.horizontalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) column targetY)
      (quadrantAt column targetY) ≠ none) :
    VerticalSeamPath (iterateRefine (outerLevel + 2) root)
      outerWest outerEast column row boundary := by
  subst source
  exact Or.inr ⟨targetY, between, interior,
    evenPath_of_sameFamilyAncestors sourceAncestor targetAncestor⟩

/-- Horizontal dual of `verticalSeamPath_of_sameFamilyBetweenTarget`. -/
theorem horizontalSeamPath_of_sameFamilyBetweenTarget
    {root : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary targetX : Nat} {family : HierarchyFamily}
    (sourceEq : source = verticalPort
      (iterateRefine (outerLevel + 2) root) boundary row)
    (sourceAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root) source
      outerLevel outerBlockX outerBlockY family)
    (targetAncestor : CanonicalCycleAncestorWithinFamily
      (iterateRefine (outerLevel + 2) root)
      (verticalPort (iterateRefine (outerLevel + 2) root) targetX row)
      outerLevel outerBlockX outerBlockY family)
    (between : StrictBetween column boundary targetX)
    (interior : Signals.verticalInterior?
      (componentAt (iterateRefine (outerLevel + 2) root) targetX row)
      (quadrantAt targetX row) ≠ none) :
    HorizontalSeamPath (iterateRefine (outerLevel + 2) root)
      outerSouth outerNorth row column boundary := by
  subst source
  exact Or.inr ⟨targetX, between, interior,
    evenPath_of_sameFamilyAncestors sourceAncestor targetAncestor⟩

end PairCoverSeamResidualDirectPathBridges
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
