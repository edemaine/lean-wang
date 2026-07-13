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
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorBridges
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
