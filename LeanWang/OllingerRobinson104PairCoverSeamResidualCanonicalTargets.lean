/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualCanonicalAncestorBridges

/-!
# Pure canonical targets for residual seam selection

These certificates separate finite coordinate choice from red-graph paths.
A target records a canonical cycle in the same even/odd hierarchy family as
the actual source ancestor.  The bridge library then supplies the even path
through their common outer cycle automatically.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualCanonicalTargets

open OrientedRedCycles RedCycles RedShadeCycles RedShadeGraph
  RedShadeCycleBridgeComposition
  PairCoverSeamResidualCycles PairCoverSeamResidualCycleBridges
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualCanonicalAncestorBridges

set_option maxRecDepth 20000

/-- Two levels belong to the same parity family below a common outer level. -/
def SameHierarchyFamily (outerLevel firstLevel secondLevel : Nat) : Prop :=
  (∃ firstDepth secondDepth,
    outerLevel = firstLevel + 2 * firstDepth ∧
      outerLevel = secondLevel + 2 * secondDepth) ∨
  (∃ firstDepth secondDepth,
    outerLevel = firstLevel + 2 * firstDepth + 1 ∧
      outerLevel = secondLevel + 2 * secondDepth + 1)

/-- Pure hierarchy and coordinate data for a row-separating canonical cycle. -/
def CanonicalRowTarget
    (outerLevel outerBlockX outerBlockY outerWest outerEast : Nat)
    (column boundary row ancestorLevel : Nat) : Prop :=
  ∃ level blockX blockY,
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    SameHierarchyFamily outerLevel ancestorLevel level ∧
    quarterWest outerWest <
      quarterWest (2 ^ level * (4 * blockX + 1)) ∧
    quarterWest (2 ^ level * (4 * blockX + 1)) <
      quarterEast outerEast ∧
    ((quarterSouth (2 ^ level * (4 * blockY + 1)) < row ∧
        row < quarterNorth (2 ^ level * (4 * blockY + 3))) ∨
      (quarterWest (2 ^ level * (4 * blockX + 1)) < column ∧
        column < quarterEast (2 ^ level * (4 * blockX + 3))) ∧
        PairCoverSeamPathSearch.StrictBetween row boundary
          (quarterSouth (2 ^ level * (4 * blockY + 1))) ∨
      (quarterWest (2 ^ level * (4 * blockX + 1)) < column ∧
        column < quarterEast (2 ^ level * (4 * blockX + 3))) ∧
        PairCoverSeamPathSearch.StrictBetween row boundary
          (quarterNorth (2 ^ level * (4 * blockY + 3))))

/-- Horizontal dual of `CanonicalRowTarget`. -/
def CanonicalColumnTarget
    (outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat)
    (boundary row column ancestorLevel : Nat) : Prop :=
  ∃ level blockX blockY,
    HierarchyAddressWithin outerLevel outerBlockX level blockX ∧
    HierarchyAddressWithin outerLevel outerBlockY level blockY ∧
    SameHierarchyFamily outerLevel ancestorLevel level ∧
    quarterSouth outerSouth <
      quarterSouth (2 ^ level * (4 * blockY + 1)) ∧
    quarterSouth (2 ^ level * (4 * blockY + 1)) <
      quarterNorth outerNorth ∧
    ((quarterWest (2 ^ level * (4 * blockX + 1)) < column ∧
        column < quarterEast (2 ^ level * (4 * blockX + 3))) ∨
      (quarterSouth (2 ^ level * (4 * blockY + 1)) < row ∧
        row < quarterNorth (2 ^ level * (4 * blockY + 3))) ∧
        PairCoverSeamPathSearch.StrictBetween column boundary
          (quarterWest (2 ^ level * (4 * blockX + 1))) ∨
      (quarterSouth (2 ^ level * (4 * blockY + 1)) < row ∧
        row < quarterNorth (2 ^ level * (4 * blockY + 3))) ∧
        PairCoverSeamPathSearch.StrictBetween column boundary
          (quarterEast (2 ^ level * (4 * blockX + 3))))

/-- Convert a pure canonical row target into the graph witness consumed by the
residual semantic proof. -/
theorem rowSeparatingCycle_of_target
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column boundary row : Nat}
    (ancestor : CanonicalCycleAncestorWithin
      (iterateRefine (outerLevel + 2) grid) source
      outerLevel outerBlockX outerBlockY)
    (sourceEq : source = PairCoverSeamShadePaths.horizontalPort
      (iterateRefine (outerLevel + 2) grid) column boundary)
    (target : ∀ ancestorLevel ancestorBlockX ancestorBlockY,
      HierarchyAddressWithin outerLevel outerBlockX
        ancestorLevel ancestorBlockX →
      HierarchyAddressWithin outerLevel outerBlockY
        ancestorLevel ancestorBlockY →
      CanonicalRowTarget outerLevel outerBlockX outerBlockY
        outerWest outerEast column boundary row ancestorLevel) :
    RowSeparatingCycle (iterateRefine (outerLevel + 2) grid)
      outerWest outerEast column boundary row := by
  rcases ancestor with ⟨ancestorLevel, ancestorBlockX, ancestorBlockY,
    ancestorXWithin, ancestorYWithin, ancestorCycle, entry,
    entryOnCycle, sourcePath⟩
  rcases target ancestorLevel ancestorBlockX ancestorBlockY
      ancestorXWithin ancestorYWithin with
    ⟨level, blockX, blockY, xWithin, yWithin, family,
    westInside, westInside', separation⟩
  have targetCycle := OrientedRedBoardTranslations.at_scale
    (iterateRefine (outerLevel - level) grid) level blockX blockY
  have levelLe : level ≤ outerLevel := xWithin.1
  have targetGridEq :
      iterateRefine (level + 2) (iterateRefine (outerLevel - level) grid) =
        iterateRefine (outerLevel + 2) grid := by
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  rw [targetGridEq] at targetCycle
  have bridge : EvenCycleBridge (iterateRefine (outerLevel + 2) grid)
      (2 ^ ancestorLevel * (4 * ancestorBlockX + 1))
      (2 ^ ancestorLevel * (4 * ancestorBlockX + 3))
      (2 ^ ancestorLevel * (4 * ancestorBlockY + 1))
      (2 ^ ancestorLevel * (4 * ancestorBlockY + 3))
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) := by
    rcases family with family | family
    · rcases family with
        ⟨ancestorDepth, targetDepth, ancestorLevelEq, targetLevelEq⟩
      exact evenFamilyBridgeWithin ancestorLevelEq targetLevelEq
        ancestorXWithin ancestorYWithin xWithin yWithin
    · rcases family with
        ⟨ancestorDepth, targetDepth, ancestorLevelEq, targetLevelEq⟩
      exact oddFamilyBridgeWithin ancestorLevelEq targetLevelEq
        ancestorXWithin ancestorYWithin xWithin yWithin
  subst source
  exact rowSeparatingCycle_of_bridge ancestorCycle targetCycle
    entryOnCycle sourcePath bridge westInside westInside' separation

/-- Convert a pure canonical column target into the graph witness consumed by
the residual semantic proof. -/
theorem columnSeparatingCycle_of_target
    {grid : Nat → Nat → Index} {source : Port}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {boundary row column : Nat}
    (ancestor : CanonicalCycleAncestorWithin
      (iterateRefine (outerLevel + 2) grid) source
      outerLevel outerBlockX outerBlockY)
    (sourceEq : source = PairCoverSeamShadePaths.verticalPort
      (iterateRefine (outerLevel + 2) grid) boundary row)
    (target : ∀ ancestorLevel ancestorBlockX ancestorBlockY,
      HierarchyAddressWithin outerLevel outerBlockX
        ancestorLevel ancestorBlockX →
      HierarchyAddressWithin outerLevel outerBlockY
        ancestorLevel ancestorBlockY →
      CanonicalColumnTarget outerLevel outerBlockX outerBlockY
        outerSouth outerNorth boundary row column ancestorLevel) :
    ColumnSeparatingCycle (iterateRefine (outerLevel + 2) grid)
      outerSouth outerNorth boundary row column := by
  rcases ancestor with ⟨ancestorLevel, ancestorBlockX, ancestorBlockY,
    ancestorXWithin, ancestorYWithin, ancestorCycle, entry,
    entryOnCycle, sourcePath⟩
  rcases target ancestorLevel ancestorBlockX ancestorBlockY
      ancestorXWithin ancestorYWithin with
    ⟨level, blockX, blockY, xWithin, yWithin, family,
    southInside, southInside', separation⟩
  have targetCycle := OrientedRedBoardTranslations.at_scale
    (iterateRefine (outerLevel - level) grid) level blockX blockY
  have levelLe : level ≤ outerLevel := xWithin.1
  have targetGridEq :
      iterateRefine (level + 2) (iterateRefine (outerLevel - level) grid) =
        iterateRefine (outerLevel + 2) grid := by
    rw [PlaneRedBoards.iterateRefine_add]
    congr 1
    omega
  rw [targetGridEq] at targetCycle
  have bridge : EvenCycleBridge (iterateRefine (outerLevel + 2) grid)
      (2 ^ ancestorLevel * (4 * ancestorBlockX + 1))
      (2 ^ ancestorLevel * (4 * ancestorBlockX + 3))
      (2 ^ ancestorLevel * (4 * ancestorBlockY + 1))
      (2 ^ ancestorLevel * (4 * ancestorBlockY + 3))
      (2 ^ level * (4 * blockX + 1))
      (2 ^ level * (4 * blockX + 3))
      (2 ^ level * (4 * blockY + 1))
      (2 ^ level * (4 * blockY + 3)) := by
    rcases family with family | family
    · rcases family with
        ⟨ancestorDepth, targetDepth, ancestorLevelEq, targetLevelEq⟩
      exact evenFamilyBridgeWithin ancestorLevelEq targetLevelEq
        ancestorXWithin ancestorYWithin xWithin yWithin
    · rcases family with
        ⟨ancestorDepth, targetDepth, ancestorLevelEq, targetLevelEq⟩
      exact oddFamilyBridgeWithin ancestorLevelEq targetLevelEq
        ancestorXWithin ancestorYWithin xWithin yWithin
  subst source
  exact columnSeparatingCycle_of_bridge ancestorCycle targetCycle
    entryOnCycle sourcePath bridge southInside southInside' separation

end PairCoverSeamResidualCanonicalTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
