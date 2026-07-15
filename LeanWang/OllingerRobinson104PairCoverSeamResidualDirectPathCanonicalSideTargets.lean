/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathCornerTargets
import LeanWang.OllingerRobinson104PairCoverSeamResidualDirectPathTargets

/-!
# Canonical side choices as residual family targets

The hierarchy arithmetic only needs to choose a canonical descendant whose
closed west or south side crosses the query, or whose corresponding side lies
strictly between the query and source.  The corner-aware target lemmas turn
that coordinate data into the exact same-family target interface.
-/

namespace LeanWang.OllingerRobinson.Figure13Layers.Closed104
namespace PairCoverSeamResidualDirectPathCanonicalSideTargets

open RedCycles RedShadeCycles PairCoverSeamPathSearch
  PairCoverSeamResidualCanonicalAncestors
  PairCoverSeamResidualDirectPathBridges
  PairCoverSeamResidualDirectPathCornerTargets
  PairCoverSeamResidualDirectPathTargets Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A canonical closed west side crossing the query row, or a canonical closed
south side strictly between the source and query, supplies a row target. -/
theorem RowFamilyTarget.ofCanonicalSides
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (targetWest : quarterWest outerWest <
      quarterWest (2 ^ level * (4 * blockX + 1)))
    (targetEast : quarterWest (2 ^ level * (4 * blockX + 1)) <
      quarterEast outerEast)
    (separates :
      (quarterSouth (2 ^ level * (4 * blockY + 1)) ≤ row ∧
          row ≤ quarterNorth (2 ^ level * (4 * blockY + 3))) ∨
      ((quarterWest (2 ^ level * (4 * blockX + 1)) ≤ column ∧
          column ≤ quarterEast (2 ^ level * (4 * blockX + 3))) ∧
        StrictBetween row boundary
          (quarterSouth (2 ^ level * (4 * blockY + 1))))) :
    RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family := by
  have cycle := cycleAtLevelWithin root (blockX := blockX) (blockY := blockY)
    xWithin.1
  rcases separates with crosses | between
  · left
    rcases verticalWest xWithin yWithin inFamily cycle
        crosses.1 crosses.2 with ⟨ancestor, interior⟩
    exact ⟨quarterWest (2 ^ level * (4 * blockX + 1)),
      targetWest, targetEast, interior, ancestor⟩
  · right
    rcases horizontalSouth xWithin yWithin inFamily cycle
        between.1.1 between.1.2 with ⟨ancestor, interior⟩
    exact ⟨quarterSouth (2 ^ level * (4 * blockY + 1)),
      between.2, interior, ancestor⟩

/-- Horizontal dual of `RowFamilyTarget.ofCanonicalSides`. -/
theorem ColumnFamilyTarget.ofCanonicalSides
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (targetSouth : quarterSouth outerSouth <
      quarterSouth (2 ^ level * (4 * blockY + 1)))
    (targetNorth : quarterSouth (2 ^ level * (4 * blockY + 1)) <
      quarterNorth outerNorth)
    (separates :
      (quarterWest (2 ^ level * (4 * blockX + 1)) ≤ column ∧
        column ≤ quarterEast (2 ^ level * (4 * blockX + 3))) ∨
      ((quarterSouth (2 ^ level * (4 * blockY + 1)) ≤ row ∧
          row ≤ quarterNorth (2 ^ level * (4 * blockY + 3))) ∧
        StrictBetween column boundary
          (quarterWest (2 ^ level * (4 * blockX + 1))))) :
    ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family := by
  have cycle := cycleAtLevelWithin root (blockX := blockX) (blockY := blockY)
    xWithin.1
  rcases separates with crosses | between
  · left
    rcases horizontalSouth xWithin yWithin inFamily cycle
        crosses.1 crosses.2 with ⟨ancestor, interior⟩
    exact ⟨quarterSouth (2 ^ level * (4 * blockY + 1)),
      targetSouth, targetNorth, interior, ancestor⟩
  · right
    rcases verticalWest xWithin yWithin inFamily cycle
        between.1.1 between.1.2 with ⟨ancestor, interior⟩
    exact ⟨quarterWest (2 ^ level * (4 * blockX + 1)),
      between.2, interior, ancestor⟩

/-- Any of the four closed sides of a canonical descendant supplies a row
target when it crosses the query or separates the query from the source. -/
theorem RowFamilyTarget.ofAllCanonicalSides
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerWest outerEast : Nat}
    {column row boundary level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (separates :
      ((quarterWest outerWest <
            quarterWest (2 ^ level * (4 * blockX + 1)) ∧
          quarterWest (2 ^ level * (4 * blockX + 1)) <
            quarterEast outerEast) ∧
        (quarterSouth (2 ^ level * (4 * blockY + 1)) ≤ row ∧
          row ≤ quarterNorth (2 ^ level * (4 * blockY + 3)))) ∨
      ((quarterWest outerWest <
            quarterEast (2 ^ level * (4 * blockX + 3)) ∧
          quarterEast (2 ^ level * (4 * blockX + 3)) <
            quarterEast outerEast) ∧
        (quarterSouth (2 ^ level * (4 * blockY + 1)) ≤ row ∧
          row ≤ quarterNorth (2 ^ level * (4 * blockY + 3)))) ∨
      ((quarterWest (2 ^ level * (4 * blockX + 1)) ≤ column ∧
          column ≤ quarterEast (2 ^ level * (4 * blockX + 3))) ∧
        StrictBetween row boundary
          (quarterSouth (2 ^ level * (4 * blockY + 1)))) ∨
      ((quarterWest (2 ^ level * (4 * blockX + 1)) ≤ column ∧
          column ≤ quarterEast (2 ^ level * (4 * blockX + 3))) ∧
        StrictBetween row boundary
          (quarterNorth (2 ^ level * (4 * blockY + 3))))) :
    RowFamilyTarget root outerLevel outerBlockX outerBlockY
      outerWest outerEast column row boundary family := by
  have cycle := cycleAtLevelWithin root (blockX := blockX) (blockY := blockY)
    xWithin.1
  rcases separates with westCrosses | eastCrosses | southBetween | northBetween
  · left
    rcases verticalWest xWithin yWithin inFamily cycle
        westCrosses.2.1 westCrosses.2.2 with ⟨ancestor, interior⟩
    exact ⟨quarterWest (2 ^ level * (4 * blockX + 1)),
      westCrosses.1.1, westCrosses.1.2, interior, ancestor⟩
  · left
    rcases verticalEast xWithin yWithin inFamily cycle
        eastCrosses.2.1 eastCrosses.2.2 with ⟨ancestor, interior⟩
    exact ⟨quarterEast (2 ^ level * (4 * blockX + 3)),
      eastCrosses.1.1, eastCrosses.1.2, interior, ancestor⟩
  · right
    rcases horizontalSouth xWithin yWithin inFamily cycle
        southBetween.1.1 southBetween.1.2 with ⟨ancestor, interior⟩
    exact ⟨quarterSouth (2 ^ level * (4 * blockY + 1)),
      southBetween.2, interior, ancestor⟩
  · right
    rcases horizontalNorth xWithin yWithin inFamily cycle
        northBetween.1.1 northBetween.1.2 with ⟨ancestor, interior⟩
    exact ⟨quarterNorth (2 ^ level * (4 * blockY + 3)),
      northBetween.2, interior, ancestor⟩

/-- Horizontal dual of `RowFamilyTarget.ofAllCanonicalSides`. -/
theorem ColumnFamilyTarget.ofAllCanonicalSides
    {root : Nat → Nat → Index}
    {outerLevel outerBlockX outerBlockY outerSouth outerNorth : Nat}
    {row column boundary level blockX blockY : Nat}
    {family : HierarchyFamily}
    (xWithin : HierarchyAddressWithin outerLevel outerBlockX level blockX)
    (yWithin : HierarchyAddressWithin outerLevel outerBlockY level blockY)
    (inFamily : InHierarchyFamily outerLevel level family)
    (separates :
      ((quarterSouth outerSouth <
            quarterSouth (2 ^ level * (4 * blockY + 1)) ∧
          quarterSouth (2 ^ level * (4 * blockY + 1)) <
            quarterNorth outerNorth) ∧
        (quarterWest (2 ^ level * (4 * blockX + 1)) ≤ column ∧
          column ≤ quarterEast (2 ^ level * (4 * blockX + 3)))) ∨
      ((quarterSouth outerSouth <
            quarterNorth (2 ^ level * (4 * blockY + 3)) ∧
          quarterNorth (2 ^ level * (4 * blockY + 3)) <
            quarterNorth outerNorth) ∧
        (quarterWest (2 ^ level * (4 * blockX + 1)) ≤ column ∧
          column ≤ quarterEast (2 ^ level * (4 * blockX + 3)))) ∨
      ((quarterSouth (2 ^ level * (4 * blockY + 1)) ≤ row ∧
          row ≤ quarterNorth (2 ^ level * (4 * blockY + 3))) ∧
        StrictBetween column boundary
          (quarterWest (2 ^ level * (4 * blockX + 1)))) ∨
      ((quarterSouth (2 ^ level * (4 * blockY + 1)) ≤ row ∧
          row ≤ quarterNorth (2 ^ level * (4 * blockY + 3))) ∧
        StrictBetween column boundary
          (quarterEast (2 ^ level * (4 * blockX + 3))))) :
    ColumnFamilyTarget root outerLevel outerBlockX outerBlockY
      outerSouth outerNorth row column boundary family := by
  have cycle := cycleAtLevelWithin root (blockX := blockX) (blockY := blockY)
    xWithin.1
  rcases separates with southCrosses | northCrosses | westBetween | eastBetween
  · left
    rcases horizontalSouth xWithin yWithin inFamily cycle
        southCrosses.2.1 southCrosses.2.2 with ⟨ancestor, interior⟩
    exact ⟨quarterSouth (2 ^ level * (4 * blockY + 1)),
      southCrosses.1.1, southCrosses.1.2, interior, ancestor⟩
  · left
    rcases horizontalNorth xWithin yWithin inFamily cycle
        northCrosses.2.1 northCrosses.2.2 with ⟨ancestor, interior⟩
    exact ⟨quarterNorth (2 ^ level * (4 * blockY + 3)),
      northCrosses.1.1, northCrosses.1.2, interior, ancestor⟩
  · right
    rcases verticalWest xWithin yWithin inFamily cycle
        westBetween.1.1 westBetween.1.2 with ⟨ancestor, interior⟩
    exact ⟨quarterWest (2 ^ level * (4 * blockX + 1)),
      westBetween.2, interior, ancestor⟩
  · right
    rcases verticalEast xWithin yWithin inFamily cycle
        eastBetween.1.1 eastBetween.1.2 with ⟨ancestor, interior⟩
    exact ⟨quarterEast (2 ^ level * (4 * blockX + 3)),
      eastBetween.2, interior, ancestor⟩

end PairCoverSeamResidualDirectPathCanonicalSideTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
