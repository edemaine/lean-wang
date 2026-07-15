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

end PairCoverSeamResidualDirectPathCanonicalSideTargets
end LeanWang.OllingerRobinson.Figure13Layers.Closed104
